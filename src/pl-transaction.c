/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2020-2024, University of Amsterdam
			      VU University Amsterdam
			      CWI, Amsterdam
			      SWI-Prolog Solutions b.v.
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

#include "pl-incl.h"
#include "pl-transaction.h"
#include "pl-event.h"
#include "pl-dbref.h"
#include "pl-tabling.h"
#include "pl-proc.h"
#include "pl-util.h"
#include "pl-pro.h"
#include "pl-wam.h"
#include "pl-fli.h"
#include "pl-gc.h"
#include "pl-attvar.h"

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
This module implements _transactions_, notably _isolating_ transactions.
This reuses most of the visibility stuff we need anyway for the _logical
updates semantics_ that  dictate  that  a   running  goal  on  a dynamic
predicate does not see changes to the predicate.

Transactions take this a step further:

  - The generation space 1..GEN_TRANSACTION_BASE is used for _globally_
    visible data.
  - The remainder is separated in 2^31 segments of 2^32 generations, as
    defined by GEN_TRANSACTION_SIZE (2^32).
  - A thread starting a transaction reserves as space starting at
    GEN_TRANSACTION_BASE+TID*GEN_TRANSACTION_SIZE and sets its
    LD->transaction.generation to the base.
  - setGenerationFrame() sets the frame generation to the transaction
    (if active) or the global generation.

Clause updates are handles as follows inside a transaction:

  - The clause is added to the LD->transaction.clauses table, where
    the value is GEN_ASSERTA or GEN_ASSERTZ or the local offset of the
    deleted generation (gen-LD->transaction.gen_base). - If the clause
    was retracted, clause.tr_erased_no is incremented.

A clause is visible iff

  - Its it is visible in the frame.generation.  In a transaction, this
    means it is created inside the transaction.
  - If we are in a transaction (gen >= GEN_TRANSACTION_BASE) and the
    clause was visible in the transaction start generation *and* the
    clause was not retracted in this transaction, it is visible.  The
    latter is the case if `clause.tr_erased_no > 0`, the clause is in
    our LD->transaction.clauses table at a generation smaller than the
    current.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */


typedef uintptr_t tr_gen_t;

/* Avoid conflict with HTABLE_TOMBSTONE and HTABLE_SENTINEL */
#define GEN_ASSERTA		((tr_gen_t)(void*)-3)
#define GEN_ASSERTZ		((tr_gen_t)(void*)-4)
#define GEN_NESTED_RETRACT	((tr_gen_t)(void*)-5)

#define IS_ASSERT_GEN(g) ((g)==GEN_ASSERTA||(g)==GEN_ASSERTZ)

typedef struct tr_stack
{ struct tr_stack  *parent;		/* parent transaction */
  gen_t		    gen_nest;		/* Saved nesting generation */
  gen_t             generation;		/* Parent generation */
  TablePW	    clauses;		/* Parent changed clauses */
  TablePW	    predicates;		/* Parent changed predicates */
  struct tbl_trail *table_trail;	/* Parent changes to tables */
  term_t	    id;			/* Parent goal */
  unsigned int	    flags;		/* TR_* flags */
  uint64_t	    snapshots;		/* Snapshots made before the start */
} tr_stack;

static void
tr_free_clause_symbol(table_key_t k, table_value_t v)
{ Clause cl = val2ptr(k);
  (void)v;

  release_clause(cl);
}

#define tr_clause_table(_) LDFUNC(tr_clause_table, _)
static TablePW
tr_clause_table(DECL_LD)
{ TablePW t;

  if ( !(t=LD->transaction.clauses) )
  { t = newHTablePW(16);
    t->free_symbol = tr_free_clause_symbol;
    LD->transaction.clauses = t;
  }

  return t;
}

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
This distinguishes three cases.

  - If we retract a globally visible clause we may need to commit and we
    need to know the generation at which we retracted the clause.

  - If the clause was added in an outer transaction we can update
    the generation and put it into our table such that we can undo
    the generation update (discard) or retract the clause (commit)

  - If we added the clause ourselves, we no longer have to commit it.
    Its visibility is guaranteed by the created and erased generations,
    so there is no need to keep it in our tables.

    (*) This is not true.  Commit/discard need to move the generations
    out of the transaction or later transactions will see this clause.
    We cannot do that now as the clause may be visible from a choice
    point in the transaction.  What to do?  I see two options:

    - Make clause CG set a flag and trigger us, so we can check the
      table and removed GCed clauses from it.
    - Scan here to see whether the clause is involved in a choicepoint.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

int
transaction_retract_clause(DECL_LD Clause clause)
{ if ( clause->generation.created < LD->transaction.gen_base )
  { tr_gen_t lgen = (tr_gen_t)( next_generation(clause->predicate) -
				LD->transaction.gen_base );

    acquire_clause(clause);
    ATOMIC_INC(&clause->tr_erased_no);
    addHTablePW(tr_clause_table(), clause, lgen);

    return true;
  } else if ( clause->generation.created <= LD->transaction.gen_nest )
  { gen_t egen = next_generation(clause->predicate);
    if ( !egen )
      return PL_representation_error("transaction_generations"),-1;
    clause->generation.erased = egen;
    acquire_clause(clause);
    addHTablePW(tr_clause_table(), clause, GEN_NESTED_RETRACT);

    return true;
#if 0					/* see (*) */
  } else if ( LD->transaction.clauses )
  { deleteHTablePW(LD->transaction.clauses, clause);
#endif
  }
  DEBUG(MSG_TRANSACTION,
	Sdprintf("Deleting locally asserted clause for %s %s..%s\n",
		 predicateName(clause->predicate),
		 generationName(clause->generation.created),
		 generationName(clause->generation.erased)));

  return false;
}

int
transaction_assert_clause(DECL_LD Clause clause, ClauseRef where)
{ uintptr_t lgen = (where == CL_START ? GEN_ASSERTA : GEN_ASSERTZ);

  acquire_clause(clause);
  addHTablePW(tr_clause_table(), clause, lgen);

  return true;
}


int
transaction_visible_clause(DECL_LD Clause cl, gen_t gen)
{ if ( cl->generation.created <= LD->transaction.gen_start &&
       cl->generation.erased   > LD->transaction.gen_start )
  { if ( cl->tr_erased_no )
    { tr_stack s = { .clauses = LD->transaction.clauses,
                     .parent  = LD->transaction.stack
		   };
      tr_stack *stack;

      for(stack=&s; stack; stack=stack->parent)
      { tr_gen_t lgen;

	if ( stack->clauses &&
	     (lgen = (tr_gen_t)lookupHTablePW(stack->clauses, cl)) &&
	     !IS_ASSERT_GEN(lgen) )
	{ if ( lgen+LD->transaction.gen_base <= gen )
	    return false;
	}
      }
    }

    return true;
  }

  return false;
}


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Notion of last modified for a predicate   when  inside a transaction. If
the transaction did not modify the predicate  this should be at most our
global start transaction. If we did modify   we define the last modified
to be the global start plus the local offset. Alternatively we could use
the real transaction number, but that cannot  be represented as a 64-bit
signed integer and thus is either  negative (upsetting simple arithmetic
on modification stamps) or is a  GMP   number.  The latter is not always
present and in any case, using GMP is relatively costly.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

#define LGEN(gen)		  ((tr_gen_t)((gen)-LD->transaction.gen_base))
#define GGEN(lgen)		  ((lgen)+LD->transaction.gen_base)
#define LGEN_FLAGS_VAL(gen,flags) ((LGEN(gen)<<2)|flags)
#define VAL_LGEN(ptr)		  ((ptr)>>2)
#define VAL_GEN(ptr)		  GGEN(VAL_LGEN(ptr))
#define VAL_GEN_FLAGS(ptr)	  ((ptr)&0x3)
#define VAL_ADD_FLAGS(ptr, flags) ((ptr)|(flags))

gen_t
transaction_last_modified_predicate(DECL_LD Definition def)
{ TablePW table;

  if ( (table=LD->transaction.predicates) )
  { tr_gen_t lgen;

    if ( (lgen = (tr_gen_t)lookupHTablePW(table, def)) )
    { uintptr_t lmod = VAL_LGEN(lgen);
      return LD->transaction.gen_start + lmod;
    }
  }

  return def->last_modified > LD->transaction.gen_start
		? LD->transaction.gen_start
		: def->last_modified;
}

void
transaction_set_last_modified(Definition def, gen_t gen, int flags)
{ GET_LD
  tr_gen_t lgen0;
  int oflags;

  if ( !LD->transaction.predicates )
    LD->transaction.predicates = newHTablePW(16);

  lgen0  = (tr_gen_t)lookupHTablePW(LD->transaction.predicates, def);
  oflags = VAL_GEN_FLAGS(lgen0);

  updateHTablePW(LD->transaction.predicates, def,
		 LGEN_FLAGS_VAL(gen, oflags|flags));
}


#define set_modified(gen) LDFUNC(set_modified, gen)
static void
set_modified(DECL_LD gen_t gen)
{ if ( LD->transaction.predicates )
  { FOR_TABLE(LD->transaction.predicates, n, v)
    { Definition def = val2ptr(n);
      int flags = VAL_GEN_FLAGS(v);

      setLastModifiedPredicate(def, gen, flags);
    }

    destroyHTablePW(LD->transaction.predicates);
    LD->transaction.predicates = NULL;
  }
}

static void
retract_clause_gen(Clause clause, gen_t generation)
{ if ( clause->generation.erased > generation )
    clause->generation.erased = generation;
}

#define transaction_commit(_) LDFUNC(transaction_commit, _)
static bool
transaction_commit(DECL_LD)
{ if ( LD->transaction.clauses )
  { gen_t gen_commit;

    PL_LOCK(L_GENERATION);
    gen_commit = global_generation()+1;

    FOR_TABLE(LD->transaction.clauses, n, v)
    { Clause cl = val2ptr(n);
      tr_gen_t lgen = (tr_gen_t)v;

      if ( IS_ASSERT_GEN(lgen) )
      { if ( isoff(cl, CL_ERASED) )
	{ cl->generation.erased  = GEN_MAX;
	  MEMORY_RELEASE();
	  cl->generation.created = gen_commit;
	  DEBUG(MSG_COMMIT,
	      Sdprintf("Commit added clause %p for %s\n",
		       cl, predicateName(cl->predicate)));
	} else
	{ DEBUG(MSG_COMMIT,
		Sdprintf("Discarded in-transaction clause %p for %s\n",
			 cl, predicateName(cl->predicate)));
	  cl->generation.erased  = GEN_TR_ASSERT_ERASE;
	  MEMORY_RELEASE();
	  cl->generation.created = GEN_TR_ASSERT_ERASE;
	}
      } else if ( lgen == GEN_NESTED_RETRACT )
      { retract_clause_gen(cl, gen_commit);
      } else
      { DEBUG(MSG_COMMIT,
	      Sdprintf("Commit erased clause %p for %s\n",
		       cl, predicateName(cl->predicate)));
	ATOMIC_DEC(&cl->tr_erased_no);
	retract_clause_gen(cl, gen_commit);
      }
    }
    MEMORY_RELEASE();
    GD->_generation = gen_commit;
    PL_UNLOCK(L_GENERATION);

    FOR_TABLE(LD->transaction.clauses, n, v)
    { Clause cl = val2ptr(n);
      tr_gen_t lgen = (tr_gen_t)v;

      if ( !IS_ASSERT_GEN(lgen) )
	retract_clause(cl, cl->generation.erased);
    }

    set_modified(gen_commit);
    destroyHTablePW(LD->transaction.clauses);
    LD->transaction.clauses = NULL;
  }

  return true;
}

#define transaction_discard(_) LDFUNC(transaction_discard, _)
static bool
transaction_discard(DECL_LD)
{ int rc = true;

  if ( LD->transaction.clauses )
  { FOR_TABLE(LD->transaction.clauses, n, v)
    { Clause cl = val2ptr(n);
      tr_gen_t lgen = (tr_gen_t)v;
      Definition def = cl->predicate;
      atom_t action = 0;

      if ( IS_ASSERT_GEN(lgen) )
      { if ( isoff(cl, CL_ERASED) )
	{ cl->generation.erased  = GEN_TR_DISCARD_ASSERT;
	  MEMORY_RELEASE();
	  cl->generation.created = GEN_TR_DISCARD_ASSERT;
	  retract_clause(cl, cl->generation.created);
	  DEBUG(MSG_COMMIT,
		Sdprintf("Discarded asserted clause %p for %s\n",
			 cl, predicateName(cl->predicate)));
	  action = (lgen==GEN_ASSERTA ? ATOM_asserta : ATOM_assertz);
	} else
	{ cl->generation.erased  = GEN_TR_DISCARD_ASSERT_ERASE;
	  MEMORY_RELEASE();
	  cl->generation.created = GEN_TR_DISCARD_ASSERT_ERASE;
	  DEBUG(MSG_COMMIT,
		Sdprintf("Discarded asserted&retracted "
			 "clause %p for %s\n",
			 cl, predicateName(cl->predicate)));
	}
      } else if ( lgen == GEN_NESTED_RETRACT )
      { cl->generation.erased = LD->transaction.gen_max;
	action = ATOM_retract;
      } else
      { ATOMIC_DEC(&cl->tr_erased_no);
	action = ATOM_retract;
      }

      if ( def && def->events && action &&
	   !(LD->transaction.flags&TR_BULK) )
      { if ( !predicate_update_event(def, action, cl,
				     P_EVENT_ROLLBACK) )
	  rc = false;
      }
    };
    destroyHTablePW(LD->transaction.clauses);
    LD->transaction.clauses = NULL;
    if ( LD->transaction.predicates )
    { destroyHTablePW(LD->transaction.predicates);
      LD->transaction.predicates = NULL;
    }
  }

  return rc;
}

static void
merge_clause_tables(TablePW into, TablePW from)
{ FOR_TABLE(from, n, v)
  { Clause cl = val2ptr(n);

    if ( addHTablePW(into, cl, v) == v )
      acquire_clause(cl);		/* new in outer table */
    else
      updateHTablePW(into, cl, v);	/* already in outer table */
  };
}

#define merge_pred_tables(into, from) LDFUNC(merge_pred_tables, into, from)
static void
merge_pred_tables(DECL_LD TablePW into, TablePW from)
{ FOR_TABLE(from, n, v)
  { Definition def = val2ptr(n);
    tr_gen_t lgen = (tr_gen_t)v;
    tr_gen_t lgen0 = (tr_gen_t)lookupHTablePW(into, def);
    int oflags = VAL_GEN_FLAGS(lgen0);

    updateHTablePW(into, def, VAL_ADD_FLAGS(lgen, oflags));
  };
}


		 /*******************************
		 *	      UPDATES		*
		 *******************************/

typedef struct tr_update
{ Clause    clause;
  functor_t update;
} tr_update;

static gen_t
update_gen(const tr_update *u)
{ return u->update == FUNCTOR_erased1 ?
		u->clause->generation.erased :
		u->clause->generation.created;
}

static int
cmp_updates(const void *ptr1, const void *ptr2)
{ const tr_update *u1 = ptr1;
  const tr_update *u2 = ptr2;
  gen_t g1 = update_gen(u1);
  gen_t g2 = update_gen(u2);

  return g1 < g2 ? -1 : g1 > g2 ? 1 : 0;
}


#define transaction_updates(b) LDFUNC(transaction_updates, b)
static int
transaction_updates(DECL_LD Buffer b)
{ if ( LD->transaction.clauses )
  { FOR_TABLE(LD->transaction.clauses, n, v)
    { Clause cl = val2ptr(n);
      tr_gen_t lgen = (tr_gen_t)v;

      if ( IS_ASSERT_GEN(lgen) )
      { if ( isoff(cl, CL_ERASED) )
	{ tr_update u;
	  u.clause = cl;
	  if ( lgen == GEN_ASSERTA )
	    u.update = FUNCTOR_asserta1;
	  else
	    u.update = FUNCTOR_assertz1;
	  addBuffer(b, u, tr_update);
	}
      } else if ( !is_trie_clause(cl) )
      { tr_update u;
	u.clause = cl;
	u.update = FUNCTOR_erased1;
	addBuffer(b, u, tr_update);
      }
    };
    qsort(baseBuffer(b, void),
	  entriesBuffer(b, tr_update), sizeof(tr_update),
	  cmp_updates);
  }

  return true;
}


#define announce_updates(updates) LDFUNC(announce_updates, updates)
static bool
announce_updates(DECL_LD Buffer updates)
{ tr_update *u, *e;

  u = baseBuffer(updates, tr_update);
  e = topBuffer(updates, tr_update);

  for(; u<e; u++)
  { Definition def = u->clause->predicate;

    if ( !predicate_update_event(def, nameFunctor(u->update), u->clause, 0) )
      return false;
  }

  return true;
}


		 /*******************************
		 *	PROLOG CONNECTION	*
		 *******************************/

#define closeTransactionSnapshots(n) LDFUNC(closeTransactionSnapshots, n)
#define LDFUNC_DECLARATIONS
static void closeTransactionSnapshots(uint64_t n);
#undef LDFUNC_DECLARATIONS

/* The start generation of a transaction pins the global view of its
 * goal: clause GC marks it for every dirty predicate (see
 * markPredicatesInEnvironments()).  A clause GC that read the global
 * generation before our store became visible may not see the store
 * when it marks.  We therefore store, execute a full barrier and read
 * the global generation again until it is unchanged, which pairs with
 * the barrier clause GC executes after reading the start generation.
 */

#define setTransactionStart(_) LDFUNC(setTransactionStart, _)
static void
setTransactionStart(DECL_LD)
{ gen_t gen;

  do
  { gen = global_generation();
    LD->transaction.gen_start = gen;
    MEMORY_BARRIER();
  } while ( gen != global_generation() );
}

#define transaction(goal, constraint, lock, flags) LDFUNC(transaction, goal, constraint, lock, flags)
static int
transaction(DECL_LD term_t goal, term_t constraint, term_t lock, int flags)
{ int rc;
  buffer updates;

  initBuffer(&updates);

  if ( LD->transaction.generation )	/* nested transaction */
  { tr_stack parent = { .generation  = LD->transaction.generation,
			.gen_nest    = LD->transaction.gen_nest,
			.clauses     = LD->transaction.clauses,
			.predicates  = LD->transaction.predicates,
			.table_trail = LD->transaction.table_trail,
			.parent      = LD->transaction.stack,
			.id          = LD->transaction.id,
			.flags       = LD->transaction.flags,
			.snapshots   = LD->transaction.snapshots
		      };

    LD->transaction.clauses     = NULL;
    LD->transaction.predicates  = NULL;
    LD->transaction.id          = goal;
    LD->transaction.stack       = &parent;
    LD->transaction.gen_nest    = LD->transaction.generation;
    LD->transaction.flags       = flags;
    LD->transaction.table_trail = NULL;
    rc = callProlog(NULL, goal, PL_Q_PASS_EXCEPTION, NULL);
    if ( rc && constraint )
      rc = callProlog(NULL, constraint, PL_Q_PASS_EXCEPTION, NULL);
    if ( rc && (flags&TR_TRANSACTION) )
    { if ( LD->transaction.table_trail )
      { if ( parent.table_trail )
	{ merge_tabling_trail(parent.table_trail, LD->transaction.table_trail);
	} else
	{ parent.table_trail = LD->transaction.table_trail;
	}
      }

      if ( LD->transaction.predicates )
      { if ( parent.predicates )
	{ merge_pred_tables(parent.predicates,
			    LD->transaction.predicates);
	  destroyHTablePW(LD->transaction.predicates);
	} else
	{ parent.predicates = LD->transaction.predicates;
	}
      }

      if ( LD->transaction.clauses )
      {	if ( parent.clauses )
	{ if ( (flags&TR_BULK) )
	  { transaction_updates(&updates);
	    if ( !announce_updates(&updates) )
	      goto nested_discard;
	  }
	  merge_clause_tables(parent.clauses, LD->transaction.clauses);
	  destroyHTablePW(LD->transaction.clauses);
	} else
	{ parent.clauses = LD->transaction.clauses;
	}
      }
    } else
    { nested_discard:
      rc = transaction_discard() && rc;
      rc = transaction_rollback_tables() && rc;
      LD->transaction.generation = parent.generation;
      closeTransactionSnapshots(parent.snapshots);
    }
    LD->transaction.gen_nest    = parent.gen_nest;
    LD->transaction.clauses     = parent.clauses;
    LD->transaction.predicates  = parent.predicates;
    LD->transaction.table_trail = parent.table_trail;
    LD->transaction.stack       = parent.parent;
    LD->transaction.id          = parent.id;
    LD->transaction.flags	= parent.flags;
  } else
  {
#ifdef O_PLMT
    int tid = PL_thread_self();
    pl_mutex *mutex = NULL;
    if ( lock && !get_mutex(lock, &mutex, true) )
      return false;
#define TR_LOCK() PL_mutex_lock(mutex)
#define TR_UNLOCK() PL_mutex_unlock(mutex)
#else
    int tid = 1;			/* without threads we get -2 */
#define TR_LOCK() true
#define TR_UNLOCK() (void)0
#endif

    setTransactionStart();
    LD->transaction.gen_base   = GEN_TRANSACTION_BASE + tid*GEN_TRANSACTION_SIZE;
    LD->transaction.gen_max    = LD->transaction.gen_base+GEN_TRANSACTION_SIZE-6;
    LD->transaction.generation = LD->transaction.gen_base;
    LD->transaction.id         = goal;
    rc = callProlog(NULL, goal, PL_Q_PASS_EXCEPTION, NULL);
    if ( rc && (flags&TR_TRANSACTION) )
    { int locked = false;
      if ( constraint )
      { if ( (rc=TR_LOCK()) )
	{ locked = true;
	  closeTransactionSnapshots(0); /* their view moves with gen_start */
	  setTransactionStart();
	  rc = callProlog(NULL, constraint, PL_Q_PASS_EXCEPTION, NULL);
	}
      }
      if ( rc && (flags&TR_BULK) )
      { transaction_updates(&updates);
	rc = announce_updates(&updates);
      }
      if ( rc )
      { rc = ( transaction_commit_tables() &&
	       transaction_commit() );
	if ( locked ) TR_UNLOCK();
      } else
      { if ( locked ) TR_UNLOCK();
	LD->transaction.generation = 0;	/* avoid recording the rollback */
	transaction_discard();
	transaction_rollback_tables();
      }
    } else
    { LD->transaction.generation = 0;  /* avoid recording the rollback */
      rc = transaction_discard() && rc;
      rc = transaction_rollback_tables() && rc;
    }
    closeTransactionSnapshots(0);
    LD->transaction.id         = 0;
    LD->transaction.generation = 0;
    LD->transaction.gen_max    = 0;
    LD->transaction.gen_base   = GEN_INFINITE;
    LD->transaction.gen_start  = 0;
    LD->transaction.flags      = 0;
#ifdef O_PLMT
    if ( mutex )
      put_mutex(mutex);
#endif
  }

  if ( (flags&TR_BULK) )
    discardBuffer(&updates);

  return rc;
}

static const PL_option_t transaction_options[] =
{ { ATOM_bulk,		 OPT_BOOL },
  { NULL_ATOM,		 0 }
};

static
PRED_IMPL("$transaction", 2, transaction, PL_FA_TRANSPARENT)
{ PRED_LD
  int flags = TR_TRANSACTION;
  int bulk = false;

  if ( !PL_scan_options(A2, 0, "transaction_option",
			transaction_options, &bulk) )
    return false;
  if ( bulk )
    flags |= TR_BULK;

  return transaction(A1, 0, 0, flags);
}

static
PRED_IMPL("$transaction", 3, transaction, PL_FA_TRANSPARENT)
{ PRED_LD

  return transaction(A1, A2, A3, TR_TRANSACTION);
}

static
PRED_IMPL("$snapshot", 1, snapshot, PL_FA_TRANSPARENT)
{ PRED_LD

  return transaction(A1, 0, 0, TR_SNAPSHOT);
}

static
PRED_IMPL("current_transaction", 1, current_transaction, PL_FA_NONDETERMINISTIC)
{ PRED_LD
  tr_stack *stack;
  term_t id0, id;
  Module m0 = contextModule(environment_frame);

  switch( CTX_CNTRL )
  { case FRG_FIRST_CALL:
    { if ( !LD->transaction.id )
	return false;
      id0 = LD->transaction.id;
      stack = LD->transaction.stack;
      break;
    }
    case FRG_REDO:
    { stack = CTX_PTR;
      id0 = stack->id;
      break;
    }
    default:
      return true;
  }

  id = PL_new_term_ref();
  Mark(fli_context->mark);
  for(;;)
  { Module m = NULL;
    int rc;

    if ( !PL_strip_module(id0, &m, id) )
      return false;
    if ( m == m0 )
      rc = PL_unify(A1, id);
    else
      rc = PL_unify(A1, id0);

    if ( rc )
    { if ( stack )
	ForeignRedoPtr(stack);
      else
	return true;
    }
    Undo(fli_context->mark);

    if ( stack )
    { id0 = stack->id;
      stack = stack->parent;
    } else
      return false;
  }
}

#define add_update(cl, action, tail, head, tmp) LDFUNC(add_update, cl, action, tail, head, tmp)
static bool
add_update(DECL_LD Clause cl, functor_t action,
	   term_t tail, term_t head, term_t tmp)
{ return ( PL_put_clref(tmp, cl) &&
	   PL_cons_functor(tmp, action, tmp) &&
	   PL_unify_list(tail, head, tail) &&
	   PL_unify(head, tmp)
	 );
}

static
PRED_IMPL("transaction_updates", 1, transaction_updates, 0)
{ PRED_LD

  if ( !LD->transaction.generation )
    return false;			/* error? */

  if ( LD->transaction.clauses )
  { tmp_buffer buf;
    tr_update *u, *e;
    term_t tail = PL_copy_term_ref(A1);
    term_t head = PL_new_term_ref();
    term_t tmp  = PL_new_term_ref();
    int rc = true;

    initBuffer(&buf);
    transaction_updates((Buffer)&buf);
    u = baseBuffer(&buf, tr_update);
    e = topBuffer(&buf, tr_update);

    for(; u<e; u++)
    { if ( !add_update(u->clause, u->update, tail, head, tmp) )
      { rc = false;
	break;
      }
    }
    discardBuffer(&buf);

    return rc && PL_unify_nil(tail);
  } else
  { return PL_unify_nil(A1);
  }
}

#ifdef O_DEBUG
static
PRED_IMPL("pred_generations", 1, pred_generations, PL_FA_TRANSPARENT)
{ PRED_LD
  Procedure proc;

  if ( get_procedure(A1, &proc, 0, GP_NAMEARITY) )
  { Definition def = getProcDefinition(proc);
    gen_t gen = current_generation(def);
    ClauseRef c;

    Sdprintf("Clauses for %s at %s (gen_start = %s)\n",
	     predicateName(def), generationName(gen),
	     generationName(LD->transaction.gen_start));

    acquire_def(def);
    for(c = def->impl.clauses.first_clause; c; c = c->next)
    { Clause cl = c->value.clause;

      Sdprintf("  %s %p %s..%s%s\n",
	       visibleClause(cl, gen) ? "V" : "i",
	       cl,
	       generationName(cl->generation.created),
	       generationName(cl->generation.erased),
	       ison(cl, CL_ERASED) ? " (erased)" : "");
    }
    release_def(def);

    return true;
  }

  return false;
}
#endif


#define META PL_FA_TRANSPARENT
#define NDET PL_FA_NONDETERMINISTIC

		 /*******************************
		 *	 DATABASE SNAPSHOTS	*
		 *******************************/

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
A database snapshot is a handle to the generation of the database at the
time db_snapshot/1 was called.  db_snapshot_clause/3 enumerates the
clauses of a predicate that are visible in this generation, also if they
are erased later.  This is the same information snapshot/1 uses, but the
handle can be kept while the calling goal continues and modifies the
database.

Clause GC keeps the clauses that are visible to an open snapshot.  The
generation is read and the snapshot is added to the list while holding
the lock that markDBSnapshots() holds, so a clause GC either sees the
snapshot or the snapshot is not older than the start of this clause GC.

A snapshot is closed by db_snapshot_close/1 or when its handle is
reclaimed by atom GC.  As an open snapshot keeps all clauses that are
erased after it was created, goals that create many snapshots should
close them.  A snapshot can only be used and closed by the engine that
created it.  This engine cannot close the snapshot while it is starting
a goal in it, so no clause GC can run between reading the generation of
an open snapshot and the frame that uses it.

db_snapshot_scope(-Snapshot, :Goal) creates a snapshot that lives as
long as its own frame, i.e., while Goal runs, and costs no allocation:

    db_snapshot_scope(Snapshot, Goal) :-
	'$db_snapshot_scope'(Snapshot),
	call(Goal),
	integer(Snapshot).

'$db_snapshot_scope'/1 gives the frame of db_snapshot_scope/2 the
current generation and flags it FR_SNAPSHOT.  Snapshot is a number that
no other scope in the process gets; it stays in the first argument of
the frame, which the final integer/1 keeps alive.  Snapshot is valid while
the frame of db_snapshot_scope/2 with this number is an ancestor of the
frame that uses it, see scope_generation().  Clause GC keeps, for all
predicates, the clauses visible in the generation of every frame flagged
FR_SNAPSHOT.  The generation is read and the frame is flagged while
holding the scan lock of the thread, which clause GC holds while it
scans the frames of a thread, so a clause GC either sees the flag or the
generation is not older than the start of this clause GC.

A snapshot that is created inside a transaction is the database as this
transaction sees it at that time.  It also holds the generation of the
transaction, which is used for the predicates that take part in
transactions.  As for any goal in a transaction, the other predicates
are read in their current state.  Clause GC keeps the clauses that are
visible in either generation.  The generation of the transaction has no
meaning after the changes it refers to are committed or discarded, so
the snapshot is closed if the transaction ends and if a nested
transaction it was created in is discarded.  The generation cannot tell
the latter: before its first change a nested transaction has the
generation of its parent.  The engine therefore numbers the snapshots
it makes in transactions, and a nested transaction that is discarded
closes those with a higher number than at its start.  transaction/3
also closes these snapshots before it calls its constraint, as it then
moves the start of the transaction to the current generation.  See
closeTransactionSnapshots().  A snapshot of db_snapshot_scope/2 is gone
before that: its frame ends with the goal of the transaction.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

typedef struct db_snapshot
{ gen_t		      generation;	/* 0: closed */
  gen_t		      tr_generation;	/* generation in my transaction or 0 */
  uint64_t	      tr_number;	/* number in my engine's transactions */
  uint64_t	      owner;		/* engine that created me */
  struct db_snapshot *next;
  struct db_snapshot *prev;
} db_snapshot;

static db_snapshot *db_snapshots = NULL;	/* open snapshots */
static int64_t db_snapshot_scopes = 0;		/* last db_snapshot_scope/2 */

/* A snapshot belongs to the engine that created it.  We identify the
 * engine by its sequence number, which, unlike its thread id, is not
 * reused.
 */

#ifdef O_ENGINES
#define SNAPSHOT_OWNER() (LD->thread.seq_id)
#else
#define SNAPSHOT_OWNER() ((uint64_t)0)
#endif

static void
unlink_db_snapshot(db_snapshot *sn)	/* holding L_MISC */
{ if ( sn->generation )
  { if ( sn->prev )
      sn->prev->next = sn->next;
    else
      db_snapshots = sn->next;
    if ( sn->next )
      sn->next->prev = sn->prev;
    sn->generation = 0;
  }
}

static void
close_db_snapshot(db_snapshot *sn)
{ PL_LOCK(L_MISC);
  unlink_db_snapshot(sn);
  PL_UNLOCK(L_MISC);
}

/* Close the snapshots this engine made in a transaction after it made
 * `n` of them.  Called with the number at the start of a nested
 * transaction that is discarded and with 0 if the outermost transaction
 * ends or transaction/3 calls its constraint.
 */

static void
closeTransactionSnapshots(DECL_LD uint64_t n)
{ if ( db_snapshots )
  { uint64_t owner = SNAPSHOT_OWNER();
    db_snapshot *next;

    PL_LOCK(L_MISC);
    for(db_snapshot *sn = db_snapshots; sn; sn = next)
    { next = sn->next;
      if ( sn->owner == owner && sn->tr_number > n )
	unlink_db_snapshot(sn);
    }
    PL_UNLOCK(L_MISC);
  }
}

static int
release_db_snapshot(atom_t aref)
{ db_snapshot *sn = PL_blob_data(aref, NULL, NULL);

  close_db_snapshot(sn);
  PL_free(sn);

  return true;
}

static int
write_db_snapshot(IOSTREAM *s, atom_t aref, int flags)
{ db_snapshot *sn = PL_blob_data(aref, NULL, NULL);
  (void)flags;

  Sfprintf(s, "<db_snapshot>(%p)", sn);
  return true;
}

static PL_blob_t db_snapshot_blob =
{ PL_BLOB_MAGIC,
  PL_BLOB_UNIQUE|PL_BLOB_NOCOPY,
  "db_snapshot",
  release_db_snapshot,
  NULL,
  write_db_snapshot
};

static bool
get_db_snapshot(term_t t, db_snapshot **snp)
{ void *data;
  PL_blob_t *type;

  if ( PL_get_blob(t, &data, NULL, &type) && type == &db_snapshot_blob )
  { *snp = data;
    return true;
  }

  return PL_type_error("db_snapshot", t);
}

/* A snapshot of db_snapshot_scope/2 is the number of its scope, unique
 * in the process, so a number passed to another engine or thread cannot
 * match a scope there.  It is valid while an ancestor of the frame that
 * uses it is the frame of db_snapshot_scope/2 whose first argument is
 * this number.  This frame is flagged FR_SNAPSHOT, so clause GC keeps the
 * clauses visible in its generation.  Made in a transaction, this is a
 * generation of the transaction.  As for any frame, it is only used for
 * the predicates that take part in transactions.
 */

#define scope_generation(id, def, gen) \
	LDFUNC(scope_generation, id, def, gen)

static bool
scope_generation(DECL_LD word id, Definition def, gen_t *gen)
{ for(LocalFrame fr = environment_frame; fr; fr = parentFrame(fr))
  { if ( isSnapshotScopeFrame(fr) )
    { Word p = argFrameP(fr, 0);

      deRef(p);
      if ( *p == id )			/* both tagged integers */
      { gen_t g = generationFrame(fr);

	if ( g >= GEN_TRANSACTION_BASE && !(def && ison(def, P_TRANSACT)) )
	  g = GEN_INVALID;		/* see snapshot_generation() */
	*gen = g;
	return true;
      }
    }
  }

  return false;
}

/* Get the generation of the open snapshot `w`, a dereferenced cell, for
 * the clauses of `def`.  False, without an exception, if `w` is not a
 * snapshot this engine can use.  GEN_INVALID if the snapshot was made in
 * a transaction and `def` does not take part in transactions: the goal
 * then sees the current database, as any goal in the transaction, and
 * keeps the generation it got at its call port.  A fresh generation
 * stored without the loop of setGenerationFrame() could be missed by
 * clause GC.
 */

#define snapshot_generation(w, def, gen) \
	LDFUNC(snapshot_generation, w, def, gen)

static bool
snapshot_generation(DECL_LD word w, Definition def, gen_t *gen)
{ if ( isTaggedInt(w) )
    return scope_generation(w, def, gen);
  if ( isAtom(w) )
  { Atom a = atomValue(w);
    db_snapshot *sn = (db_snapshot *)a->name;

    if ( a->type == &db_snapshot_blob &&
	 sn->owner == SNAPSHOT_OWNER() && sn->generation )
    { if ( !sn->tr_generation )
	*gen = sn->generation;
      else if ( def && ison(def, P_TRANSACT) )
	*gen = sn->tr_generation;
      else
	*gen = GEN_INVALID;		/* as for any goal in a transaction */
      return true;
    }
  }

  return false;
}

/* Raise the error for `t` if snapshot_generation() is false for it */

static bool
db_snapshot_error(term_t t)
{ GET_LD
  atom_t type = PL_new_atom("db_snapshot");
  Word p = valTermRef(t);
  Atom a = NULL;
  bool rc;

  deRef(p);
  if ( isAtom(*p) && (a=atomValue(*p))->type != &db_snapshot_blob )
    a = NULL;
  if ( a && ((db_snapshot *)a->name)->owner != SNAPSHOT_OWNER() )
    rc = PL_error(NULL, 0, NULL, ERR_PERMISSION, ATOM_access, type, t);
  else if ( a || isInteger(*p) )	/* closed or no such scope */
    rc = PL_error(NULL, 0, NULL, ERR_EXISTENCE, type, t);
  else
    rc = PL_error(NULL, 0, NULL, ERR_TYPE, type, t);
  PL_unregister_atom(type);

  return rc;
}

/* Get the generation of an open snapshot for the clauses of `def`.  If
 * `def` is NULL, we only verify that we can use the snapshot.
 */

bool
get_db_snapshot_generation(term_t t, Definition def, gen_t *gen)
{ GET_LD
  Word p = valTermRef(t);

  deRef(p);
  return snapshot_generation(*p, def, gen) || db_snapshot_error(t);
}

/* Called by clause GC after it reset the predicates in `ddis`: all
 * open snapshots access all these predicates.  `ddis` is the table of
 * dirty predicates or the thread-local predicates of localClauseGC().
 */

void
markDBSnapshots(TablePP ddis)
{ PL_LOCK(L_MISC);
  if ( db_snapshots )
  { FOR_TABLE(ddis, n, v)
    { DirtyDefInfo ddi = val2ptr(v);

      for(db_snapshot *sn = db_snapshots; sn; sn = sn->next)
      { ddi_add_access_gen(ddi, sn->generation);
	if ( sn->tr_generation )
	  ddi_add_access_gen(ddi, sn->tr_generation);
      }
    }
  }
  PL_UNLOCK(L_MISC);
}

/* Clause GC calls addSnapshotGeneration() for every frame it finds that
 * is flagged FR_SNAPSHOT and then markSnapshotGenerations() for the
 * predicates in `ddis`, which keep the clauses visible in each of these
 * generations.  Frames of a goal of db_snapshot_call/2 mostly follow the
 * frame of their snapshot, so we only skip a repeat of the last
 * generation here and sort out the others before marking.
 */

void
addSnapshotGeneration(Buffer gens, gen_t gen)
{ if ( isEmptyBuffer(gens) || topBuffer(gens, gen_t)[-1] != gen )
    addBuffer(gens, gen, gen_t);
}

static int
compare_generations(const void *p1, const void *p2)
{ gen_t g1 = *(const gen_t*)p1;
  gen_t g2 = *(const gen_t*)p2;

  return g1 < g2 ? -1 : g1 > g2 ? 1 : 0;
}

void
markSnapshotGenerations(TablePP ddis, Buffer gens)
{ size_t count = entriesBuffer(gens, gen_t);

  if ( count > 0 )
  { gen_t *g = baseBuffer(gens, gen_t);
    size_t n = 1;

    qsort(g, count, sizeof(gen_t), compare_generations);
    for(size_t i=1; i<count; i++)
    { if ( g[i] != g[n-1] )
	g[n++] = g[i];
    }

    FOR_TABLE(ddis, k, v)
    { DirtyDefInfo ddi = val2ptr(v);

      for(size_t i=0; i<n; i++)
	ddi_add_access_gen(ddi, g[i]);
    }
  }
}

#define new_db_snapshot(_) LDFUNC(new_db_snapshot, _)
static db_snapshot *
new_db_snapshot(DECL_LD)
{ db_snapshot *sn = PL_malloc(sizeof(*sn));

  sn->owner = SNAPSHOT_OWNER();
  sn->tr_generation = LD->transaction.generation;
  sn->tr_number = sn->tr_generation ? ++LD->transaction.snapshots : 0;
  PL_LOCK(L_MISC);
  sn->generation = global_generation();
  sn->prev = NULL;
  sn->next = db_snapshots;
  if ( db_snapshots )
    db_snapshots->prev = sn;
  db_snapshots = sn;
  PL_UNLOCK(L_MISC);

  return sn;
}

/** db_snapshot(-Snapshot) is det.
 *
 *  Snapshot is a handle to the current state of the dynamic predicates.
 */

static
PRED_IMPL("db_snapshot", 1, db_snapshot, 0)
{ PRED_LD
  db_snapshot *sn = new_db_snapshot();

  if ( PL_unify_blob(A1, sn, sizeof(*sn), &db_snapshot_blob) )
    return true;
  close_db_snapshot(sn);		/* the blob is reclaimed by atom GC */
  return false;
}

/** '$db_snapshot_scope'(-Snapshot) is det.
 *
 *  Make the frame of our caller, db_snapshot_scope/2, hold a snapshot
 *  of the current state and unify Snapshot with a new number for this
 *  scope.  See above.
 */

static
PRED_IMPL("$db_snapshot_scope", 1, db_snapshot_scope, 0)
{ PRED_LD
  Procedure proc = _PL_predicate("db_snapshot_scope", 2, "$syspreds",
				 &GD->procedures.db_snapshot_scope2);
  LocalFrame fr;
  Word p;
  int64_t id;
  gen_t gen;

  if ( !hasGlobalSpace(0) &&		/* room for bindConst() below; */
       !ensureGlobalSpace(0, ALLOW_GC) ) /* this may move the stacks */
    return false;
  fr = environment_frame->parent;
  p  = valTermRef(A1);
  if ( fr->predicate != proc->definition )
    return PL_permission_error("call", "db_snapshot_scope", A1);
  deRef(p);
  if ( !canBind(*p) )			/* Snapshot will be a new number */
    return false;
  if ( (id=ATOMIC_INC(&db_snapshot_scopes)) > PLMAXTAGGEDINT )
    return PL_resource_error("db_snapshot_scopes"); /* never reuse one */

#ifdef O_PLMT
  simpleMutexLock(&LD->thread.scan_lock);
#endif
  if ( !(gen=LD->transaction.generation) )
    gen = global_generation();
  setGenerationFrameVal(fr, gen);
  set(fr, FR_SNAPSHOT);
#ifdef O_PLMT
  simpleMutexUnlock(&LD->thread.scan_lock);
#endif

  return bindConst(p, consInt(id));
}

/** db_snapshot_close(+Snapshot) is det.
 *
 *  Close Snapshot.  Clauses that are only visible to Snapshot become
 *  subject to clause GC.  Closing a closed snapshot has no effect.  A
 *  snapshot of db_snapshot_scope/2 ends with its goal and cannot be
 *  closed.
 */

static
PRED_IMPL("db_snapshot_close", 1, db_snapshot_close, 0)
{ PRED_LD
  db_snapshot *sn = NULL;

  if ( PL_is_integer(A1) )
    return PL_permission_error("close", "db_snapshot", A1);
  if ( !get_db_snapshot(A1, &sn) )
    return false;
  if ( sn->owner != SNAPSHOT_OWNER() )
    return PL_permission_error("close", "db_snapshot", A1);
  close_db_snapshot(sn);

  return true;
}

BeginPredDefs(transaction)
  PRED_DEF("db_snapshot",         1, db_snapshot,         0)
  PRED_DEF("$db_snapshot_scope",  1, db_snapshot_scope,   0)
  PRED_DEF("db_snapshot_close",   1, db_snapshot_close,   0)
  PRED_DEF("$transaction",        2, transaction,         META)
  PRED_DEF("$transaction",        3, transaction,         META)
  PRED_DEF("$snapshot",           1, snapshot,            META)
  PRED_DEF("current_transaction", 1, current_transaction, NDET|META)
  PRED_DEF("transaction_updates", 1, transaction_updates, 0)
#ifdef O_DEBUG
  PRED_DEF("pred_generations",    1, pred_generations,    META)
#endif
EndPredDefs
