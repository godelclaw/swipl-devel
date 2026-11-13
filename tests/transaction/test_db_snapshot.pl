/*  Part of SWI-Prolog

    Tests for db_snapshot/1, db_snapshot_scope/2, db_snapshot_call/2,
    db_snapshot_clause/3 and db_snapshot_close/1.
*/

:- module(test_db_snapshot,
          [ test_db_snapshot/0
          ]).
:- use_module(library(plunit)).
:- use_module(library(aggregate)).
:- use_module(library(lists)).
:- use_module(library(prolog_wrap)).

test_db_snapshot :-
    run_tests([ db_snapshot,
                db_snapshot_call
              ]).

:- begin_tests(db_snapshot).

:- dynamic p/2.

fill(N) :-
    retractall(p(_,_)),
    forall(between(1, N, I),
           ( atom_concat(k, I, K),
             assertz(p(I, K))
           )).

count(S, Goal, Count) :-
    aggregate_all(count, db_snapshot_clause(S, Goal, true), Count).

cleanup :-
    retractall(p(_,_)),
    retractall(r(_)).

test(assert, [Old-New == 3-4, cleanup(cleanup)]) :-
    fill(3),
    db_snapshot(S),
    assertz(p(4, k4)),
    count(S, p(_,_), Old),
    aggregate_all(count, p(_,_), New).
test(retract, [Old-New == 3-0, cleanup(cleanup)]) :-
    fill(3),
    db_snapshot(S),
    retractall(p(_,_)),
    count(S, p(_,_), Old),
    aggregate_all(count, p(_,_), New).
test(keyed, [Counts == [1,1,1,0], cleanup(cleanup)]) :-
    fill(200),
    db_snapshot(S),
    forall(( between(1, 200, I), I mod 2 =:= 0 ), retract(p(I, _))),
    assertz(p(201, k201)),
    count(S, p(100,_), C1),             % first argument, erased
    count(S, p(_,k100), C2),            % index created after the erase
    count(S, p(100,k100), C3),
    count(S, p(_,k201), C4),            % added later
    Counts = [C1,C2,C3,C4].
test(order, [Is == [1,2,3,4,5], cleanup(cleanup)]) :-
    fill(5),
    db_snapshot(S),
    retract(p(3, _)),
    asserta(p(0, k0)),
    findall(I, db_snapshot_clause(S, p(I,_), true), Is).
test(lazy_consume, [Seen == 100, cleanup(cleanup)]) :-
    % Each answer is retracted before the next one is requested.
    fill(100),
    db_snapshot(S),
    aggregate_all(count,
                  ( db_snapshot_clause(S, p(I,K), true),
                    retract(p(I,K)),
                    assertz(p(I,new))
                  ),
                  Seen).
test(join, [Pairs == [1-1,1-2,2-1,2-2], cleanup(cleanup)]) :-
    % Both goals of the join read the same state.
    retractall(p(_,_)),
    assertz(p(a, 1)), assertz(p(a, 2)),
    db_snapshot(S),
    findall(X-Y,
            ( db_snapshot_clause(S, p(a,X), true),
              retract(p(a,X)),
              db_snapshot_clause(S, p(a,Y), true)
            ),
            Pairs).
test(two, [C1-C2 == 2-3, cleanup(cleanup)]) :-
    fill(2),
    db_snapshot(S1),
    assertz(p(3, k3)),
    db_snapshot(S2),
    retractall(p(_,_)),
    count(S1, p(_,_), C1),
    count(S2, p(_,_), C2).
test(clause_gc, [Count == 200, cleanup(cleanup)]) :-
    % An open snapshot keeps erased clauses over clause GC.
    fill(200),
    db_snapshot(S),
    retractall(p(_,_)),
    garbage_collect_clauses,
    fill(10),
    retractall(p(_,_)),
    garbage_collect_clauses,
    count(S, p(_,_), Count).
test(rule, [Body == (q,r), cleanup(retractall(s))]) :-
    dynamic(s/0),
    assertz((s :- q, r)),
    db_snapshot(S),
    retractall(s),
    db_snapshot_clause(S, s, Body).
test(close, [error(existence_error(db_snapshot, _)), cleanup(cleanup)]) :-
    fill(3),
    db_snapshot(S),
    db_snapshot_close(S),
    db_snapshot_close(S),
    db_snapshot_clause(S, p(_,_), true).
test(type, [error(type_error(db_snapshot, foo))]) :-
    db_snapshot_clause(foo, p(_,_), true).
test(thread, [ condition(current_prolog_flag(threads, true)),
               Count == 200,
               cleanup(cleanup)
             ]) :-
    % Another thread erases everything and runs clause GC.
    fill(200),
    db_snapshot(S),
    thread_create(( retractall(p(_,_)),
                    garbage_collect_clauses
                  ), Id),
    thread_join(Id, true),
    count(S, p(_,k100), 1),
    count(S, p(_,_), Count).

test(thread_local, [Xs == [1], cleanup(retractall(tl(_)))]) :-
    % The clause GC for thread-local predicates honours snapshots.
    assertz(tl(1)),
    db_snapshot(S),
    retractall(tl(_)),
    forall(between(2, 3000, I), ( assertz(tl(I)), retract(tl(I)) )),
    findall(X, db_snapshot_clause(S, tl(X), true), Xs).
test(transaction_gc, [Xs == [old], cleanup(cleanup)]) :-
    % Clause GC keeps the clauses a snapshot sees in its transaction.
    transaction(( assertz(p(1, old)),
                  db_snapshot(S),
                  retract(p(1, old)),
                  assertz(p(2, new)),
                  garbage_collect_clauses,
                  findall(X, db_snapshot_clause(S, p(_,X), true), Xs)
                )).
test(transaction_constraint, [ error(existence_error(db_snapshot, _)),
                               cleanup(cleanup)
                             ]) :-
    % transaction/3 moves the start of the transaction before it calls
    % the constraint.  This closes the snapshots of the transaction.
    fill(1),
    transaction(db_snapshot(S),
                db_snapshot_clause(S, p(_,_), true),
                test_db_snapshot_constraint).
test(unify_fails, [Size == Size0, cleanup(retractall(uf(_)))]) :-
    % A snapshot that is not returned keeps no erased clauses.
    erase_cycle(true, Size0),
    erase_cycle(\+ db_snapshot(not_a_snapshot), Size).
test(thread_reuse, [ condition(current_prolog_flag(threads, true)),
                     true(Error = permission_error(access, db_snapshot, _)),
                     cleanup(cleanup)
                   ]) :-
    % A thread that reuses the id of the thread that created the
    % snapshot cannot use it.
    fill(3),
    thread_self(Me),
    thread_create(( db_snapshot(S0),
                    thread_send_message(Me, snapshot(S0))
                  ), Id1),
    thread_get_message(snapshot(S)),
    thread_join(Id1),
    thread_create(( catch(( db_snapshot_clause(S, p(_,_), true),
                            Result = ok
                          ),
                          error(E, _),
                          Result = E),
                    thread_send_message(Me, result(Result))
                  ), Id2),
    thread_get_message(result(Error)),
    thread_join(Id2).

test(transaction_before, [Xs == [1], cleanup(cleanup)]) :-
    assertz(r(1)),
    db_snapshot(S),
    transaction(( assertz(r(2)),
                  findall(X, db_snapshot_clause(S, r(X), true), Xs)
                )).
test(transaction_end, [ error(existence_error(db_snapshot, _)),
                        cleanup(cleanup)
                      ]) :-
    assertz(r(1)),
    transaction(db_snapshot(S)),
    db_snapshot_clause(S, r(_), true).
test(transaction_nested_commit, [Xs == [1,2,3], cleanup(cleanup)]) :-
    assertz(r(1)),
    transaction(( assertz(r(2)),
                  transaction(( assertz(r(3)),
                                db_snapshot(S)
                              )),
                  assertz(r(4)),
                  findall(X, db_snapshot_clause(S, r(X), true), Xs)
                )).
test(transaction_nested_discard, [ error(existence_error(db_snapshot, _)),
                                   cleanup(cleanup)
                                 ]) :-
    assertz(r(1)),
    transaction(( \+ transaction(( assertz(r(2)),
                                   db_snapshot(S0),
                                   nb_setval(test_db_snapshot_discarded, S0),
                                   fail
                                 )),
                  nb_getval(test_db_snapshot_discarded, S),
                  db_snapshot_clause(S, r(_), true)
                )).
test(transaction_discard_unchanged,
     [ error(existence_error(db_snapshot, _)),
       cleanup(cleanup)
     ]) :-
    % Made before the nested transaction changed anything
    assertz(r(1)),
    transaction(( \+ transaction(( db_snapshot(S0),
                                   nb_setval(test_db_snapshot_discarded, S0),
                                   fail
                                 )),
                  nb_getval(test_db_snapshot_discarded, S),
                  db_snapshot_clause(S, r(_), true)
                )).
test(transaction_discard_write_after,
     [ error(existence_error(db_snapshot, _)),
       cleanup(cleanup)
     ]) :-
    assertz(r(1)),
    transaction(( \+ transaction(( db_snapshot(S0),
                                   nb_setval(test_db_snapshot_discarded, S0),
                                   assertz(r(2)),
                                   fail
                                 )),
                  nb_getval(test_db_snapshot_discarded, S),
                  db_snapshot_clause(S, r(_), true)
                )).
test(transaction_discard_committed,
     [ error(existence_error(db_snapshot, _)),
       cleanup(cleanup)
     ]) :-
    % Made in a nested transaction that committed into one that is
    % discarded
    assertz(r(1)),
    transaction(( \+ transaction(( transaction(db_snapshot(S0)),
                                   nb_setval(test_db_snapshot_discarded, S0),
                                   fail
                                 )),
                  nb_getval(test_db_snapshot_discarded, S),
                  db_snapshot_clause(S, r(_), true)
                )).
test(snapshot_end, [ error(existence_error(db_snapshot, _)),
                      cleanup(cleanup)
                    ]) :-
    % snapshot/1 is a transaction that is always discarded
    assertz(r(1)),
    snapshot(db_snapshot(S)),
    db_snapshot_clause(S, r(_), true).
test(transaction_discard_keeps, [Xs-Ys == [1]-[1], cleanup(cleanup)]) :-
    % Made by the parent and by a nested transaction that committed
    % before the discarded one started
    assertz(r(1)),
    transaction(( db_snapshot(S1),
                  transaction(db_snapshot(S2)),
                  \+ transaction(( assertz(r(2)), fail )),
                  findall(X, db_snapshot_clause(S1, r(X), true), Xs),
                  findall(Y, db_snapshot_clause(S2, r(Y), true), Ys)
                )).
test(scope, [Xs == [1,2], cleanup(cleanup)]) :-
    % Goal sees the state at the call, also after it changed it
    assertz(r(1)), assertz(r(2)),
    db_snapshot_scope(S,
                      ( retractall(r(_)),
                        assertz(r(3)),
                        findall(X, db_snapshot_clause(S, r(X), true), Xs)
                      )).
test(scope_lazy, [Pairs == [1-5,2-5,3-5,4-5,5-5], cleanup(cleanup)]) :-
    % Answers one at a time, each followed by a write
    forall(between(1, 5, I), assertz(r(I))),
    findall(X-N,
            db_snapshot_scope(S,
                              ( db_snapshot_clause(S, r(X), true),
                                retract(r(X)),
                                aggregate_all(count,
                                              db_snapshot_clause(S, r(_), true),
                                              N)
                              )),
            Pairs).
test(scope_after, [ error(existence_error(db_snapshot, _)),
                    cleanup(cleanup)
                  ]) :-
    % The snapshot only exists while Goal runs
    assertz(r(1)),
    db_snapshot_scope(S, true),
    db_snapshot_clause(S, r(_), true).
test(scope_after_unchanged, [error(existence_error(db_snapshot, _))]) :-
    % This clause sees the same generation, but holds no snapshot
    db_snapshot_scope(S, true),
    db_snapshot_clause(S, r(_), true).
test(scope_other_scope, [ error(existence_error(db_snapshot, _)),
                          cleanup(cleanup)
                        ]) :-
    % A snapshot is not valid inside the goal of another one
    assertz(r(1)),
    db_snapshot_scope(S1, true),
    assertz(r(2)),
    db_snapshot_scope(_, db_snapshot_clause(S1, r(_), true)).
test(scope_cut, [error(existence_error(db_snapshot, _)), cleanup(cleanup)]) :-
    assertz(r(1)),
    db_snapshot_scope(S, (true ; true)),
    !,
    db_snapshot_clause(S, r(_), true).
test(scope_exception, [ error(existence_error(db_snapshot, _)),
                        cleanup(cleanup)
                      ]) :-
    assertz(r(1)),
    catch(db_snapshot_scope(S0, throw(done(S0))), done(S), true),
    db_snapshot_clause(S, r(_), true).
test(scope_gc, [Count == 200, cleanup(cleanup)]) :-
    % Clause GC keeps what the frame of db_snapshot_scope/2 sees
    forall(between(1, 200, I), assertz(r(I))),
    db_snapshot_scope(S,
                      ( retractall(r(_)),
                        garbage_collect_clauses,
                        forall(between(1, 50, I), (assertz(r(I)), retract(r(I)))),
                        garbage_collect_clauses,
                        aggregate_all(count, db_snapshot_clause(S, r(_), true),
                                      Count)
                      )).
test(scope_gc_thread, [ condition(current_prolog_flag(threads, true)),
                        Counts == [200,1],
                        cleanup(cleanup)
                      ]) :-
    % Another thread erases everything and runs clause GC
    fill(200),
    db_snapshot_scope(S,
                      ( thread_create(( retractall(p(_,_)),
                                        garbage_collect_clauses
                                      ), Id),
                        thread_join(Id, true),
                        count(S, p(_,_), C1),
                        count(S, p(_,k100), C2),
                        Counts = [C1,C2]
                      )).
test(scope_deep, [X == 1, cleanup(cleanup)]) :-
    % The snapshot is found from a frame far below the scope
    assertz(r(1)),
    db_snapshot_scope(S, ( retractall(r(_)), deep(1000, S, X) )).
test(scope_many, [Counts == Expected, cleanup(cleanup)]) :-
    % Clause GC while 100 scopes of different generations are open
    numlist(1, 100, Expected),
    many_scopes(100, Counts).
test(scope_transactions, [ error(existence_error(db_snapshot, _)),
                           cleanup(cleanup)
                         ]) :-
    % Transactions start at the same generation; the snapshot of the
    % first is not valid in the second
    assertz(r(1)),
    transaction(db_snapshot_scope(S1, true)),
    retractall(r(_)), assertz(r(2)),
    transaction(db_snapshot_scope(_, db_snapshot_clause(S1, r(_), true))).
test(scope_discarded, [ error(existence_error(db_snapshot, _)),
                        cleanup(cleanup)
                      ]) :-
    % A discarded nested transaction rewinds the generation
    transaction(( \+ transaction(( assertz(r(inner)),
                                   db_snapshot_scope(S0, true),
                                   nb_setval(test_db_snapshot_discarded, S0),
                                   fail
                                 )),
                  nb_getval(test_db_snapshot_discarded, S),
                  assertz(r(outer)),
                  db_snapshot_scope(_, db_snapshot_clause(S, r(_), true))
                )).
test(scope_number, [ true((integer(S), S > 0, S < 1<<40)),
                     cleanup(cleanup)
                   ]) :-
    % Also in a transaction the snapshot is a small number
    transaction(db_snapshot_scope(S, true)).
test(scope_shift, [error(existence_error(reset, ball)), cleanup(cleanup)]) :-
    % A continuation cannot be captured beyond the scope
    reset(db_snapshot_scope(_, shift(ball)), ball, _).
test(scope_reset_inside, [Xs == [1], cleanup(cleanup)]) :-
    assertz(r(1)),
    db_snapshot_scope(S, ( reset(shift(b), b, Cont),
                           retractall(r(_)),
                           call(Cont),
                           findall(X, db_snapshot_clause(S, r(X), true), Xs)
                         )).
test(scope_close, [ error(permission_error(close, db_snapshot, _)),
                    cleanup(cleanup)
                  ]) :-
    db_snapshot_scope(S, db_snapshot_close(S)).
test(scope_other_module, [ error(permission_error(call, db_snapshot_scope, _)),
                           cleanup(abolish(test_db_snapshot_m:db_snapshot_scope/2))
                         ]) :-
    % Only the frame of system's db_snapshot_scope/2 can hold a snapshot
    assertz((test_db_snapshot_m:db_snapshot_scope(S, G) :-
                 system:'$db_snapshot_scope'(S), call(G))),
    test_db_snapshot_m:db_snapshot_scope(_, true).
test(scope_engine_alias, [ condition(current_prolog_flag(engines, true)),
                            error(existence_error(db_snapshot, _)),
                            cleanup(cleanup)
                          ]) :-
    % A snapshot cannot be used in another engine, also not in a scope
    % that engine opened, whatever number that scope gets
    assertz(r(old)),
    db_snapshot_scope(S,
                      ( assertz(r(new)),
                        setup_call_cleanup(
                            engine_create(Xs,
                                          ( scopes_before(S),
                                            db_snapshot_scope(_,
                                                findall(X, db_snapshot_clause(S, r(X), true), Xs))
                                          ),
                                          E),
                            engine_next(E, _),
                            engine_destroy(E)))).
test(scope_engine_private, [ condition(current_prolog_flag(engines, true)),
                              error(existence_error(db_snapshot, _)),
                              cleanup(retractall(scope_tl(_)))
                            ]) :-
    % Neither for thread-local predicates
    assertz(scope_tl(main)),
    db_snapshot_scope(S,
                      setup_call_cleanup(
                          engine_create(Xs,
                                        ( assertz(scope_tl(engine)),
                                          scopes_before(S),
                                          db_snapshot_scope(_,
                                              findall(X, db_snapshot_clause(S, scope_tl(X), true), Xs))
                                        ),
                                        E),
                          engine_next(E, _),
                          engine_destroy(E))).
test(scope_bound, [fail]) :-
    % Snapshot must be unbound: a number fails, also the next one
    db_snapshot_scope(S0, true),
    S1 is S0+1,
    db_snapshot_scope(S1, true).
test(scope_attvar, [X == S]) :-
    freeze(S, X = S),
    db_snapshot_scope(S, true).
test(scope_stack_gc, [Xs == [1], cleanup(cleanup)]) :-
    % Stack GC keeps the number of the snapshot in its frame
    assertz(r(1)),
    db_snapshot_scope(S, ( retractall(r(_)),
                           garbage_collect,
                           findall(X, db_snapshot_clause(S, r(X), true), Xs)
                         )).
test(scope_nested, [X1-X2 == [1]-[1,2], cleanup(cleanup)]) :-
    assertz(r(1)),
    db_snapshot_scope(S1,
                      ( assertz(r(2)),
                        db_snapshot_scope(S2,
                                          ( assertz(r(3)),
                                            findall(X, db_snapshot_clause(S1, r(X), true), X1),
                                            findall(X, db_snapshot_clause(S2, r(X), true), X2)
                                          ))
                      )).
test(scope_thread, [ condition(current_prolog_flag(threads, true)),
                     true(R = existence_error(db_snapshot, _)),
                     cleanup(cleanup)
                   ]) :-
    % The snapshot only exists for the frames of the thread that made it
    assertz(r(1)),
    thread_self(Me),
    db_snapshot_scope(S,
                      ( thread_create(( catch(( db_snapshot_clause(S, r(_), true),
                                                R0 = ok
                                              ),
                                              error(R0, _),
                                              true),
                                        thread_send_message(Me, result(R0))
                                      ), Id),
                        thread_get_message(result(R)),
                        thread_join(Id)
                      )).
test(scope_transaction, [Xs == [1,2], cleanup(cleanup)]) :-
    % Made in a transaction, the snapshot sees the transaction's writes
    assertz(r(1)),
    transaction(( assertz(r(2)),
                  db_snapshot_scope(S,
                                    ( retract(r(1)),
                                      assertz(r(3)),
                                      findall(X, db_snapshot_clause(S, r(X), true), Xs)
                                    ))
                )).
test(scope_transaction_gc, [Xs == [old], cleanup(cleanup)]) :-
    transaction(( assertz(r(old)),
                  db_snapshot_scope(S,
                                    ( retract(r(old)),
                                      assertz(r(new)),
                                      garbage_collect_clauses,
                                      findall(X, db_snapshot_clause(S, r(X), true), Xs)
                                    ))
                )).
test(scope_thread_local, [Xs == [1], cleanup(retractall(tl(_)))]) :-
    % The clause GC for thread-local predicates honours the scope
    assertz(tl(1)),
    db_snapshot_scope(S,
                      ( retractall(tl(_)),
                        forall(between(2, 3000, I), ( assertz(tl(I)), retract(tl(I)) )),
                        findall(X, db_snapshot_clause(S, tl(X), true), Xs)
                      )).
test(scope_notransact, [Xs == [1,2], cleanup(retractall(nt(_)))]) :-
    % In a transaction, a predicate that does not take part in
    % transactions is read in its current state, as by any goal
    assertz(nt(1)),
    transaction(db_snapshot_scope(S,
                                  ( assertz(nt(2)),
                                    findall(X, db_snapshot_clause(S, nt(X), true), Xs)
                                  ))).
test(notransact, [Xs == [1,2], cleanup(retractall(nt(_)))]) :-
    assertz(nt(1)),
    transaction(( db_snapshot(S),
                  assertz(nt(2)),
                  findall(X, db_snapshot_clause(S, nt(X), true), Xs)
                )).
test(scope_not_a_snapshot, [ error(existence_error(db_snapshot, _)),
                             cleanup(cleanup)
                           ]) :-
    % A reference to a frame that holds no snapshot
    assertz(r(1)),
    prolog_current_frame(Frame),
    db_snapshot_clause(Frame, r(_), true).
test(scope_engine, [ condition(current_prolog_flag(engines, true)),
                     Xs == [1,2],
                     cleanup(cleanup)
                   ]) :-
    % Clause GC keeps what the scope of a suspended engine sees
    assertz(r(1)), assertz(r(2)),
    setup_call_cleanup(
        engine_create(Xs0,
                      db_snapshot_scope(S,
                                        ( engine_yield(ready),
                                          findall(X, db_snapshot_clause(S, r(X), true), Xs0)
                                        )),
                      E),
        ( engine_next(E, ready),
          retractall(r(_)),
          garbage_collect_clauses,
          engine_next(E, Xs)
        ),
        engine_destroy(E)).
test(scope_before_transaction, [Xs == [1], cleanup(cleanup)]) :-
    assertz(r(1)),
    db_snapshot_scope(S,
                      transaction(( assertz(r(2)),
                                    findall(X, db_snapshot_clause(S, r(X), true), Xs)
                                  ))).

many_scopes(0, []) :-
    !,
    retractall(r(_)),
    garbage_collect_clauses.
many_scopes(N, [C|Cs]) :-
    assertz(r(N)),
    db_snapshot_scope(S,
                      ( N1 is N-1,
                        many_scopes(N1, Cs),
                        aggregate_all(count, db_snapshot_clause(S, r(_), true), C)
                      )).

deep(0, S, X) :-
    !,
    db_snapshot_clause(S, r(X), true).
deep(N, S, X) :-
    N1 is N-1,
    deep(N1, S, X),
    true.

% Open scopes until the next one would get number S if numbers were
% given per engine.
scopes_before(S) :-
    N is S-1,
    forall(between(1, N, _), db_snapshot_scope(_, true)).

:- thread_local tl/1, scope_tl/1.
:- dynamic uf/1, r/1, nt/1.
:- '$notransact'(nt/1).

erase_cycle(Goal, Size) :-
    forall(between(1, 50, I), assertz(uf(I))),
    call(Goal),
    retractall(uf(_)),
    garbage_collect_clauses,
    predicate_property(uf(_), size(Size)).

test(clause_static, [error(permission_error(access, private_procedure, _))]) :-
    db_snapshot(S),
    db_snapshot_clause(S, lists:append(_,_,_), _).
test(clause_undefined, [fail]) :-
    db_snapshot(S),
    db_snapshot_clause(S, no_such_predicate_for_db_snapshot(_), _).

:- end_tests(db_snapshot).

:- begin_tests(db_snapshot_call).

:- dynamic p/2, r/1, rec/2, nest/2, lc/1, tr/1, p8/8, rs/1.
:- table td/1.
:- dynamic td/1.
:- module_transparent tr/1.
:- thread_local tl/1.

fill(N) :-
    retractall(p(_,_)),
    forall(between(1, N, I),
           ( atom_concat(k, I, K),
             assertz(p(I, K))
           )).

count(S, Goal, Count) :-
    aggregate_all(count, db_snapshot_call(S, Goal), Count).

cleanup :-
    retractall(p(_,_)),
    retractall(r(_)),
    retractall(nest(_,_)),
    retractall(lc(_)),
    retractall(tr(_)),
    retractall(tl(_)).

gc_then_call(Me, S, Goal) :-
    (   undo(thread_signal(Me, garbage_collect)),
        fail
    ;   db_snapshot_call(S, Goal)
    ).

retry_once(exit, Frame, retry) :-
    nb_getval(test_db_snapshot_retry, true),
    prolog_frame_attribute(Frame, goal, Goal),
    strip_module(Goal, _, r(_)),
    !,
    nb_setval(test_db_snapshot_retry, false).
retry_once(_, _, continue).

%   reentered(+Action, +Template, :Goal, -Xs)
%
%   Find the answers of Goal while a debugger hook runs Action at the
%   exit of '$db_snapshot_goal'/2, between this helper and the call of
%   the goal of db_snapshot_call/2.

reentered(Action, Template, Goal, Xs) :-
    Helper = system:'$db_snapshot_goal'(_,_),
    nb_setval(test_db_snapshot_reenter, Action),
    '$get_predicate_attribute'(Helper, trace, Trace),
    current_prolog_flag(access_level, Access),
    assert((user:prolog_trace_interception(Port, Frame, _, Act) :-
                reenter(Port, Frame, Act)), Hook),
    setup_call_cleanup(
        ( set_prolog_flag(access_level, system),
          '$set_predicate_attribute'(Helper, trace, true),
          trace
        ),
        findall(Template, Goal, Xs),
        ( notrace, nodebug,
          '$set_predicate_attribute'(Helper, trace, Trace),
          set_prolog_flag(access_level, Access),
          erase(Hook)
        )).

reenter(exit, Frame, Act) :-
    nb_getval(test_db_snapshot_reenter, Action),
    Action \== done,
    prolog_frame_attribute(Frame, goal, Goal),
    strip_module(Goal, _, '$db_snapshot_goal'(_,_)),
    !,
    nb_setval(test_db_snapshot_reenter, done),
    reenter_action(Action, Act).
reenter(_, _, continue).

reenter_action(call(S), continue) :-
    garbage_collect,
    findall(X, db_snapshot_call(S, lc(X)), Xs),
    nb_setval(test_db_snapshot_hook, Xs).
reenter_action(plain, continue) :-
    garbage_collect,
    findall(X, lc(X), Xs),
    nb_setval(test_db_snapshot_hook, Xs).
reenter_action(close(S), continue) :-
    db_snapshot_close(S).
reenter_action(fail, fail).
reenter_action(wrap, continue) :-
    wrap_predicate(r(_), test_db_snapshot, Wrapped, Wrapped).
reenter_action(static, continue) :-
    compile_predicates([rs/1]).

test(assert, [Old-New == 3-4, cleanup(cleanup)]) :-
    fill(3),
    db_snapshot(S),
    assertz(p(4, k4)),
    count(S, p(_,_), Old),
    aggregate_all(count, p(_,_), New).
test(retract, [Old-New == 3-0, cleanup(cleanup)]) :-
    fill(3),
    db_snapshot(S),
    retractall(p(_,_)),
    count(S, p(_,_), Old),
    aggregate_all(count, p(_,_), New).
test(keyed, [Counts == [1,1,1,0], cleanup(cleanup)]) :-
    fill(200),
    db_snapshot(S),
    forall(( between(1, 200, I), I mod 2 =:= 0 ), retract(p(I, _))),
    assertz(p(201, k201)),
    count(S, p(100,_), C1),
    count(S, p(_,k100), C2),
    count(S, p(100,k100), C3),
    count(S, p(_,k201), C4),
    Counts = [C1,C2,C3,C4].
test(order, [Is == [1,2,3,4,5], cleanup(cleanup)]) :-
    fill(5),
    db_snapshot(S),
    retract(p(3, _)),
    asserta(p(0, k0)),
    findall(I, db_snapshot_call(S, p(I,_)), Is).
test(lazy_consume, [Seen == 100, cleanup(cleanup)]) :-
    fill(100),
    db_snapshot(S),
    aggregate_all(count,
                  ( db_snapshot_call(S, p(I,K)),
                    retract(p(I,K)),
                    assertz(p(I,new))
                  ),
                  Seen).
test(join, [Pairs == [1-1,1-2,2-1,2-2], cleanup(cleanup)]) :-
    retractall(p(_,_)),
    assertz(p(a, 1)), assertz(p(a, 2)),
    db_snapshot(S),
    findall(X-Y,
            ( db_snapshot_call(S, p(a,X)),
              retract(p(a,X)),
              db_snapshot_call(S, p(a,Y))
            ),
            Pairs).
test(not_sticky, [Now == [1,2,3,4], cleanup(cleanup)]) :-
    % Only the goal itself reads the snapshot.
    fill(3),
    db_snapshot(S),
    assertz(p(4, k4)),
    once(db_snapshot_call(S, p(1,_))),
    findall(I, p(I,_), Now).
test(rule_body, [Xs == [1,2,3,4], cleanup(cleanup)]) :-
    % The clause of r/1 is selected in the snapshot; its body runs now.
    fill(3),
    assertz((r(X) :- p(X,_))),
    db_snapshot(S),
    retractall(r(_)),
    assertz(p(4, k4)),
    findall(X, db_snapshot_call(S, r(X)), Xs).
test(clause_gc, [Count == 200, cleanup(cleanup)]) :-
    fill(200),
    db_snapshot(S),
    retractall(p(_,_)),
    garbage_collect_clauses,
    count(S, p(_,_), Count).
test(thread_local, [Xs == [1], cleanup(cleanup)]) :-
    assertz(tl(1)),
    db_snapshot(S),
    retractall(tl(_)),
    forall(between(2, 3000, I), ( assertz(tl(I)), retract(tl(I)) )),
    findall(X, db_snapshot_call(S, tl(X)), Xs).
test(signal_undo, [ condition(current_prolog_flag(threads, true)),
                    N == 0,
                    cleanup(cleanup)
                  ]) :-
    % Signals and undo goals that run at the call port of the goal do
    % not change the generation of its frame.
    assertz(p(1, k1)), assertz(p(2, k2)),
    db_snapshot(S),
    assertz(p(99, k99)),
    thread_self(Me),
    forall(between(1, 2000, _),
           ( thread_signal(Me, (undo(true), fail ; true)),
             forall(db_snapshot_call(S, p(X, _)), X \== 99)
           )),
    aggregate_all(count, ( db_snapshot_call(S, p(X, _)), X == 99 ), N).
test(gc_before_goal, [ condition(current_prolog_flag(threads, true)),
                       Xs == [1],
                       cleanup(cleanup)
                     ]) :-
    % A garbage collection before the goal is called keeps Snapshot.
    % The undo goal runs at the call port of db_snapshot_call/2; the
    % signal it raises is handled at the next one, of the helper.
    assertz(r(1)),
    db_snapshot(S),
    retractall(r(_)), assertz(r(2)),
    thread_self(Me),
    findall(X, gc_then_call(Me, S, r(X)), Xs).
test(tail_call,[Xs == [from_undo], cleanup(retractall(rec(_,_)))]) :-
    % The last call of a clause may reuse the frame of the goal.  It
    % reads the current database, here after running the undo goal.
    assertz((rec(1, X) :-
                 ( undo(assertz(rec(0, from_undo))), fail ; true ),
                 rec(0, X))),
    db_snapshot(S),
    findall(X, db_snapshot_call(S, rec(1, X)), Xs).
test(last_call, [Xs == [from_undo], cleanup(cleanup)]) :-
    % As tail_call, calling another predicate that is transparent.
    assertz((lc(X) :-
                 ( undo(assertz(tr(from_undo))), fail ; true ),
                 tr(X))),
    db_snapshot(S),
    findall(X, db_snapshot_call(S, lc(X)), Xs).
test(transaction, [Xs-Ys == [1,2]-[1,2], cleanup(cleanup)]) :-
    % A snapshot that is created in a transaction is the database as
    % this transaction sees it.
    assertz(r(1)),
    transaction(( assertz(r(2)),
                  db_snapshot(S),
                  retract(r(1)),
                  assertz(r(3)),
                  findall(X, db_snapshot_call(S, r(X)), Xs),
                  findall(X, db_snapshot_clause(S, r(X), true), Ys)
                )).
test(helper, [error(permission_error(call, db_snapshot_call, _))]) :-
    % Only db_snapshot_call/2 prepares a goal
    db_snapshot(S),
    '$db_snapshot_goal'(S, r(_)).
test(nested, [Xs == [old(1),old(2),new(3)], cleanup(cleanup)]) :-
    assertz(r(1)), assertz(r(2)),
    db_snapshot(S1),
    retractall(r(_)), assertz(r(3)),
    assertz((nest(S, X) :-
                 (   db_snapshot_call(S, r(Y)), X = old(Y)
                 ;   r(Y), X = new(Y)
                 ))),
    db_snapshot(S2),
    findall(X, db_snapshot_call(S2, nest(S1, X)), Xs).
test(retry, [Xs == [1,2], cleanup(cleanup)]) :-
    % The debugger retries the goal in the same snapshot.
    assertz(r(1)), assertz(r(2)),
    db_snapshot(S),
    retractall(r(_)), assertz(r(3)),
    nb_setval(test_db_snapshot_retry, true),
    assert((user:prolog_trace_interception(Port, Frame, _, Action) :-
                retry_once(Port, Frame, Action)), Hook),
    call_cleanup(
        setup_call_cleanup(
            trace,
            findall(X, db_snapshot_call(S, r(X)), Xs),
            ( notrace, nodebug )),
        erase(Hook)).
test(reenter, [Xs-Hook == [1]-[a], cleanup(cleanup)]) :-
    % A debugger hook calls db_snapshot_call/2 before the goal of an
    % outer one is called
    assertz(r(1)), assertz(lc(a)),
    db_snapshot(S), db_snapshot(S2),
    retractall(r(_)), assertz(r(2)), retractall(lc(_)),
    reentered(call(S2), X, db_snapshot_call(S, r(X)), Xs),
    nb_getval(test_db_snapshot_hook, Hook).
test(reenter_plain, [Xs-Hook == [1]-[], cleanup(cleanup)]) :-
    assertz(r(1)), assertz(lc(a)),
    db_snapshot(S),
    retractall(r(_)), assertz(r(2)), retractall(lc(_)),
    reentered(plain, X, db_snapshot_call(S, r(X)), Xs),
    nb_getval(test_db_snapshot_hook, Hook).
test(reenter_close, [ error(existence_error(db_snapshot, _)),
                      cleanup(cleanup)
                    ]) :-
    % The hook closes the snapshot before the goal is called
    assertz(r(1)),
    db_snapshot(S),
    reentered(close(S), X, db_snapshot_call(S, r(X)), _).
test(reenter_fail, [Xs == [2], cleanup(cleanup)]) :-
    % The request of a db_snapshot_call/2 that the debugger made fail
    % does not reach the next goal
    assertz(r(1)),
    db_snapshot(S),
    retractall(r(_)), assertz(r(2)),
    reentered(fail, X, ( db_snapshot_call(S, r(X)) ; r(X) ), Xs).
test(wrapped, [ error(permission_error(access, wrapped_procedure, _)),
                cleanup(( unwrap_predicate(r(_), test_db_snapshot),
                          cleanup
                        ))
              ]) :-
    assertz(r(1)),
    wrap_predicate(r(_), test_db_snapshot, Wrapped, Wrapped),
    db_snapshot(S),
    db_snapshot_call(S, r(_)).
test(wrapped_late, [ error(permission_error(access, wrapped_procedure, _)),
                     cleanup(( unwrap_predicate(r(_), test_db_snapshot),
                               cleanup
                             ))
                   ]) :-
    % A wrapper that is added after the helper checked the goal
    assertz(r(old)),
    db_snapshot(S),
    retractall(r(_)), assertz(r(new)),
    reentered(wrap, X, db_snapshot_call(S, r(X)), _).
test(scope_wrapped_late,
     [ error(permission_error(access, wrapped_procedure, _)),
       cleanup(( unwrap_predicate(r(_), test_db_snapshot),
                 cleanup
               ))
     ]) :-
    assertz(r(old)),
    db_snapshot_scope(S,
                      ( retractall(r(_)), assertz(r(new)),
                        reentered(wrap, X, db_snapshot_call(S, r(X)), _)
                      )).
test(tabled, [error(permission_error(access, wrapped_procedure, _))]) :-
    db_snapshot(S),
    db_snapshot_call(S, td(_)).
test(static_late, [ error(permission_error(access, private_procedure, _)),
                    cleanup(( abolish(rs/1), dynamic(rs/1) ))
                  ]) :-
    % The predicate is made static after the helper checked the goal
    assertz(rs(1)),
    db_snapshot(S),
    reentered(static, X, db_snapshot_call(S, rs(X)), _).
test(control, [error(permission_error(access, private_procedure, _))]) :-
    db_snapshot(S),
    db_snapshot_call(S, ( r(_), true )).
test(call_n, [ error(permission_error(access, private_procedure, _)),
               cleanup(retractall(p8(_,_,_,_,_,_,_,_)))
             ]) :-
    % The meta-call compiles call/N with N > 8 into a clause of its own,
    % also if the module defines a dynamic call/9
    context_module(M),
    dynamic(db_snapshot_call_n:call/9),
    assertz(p8(a,b,c,d,e,f,g,old)),
    db_snapshot(S),
    retractall(p8(_,_,_,_,_,_,_,_)), assertz(p8(a,b,c,d,e,f,g,new)),
    db_snapshot_call(S, db_snapshot_call_n:call(M:p8, a,b,c,d,e,f,g,_)).
test(call_n_undeclared,
     [ error(permission_error(access, private_procedure, call/9)),
       cleanup(retractall(p8(_,_,_,_,_,_,_,_)))
     ]) :-
    % As call/2 ... call/8, rather than failing as an undefined predicate
    assertz(p8(a,b,c,d,e,f,g,old)),
    db_snapshot(S),
    db_snapshot_call(S, call(p8, a,b,c,d,e,f,g,_)).
test(engine, [ condition(current_prolog_flag(engines, true)),
               AB == [1,2],
               cleanup(cleanup)
             ]) :-
    % An engine that creates its own snapshot is a stable cursor.
    assertz(p(1, k1)), assertz(p(2, k2)),
    setup_call_cleanup(
        engine_create(X, ( db_snapshot(S), db_snapshot_call(S, p(X, _)) ), E),
        ( engine_next(E, A),
          retractall(p(_,_)), assertz(p(99, k99)),
          engine_next(E, B)
        ),
        engine_destroy(E)),
    AB = [A,B].
test(undefined, [fail]) :-
    db_snapshot(S),
    db_snapshot_call(S, no_such_predicate_for_db_snapshot(_)).
test(static, [error(permission_error(access, private_procedure, _))]) :-
    db_snapshot(S),
    db_snapshot_call(S, lists:append(_,_,_)).
test(closed, [error(existence_error(db_snapshot, _)), cleanup(cleanup)]) :-
    fill(3),
    db_snapshot(S),
    db_snapshot_close(S),
    db_snapshot_call(S, p(_,_)).
test(scope_blob_frame, [ error(existence_error(db_snapshot, _)),
                          cleanup(cleanup)
                        ]) :-
    % The frame of a goal of db_snapshot_call/2 holds no scope
    assertz(r(1)),
    db_snapshot(B),
    db_snapshot_scope(S, true),
    db_snapshot_call(B, scope_user(S, _)).
test(other_thread, [ condition(current_prolog_flag(threads, true)),
                     error(permission_error(access, db_snapshot, _)),
                     cleanup(cleanup)
                   ]) :-
    fill(3),
    thread_self(Me),
    thread_create(( db_snapshot(S0),
                    thread_send_message(Me, snapshot(S0)),
                    thread_get_message(done)
                  ), Id),
    thread_get_message(snapshot(S)),
    call_cleanup(db_snapshot_call(S, p(_,_)),
                 ( thread_send_message(Id, done),
                   thread_join(Id, _)
                 )).

:- dynamic scope_user/2.

scope_user(S, Xs) :-
    findall(X, db_snapshot_call(S, r(X)), Xs),
    true.

:- end_tests(db_snapshot_call).
