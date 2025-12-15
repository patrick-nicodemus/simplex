From Simplex.Basics Require Import Basics Eq Nat.
From elpi Require Import elpi.

Elpi Db core_hint.db lp:{{
    kind tag type. % A tag is just a category for a hint.
    % Instead of having many hint databases, we have one hint database with many tags.
    type core tag. % Our replacement for the core auto database.
    pred applicable o:tag i:goal o:open-tactic.

    applicable core (goal _ _ (prod Name Type _)  _ _) (refine (fun Name Type _)).
}}.

Elpi Tactic next_valid.
Elpi Accumulate Db core_hint.db. 
Elpi Accumulate lp:{{ 
    solve G GL :-
        applicable _ G Tac,
        Tac G GL.
}}.

Elpi Tactic naive_nb.
Elpi Accumulate Db core_hint.db.
Elpi Accumulate lp:{{
    solve G GL :-
        applicable _ G Tac, !,
        Tac G GL',
        coq.ltac.all (coq.ltac.open solve) GL' GL
    .
}}.

Module Test.
Goal forall (x : nat), x = x.
Proof.
    ltac1:(elpi next_valid).
Abort.
End Test.