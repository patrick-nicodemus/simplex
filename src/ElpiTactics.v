From elpi Require Import elpi.

Elpi Db core_hint.db lp:{{
    kind tag type. % A tag is just a category for a hint.
    pred applicable o:tag i:goal o:open-tactic.
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
