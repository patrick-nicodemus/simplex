From Simplex.Basics Require Import Basics Eq Nat.
From elpi Require Export elpi.

Elpi File core_functionality lp:{{ 
    namespace unshelve-refine {
        pred tac o:term o:goal o:list sealed-goal.
        tac T (goal _ RawEv Ty Ev _) GL :-
            rm-evar RawEv Ev,
            (@keepunivs! => coq.elaborate-skeleton T Ty TR ok),
            coq.ltac.collect-goals TR Gs Ghidden,
            RawEv = T,
            Ev = TR,
            std.append Ghidden Gs GL.
    }
}}.

Elpi File constructor lp:{{
   namespace constructor { 
   type tac open-tactic.
   tac (goal _ _ Ty _ _ as G) GS :- std.do! [
    @ltacfail! _ =>
      std.assert! (whd Ty [] Ty' _, (global (indt GR) = Ty'; pglobal (indt GR) _ = Ty'))
       "The goal is not an inductive type",
    coq.env.indt GR _ _ _ _ Ks Kt,
    std.exists2 Ks Kt (k\ t\ sigma P\
      coq.saturate t (global (indc k)) P,
    refine P G GS)
  ].
  }
}}.

Elpi Db core_hint.db lp:{{
    kind tag type. % A tag is just a category for a hint.
    % Instead of having many hint databases, we have one hint database with many tags.
    type core tag. % Our replacement for the core auto database.
    pred applicable o:tag i:goal o:open-tactic.
}}.

(* Elpi Accumulate core_hint.db File constructor. *)
Elpi Accumulate core_hint.db File core_functionality.
Elpi Accumulate core_hint.db lp:{{
    % If it's a lambda, you can try intro.
    applicable core (goal _ _ (prod Name Type _)  _ _) (refine (fun Name Type _)).

    % Constructor (global case)
    applicable core (goal _ _ Ty _ _ ) Tac :-
      whd Ty [] Ty' _,
      global (indt GR) = Ty',
      coq.env.indt GR _ _ _ _ Ks Kt,
      (Tac = G\ GS\
        std.exists2 Ks Kt (k\ t\ sigma P\
           coq.saturate t (global (indc k)) P,
           unshelve-refine.tac P G GS)).

    % Constructor (pglobal case)
    applicable core (goal _ _ Ty _ _ ) Tac :-
      whd Ty [] Ty' _,
      pglobal (indt GR) U = Ty',
      coq.env.indt GR _ _ _ _ Ks Kt,
       (Tac = G\ GS\
        std.exists2 Ks Kt (k\ t\ sigma P\
           coq.saturate t (pglobal (indc k) U) P,
           unshelve-refine.tac P G GS)).
}}.

Elpi Tactic next_valid.
Elpi Accumulate Db core_hint.db. 
Elpi Accumulate lp:{{ 
    solve G GL :- 
        applicable _ G _Tac,
        refine _ G GL.
        %Tac G GL.
}}.

Elpi Tactic naive_nb.
Elpi Accumulate Db core_hint.db.
Elpi Accumulate lp:{{
    solve G GL :-
        applicable _ G Tac, 
        Tac G GL', !,
        coq.ltac.all (coq.ltac.open solve) GL' GL
    .
}}.

Module Test.
Goal forall (x : nat), x = x.
Proof.
    ltac1:(elpi next_valid).
Abort.
End Test.