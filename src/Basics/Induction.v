From Simplex Require Import Basics.Basics.

From elpi Require Import elpi.

Class Implication@{s1 s2;u1 u2|} (A : Type@{s1;u1}) (B : Type@{s2;u2})
  := impl : A -> B.

Elpi Db induction.db lp:{{
      pred associated i:term, o:term.
  }}.

Elpi Tactic induction.
Elpi Accumulate Db induction.db.
Elpi Accumulate lp:{{
    solve (goal _Ctx _RawSolution _Ty _Solution Args as G) GL :-
      coq.say Args,
      Args = [trm Trm],
      coq.say "Yip!"
      associated Trm Trm',
      coq.say "Hi!"
      coq.ltac.call "induction" [trm Trm'] G GL.
  }}.
