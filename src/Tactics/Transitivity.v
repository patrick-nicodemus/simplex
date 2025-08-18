From Simplex Require Import Basics.Basics Basics.Relations.

From elpi Require Import elpi.
(* Elpi Tactic show. *)
(* Elpi Accumulate lp:{{ *)
(*       solve (goal Ctx _Trigger Type Proof _ ) _ :- *)
(*             soq.say "Goal" Ctx "|-" Proof ":" Type. *)
(*   }}. *)

(* Elpi Accumulate lp:{{ *)
(*     solve (goal _Ctx _Trigger _GoalType _Prooftm _Args as G) GL :- *)
(*       refine {{_}} G GL. *)
(*   }}. *)

Elpi Tactic transitivity.
Elpi Accumulate lp:{{
    func isTransitive term, term -> term.
    isTransitive T R A :-
      coq.elaborate-skeleton _ {{@Transitive lp:T lp:R}} A ok.
      
    solve (goal _Ctx _Trigger GoalType _Prooftm Args as G) GL :-
      GoalType = {{ lp:R lp:X lp:Z }},
      coq.typecheck X XType ok,
      isTransitive XType R PfTrans,
      Args = [trm Y],
      refine {{lp:PfTrans lp:X lp:Y lp:Z _ _}} G GL.
  }}.
