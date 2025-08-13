Require Corelib.Init.Datatypes.
Create HintDb typeclass_instances discriminated.
Declare Scope type_scope.
Bind Scope type_scope with Sortclass.
Delimit Scope type_scope with type.

#[warnings="-w -notation-overridden"]
Notation "A -> B" := (forall _ : A, B) (at level 99, B at level 200).

(** Weakened from "Set Typeclasses Strict Resolution" *)
#[export] Set Typeclasses Default Mode "!".
#[export] Unset Typeclass Resolution For Conversion.
#[export] Set Universe Polymorphism.
#[export] Set Primitive Projections.
#[global] Set Printing Unfolded Projection As Match.
#[local] Set Implicit Arguments.

Require Export Ltac2.Ltac2.
Add Search Blacklist "_subproof" "_subterm" "Private_".

Import Ltac2.Std.
Ltac2 hnf_red_flags :=
    {
      rStrength := Head;
      rBeta := true;
      rMatch := true;
      rFix := true;
      rCofix := true;
      rZeta := true;
      rDelta := true;
      rConst := []
    }.

Inductive Squash (A : Type) : SProp :=
| unbox (a : A) : Squash A.

Class SProp_iff (A : Type) := sprop_elim : Squash A -> A.
