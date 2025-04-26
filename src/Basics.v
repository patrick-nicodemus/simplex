Declare Scope type_scope.
Bind Scope type_scope with Sortclass.

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

Definition flip@{s0 s1 s2|u0 u1 u2|}
  (A : Type@{s0|u0})
  (B : Type@{s1|u1})
  (C : forall (a : A) (b : B), Type@{s2|u2})
  (f : forall (a : A) (b : B), C a b)
  : forall (b : B) (a : A), C a b
  := fun (b : B) (a : A) => f a b.
