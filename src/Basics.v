Declare Scope type_scope.
Bind Scope type_scope with Sortclass.

#[warnings="-w -notation-overridden"]
Notation "A -> B" := (forall _ : A, B) (at level 99, B at level 200).

#[export] Set Typeclasses Strict Resolution.
#[export] Unset Typeclass Resolution For Conversion.
#[export] Set Universe Polymorphism.
#[export] Set Primitive Projections.
#[global] Set Printing Unfolded Projection As Match.

Inductive sUnit : SProp := stt.
Inductive sEmpty : SProp := .

Definition not@{s|u|} (A : Type@{s|u}) := A -> sEmpty.

#[warnings="-w -notation-overridden"]
Notation "~ x" := (not x) (at level 75, right associativity) : type_scope.

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
