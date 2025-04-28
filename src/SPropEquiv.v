From Simplex Require Import Basics.
Class SPropEquiv (A : Type) (B : SProp) := {
    to_sprop : A -> B;
    to_type : B -> A
  }.
