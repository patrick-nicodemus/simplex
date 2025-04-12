From Simplex Require Import Basics.
Inductive eq {A : Type} (a : A) : A -> Type :=
  eq_refl : eq a a.

Local Set Warnings "-notation-overridden".
Notation "x = y" := (eq x y)
                      (at level 70, y at next level, no associativity) : type_scope.
Notation "x = y" := (eq x y)
    (at level 70, y at next level, no associativity).
Register eq as core.identity.type.
Register eq_refl as core.identity.refl.
Register eq_rect as core.identity.ind.
