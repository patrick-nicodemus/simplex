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

Module Strict_anti_univalence.
  (** Importing this module leads to inconsistency with the univalence axiom.  *)
  Local Set Definitional UIP.
  Local Set Universe Polymorphism.
  Inductive SEq@{u} {A : Type@{u}} (a : A) : A -> SProp :=
    eq_refl : SEq a a.

  Module Interval.
    Private Inductive I :=
    | zero
    | one.

    Axiom seg : SEq zero one.
    Definition I_elim (P : I -> Type) (p0 : P zero) (p1 : P one)
      (peq : (match seg in SEq _ z return forall (y : P z), Type
              with | eq_refl _ => fun y => p0 = y end) p1)
      : forall (i : I), P i
      := fun i => match i with
               | zero => p0
               | one => p1
               end.
  End Interval.
End Strict_anti_univalence.

Module Strict.
  (** Importing this module "should be consistent" with univalence (https://arxiv.org/pdf/1311.4002), see also (https://www.sciencedirect.com/science/article/pii/S0022404921000232?via%3Dihub), end of section 2 *)
  Local Set Definitional UIP.
  Inductive SEq {A : Set} (a : A) : A -> SProp :=
    eq_refl : SEq a a.

  Module Interval.
    Private Inductive I :=
    | zero
    | one.

    Axiom seg : SEq zero one.
    Definition I_elim (P : I -> Type) (p0 : P zero) (p1 : P one)
      (peq : (match seg in SEq _ z return forall (y : P z), Type
              with | eq_refl _ => fun y => p0 = y end) p1)
      : forall (i : I), P i
      := fun i => match i with
               | zero => p0
               | one => p1
               end.
  End Interval.
End Strict.
