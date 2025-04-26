From Simplex Require Import Basics Relations.

Inductive eq@{u} {A : Type@{u}} (a : A) : A -> Type@{u} :=
  eq_refl : eq a a.

Local Set Warnings "-notation-overridden".
Notation "x = y" := (eq x y)
                      (at level 70, y at next level, no associativity) : type_scope.
Notation "x = y" := (eq x y)
    (at level 70, y at next level, no associativity).
Register eq as core.identity.type.
Register eq_refl as core.identity.refl.
Register eq_rect as core.identity.ind.

Instance eq_refl' (A : Type) : Reflexive (eq (A:=A)) := @eq_refl A.

Instance eq_trans (A : Type) : Transitive (eq (A:=A)) :=
  fun (a b c : A) (p : a = b) =>
    match p in _ = b return b = c -> a = c with
    | eq_refl _ => fun q => q
    end.

Instance eq_sym (A : Type) : Symmetric (eq (A:=A)) :=
  fun (a b : A) (p : a = b) =>
    match p in _ = b return b = a with
    | eq_refl _ => eq_refl a
    end.

Definition f_equal (A B : Type) (f : A -> B) (x y : A) : x = y -> f x = f y
  := fun p => match p with eq_refl _ => eq_refl (f x) end.

Module Strict_anti_univalence.
  (** Importing this module leads to inconsistency with the univalence axiom. *)
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

Module Strict_hSets.
  (** Idea of this module: if a type is known to be an HSet, then we are allowed to use strict equality on its elements. *)
  Class IsHProp@{u} (A: Type@{u}) : Type@{u}
    := is_hprop: forall x y : A, eq@{u} x y.
  Class IsHSet@{u} (A :Type@{u})
    := hprop_eq : forall x y : A, IsHProp (eq@{u} x y).

  Record HSet@{u} := {
      carrier :> Type@{u};
      is_hset : IsHSet carrier
    }.

  Local Set Definitional UIP.
  Inductive SEq@{u} {A : HSet@{u}} (a : A) : A -> SProp :=
    eq_refl : SEq a a.

  Module Interval.
    Private Inductive I :=
    | zero
    | one.
  (* This is an HSet, but we have to prove that before we can move on. *)
  (*   Axiom seg : SEq zero one. *)
  (*   Definition I_elim (P : I -> Type) (p0 : P zero) (p1 : P one) *)
  (*     (peq : (match seg in SEq _ z return forall (y : P z), Type *)
  (*             with | eq_refl _ => fun y => p0 = y end) p1) *)
  (*     : forall (i : I), P i *)
  (*     := fun i => match i with *)
  (*              | zero => p0 *)
  (*              | one => p1 *)
  (*              end. *)
  End Interval.
End Strict_hSets.


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

Module SEqType.
  Class class_of (A: Type) := {
      seq_rel : A -> A -> SProp;
      seq_if : forall (a b : A), seq_rel a b -> eq a b;
      seq_only_if : forall (a b : A), eq a b -> seq_rel a b
    }.

  Structure t := {
      sort : Type;
      is_seqtype : class_of sort
    }.
  Module Exports.
    Arguments seq_rel [A] {class_of} a b : simpl never.
    Infix "==" := seq_rel (at level 70).
  End Exports.
End SEqType.
Export SEqType.Exports.

Instance seq_rel_reflexive@{u} (A : Type@{u}) `{class : SEqType.class_of A} :
  Reflexive@{SProp|u Set} (@SEqType.seq_rel A class)
  := fun h => SEqType.seq_only_if h h (eq_refl h).

Instance seq_rel_transitive@{u} (A : Type@{u}) `{class : SEqType.class_of A} :
  Transitive@{SProp|u Set} (@SEqType.seq_rel A class).
Proof.
  intros x y z p.
  apply (SEqType.seq_if) in p. destruct p. exact (fun q => q).
Defined.

Instance seq_rel_symmetric@{u} (A : Type@{u}) `{class : SEqType.class_of A} :
  Symmetric@{SProp|u Set} (@SEqType.seq_rel A class).
Proof.
  intros x y p.
  apply (SEqType.seq_if) in p. destruct p. exact (reflexive _).
Defined.
