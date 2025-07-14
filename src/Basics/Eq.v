From Simplex Require Import Basics Relations.
Local Set Implicit Arguments.

Section eq.
Unset Elimination Schemes.
Inductive eq@{u} {A : Type@{u}} (a : A) : A -> Type@{u} :=
  eq_refl : eq a a.

Definition eq_rect@{s;u u'} {A : Type@{u}} (a : A)
  (P : (forall (a' : A), eq a a' -> Type@{s|u'})) :
  (P a (eq_refl a)) -> (forall (a' : A) (p : eq a a'), P a' p)
  := fun s a' p => match p with eq_refl _ => s end.
End eq.

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

Definition transport@{s;u0 u1|} (A : Type@{u0})
  (P : A -> Type@{s|u1})
  (a b : A) (p : a = b)
  : P b -> P a
  := match p with | eq_refl _ => fun x => x end.

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

  Definition to {A : Type} {a b : A} (p : a = b) : SEq a b := match p with Eq.eq_refl _ => eq_refl _ end.

  Definition from {A : Type} {a b : A} (q : SEq a b) : a = b := match q with eq_refl _ => Eq.eq_refl _ end.
  
  Lemma to_from_inv (A : Type) (a b : A) (p : a = b) : from (to p) = p.
  Proof.
    destruct p. reflexivity.
  Defined.

  Theorem UIP : forall (A : Type) (a : A) (p : a = a), p = Eq.eq_refl a.
  Proof.
    intros A a p.
    rewrite <- (to_from_inv p).
    change (to p) with (to (Eq.eq_refl a)).
    reflexivity.
  Defined.
    
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
  := fun h => SEqType.seq_only_if@{u} (eq_refl h).

Instance seq_rel_transitive@{u} (A : Type@{u}) `{class : SEqType.class_of@{u} A} :
  Transitive@{SProp|u Set} (@SEqType.seq_rel A class).
Proof.
  intros x y z p.
  apply (SEqType.seq_if) in p. destruct p. exact (fun q => q).
Defined.

Instance seq_rel_symmetric@{u} (A : Type@{u}) `{class : SEqType.class_of@{u} A} :
  Symmetric@{SProp|u Set} (@SEqType.seq_rel@{_} A class).
Proof.
  intros x y p.
  apply (SEqType.seq_if) in p. destruct p. exact (reflexive _).
Defined.

Theorem isContr_lemma (A : Type) (H : forall y z : A, y = z)
  (y0 z0 y1 z1 : A) (p : y0 = y1) (q : z0 = z1)
  :
  p = match H y0 z0 in eq _ z0 return forall q : z0 = z1, y0 = y1
      with
      | eq_refl _ => match H y1 z1 in eq _ z1 return forall q : y0 = z1, y0 = y1 with
                    |  eq_refl _ => fun q => q
                    end
      end q.
Proof.
  destruct q, p, (H y0 z0).
  exact (eq_refl _).
Defined.

Theorem isContr_up (A : Type) (H : forall y z : A, y = z)
  (y z : A) (p q : y = z) : p = q.
Proof.
  rewrite (isContr_lemma H p q).
  apply symmetry.
  apply isContr_lemma.
Defined.
