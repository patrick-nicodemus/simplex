From Simplex Require Import Basics Relations Datatypes_core.
Local Set Implicit Arguments.

Section eq.
Unset Elimination Schemes.
Inductive eq@{u} {A : Type@{u}} (a : A) : A -> Type@{u} :=
  eq_refl : eq a a.

Definition eq_rect@{s;u u'} {A : Type@{u}} (a : A)
  (P : (forall (a' : A), eq a a' -> Type@{s;u'})) :
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
  (P : A -> Type@{s;u1})
  (a b : A) (p : a = b)
  : P b -> P a
  := match p with | eq_refl _ => fun x => x end.

Instance eq_sym (A : Type) : Symmetric (eq (A:=A)) :=
  fun (a b : A) (p : a = b) =>
    match p in _ = b return b = a with
    | eq_refl _ => eq_refl a
    end.

Local Infix "·" := transitive (at level 60).

Definition eq_assoc {A : Type}
  {a b c d: A} (p : a = b) (q : b = c) (r : c = d)
  : (p · q) · r = p · (q · r).
Proof.
  destruct r.
  destruct q.
  destruct p.
  reflexivity.
Defined.

Definition f_equal {A B : Type} (f : A -> B) [x y : A] : x = y -> f x = f y
  := fun p => match p with eq_refl _ => eq_refl (f x) end.

Record bijection (A B : Type) :=
  {
    section : A -> B;
    retraction : B -> A;
    lr_inv : forall (a : A), retraction (section a) = a;
    rl_inv : forall (b : B), section (retraction b) = b;
  }.

Class IsHProp@{u} (A: Type@{u}) : Type@{u}
  := is_hprop: forall x y : A, eq@{u} x y.

Instance IsHProp_unit : IsHProp unit.
Proof.
  intros x y.
  destruct x, y.
  reflexivity.
Defined.

Instance IsHProp_empty : IsHProp empty.
Proof.
  intros x ; destruct x.
Defined.

Class IsHSet@{u} (A :Type@{u})
  := hprop_eq : forall x y : A, IsHProp (eq@{u} x y).

Definition eq_natural (A B: Type) (f g : A -> B) (h : forall x, f x = g x)
  (a0 a1 : A) (s : a0 = a1)
  : f_equal f s · (h a1) = (h a0) · f_equal g s.
Proof.
  destruct s.
  simpl; destruct (h a0).
  exact (eq_refl _).
Defined.

Definition hcomp2 {A : Type} {a b c : A} [p1 q1 : a = b] [p2 q2 : b = c]
  : (p1 = q1) -> (p2 = q2) -> (p1 · p2) = (q1 · q2).
Proof.
  intro h; destruct h.
  intro h'; destruct h'.
  reflexivity.
Defined.

Definition h_inv {A : Type} {a b : A} {p q : a = b} (s : p = q) :
  (p^ = q^).
Proof.
  destruct s.
  reflexivity.
Defined.

(* Theorem h_invl {A : Type} {a b : A} (p q : a = b) (s : p = q) *)
(*   : hcomp2 s (h_inv p q s) *)

Definition post_whisker {A : Type} {a b c : A} [p q : a = b]
  (s : p = q) (h : b = c)
  := hcomp2 s (eq_refl h).

Definition pre_whisker {A : Type} {a b c : A} [p q : b = c] (h : a = b) (s : p = q)
  (s : p = q) 
  := hcomp2 (eq_refl h) s.

Definition right_unitor {A : Type} {a b :A} (q : a = b) : q · eq_refl _ = q.
Proof.
  destruct q.
  reflexivity.
Defined.

Theorem postcomp_iso {A : Type} {a b c : A} (p q : a = b) (s : b = c)
  (h : p · s = q · s) : p = q.
Proof.
  revert h.
  destruct s.
  destruct (right_unitor p)^.
  destruct (right_unitor q)^.  
  exact (fun x => x).
Defined.

Theorem precomp_iso {A : Type} {a b c : A} (s : a = b) (p q : b = c) 
  (h : s · p = s · q) : p = q.
Proof.
  destruct s.
  exact h.
Defined.

Theorem hcomp2_rid_nat {A : Type} {a b : A} (p q : a = b) (s : p = q) :
  (hcomp2 s (eq_refl (eq_refl b))) · (right_unitor q) =
    right_unitor p · s.
Proof.
  destruct s.
  simpl. unfold transitive; simpl.
  exact (right_unitor _ )^.
Defined.

Theorem ap_inv (A : Type) (a b c d : A) (p : a = b) (q : b = d)
  (s : a = c) (t : c = d)
  (k : p · q = s · t) : p · q · t^ = s.
Proof.
  destruct t.
  unfold symmetry. unfold eq_sym.
  destruct (right_unitor s)^.
  destruct (right_unitor (p · q))^.
  exact k.
Defined.

Theorem post_whisker_faithful {A : Type} {a b c : A} [p q : a = b]
  (s1 s2 : p = q) (h : b = c) :
  post_whisker s1 h = post_whisker s2 h -> s1 = s2.
Proof.
  intro t.
  destruct h.
  unfold post_whisker in t.
  apply (f_equal (fun z => z · (right_unitor q))) in t.
  rewrite hcomp2_rid_nat in t.
  rewrite hcomp2_rid_nat in t.
  apply precomp_iso in t.
  exact t.
Defined.

Theorem bijection_preserves_hprop (A B: Type) :
  bijection A B -> IsHProp A -> IsHProp B.
Proof.
  intros [section retraction' lr_inv' rl_inv'] is_hprop'.
  intros p q.
  destruct (rl_inv' p).
  destruct (rl_inv' q).
  destruct (is_hprop' (retraction' p) (retraction' q)).
  reflexivity.
Defined.

Theorem bijection_preserves_hset (A B : Type) (p : bijection A B) :
  IsHSet A -> IsHSet B.
Proof.
  intros IsHSetA b b'.
  eapply (@bijection_preserves_hprop ((retraction p b) = (retraction p b'))).
  - unshelve econstructor.
    + intro k. apply (f_equal (section p)) in k.
      destruct (rl_inv p b)^.
      destruct (rl_inv p b')^.
      exact k.
    + exact (f_equal (retraction p) (x:=b) (y:=b')).
    + apply (fun a => IsHSetA (retraction p b) (retraction p b') _ a).
    + simpl. intro eq_bb'.
      destruct eq_bb',
        (rl_inv p b).
      reflexivity.
  - apply IsHSetA.
Defined.

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
  Record HSet@{u} := {
      carrier :> Type@{u};
      is_hset : IsHSet carrier
    }.

  Local Set Definitional UIP.
  Inductive SEq@{u} {A : HSet@{u}} (a : A) : A -> SProp :=
    seq_refl : SEq a a.

  Module Interval.
    Private Inductive I :=
    | zero
    | one.

    Definition EC : I -> I -> Set :=
      fun i => match i with
            | zero => fun j => match j with
                     | zero => unit
                     | one => empty
                     end
            | one => fun j => match j with
                    | zero => empty
                    | one => unit
                    end
            end.

    Instance IsHPropEC (i j : I) : IsHProp (EC i j).
    Proof.
      destruct i, j; exact _.
    Defined.

    Definition encode : forall i j : I,
        EC i j -> i = j
      := fun i => match i return forall j : I, EC i j -> i = j with
         | zero => fun j => match j return EC zero j -> eq _ j with
                  | zero => fun _ => eq_refl zero
                  | one => fun e => match e with end
                  end
         | one => fun j => match j with
                 | zero => fun e => match e with end
                 | one => fun _ => eq_refl one
                 end
               end.

    Definition decode : forall i j : I,
        i = j -> EC i j
      := fun i j p => match p with
                   | eq_refl _ =>
                       match i with
                       | zero => tt
                       | one => tt
                       end
                   end.

    Theorem encode_decode_sect :
      forall (i j: I) (a : EC i j), decode (encode _ _ a) = a.
    Proof.
      intros i j; destruct i, j.
      - simpl. intro a; destruct a; reflexivity.
      - simpl. intro a; destruct a.
      - simpl. intro a; destruct a.
      - simpl. intro a; destruct a; reflexivity.
    Defined.

    Theorem encode_decode_retr :
      forall (i j: I) (a : i = j), encode i j (decode a) = a.
    Proof.
      intros i j a; destruct a, i; reflexivity.
    Defined.

    Definition EC_bijection (i j : I) : bijection (EC i j) (i = j) :=
      {|
        section := encode i j;
        retraction := decode (i:=i) (j:=j);
        lr_inv := fun a => encode_decode_sect i j a;
        rl_inv := fun a => encode_decode_retr (i:=i) (j:=j) a;
      |}.

    Instance I_IsHSet : IsHSet I.
    Proof.
      intros i j.
      apply (bijection_preserves_hprop (EC_bijection i j)).
      exact _.
    Defined.
    
    Axiom seg : SEq (A:= {| carrier := I; is_hset := _ |}) zero one.

    Definition I_elim (P : I -> Type) (p0 : P zero) (p1 : P one)
      (peq : (match seg in SEq _ z return forall (y : P z), Type
              with | seq_refl _ => fun y => p0 = y end) p1)
      : forall (i : I), P i
      := fun i => match i with
               | zero => p0
               | one => p1
               end.
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
  Reflexive@{SProp;u Set} (@SEqType.seq_rel A class)
  := fun h => SEqType.seq_only_if@{u} (eq_refl h).

Instance seq_rel_transitive@{u} (A : Type@{u}) `{class : SEqType.class_of@{u} A} :
  Transitive@{SProp;u Set} (@SEqType.seq_rel A class).
Proof.
  intros x y z p.
  apply (SEqType.seq_if) in p. destruct p. exact (fun q => q).
Defined.

Instance seq_rel_symmetric@{u} (A : Type@{u}) `{class : SEqType.class_of@{u} A} :
  Symmetric@{SProp;u Set} (@SEqType.seq_rel@{_} A class).
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
