From Simplex Require Import Basics Relations Datatypes_core Eq.
Local Set Implicit Arguments.

Local Set Definitional UIP.
Unset Elimination Schemes.

(** This file defines the strict-prop valued equality seq. In order to
    preserve some homotopical content and make HoTT-style mathematics
    possible (including compatibility with univalence) we restrict the
    usage of SProp by making it private and defining our own
    eliminators. The effects of these are similar to declaring
    truncation axioms except that they do not block computation
    (although they do introduce potential nontermination - pick your
    poison).

    Importing this module causes all sets to become
    0-truncated and all types in Type@{1} to become 1-truncated (in
    particular, Set is 1-truncated).
 *)

Private Inductive seq@{u} {A : Type@{u}} (a : A) : A -> SProp :=
  seq_refl : seq a a.

Infix "≡" := seq (at level 44).

Instance Reflexive_seq@{u} {A :Type@{u}} :
  Reflexive@{SProp;u Set} (@seq A) := fun x => seq_refl _.

Instance Symmmetric_seq@{u} {A :Type@{u}} : Symmetric@{SProp;u Set} (@seq A) 
  := fun x y p => match p in seq _ y return seq y x with
               | seq_refl _ => seq_refl _
               end.

Instance Transitive_seq@{u} {A :Type@{u}} : Transitive@{SProp;u Set} (@seq A) 
  := fun x y z p => match p in seq _ y return seq y z -> seq x z with
                 | seq_refl _ => fun q => q
                 end.

(** The usual path induction scheme with an extra requirement -
    it can only be used at contractible components of a space. *)
Definition seq_rec@{s;u u1}  {A : Type@{u}} (a : A)
  (h: forall b, IsHProp (a = b))
  (P : forall b, a ≡ b -> Type@{s;u1})
  : P a (seq_refl a) -> forall (b : A) (p : a ≡ b), P b p
  := fun e b p => match p with
               | seq_refl _ => e
               end.

(** Elimination into SProps is unrestricted. *)
Definition seq_selim@{u} {A : Type@{u}} (a : A)
  (P : forall b, a ≡ b -> SProp)
  : P a (seq_refl a) -> forall (b : A) (p : a ≡ b), P b p
  := fun e b p => match p with
               | seq_refl _ => e
               end.

(** Elimination out of Sets is unrestricted.
    A consequence of this definition is that
    all objects of Set are hsets. *)
Definition seq_set@{s;u} {A : Set} (a : A)
  (P : forall b, a ≡ b -> Type@{s;u})
  : P a (seq_refl a) -> forall (b : A) (p : a ≡ b), P b p
  := fun e b p => match p with
           | seq_refl _ => e
               end.

Module Type U1_Truncated_Sig.
  Parameter u1_2truncated : forall (A : Type@{Set+1}) (a b: A), IsHSet (a = b).
End U1_Truncated_Sig.

(** This module exports a proof that the next level universe
    beyond Set is 2-truncated. There is an
    an hSet of ways two Sets can be identified.
 *)
Module U1_Truncated : U1_Truncated_Sig.
  Definition to@{u} (A : Type@{u}) (a b : A) : a ≡ b -> a = b
    := fun e => match e with seq_refl _ => eq_refl _ end.

  Definition from@{u} (A : Type@{u}) (a b : A) : a = b -> a ≡ b
    := fun e => match e with eq_refl _ => seq_refl _ end.

  Definition endo@{u} (A : Type@{u}) (a b: A) : a = b -> a = b
    := fun p => to (from p).

  Definition endo_id@{u} (A: Type@{u}) (a b: A) (p : a = b) : endo p = p
    := match p with eq_refl _ => eq_refl _ end.

  Theorem all_hsets@{u} (A: Type@{u}) (a b: A) (p q: a = b) : p = q.
  Proof.
    destruct (endo_id p).
    destruct (endo_id q).
    reflexivity.
  Defined.
                   
  Definition u1_2truncated (A : Type@{Set+1}) (a b: A) : IsHSet (a = b)
    := all_hsets (A:= a=b).
End U1_Truncated.
Export U1_Truncated.

Record HSet@{u} := {
    carrier :> Type@{u};
    is_hset : IsHSet carrier
  }.

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
  
  Axiom seg : seq (A:= {| carrier := I; is_hset := _ |}) zero one.

  Definition I_elim (P : I -> Type) (p0 : P zero) (p1 : P one)
    (peq : (match seg in seq _ z return forall (y : P z), Type
            with | seq_refl _ => fun y => p0 = y end) p1)
    : forall (i : I), P i
    := fun i => match i with
             | zero => p0
             | one => p1
             end.
End Interval.

Module S1.
  (* This can't live in Set. TODO: When universe polymorphism is merged,
      change to Set+1 *)
  Private Inductive t : Type := pt.
  Axiom loop : pt = pt.

  Definition elim (P : t -> Type)
    (P_loop : P pt = transport (fun _ => Type) loop (P pt))
    (pf_P_pt : P pt)
    (pf_P_loop : transport P loop pf_P_pt = pf_P_pt)
    : forall (x : t), P x
    := fun x => match x with pt => pf_P_pt end.
End S1.

(** I'm not sure of any examples of this right now which are not hSets.
    I can't think of a proof of equivalence
    It seems like it might be "morally" equivalent,
    topologically if Δ : X -> X x X is a fibered retract of X^I -> X x X
    then X is path discrete. Certainly if it's a deformation retract
    then X is discrete. 
 *)
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
