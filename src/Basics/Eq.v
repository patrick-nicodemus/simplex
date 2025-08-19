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

Definition apd@{u0 u1} [A : Type@{u0}]
  (P : A -> Type@{u1})
  (f : forall (a: A), P a)
  (a b : A) (p : a = b) :
  (f a = transport P p (f b))
    := match p with | eq_refl _ => eq_refl _ end.

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

Definition sym_inv {A : Type} {a b : A} (p : a = b) : p^^ = p.
Proof.
  destruct p; reflexivity.
Defined.

Definition h_inv' {A : Type} {a b :A} {p q : a = b} : p^ = q^ -> p = q.
Proof.
  intro s.
  apply h_inv in s.
  destruct (sym_inv p)^.
  destruct (sym_inv q)^.
  exact s.
Defined.

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

Lemma apd1 [A: Type] (a x1 x2 : A) (p : x1 = x2) (q: a = x2):
  transport (fun x => a = x) p q = q · p^.
Proof.
  destruct p.
  simpl. unfold symmetry. simpl.
  apply symmetry; exact (right_unitor _).
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

Theorem sig_eq@{s;+|} (A : Type) (P : A->Type@{_})
  (x y : @sig A P ) :
  forall p : ex_val x = ex_val y,
    ex_pf x = transport P p (ex_pf y) -> x = y.
Proof.
  destruct x, y.
  simpl.
  destruct p.
  simpl; intro k; destruct k.
  reflexivity.
Defined.

Theorem sig2_eq@{s;+|} (A : Type)
  (P : A->Type@{_})
  (Q : A->Type@{_})
  (x y : @sig2 A P Q) :
  forall p : ex2val x = ex2val y,
    ex2P x = transport P p (ex2P y) ->
    ex2Q x = transport Q p (ex2Q y) ->
    x = y.
Proof.
  destruct x, y.
  simpl.
  destruct p.
  simpl; intro k; destruct k.
  intro k; destruct k.
  reflexivity.
Defined.
