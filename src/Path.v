From Simplex Require Import Basics Graph Nat Eq PreOrder.Core Tactics.
#[local] Set Implicit Arguments.
(** Paths through a directed graph. *)

Inductive path@{s|u0 u1|} (A : Type@{u0}) (R : A -> A -> Type@{s|u1}) (a : A)
  : A -> Type@{max(u0,u1)}
  := 
| nil : path R a a
| cons (x y : A) (f : R x y) (p : path R a x) : path R a y.

Definition length@{s|u0 u1|} (A : Type@{u0}) (R : A -> A -> Type@{s|u1}) (a : A)
  : forall (b : A), path@{s|u0 u1} R a b -> nat
  := fix length _ path :=
    match path with
    | nil _ _ => 0
    | cons _ _ p' => Nat.S(length _ p')
    end.

Theorem length0@{s|u0 u1|} (A : Type@{u0}) (R : A -> A -> Type@{s|u1})
  (a b: A) (p : path R a b) (eq_pf : length p == 0) : a = b.
Proof.
  destruct p.
  - reflexivity.
  - simpl in eq_pf. contradiction.
Defined.

Theorem length1@{s|u0 u1|} (A : Type@{u0}) (R : A -> A -> Type@{s|u1})
  (a b: A) (p : path R a b) (eq_pf : length p == 1) : R a b.
Proof.
  destruct p.
  - contradiction.
  - simpl in eq_pf. apply length0 in eq_pf; destruct eq_pf. exact f.
Defined.

Definition nth_vertex @{s|u0 u1|} (A : Type@{u0}) (R : A -> A -> Type@{s|u1}) (a : A)
  : forall (b : A) (n : nat), path@{s|u0 u1} R a b -> A
  := fix nth b n p :=
    match n with
    | 0 => b
    | S n' => match p with
             | nil _ _ => a
             | cons _ _ p => nth _ n' p
             end
    end.

Definition drop@{s|u0 u1|} (A : Type@{u0}) (R : A -> A -> Type@{s|u1})
  (a : A)
  : forall (b : A) (n : nat) (p : path@{s|u0 u1} R a b), path@{s|u0 u1} R a (nth_vertex n p).
Proof.
  intros b n; revert b.
  refine ((fix recfun (n : nat) := _) n).
  destruct n.
  - exact (fun _ x => x).
  - intros b p; destruct p; simpl.
    + exact (nil _ _).
    + apply recfun.
Defined.

Definition take@{s|u0 u1|} (A : Type@{u0}) (R : A -> A -> Type@{s|u1})
  (a : A)
  : forall (b : A) (n : nat) (p : path@{s|u0 u1} R a b), path@{s|u0 u1} R (nth_vertex n p) b.
Proof.
  intros b n; revert b.
  refine ((fix recfun (n : nat) := _) n); destruct n.
  - simpl. exact (fun _ _ => nil _ _).
  - intros b p; destruct p; simpl.
    + exact (nil _ _).
    + exact (cons _ f (recfun n x p)).
Defined.

Theorem drop_length@{s|u0 u1|} (A : Type@{u0}) (R : A -> A -> Type@{s|u1})
  (a : A) (b :A) (p : path@{s|u0 u1} R a b) k (le : Nat.le k (length p))
  : length (drop k p) = length p - k.
Proof.
  revert k le.
  refine ((fix recp (b0 : A) (p0 : path@{s|u0 u1} R a b0) := _ ) b p).
  destruct p0.
  - intro k. destruct k; reflexivity.
  -  intro k. destruct k.
    + intros; reflexivity.
    + simpl. intro h. apply recp. exact h.
Defined.

Print Notation "_ <= _".
Print "_ <= _".
Print Canonical Projections.
Theorem take_length@{s|u0 u1|} (A : Type@{u0}) (R : A -> A -> Type@{s|u1})
  a b (p : path R a b) (k : nat) (le : k <= length p)
  : length (take k p) = k.
Proof.
  revert k le.
  refine ((fix recfun (b0 : A) (p0 : path R a b0) := _) b p); clear b p.
  destruct p0.
  - simpl. intro k; destruct k.
    + intros _; reflexivity.
    + intros ?; contradiction.
  - simpl. intros k h; destruct k.
    + reflexivity.
    + simpl. apply eq_S. apply recfun. exact h.
Defined.
