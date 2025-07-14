From Simplex Require Import Basics Datatypes List Graph Nat Eq PreOrder.Core Tactics.
#[local] Set Implicit Arguments.

(** TODO: Group this code by [path] and [path_on] *)
(** Paths through a directed graph. *)
Inductive path@{s;u0 u1} (A : Type@{u0}) (R : A -> A -> Type@{s;u1}) (a : A)
  : A -> Type@{max(u0,u1)}
  := 
| nil : path R a a
| cons (x y : A) (f : R x y) (p : path R a x) : path R a y.

(** Paths "riding" a given list of nodes. *)
Open Scope list_scope.

Fixpoint path_on@{s;u0 u1} (A : Type@{u0}) (R : A -> A -> Type@{s;u1})
  (a : A) (l : list A) : Type@{s;u1} :=
  match l with
  | List.nil => unit@{s;}
  | hd :: tl => (R a hd * path_on R hd tl)%type
  end.

Definition length@{s;u0 u1} (A : Type@{u0}) (R : A -> A -> Type@{s;u1}) (a : A)
  : forall (b : A), path@{s;u0 u1} R a b -> nat
  := fix length _ path :=
    match path with
    | nil _ _ => 0
    | cons _ _ p' => Nat.S(length _ p')
    end.

Theorem length0@{s;u0 u1} (A : Type@{u0}) (R : A -> A -> Type@{s;u1})
  (a b: A) (p : path R a b) (eq_pf : length p == 0) : a = b.
Proof.
  destruct p.
  - reflexivity.
  - simpl in eq_pf. contradiction.
Defined.

Theorem length1@{s;u0 u1} (A : Type@{u0}) (R : A -> A -> Type@{s;u1})
  (a b: A) (p : path R a b) (eq_pf : length p == 1) : R a b.
Proof.
  destruct p.
  - contradiction.
  - simpl in eq_pf. apply length0 in eq_pf; destruct eq_pf. exact f.
Defined.

Theorem length1_on@{s;u0 u1} (A : Type@{u0}) (R : A -> A -> Type@{s;u1})
  (a : A) (l : list A) (p : path_on@{s;u0 u1} R a l) (eq_pf : List.length l == 1)
  : R a (List.last a l).
Proof.
  destruct l.
  - simpl in eq_pf. change _ with (List.length l == 0) in eq_pf.
    symmetry in eq_pf. apply List.length0 in eq_pf. destruct (eq_pf^).
    exact (fst p).
  - contradiction.
Defined.

Definition nth_vertex @{s;u0 u1} (A : Type@{u0}) (R : A -> A -> Type@{s;u1}) (a : A)
  : forall (b : A) (n : nat), path@{s;u0 u1} R a b -> A
  := fix nth b n p :=
    match n with
    | 0 => b
    | S n' => match p with
             | nil _ _ => a
             | cons _ _ p => nth _ n' p
             end
    end.

Definition drop@{s;u0 u1} (A : Type@{u0}) (R : A -> A -> Type@{s;u1})
  (a : A)
  : forall (b : A) (n : nat) (p : path@{s;u0 u1} R a b), path@{s;u0 u1} R a (nth_vertex n p).
Proof.
  intros b n; revert b.
  refine ((fix recfun (n : nat) := _) n).
  destruct n.
  - exact (fun _ x => x).
  - intros b p; destruct p; simpl.
    + exact (nil _ _).
    + apply recfun.
Defined.

Definition take@{s;u0 u1} (A : Type@{u0}) (R : A -> A -> Type@{s;u1})
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

Definition take_on@{s;u0 u1} (A : Graph.t@{s;u0 u1})
  (a : A) (l : list A) (k : nat) :
  forall (p : path_on@{s;u0 u1} (Graph.Hom (t:=A)) a l),
    path_on@{s;u0 u1} (Graph.Hom (t:=A)) a (List.take k l).
Proof.
  revert a l k.
  refine (fix rect a l k := match l with | hd :: tl => _ | List.nil => _ end).
  - destruct k.
    + intros. exact tt.
    + simpl; intros. refine ({| fst := fst p; snd := _ |}).
      apply rect. exact (snd p).
  - destruct k; exact (fun a => a).
Defined.

Definition drop_on@{s;u0 u1} (A : Graph.t@{s;u0 u1})
  (a : A) (l : list A) (k : nat) :
  forall (p : path_on@{s;u0 u1} (Graph.Hom (t:=A)) a l),
    path_on@{s;u0 u1} (Graph.Hom (t:=A)) (List.nth k a l)
      (List.drop k l).
Proof.
  revert a l k.
  refine (fix rect a l k := match l with | hd :: tl => _ | List.nil => _ end).
  - destruct k.
    + exact (fun x => x).
    + simpl; intros. apply rect. exact (snd p).
  - destruct k; exact (fun a => a).
Defined.

Theorem drop_length@{s;u0 u1} (A : Type@{u0}) (R : A -> A -> Type@{s;u1})
  (a : A) (b :A) (p : path@{s;u0 u1} R a b) k (le : Nat.le k (length p))
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

Theorem take_length@{s;u0 u1} (A : Type@{u0}) (R : A -> A -> Type@{s;u1})
  a b (p : path@{s;u0 u1} R a b) (k : nat) (le : k <= length p)
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
