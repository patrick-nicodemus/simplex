From Simplex Require Import Basics.Basics Basics.Nat Eq Tactics.
Set Implicit Arguments.

Inductive list@{s;u} (A: Type@{s;u}) : Type@{u} :=
| cons (hd: A) (tl: list A) : list A
| nil : list A.

Arguments nil {A}.

Infix "::" := cons (at level 60, right associativity) : list_scope.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..) : list_scope.
Open Scope list_scope.

Definition length@{s;u} (A : Type@{s;u}) : list A -> nat :=
  fix r l := match l with | nil => O | cons _ tl => S(r tl) end.

Theorem length0@{s;u} (A: Type@{s;u}) (l : list A) : (0 == length l) -> l = nil.
Proof.
  destruct l.
  - intro. contradiction.
  - intro. reflexivity.
Defined.

(** A version of [nth] which is meant to operate on non-empty lists
    presented as a pair of arguments [(hd,tl)].
    If the index is out of bounds,
    [nth] returns the last element of the list. *)
Fixpoint nth@{s;u0|} (A : Type@{s;u0}) (n : nat) (a : A) (l : list A) : A :=
  match n with
  | O => a
  | S n' => match l with
           | nil => a
           | hd :: tl => nth n' hd tl
           end
  end.

(* Fixpoint last@{s;u} {A:Type@{s|u}} (a : A) (l : list A) : A := *)
(*   match l with *)
(*   | nil => a *)
(*   | hd :: tl => last hd tl *)
(*   end. *)
Definition last@{s;u} {A:Type@{s;u}} (a : A) (l : list A) : A :=
  List.nth (List.length l) a l.

Fixpoint drop@{s;u0|} (A : Type@{s;u0}) (n : nat)  (l : list A) : list A :=
  match n with
  | O => l
  | S n' =>
      match l with
      | nil => nil
      | cons hd tl => drop n' tl
      end
  end.

Fixpoint take@{s;u0|} (A : Type@{s;u0}) (n : nat)  (l : list A) : list A :=
  match n with
  | O => nil
  | S n' =>   match l with
             | nil => nil
             | cons hd tl => hd :: (take n' tl)
             end
  end.

Theorem drop_length@{s;u0|} (A : Type@{s;u0}) (l : list@{s;u0} A) (k : nat)
  (le : Nat.le k (length l))
  : length (drop k l) = length l - k.
Proof.
  revert l le.
  revert k.
  refine (fix rect (k0:nat) {struct k0} :=
             match k0 return forall (l : list A),
                 le k0 (length l) -> length (drop k0 l) = length l - k0
            with | O => _ | S k' => _ end).
  - simpl. intros l _. destruct (Relations.symmetry (sub_0_r (length l))).
    reflexivity.
  - simpl. destruct l.
    + intro h. simpl. apply rect, h.
    + simpl. intro; contradiction.
Defined.

Theorem take_length@{s;u0|} (A : Type@{s;u0}) (l : list@{s;u0} A) (k : nat)
  (le : Nat.le k (length l))
  : length (take k l) = k.
Proof.
  revert l le.
  revert k.
  refine (fix rect (k0:nat) {struct k0} :=
             match k0 return forall (l : list A),
                 le k0 (length l) -> length (take k0 l) = k0
            with | O => _ | S k' => _ end).
  - reflexivity.
  - simpl. destruct l.
    + intro h. simpl. apply eq_S. apply rect, h.
    + simpl. intro; contradiction.
Defined.

Lemma nth_last_take : forall (A : Type)(a : A) (l : list A) (k : nat),
    List.nth k a l = List.last a (List.take k l).
Proof.
  intros A a l; revert a.
  induction l.
  - simpl. intro a; destruct k.
    + simpl. reflexivity.
    + simpl. apply IHl.
  - intros a k. destruct k; reflexivity.
Defined.

Lemma nth_last_drop : forall (A :Type)(a: A) (l :  list A) (k : nat),
    last (List.nth k a l) (List.drop k l) = List.last a l.
Proof.
  intros A a l; revert a.
  induction l.
  - intros a k. destruct k; simpl.
    + reflexivity.
    + apply IHl.
  - intros a k; destruct k; reflexivity.      
Defined.
