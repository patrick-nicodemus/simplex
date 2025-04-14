From Corelib Require Import Datatypes.
Notation nat := nat.
Require Import Simplex.Basics.

(* The scope is automatically opened in a file that imports this one. *)
Inductive le' : nat -> nat -> Set :=
| le_O n : le' O n
| le_S n m : le' n m -> le' (S n) (S m).
Arguments le_S {_ _}.
Infix "<='" := le' (at level 70).

Fixpoint le (n : nat) : forall (m : nat), SProp :=
  match n with
  | O => fun _ => sUnit
  | S n' => fun m => match m with
                 | O => sEmpty
                 | S m' => le n' m'
                 end
  end.
Infix "<=" := le (at level 70).

Definition le_to_le' : forall (n m : nat), n <= m -> n <=' m
  := fix lerec (n m : nat) : n <= m -> n <=' m
    := match n with
       | O => fun _ => le_O m
       | S n' => match m return (S n') <= m -> (S n') <=' m with
                | O => fun p => match p with end
                | S m' => fun p => le_S (lerec n' m' p)
                end
       end.

Definition le'_to_le : forall (n m : nat), n <=' m -> n <= m
  := fix lerec (n m : nat) (p: n <=' m) : n <= m
    := match p in n <=' m return n <= m with
       | le_O n' => stt
       | @le_S n' m' p' => lerec n' m' p'
       end.

#[universes(polymorphic=yes)]
Fixpoint le_induction@{s|u|}
  (P : nat -> nat -> Type@{s|u})
  (H0 : forall n : nat, P O n)
  (HS : forall n m : nat, P n m -> P (S n) (S m))
  (n m : nat) (p : n <= m)
  : P n m
  := match n return (forall m : nat, n <= m -> P n m) with
     | O => fun m _ => H0 _
     | S n' => fun m => match m return (S n') <= m -> P (S n') m with
                    | O => fun p => match p with end
                    | S m' => fun p => HS n' m' (le_induction P H0 HS n' m' p)
                    end
     end m p.

Fixpoint le_refl (x : nat) : x <= x
  := match x with
     | O => stt
     | S y => le_refl y
     end.

Definition nle_Sn_O  : forall (n : nat), ~ (S n <= O)
  := fun n p => p.

Theorem le_trans {n m k : nat} : n <= m -> m <= k -> n <= k.
Proof.
  intro H; revert n m H k.
  apply (le_induction (fun n m => forall k, m <= k -> n <= k)).
  - constructor.
  - intros n m H k; simpl. destruct k.
    + exact (fun x => x).
    + apply H.
Defined.

Open Scope nat_scope.
Arguments Nat.of_uint d%_dec_uint_scope.
Arguments Nat.of_int d%_dec_int_scope.
Number Notation Number.uint Number.uint_of_uint Number.uint_of_uint
  : dec_uint_scope.
Number Notation Number.int Number.int_of_int Number.int_of_int
  : dec_int_scope.
Number Notation nat Nat.of_num_uint Nat.to_num_uint (abstract after 5000) : nat_scope.
