From Simplex Require Import Basics Eq.
From Simplex Require Import Datatypes.

Notation nat := Corelib.Init.Datatypes.nat.
Notation O := Corelib.Init.Datatypes.O.
Notation S := Corelib.Init.Datatypes.S.
Notation "x + y" := (Nat.add x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (Nat.sub x y) (at level 50, left associativity) : nat_scope.
Delimit Scope nat_scope with nat.

(* The scope is automatically opened in a file that imports this one. *)
Inductive le' : nat -> nat -> Set :=
| le_O n : le' O n
| le_S n m : le' n m -> le' (S n) (S m).
Arguments le_S {_ _}.

Infix "<='" := le' (at level 70) : nat_scope.

Fixpoint le (n : nat) : forall (m : nat), SProp :=
  match n with
  | O => fun _ => sUnit
  | S n' => fun m => match m with
                 | O => sEmpty
                 | S m' => le n' m'
                 end
  end.

Infix "<=" := le (at level 70) : nat_scope.
Open Scope nat_scope.

Definition le_to_le' : forall (n m : nat), n <= m -> n <=' m
  := fix lerec (n m : nat) : n <= m -> n <=' m
    := match n with
       | O => fun _ => le_O m       (*  *)
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

Theorem le_n_S : forall n m : nat, n <= m -> S n <= S m.
Proof.
  exact (fun n m p => p).
Defined.

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

Arguments Nat.of_uint d%_dec_uint_scope.
Arguments Nat.of_int d%_dec_int_scope.
Number Notation Number.uint Number.uint_of_uint Number.uint_of_uint
  : dec_uint_scope.
Number Notation Number.int Number.int_of_int Number.int_of_int
  : dec_int_scope.
Number Notation nat Nat.of_num_uint Nat.to_num_uint (abstract after 5000) : nat_scope.

Definition seq : forall (n m : nat), SProp  :=
  fix seq n m :=
    match n with
    | O => match m with
          | O => sUnit
          | _ => sEmpty
          end
    | S n' => match m with
             | O => sEmpty
             | S m' => seq n' m'
             end
    end.

Definition eq_S : forall (n m : nat), n = m -> S n = S m
  := fun n m p => match p with | eq_refl _ => eq_refl (S n) end.

#[refine]
Instance seq_nat : SEqType.class_of nat := {
    seq_rel := seq;
  }.
Proof.
  - intro a; induction a.
    + intro b; destruct b > [reflexivity|].
      intro h. simpl in h.
      refine '(match h return O = S b with end).
    + intro b; destruct b.
      * intro h; refine '(match h return S a = O with end).
      * simpl. intro h. apply eq_S. apply IHa. assumption.
  - intros a b p; destruct p. induction a.
    + exact stt.
    + simpl. apply IHa.
Defined.
