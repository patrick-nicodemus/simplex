Require Corelib.Init.Nat.
Require Corelib.Init.Byte.
From Simplex Require Import Basics Relations Eq SEq Datatypes PreOrder.Core SPropEquiv Classes Tactics.
From Corelib.Init Require Import Nat.

Require Corelib.Init.Byte.

(** 1. Definitions of [Type]-valued and [SProp]-valued inequalities on [nat], proofs of equivalence; proof that [<=] forms a preorder. *)

Notation nat := Corelib.Init.Datatypes.nat.
Notation O := Corelib.Init.Datatypes.O.
Notation S := Corelib.Init.Datatypes.S.
Notation "x + y" := (Corelib.Init.Nat.add x y) (at level 50, left associativity) : nat_scope.
Notation "(+)" := Corelib.Init.Nat.add (only parsing).
Notation "x - y" := (Nat.sub x y) (at level 50, left associativity) : nat_scope.
Delimit Scope nat_scope with nat.

Number Notation Number.uint Number.uint_of_uint Number.uint_of_uint : dec_uint_scope.
Number Notation Number.int Number.int_of_int Number.int_of_int
  : dec_int_scope.
Number Notation nat Nat.of_num_uint Nat.to_num_uint (abstract after 5000) : nat_scope.

Unset Elimination Schemes.
Inductive le'@{s;} : nat -> nat -> Type@{s;Set} :=
| le_O n : le' O n
| le_S n m : le' n m -> le' (S n) (S m).
Arguments le_S {_ _}.

Infix "<='" := le' (at level 70) : nat_scope.

Fixpoint le@{s;} (n : nat) : forall (m : nat), Type@{s;Set} :=
  match n with
  | O => fun _ => unit
  | S n' => fun m => match m with
                 | O => empty
                 | S m' => le n' m'
                 end
  end.

Fixpoint le_refl : Reflexive le
  := fun x => match x with
     | O => tt
     | S y => le_refl y
     end.

Existing Instance le_refl.

Local Infix "<=" := le (at level 70) : nat_scope.
Open Scope nat_scope.

Definition le_to_le' : forall (n m : nat), le@{SProp;} n m -> le'@{Type;} n m
  := fix lerec (n m : nat) : le@{SProp;} n m -> le'@{Type;} n m
    := match n with
       | O => fun _ => le_O m       (*  *)
       | S n' => match m return le@{SProp;}(S n') m -> le'@{Type;}(S n') m with
                | O => fun p => match p with end
                | S m' => fun p => le_S@{Type;} (lerec n' m' p)
                end
       end.

Definition le'_to_le@{; u1 u2| u1 < u2} : forall (n m : nat),
    le'@{Type;} n m -> le@{SProp;} n m
  := fix lerec (n m : nat) (p: le' n m) : le n m
    := match p in n <=' m return n <= m with
       | le_O n' => tt@{s2;}
       | @le_S n' m' p' => lerec n' m' p'
       end.

From Simplex Require Import Basics.Induction.
(* Inductive Squash (A : Type) : SProp *)
(*   := unbox (a : A) : Squash A. *)

(* Class SPropEquiv (A : Type) := sprop_elim : Squash A -> A. *)

Instance le_sprop (n m : nat) : SPropEquiv (le'@{Type;} n  m).
Proof.
  intro H.
  apply le_to_le'.
  destruct H.
  apply le'_to_le.
  exact a.
Defined.

Theorem abc : forall n m : nat, Squash (le'@{Type;} n m) -> n + 1 <= m + 1.
Proof.
  intros n m h.
  
  Elpi induction.
Defined.


Instance le_le'_equiv (n m : nat)
  : SPropEquiv (le' n m) (le n m) := {
    to_sprop := le'_to_le n m;
    to_type := le_to_le' n m;
  }.

Fixpoint le_induction@{s;u|}
  (P : nat -> nat -> Type@{s;u})
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

Theorem le_n_S : forall n m : nat, n <= m -> S n <= S m.
Proof.
  exact (fun n m p => p).
Defined.

Definition nle_Sn_O@{s;} : forall (n : nat), not@{_ s;_} (S n <= O)
  := fun n p => p.

Instance le_trans@{s;} : Transitive@{s;Set Set} le.
Proof.
  intros n m k H; revert n m H k.
  apply (le_induction@{s;Set} (fun n m => forall k, m <= k -> n <= k)).
  - constructor.
  - intros n m H k; simpl. destruct k.
    + exact (fun x => x).
    + apply H.
Defined.

Definition Nat_le := PreOrder.Pack (PreOrder.Class (R:=le) _ _).
Canonical Nat_le.

Arguments Nat.of_uint d%_dec_uint_scope.
Arguments Nat.of_int d%_dec_int_scope.
Number Notation Number.uint Number.uint_of_uint Number.uint_of_uint : dec_uint_scope.
Number Notation Number.int Number.int_of_int Number.int_of_int
  : dec_int_scope.
Number Notation nat Nat.of_num_uint Nat.to_num_uint (abstract after 5000) : nat_scope.

(** 2. [SProp]-valued equality for naturals. *)
Definition seq : forall (n m : nat), SProp  :=
  fix seq n m :=
    match n with
    | O => match m with
          | O => unit
          | _ => empty
          end
    | S n' => match m with
             | O => empty
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
      refine (match h return O = S b with end).
    + intro b; destruct b.
      * intro h; refine (match h return S a = O with end).
      * simpl. intro h. apply eq_S. apply IHa. assumption.
  - intros a b p; destruct p. induction a.
    + exact tt.
    + simpl. apply IHa.
Defined.

(** 3. Theorems of arithmetic *)
Instance plus_n_O : RightId@{Type;Set Set} (@eq nat) 0 (+).
Proof.
  intro n; induction n as [|n IHn].
  - reflexivity.
  - simpl. apply eq_S. apply IHn.
Qed.

Theorem add_succ_comm : forall (n m : nat), S n + m = n + S m.
Proof.
  intro n; induction n as [|n IHn].
  - reflexivity.
  - intro m. simpl. apply eq_S. apply IHn.
Qed.

Instance add_comm : Comm (@eq nat) (+).
Proof.
  intro n; induction n.
  - intro y. apply symmetry. apply right_id.
  - intro y. simpl. rewrite <- add_succ_comm.
    apply eq_S. apply IHn.
Qed.

Theorem sub_0_r : forall n : nat, n - 0 = n.
Proof.
  destruct n; reflexivity.
Defined.

Theorem nat_sub_diag : forall n : nat, n - n = 0.
Proof.
  induction n > [reflexivity | auto].
Qed.

Theorem add_sub : forall n m : nat, n + m - m = n.
Proof.
  intros n m; revert n; induction m as [|m IHm].
  - intros. rewrite plus_n_O. apply sub_0_r. 
  - intro n. simpl. rewrite <- add_succ_comm.
    apply IHm.
Qed.

Theorem add_sub_eq_l : forall n m p : nat, m + p = n -> n - m = p.
  intros n m p H.
  rewrite <- H.
  rewrite (comm (R:=@eq nat) (f:=(+))).
  exact (add_sub _ _).
Qed.

Theorem add_sub_eq_r: forall n m p : nat, m + p = n -> n - p = m.
Proof.
  intros n m p.
  rewrite (comm (R:=@eq nat) (f:=(+))).
  exact (add_sub_eq_l _ _ _).
Qed.

Theorem le_add_r : forall n m : nat, n <= n + m.
Proof.
  induction n as [|n IHn].
  - exact (fun _ => tt).
  - intro m; exact (IHn _).
Qed.

Theorem le_add_l : forall n m : nat, m <= n + m.
Proof.
  induction m as [|m IHm].
  - exact tt.
  - simpl. destruct n.
    + simpl. apply IHm.
    + simpl. destruct (add_succ_comm n m). exact IHm.
Qed.

Theorem nat_rect@{u} : forall P : nat -> Type@{u}, P 0 -> (forall n, P n -> P (S n)) -> (forall n, P n).
Proof.
  intros P P0 PS.
  refine (fix recfun (n : nat) {struct n} := match n with | O => _ | S n' => _ end).
  - exact P0.
  - apply PS, recfun.
Defined.

Theorem assoc : forall n m k, n + m + k == n + (m + k).
Proof.
  induction n.
  - intros m k. reflexivity.
  - intros m k. apply IHn.
Defined.
