From Simplex Require Import Basics.Basics Eq.
From Simplex Require Export Basics.Datatypes_core.
Local Set Implicit Arguments.

Theorem prod_eq (A B : Type) (p q : A * B)
  : fst p = fst q -> snd p = snd q -> p = q.
Proof.
  destruct p, q; simpl in *.
  intros fsteq sndeq.
  destruct fsteq.
  destruct sndeq.
  reflexivity.
Defined.

Definition sig_trans@{s;u0 u1|}
  (A : Type@{u0})
  (P : A -> Type@{s;u1})
  (a : A)
  (p : sig P) :
  a = ex_val p -> P a
  := fun eqp => transport _ eqp (ex_pf p).
