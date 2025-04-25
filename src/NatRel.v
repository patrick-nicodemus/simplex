From Simplex Require Import Basics Nat Graph PreOrder.

Canonical nat_rel := Graph.Pack le.

Module Example1.
  Canonical nat_rel := Graph.Pack le.
  Canonical nat_preorder : PreOrder.t
    := PreOrder.Pack (PreOrder.Class Nat.le_refl (@Nat.le_trans)).

  Ltac2 reflexivity () :=
    exact (PreOrder.is_refl _ _).

  Set Printing All.
  Goal forall x : nat, PreOrder.Hom x x.
  Proof.
    intro x.
    reflexivity ().
  Defined.
  Import PreOrder.Notations.
  Definition ff : forall x y : nat, x ~> y -> x ~> y := fun x y f => f.
  Definition fmi : forall x y z : nat, x ~> y -> y ~> z -> x ~> z :=
    fun x y z f g => ff x z (f · g).
  Goal forall x y z: nat, x ~> y -> y ~> z -> x ~> z.
  Proof.
    intros x y z f g.
    (* Check ((fun (s : x ~> z) => s) (f · g)). *)
    exact (f · g)%hom.
  Defined.

  Goal forall x : nat, le x x.
    exact (fun x => (1 x)%hom).
  Defined.
End Example1.
