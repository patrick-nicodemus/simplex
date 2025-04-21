From Simplex Require Import Basics Nat Graph PreOrder.
Module Example1.
  Canonical nat_rel := Graph.Pack le.
  (* Succeed Definition J := (0 ~> 1 : SProp). *)
  
  Canonical nat_preorder : PreOrder.t
    := PreOrder.Pack
         (PreOrder.Class
            (PreOrder.Mixin nat_rel Nat.le_refl (@Nat.le_trans))).

  (* This depends on Canonical to_rel above. *)
  Goal forall (A : PreOrder.t) (x y : A), x ~> y.
  Abort.

  Ltac2 reflexivity () :=
    exact (PreOrder.is_refl _ _).

  Set Printing All.
  Goal forall x : nat, x ~> x.
  Proof.
    intro x.
    reflexivity ().
  Defined.
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
