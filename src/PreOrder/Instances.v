From Simplex Require Import Basics Eq PreOrder.Core Graph.

Definition eq_preorder (A : Type) : PreOrder.class_of (@eq A).
Proof.
  constructor; exact _.
Defined.

Definition transformation_preorder_class (A : Type) (B : PreOrder.t)
  : PreOrder.class_of (@Transformation A B).
Proof.
  constructor; exact _.
Defined.
