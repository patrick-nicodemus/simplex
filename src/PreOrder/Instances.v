From Simplex Require Import Basics Eq PreOrder.Core.

Definition eq_preorder (A : Type) : PreOrder.class_of (@eq A).
Proof.
  constructor; exact _.
Defined.
