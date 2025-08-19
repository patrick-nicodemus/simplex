From Simplex Require Import
  Basics
  Category.Category
  PreOrder.Core.

Definition PreOrderCat : Category.t.
Proof.
  refine '(@Category.Pack _ _ _).
  Abort.
