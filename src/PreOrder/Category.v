From Simplex Require Import
  Basics
  Category.Category
  PreOrder.Core
  Graph.Graph.

Definition PreOrderCat : Category.t.
Proof.
  refine '(@Category.Pack PreOrder.t GraphHom.t _).
  unshelve econstructor.
  - Abort.
