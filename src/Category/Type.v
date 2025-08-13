From Simplex Require Import Basics Category PreOrder.Core PreOrder.Instances
  Tactics.

Definition TypeIsCat@{u} : Category.class_of (fun A B : Type@{u} => A -> B).
Proof.
  naive().
Defined.

Definition TypeCat@{u} : Category.t@{;u+1 u} := Category.Pack TypeIsCat@{u}.
