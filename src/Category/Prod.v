From Simplex Require Import Basics Eq Graph Datatypes
  PreOrder.Instances
  OneBicat
  Category.

Definition product (A B : Category.t) : Category.t.
Proof.
  unshelve refine '(Category.Build _) > [
      exact ((A * B)%type)
    | apply prod_binary > [ apply Category.Hom | apply Category.Hom ]
    | unshelve econstructor
    ].
  constructor; simpl.
  - intros [w w'] [x x'] [y y'] [z z'] [f f'] [g g'] [h h'];
      simpl in *.
    apply prod_eq; apply Category.assoc.
  - intros [x0 x1] [y0 y1] [f0 f1]; simpl in *; apply prod_eq; apply Category.lu.
  - intros [x0 x1] [y0 y1] [f0 f1]; simpl in *; apply prod_eq; apply Category.ru.
Defined.
