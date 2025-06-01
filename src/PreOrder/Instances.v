From Simplex Require Import Basics Datatypes Eq PreOrder.Core Graph.
Local Set Implicit Arguments.
Definition eq_preorder (A : Type) : PreOrder.class_of (@eq A).
Proof.
  constructor; exact _.
Defined.

Definition transformation_preorder_class (A : Type) (B : PreOrder.t)
  : PreOrder.class_of (@Transformation A B).
Proof.
  constructor; exact _.
Defined.

Instance Prod_class@{s;?|?}
  (A : Type) (RA : A -> A -> Type@{s|_}) `{IsPreOrder RA}
  (B : Type) (RB : B -> B -> Type@{s|_}) `{IsPreOrder RB}
  : IsPreOrder (prod_binary RA RB).
Proof.
  constructor.
  - constructor; apply reflexive.
  - intros x y z f g; simpl in *. constructor.
    + apply transitive with (fst y) > [exact _|exact (fst f) | exact (fst g)].
    + apply transitive with (snd y) > [exact _|exact (snd f) | exact (snd g)].
Defined.

Arguments Prod_class [A] RA {IsPreOrder0} [B] RB {IsPreOrder1}.
Definition Prod@{s;?|?}
  (A : PreOrder.t@{s|_ _})
  (B : PreOrder.t@{s|_ _})
  : PreOrder.t@{s|_ _}
  := PreOrder.Pack (Prod_class (PreOrder.Hom (t:=A)) (PreOrder.Hom (t:=B))).
Canonical Prod.
