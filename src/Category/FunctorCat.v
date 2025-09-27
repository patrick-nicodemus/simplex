From Simplex Require Import
  Basics
  Graph
  Category.Category
  Category.Functor
  Category.NatTrans
  Basics.Axioms
  PreOrder.Core.


Instance functor_cat_is_preorder (A : Graph.t) (B : Category.t) {H0:Funext}
  : IsPreOrder (@NatTrans.t A B _) := {}.

Definition functor_cat_class_minimal (A : Graph.t) (B : Category.t) {H0:Funext}
  : Category.Of_Preorder.factory (PreOrder.Pack (functor_cat_is_preorder A B)).
Proof.
  constructor.
  - intros F G H K sig tau rho. simpl in *.
  (** To finish this proof we need to assume that the category B is
    a (2,1)-category. Will come back to this later after
    the theory of (2,1)-categories is developed.
   *)
    Abort.

Definition FunctorCat (A B : Category.t) : Category.t.
Proof.
Abort.

Module FunctorCat.
  Notation PreOrder := NatTrans.FunctorPreOrder.
End FunctorCat.
