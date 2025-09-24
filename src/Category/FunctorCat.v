From Simplex Require Import
  Basics
  Graph
  Category.Category
  Category.Functor
  Category.NatTrans
  Basics.Axioms
  PreOrder.Core.

#[refine]
Instance functor_cat_class_minimal (A : Graph.t) (B : Category.t) {H0:Funext}
  : Category.class_minimal (@NatTrans.t A B _)
  := {
    
  }.
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
  Abbreviation PreOrder := NatTrans.FunctorPreOrder.
End FunctorCat.
