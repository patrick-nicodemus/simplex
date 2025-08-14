From Simplex Require Import Basics Datatypes Relations Eq List Graph PreOrder.Core PreOrder.Instances OneBicat Category Functor FunctorCat Category.NatTrans.

Local Set Implicit Arguments.
Open Scope morphism_scope.
Module TwoCat.
  Import OneBicat.Notations.
(**
   Not yet completed but the plan for this is to
   have a basic notion of Cat-Graph,
   then have a "pre-bicategory" which is parametric over
   an equivalence relation on functors,
   then a TwoCat is the specialization of this relation
   to the case where the equivalence relation is equality.
 *)
End TwoCat.
