From Simplex Require Import Basics.Basics Datatypes_core Basics.Eq Basics.SEq Category.Category Graph.

Import Graph.Notations.

Class Product {C : Category.t} (x y z : C) := {
    pi_x : z ~> x;
    pi_y : z ~> y;
    univ_prod :
    forall (a : C) (f : a ~> x) (g : a ~> y),
           ∃! (@sig2 (a~>z) (fun h => h · pi_x = f)
                     (fun h => h · pi_y = g))
  }.

Class HasProducts (C : Category.t) := {
    product : C -> C -> C;
    is_Product : forall (x y : C), Product x y (product x y)
  }.
