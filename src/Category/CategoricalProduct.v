From Simplex Require Import Basics Category.Category Graph.

Import Graph.Notations.

Class Product (C : Category.t) (x y z : C) := {
    pi_x : z ~> x;
    pi_y : z ~> y;
    
  }.
