From Simplex Require Import
  Basics.Basics Category Functor Datatypes_core
  Category.ProdCat
.
                     
Module MonoidalCat.
  Class class_of (C : Category.t) := {
      tensor : Functor.t (C × C) C;
      unit : C;
    }.
End MonoidalCat.
