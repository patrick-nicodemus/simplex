From Simplex Require Import
  Basics.Basics
  Basics.Datatypes_core
  Category.Category
  Category.Functor
  Category.ProdCat
.
                     
Module MonoidalCat.
  Class class_of (C : Category.t) := {
      tensor : Functor.t (C × C) C;
      unit : C;
    }.
End MonoidalCat.
