From Simplex Require Import
  Basics.Basics
  Category.Category
  Category.Functor
  Category.FunctorCat.
Definition Bifunctor (A B C: Category.t) :=
  Functor.t A (FunctorCat.PreOrder B C).
