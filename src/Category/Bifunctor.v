From Simplex Require Import Basics Category Functor FunctorCat.
Definition Bifunctor (A B C: Category.t) :=
  Functor.t A (FunctorCat.PreOrder B C).
