From Simplex Require Import
  Basics
  Category.Category
  Bicategories.OneBicat
  Bicategories.Bicat.


(** This module defines (2,1)-categories. However, the invertible
    2-cells referred to in the name are not arbitrary invertible
    2-cells specified by the user; they are restricted to be
    *equalities* between 1-cells. Thus the usual coherence conditions
    of a bicategory become coherence conditions between paths in a
    type.

    An important motivation for this definition is that, for [C] a category
    and [D] a category, there is no functor category [C=>D],
    because without further assumptions on [D], the
    composition of natural transformations is not necessarily
    associative.
    One must assume additional coherence conditions on [D].
 *)
Module TwoOneCat.
  Import OneBicat.Notations.

  Definition mixin_of@{u0 u1} (A : Category.t@{u0 u1}) :=
    Bicategory.mixin_of (Category.to_onebicat A).

  Class class_of@{u0 u1}
    (A : Type@{u0})
    (R : A -> A -> Type@{u1})
    := Class {
           isCategory : Category.class_of R ;
           mixin : mixin_of (Category.Pack isCategory)
         }.

  Record t@{u0 u1} := {
      sort : Type@{u0};
      Hom : sort -> sort -> Type@{u1};
      class : class_of sort Hom
    }.

End TwoOneCat.
