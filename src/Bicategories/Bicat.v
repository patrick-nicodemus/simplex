From Simplex Require Import Basics PreOrder.Core OneBicat Category.

Module Bicategory.
  Record class_of@{u0 u1 u2} (A : OneBicat.t@{Type|u0 u2 u2}) := {
      is_vcat (x y : A) :
      Category.mixin_of (OneBicat.to_vpreorder A x y);
    }.

  Structure t@{u0 u1 u2} := {
      sort : Type@{u0};
      Hom : sort -> sort -> Type@{u1};
      TwoHom : forall (x y : sort), Hom x y -> Hom x y -> Type@{u2}
    }.
End Bicategory.
