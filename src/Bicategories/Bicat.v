From Simplex Require Import Basics Graph PreOrder.Core OneBicat Category.

Module Bicategory.
  Set Printing All.
  Print Canonical Projections.
  Record mixin_of@{u0 u1 u2} (A : OneBicat.t@{Type|u0 u2 u2}) := {
      is_vcat (x y : A) : Category.Mixin.mixin_of (OneBicat.to_vpreorder A x y);
      vcat (x y : A) :=
        (@Category.Build _ _  
           (Category.Build_class_minimal
              (is_vcat x y)));
      assoc_inv (w x y z : A)
        (f : vcat w x)
        (g : vcat x y)
        (h : vcat y z) :
      @Category.AreInverse
        (vcat w z)
        _ _
        (Rxy (OneBicat.assoc f g h) :
          (@Graph.Hom (OneBicat.to_hom_graph A w z) _ _))
        (Ryx (OneBicat.assoc f g h));
      lu_inv (x y : A) (f : vcat x y) : @Category.AreInverse (vcat x y) _ _ (Rxy (OneBicat.lu f)) (Ryx (OneBicat.lu f));
      ru_inv (x y : A) (f : vcat x y) : @Category.AreInverse (vcat x y) _ _ (Rxy (OneBicat.ru f)) (Ryx (OneBicat.ru f));
    }.

  Structure t@{u0 u1 u2} := {
      sort : Type@{u0};
      Hom : sort -> sort -> Type@{u1};
      TwoHom : forall (x y : sort), Hom x y -> Hom x y -> Type@{u2};
    }.
End Bicategory.
