From Simplex Require Import Basics Relations Eq Graph PreOrder.Core.
Local Set Implicit Arguments.

Module Functor.
  Open Scope morphism_scope.
  Class class_of@{u0a u1a u0b u1b}
    (A : PreOrder.t@{Type|u0a u1a})
    (B : PreOrder.t@{Type|u0a u1a})
    (F : A -> B) (fmap : forall {a b : A}, PreOrder.Hom a b -> PreOrder.Hom (F a) (F b))
    := {
      F_id : forall (x : A), fmap (1 x) = 1 (F x);
      F_comp : forall (x y z : A) (f : PreOrder.Hom x y) (g : PreOrder.Hom y z),
        fmap (f · g) = fmap f · fmap g
    }.
  Module class_of_exports.
    Arguments class_of [A B F] fmap.
  End class_of_exports.
  Import class_of_exports.
  
  Structure t@{u0a u1a u0b u1b}
    (A : PreOrder.t@{Type|u0a u1a})
    (B : PreOrder.t@{Type|u0a u1a})
    := {
      map : A -> B;
      fmap : forall (a b : A), PreOrder.Hom a b -> PreOrder.Hom (map a) (map b);
      class : class_of@{u0a u1a u0b u1b} fmap
    }.

  Module Exports.
    Export class_of_exports.
  End Exports.
End Functor.
Export Functor.Exports.

