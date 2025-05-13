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
  
  Arguments class_of [A B F] fmap.
  Notation is_functor := class_of.

  Structure t@{u0a u1a u0b u1b}
    (A : PreOrder.t@{Type|u0a u1a})
    (B : PreOrder.t@{Type|u0a u1a})
    := {
      map : A -> B;
      fmap : forall (a b : A), PreOrder.Hom a b -> PreOrder.Hom (map a) (map b);
      class : class_of@{u0a u1a u0b u1b} fmap
    }.

  Definition to_graph_hom (A B : PreOrder.t) (F : t A B) :
    GraphHom.t A B := {| GraphHom.map := map F; GraphHom.fmap := fmap F |}.
  Coercion to_graph_hom : t >-> GraphHom.t.

End Functor.

Export (coercions) Functor.
