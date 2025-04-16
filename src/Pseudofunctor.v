From Simplex Require Import Basics Graph PreOrder TwoGraph Bicat.
Local Set Implicit Arguments.
Local Open Scope morphism_scope.

Module Lax1Functor.
  Class mixin_of@{s1 s2|u0a u1a u0b u1b u2b|}
    (A : PreOrder.t@{s1|u0a u1a})
    (B : TwoGraph.t@{s2|u0b u1b u2b}) {Bp: PreOrder.mixin_of B}
    (F : GraphHom.t A B)
    : Type@{s2|max(u0a,u1a,u2b)}
    := Mixin {
      luc : forall (x : A), 1 (F x) ⇒ fmap F (1 x);
      lfc : forall (x y z: A) (f : x ~> y) (g : y ~> z),
        (fmap F f) · (fmap F g) ⇒ fmap F (f · g)
    }.
  Class class_of@{s1 s2|+|+}
    (A : TwoGraph.t@{s1|_ _ _ }) (Ap : PreOrder.mixin_of A)
    (B : TwoGraph.t@{s2|_ _ _}) (Bp : PreOrder.mixin_of B) (F: A -> B)
    := Class {
      is2graph_hom: TwoGraphHom.class_of F;
      mixin : mixin_of (A:=PreOrder.Pack (PreOrder.Class Ap)) (Bp:=Bp) 
               (TwoGraphHom.to_graph_hom (TwoGraphHom.Pack is2graph_hom))
         }.
  Local Existing Instance OneBicat.is_preorder_mixin.
  Structure t@{s1 s2|u0a u1a u2a u0b u1b u2b|}
    (A : OneBicat.t@{s1|u0a u1a u2a})
    (B : OneBicat.t@{s2|u0b u1b u2b})
    := Pack {
           map : A -> B;
           class: class_of _ _ map
         }.
End Lax1Functor.

Module Colax1Functor.
  Class mixin_of@{s1 s2|+|+}
    (A : PreOrder.t@{s1|_ _})
    (B : TwoGraph.t@{s2|_ _ _}) {Bp: PreOrder.mixin_of B}
    (F : GraphHom.t A B)
    := colax_mixin
      : Lax1Functor.mixin_of@{s1 s2|_ _ _ _ _}
          (B:=TwoGraph.co B) F.

  Typeclasses Transparent mixin_of.

  Class class_of@{s1 s2|+|+}
    (A : TwoGraph.t@{s1|_ _ _}) (Ap : PreOrder.mixin_of A)
    (B : TwoGraph.t@{s2|_ _ _}) (Bp : PreOrder.mixin_of B) (F: A -> B)
    := Class {
      is2graph_hom: TwoGraphHom.class_of F;
      mixin : mixin_of (A:=PreOrder.Pack (PreOrder.Class Ap)) (Bp:=Bp) 
               (TwoGraphHom.to_graph_hom (TwoGraphHom.Pack is2graph_hom))
         }.

  Definition t@{s1 s2|+|+}
    (A : OneBicat.t@{s1|_ _ _})
    (B : OneBicat.t@{s2|_ _ _})
    := Lax1Functor.t A (OneBicat.co B).
End Colax1Functor.

Module Pseudo1Functor.
  Class mixin_of@{s1 s2|u0a u1a u0b u1b u2b|}
    (A : PreOrder.t@{s1|u0a u1a})
    (B : TwoGraph.t@{s2|u0b u1b u2b}) {Bp: PreOrder.mixin_of B}
    (F : GraphHom.t A B)
    : Type@{s2|max(u0a,u1a,u2b)}
    := Mixin {
           is_lax : Lax1Functor.mixin_of F;
           is_colax : Colax1Functor.mixin_of F;
         }.

  Class class_of@{s1 s2|+|+}
    (A : TwoGraph.t@{s1|_ _ _}) (Ap : PreOrder.mixin_of A)
    (B : TwoGraph.t@{s2|_ _ _}) (Bp : PreOrder.mixin_of B) (F: A -> B)
    := Class {
      is2graph_hom: TwoGraphHom.class_of F;
      mixin : mixin_of (A:=PreOrder.Pack (PreOrder.Class Ap)) (Bp:=Bp) 
               (TwoGraphHom.to_graph_hom (TwoGraphHom.Pack is2graph_hom))
         }.

  Local Existing Instance OneBicat.is_preorder_mixin.
  Structure t@{s1 s2|+|+}
    (A : OneBicat.t@{s1|_ _ _})
    (B : OneBicat.t@{s2|_ _ _})
    := Pack {
           map : A -> B;
           class: class_of _ _ map
         }.
End Pseudo1Functor.
