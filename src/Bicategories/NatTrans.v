From Simplex Require Import Basics Graph PreOrder.Core TwoGraph OneBicat.
Local Set Implicit Arguments.
Local Open Scope morphism_scope.

Module LaxNT1.
  Class class_of (A : Graph.t) (B : TwoGraph.t) (F G : GraphHom.t A B)
    (is_trans : Transitive (@TwoGraph.Hom B))
    (trans : Transformation F G)
    := is_lax_natural
      : forall (a a' : A) (f : Graph.Hom a a'),
        TwoGraph.class (fmap F f · (trans a')) (trans a · fmap G f).

  Structure t (A : Graph.t) (B : TwoGraph.t)
    (is_trans : Transitive (@TwoGraph.Hom B))
    (F G : GraphHom.t A B) := {
      trans : Transformation F G;
      is_lax_nat : class_of F G _ trans
    }.
End LaxNT1.

Module OpLaxNT1.
  Class class_of (A : Graph.t) (B : TwoGraph.t) (F G : GraphHom.t A B)
    (is_trans : Transitive (@TwoGraph.Hom B))
    (trans : Transformation F G)
    := is_oplax_natural
      : @LaxNT1.class_of A (TwoGraph.co B) F G is_trans trans.

  Structure t (A : Graph.t) (B : TwoGraph.t)
    (is_trans : Transitive (@TwoGraph.Hom B))
    (F G : GraphHom.t A B) := {
      trans : Transformation F G;
      is_oplax_nat : class_of F G _ trans
    }.
End OpLaxNT1.

Module PseudoNT1.
  Class class_of (A : Graph.t) (B : TwoGraph.t) (F G : GraphHom.t A B)
    (is_trans : Transitive (@TwoGraph.Hom B))
    (trans : Transformation F G)
    := {
      is_lax_nat : LaxNT1.class_of F G _ trans;
      is_oplax_nat : OpLaxNT1.class_of F G _ trans;
    }.

  Structure t (A : Graph.t) (B : TwoGraph.t)
    (is_trans : Transitive (@TwoGraph.Hom B))
    (F G : GraphHom.t A B) := {
      trans : Transformation F G;
      is_nat : class_of F G _ trans
    }.
End PseudoNT1.
