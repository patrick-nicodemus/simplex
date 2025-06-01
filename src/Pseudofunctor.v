From Simplex Require Import Basics Graph PreOrder.Core TwoGraph OneBicat.
Local Set Implicit Arguments.
Local Open Scope morphism_scope.

Module Lax1Functor.
  (** Lax unity constraint, lax functoriality constraint *)
  Module _mixin.
    Import TwoGraph.Notations.
    Class mixin_of@{s1 s2;u0a u1a u0b u1b u2b|}
      (A : PreOrder.t@{s1;u0a u1a})
      (B : TwoGraph.t@{s2;u0b u1b u2b}) {Bp: PreOrder.class_of (@TwoGraph.Hom B)}
      (F : GraphHom.t A B)
      : Type@{s2|max(u0a,u1a,u2b)}
      := Mixin {
             luc_mixin : forall (x : A), 1 (F x) ⇒ GraphHom.fmap F (1 x);
             lfc_mixin : forall (x y z: A) (f : PreOrder.Hom x y) (g : PreOrder.Hom y z),
               (fmap F f) · (fmap F g) ⇒ fmap F (f · g)
           }.
  End _mixin.
  Include _mixin.

  Class class_of@{s1 s2;uA0 uA1 uA2 uB0 uB1 uB2|}
    (A : TwoGraph.t@{s1|uA0 uA1 uA2}) {Ap : PreOrder.class_of (@TwoGraph.Hom A)}
    (B : TwoGraph.t@{s2|uB0 uB1 uB2}) {Bp : PreOrder.class_of (@TwoGraph.Hom B)}
    (F: A -> B)
    := Class {
      is2graph_hom: TwoGraphHom.class_of F;
      mixin : mixin_of (A:=PreOrder.Pack Ap) (Bp:=Bp) 
               (TwoGraphHom.to_graph_hom (TwoGraphHom.Pack is2graph_hom))
         }.
  Module class_of_exports.
    Arguments is2graph_hom [A Ap B Bp F] class_of.
  End class_of_exports.
  Import class_of_exports.

  Local Existing Instance OneBicat.is_preorder_class.

  Structure t@{s1 s2;u0a u1a u2a u0b u1b u2b|}
    (A : OneBicat.t@{s1|u0a u1a u2a})
    (B : OneBicat.t@{s2|u0b u1b u2b})
    := Pack {
           map : A -> B;
           class: class_of _ _ map
         }.
  Module t_exports.
    Coercion map : t >-> Funclass.
  End t_exports.
  Import t_exports.

  Definition to_graphHom@{s1 s2;u0 u1 u2 u3 u4 u5|}
    (A : OneBicat.t@{s1|u0 u1 u2})
    (B : OneBicat.t@{s2|u3 u4 u5})
    (F: t A B)
    : GraphHom.t@{Type Type|u0 u1 u3 u4} A B
    := @GraphHom.Pack A B (map F) (is2graph_hom (class F)).
  Module to_graphHom_exports.
    Coercion to_graphHom : t >-> GraphHom.t.
    Canonical to_graphHom.
  End to_graphHom_exports.
  Import to_graphHom_exports.

  (** Lax unity constraint  *)
  Definition luc@{s1 s2;uA0 uA1 uA2 uB0 uB1 uB2}
    (A : OneBicat.t@{s1|uA0 uA1 uA2})
    (B : OneBicat.t@{s2|uB0 uB1 uB2})
    (F : t@{s1 s2|_ _ _ _ _ _} A B)
    : forall (x : A), OneBicat.two_cells (1 (F x)) (fmap F (1 x))
    := luc_mixin (mixin_of:=mixin (class_of:=(class F))).

  (** Lax functoriality constraint  *)
  Definition lfc@{s1 s2;uA0 uA1 uA2 uB0 uB1 uB2|}
    (A : OneBicat.t@{s1|uA0 uA1 uA2})
    (B : OneBicat.t@{s2|uB0 uB1 uB2})
    (F : t@{s1 s2|_ _ _ _ _ _} A B)
    : forall (x y z: A) (f : A x y) (g : A y z),
      OneBicat.two_cells ((fmap F f) · (fmap F g)) (fmap F (f · g))
    := lfc_mixin (mixin_of:=mixin (class_of:=(class F))).

  Module Exports.
    Export class_of_exports.
    Export t_exports.
    Export to_graphHom_exports.
  End Exports.
End Lax1Functor.
Export Lax1Functor.Exports.

Module Colax1Functor.
  Class mixin_of@{s1 s2;uA0 uA1 uB0 uB1 uB2}
    (A : PreOrder.t@{s1|uA0 uA1})
    (B : TwoGraph.t@{s2|uB0 uB1 uB2}) {Bp: PreOrder.class_of (@TwoGraph.Hom B)}
    (F : GraphHom.t A B)
    := colax_mixin
      : Lax1Functor.mixin_of@{s1 s2|_ _ _ _ _}
          (B:=TwoGraph.co B) F.

  Typeclasses Transparent mixin_of.

  Class class_of@{s1 s2;uA0 uA1 uA2 uB0 uB1 uB2|}
    (A : TwoGraph.t@{s1|uA0 uA1 uA2}) (Ap : PreOrder.class_of (@TwoGraph.Hom A))
    (B : TwoGraph.t@{s2|uB0 uB1 uB2}) (Bp : PreOrder.class_of (@TwoGraph.Hom B))
    (F: A -> B)
    := Class {
      is2graph_hom: TwoGraphHom.class_of F;
      mixin : mixin_of (A:=PreOrder.Pack Ap) (Bp:=Bp) 
               (TwoGraphHom.to_graph_hom (TwoGraphHom.Pack is2graph_hom))
         }.

  Definition t@{s1 s2;uA0 uA1 uA2 uB0 uB1 uB2|}
    (A : OneBicat.t@{s1|uA0 uA1 uA2})
    (B : OneBicat.t@{s2|uB0 uB1 uB2})
    := Lax1Functor.t A (OneBicat.co B).
  
  (** cuc = colax unity constraint *)
  Definition cuc@{s1 s2;uA0 uA1 uA2 uB0 uB1 uB2|}
    (A : OneBicat.t@{s1|uA0 uA1 uA2})
    (B : OneBicat.t@{s2|uB0 uB1 uB2})
    (F : t@{s1 s2|_ _ _ _ _ _} A B)
    : forall (x : A),
      @OneBicat.two_cells B _ _ (fmap F (1 x)) (1 (F x))
    := fun x => Lax1Functor.luc F x.

  (** Colax functoriality constraint  *)
  Definition cfc@{s1 s2;uA0 uA1 uA2 uB0 uB1 uB2|}
    (A : OneBicat.t@{s1|uA0 uA1 uA2})
    (B : OneBicat.t@{s2|uB0 uB1 uB2})
    (F : t@{s1 s2|_ _ _ _ _ _} A B)
    : forall (x y z: A) (f : A x y) (g : A y z),
      @OneBicat.two_cells B _ _ 
        (fmap F (f · g))
        ((fmap F f) · (fmap F g))
    := fun x y z f g => Lax1Functor.lfc F x y z f g.
End Colax1Functor.

Module Pseudo1Functor.
  Class mixin_of@{s1 s2;u0a u1a u0b u1b u2b|}
    (A : PreOrder.t@{s1|u0a u1a})
    (B : TwoGraph.t@{s2|u0b u1b u2b}) {Bp: PreOrder.class_of (@TwoGraph.Hom B)}
    (F : GraphHom.t A B)
    : Type@{s2|max(u0a,u1a,u2b)}
    := Mixin {
           is_lax : Lax1Functor.mixin_of F;
           is_colax : Colax1Functor.mixin_of F;
         }.

  Class class_of@{s1 s2;uA0 uA1 uA2 uB0 uB1 uB2|}
    (A : TwoGraph.t@{s1|uA0 uA1 uA2}) (Ap : PreOrder.class_of (@TwoGraph.Hom A))
    (B : TwoGraph.t@{s2|uB0 uB1 uB2}) (Bp : PreOrder.class_of (@TwoGraph.Hom B))
    (F: A -> B)
    := Class {
      is2graph_hom: TwoGraphHom.class_of F;
      mixin : mixin_of (A:=PreOrder.Pack Ap) (Bp:=Bp) 
               (TwoGraphHom.to_graph_hom (TwoGraphHom.Pack is2graph_hom))
         }.

  Structure t@{s1 s2;uA0 uA1 uA2 uB0 uB1 uB2|}
    (A : OneBicat.t@{s1|uA0 uA1 uA2})
    (B : OneBicat.t@{s2|uB0 uB1 uB2})
    := Pack {
           map : A -> B;
           class: class_of _ _ _ _ map
         }.
End Pseudo1Functor.
