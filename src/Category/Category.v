From Simplex Require Import Basics Eq Graph TwoGraph
  PreOrder.Core PreOrder.Instances
  OneBicat.
Local Set Implicit Arguments.
Local Open Scope morphism_scope.

Module Category.
  Definition class_of@{u0 u1} (A : Type@{u0}) (R : A -> A -> Type@{u1}) :=
    @OneBicat.class_of@{Type|u0 u1 u1} A R (fun (x y : A) => @eq (R x y)).

  Structure t := Pack {
      sort : Type;
      Hom : sort -> sort -> Type;
      class : class_of Hom
    }.
  Module t_exports.
    Coercion sort : t >-> Sortclass.
    Arguments Hom [t].
  End t_exports.
  Import t_exports.

  Record mixin_of (A : PreOrder.t) := Mixin {
      assoc : forall (w x y z : A) (f : w <= x) (g : x <= y) (h : y <= z),
        ((f · g) · h) = f · (g · h);
      lu : forall (x y : A) (f : x <= y), (1 x · f) = f;
      ru : forall (x y : A) (f : x <= y), (f · 1 y) = f
    }.

  Class class_minimal (A : Type) (R : A -> A -> Type) := {
      is_preorder : PreOrder.class_of R;
      mixin : mixin_of (PreOrder.Pack is_preorder)
    }.
  Module class_minimal_exports.
    Arguments mixin [A R].
  End class_minimal_exports.
  Import class_minimal_exports.
  
  Definition Build (A : Type) (R : A -> A -> Type) (C : class_minimal R) : t.
  Proof.
    apply (@Pack A R).
    unshelve econstructor.
    - apply C.
    - exact _.
    - intros w x y z f g h; simpl in *.
      apply couple_sym > [exact _|].
      apply (assoc (mixin C) _ _ _ _ f g h).
    - intros x y f; simpl in f.
      apply couple_sym > [exact _|].
      apply (lu (mixin C) _ _ f).
    - intros x y f; simpl in f.
      apply couple_sym > [exact _|].
      apply (ru (mixin C) _ _ f).
    - intros x y z f f' g g' h h'. simpl in h, h' |- *.
      exact
        (match h with
         | eq_refl _ => match h' with
                       | eq_refl _ => eq_refl _
                       end
         end).
  Defined.

  Definition to_graph (A : t) : Graph.t := {|
      Graph.sort := sort A;
      Graph.Hom := @Hom A
  |}.

  Definition IsPreOrder (A : t)
    : PreOrder.class_of (@Category.Hom A)
    := OneBicat.is_preorder (class A).

  Definition IsReflexive (A : t)
    := PreOrder.refl (class_of:=(IsPreOrder A)).

  Definition IsTransitive (A : t)
    := PreOrder.trans (class_of:=(IsPreOrder A)).

  Module to_graph_exports.
    Coercion to_graph : t >-> Graph.t.
    Canonical to_graph.
    Existing Instance IsReflexive.
    Existing Instance IsTransitive.
  End to_graph_exports.
  Import to_graph_exports.

  Record AreInverse (C : Category.t) (x y : C)
    (f : Category.Hom x y) (g : Category.Hom y x)
    := {
      fg_id : f · g = 1 x;
      gf_id : g · f = 1 y
    }.
  Module AreInverseExports.
    Arguments AreInverse [C x y] f g.
  End AreInverseExports.
  Import AreInverseExports.

  Module Exports.
    Export t_exports.
    Export class_minimal_exports.
    Export to_graph_exports.
    Export AreInverseExports.
  End Exports.
End Category.
Export Category.Exports.
