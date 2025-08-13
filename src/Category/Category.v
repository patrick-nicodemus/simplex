From Simplex Require Import Basics Eq Graph TwoGraph
                     PreOrder.Core PreOrder.Instances
                     Datatypes_core
                     Graph
                     OneBicat.

Import Graph.Notations.
Local Set Implicit Arguments.
Local Open Scope morphism_scope.

(** This module defines categories with the standard Martin-Löf equality on Homs. Categories are are defined as a specialization of OneBicat's to the case where the setoid equivalence relation on homs is type-valued equality. A Category.t is a triple consisting of the sort of objects, a dependent Hom type, and a proof that this pair forms a category.

   The module includes a mixin class showing how to upgrade a PreOrder.t to a category by supplying a left and right preorder. It also
   contains a coercion from a category down to a preorder, and a way to extract reflexivity and transitivity proofs.

   The module contains the [AreInverse f g] record, which is a proof that f and g are each other's inverse.
 *)

Module Category.
  Definition class_of@{u0 u1} (A : Type@{u0}) (R : A -> A -> Type@{u1}) :=
    @OneBicat.class_of@{Type;u0 u1 u1} A R (fun (x y : A) => @eq (R x y)).

  Structure t := Pack {
      sort : Type;
      Hom : sort -> sort -> Type;
      class : class_of Hom
   }.

  Module t_exports.
    Coercion sort : t >-> Sortclass.
    Instance category_is_onebicat (A : Category.t) :
      OneBicat.class_of (A:=A) (R:=Hom A) (fun x y => @eq (Hom A x y))
      := class A.
    Arguments Hom [t].
  End t_exports.
  Import t_exports.

  Definition to_onebicat (A : Category.t) : OneBicat.t :=
    {|
      OneBicat.sort := @sort A;
      OneBicat.Hom := @Hom A;
      OneBicat.two_cells := _ ;
      OneBicat.class := category_is_onebicat A
    |}.
  
  Module Mixin.
  Record mixin_of (A : PreOrder.t) := Mixin {
      assoc : forall (w x y z : A) (f : w <= x) (g : x <= y) (h : y <= z),
        ((f · g) · h) = f · (g · h);
      lu : forall (x y : A) (f : x <= y), (1 x · f) = f;
      ru : forall (x y : A) (f : x <= y), (f · 1 y) = f
     }.
  End Mixin.
  Import Mixin.

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
    - intros; apply eq_preorder.
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

  Module to_graph_exports.
    Coercion to_graph : t >-> Graph.t.
    Canonical to_graph.
  End to_graph_exports.
  Import to_graph_exports.

  Definition IsPreOrder (A : t)
    : PreOrder.class_of (@Category.Hom A)
    := OneBicat.Class_of.is_preorder (t:=class A).

  Definition to_preorder@{u0 u1} (A : t@{u0 u1})
    : PreOrder.t@{Type;u0 u1}
    := @PreOrder.Pack (sort A) _ (IsPreOrder A).

  Definition IsReflexive (A : t)
    := PreOrder.refl (class_of:=(IsPreOrder A)).

  Definition IsTransitive (A : t)
    := PreOrder.trans (class_of:=(IsPreOrder A)).

  Module PreOrder_exports.
    Canonical to_preorder.
    Coercion to_preorder : t >-> PreOrder.t.
    Existing Instance IsReflexive.
    Existing Instance IsTransitive.
    Existing Instance IsPreOrder.
  End PreOrder_exports.
  Import PreOrder_exports.
  
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

  Definition Isomorphic {C : Category.t} (x y : C) :=
    ({ f : (x ~> y), g : (y ~> x) | AreInverse f g })%type.

  Class IsIsomorphism (C : Category.t) (x y : C) (f : x ~> y) := {
      inverse : y~>x;
      is_inverse : AreInverse f inverse
    }.
  
  Definition assoc (A : t)
    : forall (w x y z: A)
        (f : Hom w x) (g : Hom x y) (h : Hom y z),
      (f · g) · h = f · (g · h).
  Proof.
    apply (OneBicat.Class_of.assoc (t:=class A)).
  Defined.
        
  Definition ru (A : t) : forall (x y : A) (f : Hom x y),
      f · 1 y = f.
  Proof.
    apply (OneBicat.Class_of.ru (t:=class A)).
  Defined.

  Definition lu (A : t) : forall (x y : A) (f : Hom x y),
      1 x · f = f.
  Proof.
    apply (OneBicat.Class_of.lu (t:=class A)).
  Defined.
  Module coherence_exports.
    Arguments assoc [A w x y z].
    Arguments ru [A x y].
    Arguments lu [A x y].
  End coherence_exports.
  Import coherence_exports.

  Module Exports.
    Export t_exports.
    Export class_minimal_exports.
    Export to_graph_exports.
    Export PreOrder_exports.
    Export AreInverseExports.
    Export coherence_exports.
  End Exports.
End Category.
Export Category.Exports.
