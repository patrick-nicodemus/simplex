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

  Record mixin_of (A : PreOrder.t) := Mixin {
      assoc : forall (w x y z : A) (f : w <= x) (g : x <= y) (h : y <= z),
        ((f · g) · h) = f · (g · h);
      lu : forall (x y : A) (f : x <= y), (1 x · f) = f;
      ru : forall (x y : A) (f : x <= y), (f · 1 y) = f
    }.

  Record class_minimal (A : Type) (R : A -> A -> Type) := {
      is_preorder : PreOrder.class_of R;
      mixin : mixin_of (PreOrder.Pack is_preorder)
    }.

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
End Category.
