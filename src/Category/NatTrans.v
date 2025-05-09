From Simplex Require Import Basics Tactics Relations Eq Graph PreOrder.Core Category.
Local Set Implicit Arguments.
Module NatTrans.
  Open Scope morphism_scope.
  Class mixin_of (A B : Graph.t) (is_transitive : Transitive (@Graph.Hom B))
    (F G : GraphHom.t A B)
    (tau : Transformation F G) :=
    is_nat' : forall (a b : A) (f : Graph.Hom a b),
        (fmap F f) · (tau b) = tau a · fmap G f.
  Module mixin_of_exports.
    Arguments mixin_of [A B is_transitive] F G tau /.
  End mixin_of_exports.
  Import mixin_of_exports.

  Structure t (A B: Graph.t)
    (is_transitive : Transitive (@Graph.Hom B))              
    (F G : GraphHom.t A B)
    := {
      trans : Transformation F G;
      is_nat : mixin_of F G trans
    }.
  Module t_exports.
    Coercion trans : t >-> Transformation.
  End t_exports.
  Import t_exports.
  
  Instance refl (A : Graph.t) (B : Category.t)
    : Reflexive (@t A B _).
  Proof.
    intro F.
    unshelve econstructor.
    - apply (@id_trans _ _ _).
    - simpl.
      intros a b f.
      unfold id_trans.
      refine (Category.ru _ · _).
      symmetry.
      apply Category.lu.
  Defined.

  Instance transitive (A : Graph.t) (B : Category.t)
    : Transitive (@t A B _).
  Proof.
    intros F G H sigma tau.
    unshelve econstructor.
    - exact (compose_trans sigma tau).
    - simpl.
      intros a b f.
      unfold compose_trans.
      simpl.
      rewrite <- Category.assoc.
      rewrite is_nat.
      rewrite Category.assoc.
      rewrite is_nat.
      symmetry; apply Category.assoc.
  Defined.
  Module Exports.
    Export t_exports.
  End Exports.
End NatTrans.
Export NatTrans.Exports.
