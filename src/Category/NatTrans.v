From Simplex Require Import Basics Tactics Relations Eq Graph PreOrder.Core Category Functor.
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
    Arguments t [A B is_transitive].
    Coercion trans : t >-> Transformation.
  End t_exports.
  Import t_exports.
  
  Definition id (A : Graph.t) (B : Category.t)
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

  Definition compose (A : Graph.t) (B : Category.t)
    : Transitive (@t A B _).
  Proof.
    intros F G H sigma tau.
    unshelve econstructor.
    - exact (compose_trans sigma tau).
    - simpl.
      intros a b f.
      unfold compose_trans; simpl.
      rewrite <- Category.assoc.
      rewrite is_nat.
      rewrite Category.assoc.
      rewrite is_nat.
      symmetry; apply Category.assoc.
  Defined.

  Definition DiagramPreOrder_class (A : Graph.t) (B : Category.t)
    : PreOrder.class_of (@t A B _).
  Proof.
    constructor > [exact (id (B:=_)) | exact (compose (B:=_)) ].
  Defined.

  Definition FunctorPreOrder_class (A : PreOrder.t) (B : Category.t)
    : PreOrder.class_of (A:=Functor.t A B) (@t A B _).
  Proof.
    constructor > [exact (id (B:=_)) | exact (compose (B:=_)) ].
  Defined.
  
  (** Beware that this is the preorder structure on all graph homomorphisms
      (i.e., "diagrams")
      when you may want the preorder structure on functors. *)
  Definition DiagramPreOrder (A : Graph.t) (B : Category.t) :=
    PreOrder.Pack (DiagramPreOrder_class A B).
  Definition FunctorPreOrder (A : PreOrder.t) (B : Category.t) :=
    PreOrder.Pack (sort:=Functor.t A B) (FunctorPreOrder_class A B).
  Module PreOrder_Exports.
    Existing Instance DiagramPreOrder_class.
    Existing Instance FunctorPreOrder_class.
    Canonical DiagramPreOrder.
    #[warnings="-redundant-canonical-projection"]
    Canonical FunctorPreOrder.
  End PreOrder_Exports.
  Import PreOrder_Exports.

  Module Exports.
    Export t_exports.
    Export PreOrder_Exports.
  End Exports.
End NatTrans.
Export NatTrans.Exports.
