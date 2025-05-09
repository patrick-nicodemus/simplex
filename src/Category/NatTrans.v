From Simplex Require Import Basics Relations Eq Graph PreOrder.Core Category.
Local Set Implicit Arguments.
Module NatTrans.
  Open Scope morphism_scope.
  Class mixin_of (A B : Graph.t) (is_transitive : Transitive (@Graph.Hom B))
    (F G : GraphHom.t A B)
    (tau : Transformation F G) :=
    is_nat' : forall (a b : A) (f : Graph.Hom a b),
        (fmap F f) · (tau b) = tau a · fmap G f.
  Module mixin_of_exports.
    Arguments mixin_of [A B is_transitive] F G tau.
  End mixin_of_exports.
  Import mixin_of_exports.

  Structure t (A B: Graph.t)
    (is_transitive : Transitive (@Graph.Hom B))              
    (F G : GraphHom.t A B)
    := {
      trans : Transformation F G;
      is_nat : mixin_of F G trans
    }.

  Instance refl (A : Graph.t) (B : Category.t)
    : Reflexive (@t A B _).
  Proof.
    intro F.
    
  Abort.
  Module Exports.
  End Exports.
End NatTrans.
Export NatTrans.Exports.
