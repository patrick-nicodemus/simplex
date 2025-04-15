From Simplex Require Import Basics Graph PreOrder TwoGraph.
Local Set Implicit Arguments.
Local Open Scope morphism_scope.

Definition Associative@{s|u0 u1 u2|} (A : TwoGraph.t@{s|u0 u1 u2})
  (t : Transitive@{Type|u0 u1} (Hom (t:=A)))
  := forall (w x y z  : A) (f : w ~> x) (g : x ~> y) (h : y ~> z),
    Couple@{s|u1 u2} _ ((f · g) · h) (f · (g · h)).

Definition LeftUnitor@{s|u0 u1 u2|}
  (A : TwoGraph.t@{s|u0 u1 u2 })
  (t : PreOrder.mixin_of@{Type|u0 u1} A)
  := forall (x y : A) (f : x ~> y), Couple@{s|u1 u2} _ ((1 x) · f) f.

Definition RightUnitor@{s|u0 u1 u2|}
  (A : TwoGraph.t@{s|u0 u1 u2})
  (t : PreOrder.mixin_of@{Type|u0 u1} A)
  := forall (x y : A) (f : x ~> y), Couple _ (f · (1 y)) f.

Module OneBicat.
  Record mixin_of@{s|u0 u1 u2|} (A : TwoGraph.t@{s|u0 u1 u2}) :=
    Mixin {
        is_preorder : PreOrder.mixin_of@{Type|u0 u1} A;
        assoc : Associative@{s|u0 u1 u2} A
                  (PreOrder.trans (mixin_of:=is_preorder));
        lu : LeftUnitor@{s|u0 u1 u2} is_preorder;
        ru : LeftUnitor@{s|u0 u1 u2} is_preorder;
        hcomp2 : forall (x y z : A) (f f' : x ~> y) (g g' : y ~> z),
          f => f' -> g => g' -> f · g => f' · g'
      }.

  Record class_of@{s|u0 u1 u2|} (A : Type@{u0}) := {
      is2graph : TwoGraph.class_of @{s|u0 u1 u2} A;
      mixin : mixin_of@{s|u0 u1 u2} (TwoGraph.Pack is2graph)
    }.

  Module class_of_conventions.
    Arguments is2graph [A].
    Arguments mixin [A].
  End class_of_conventions.
  Import class_of_conventions.

  Record t@{s|u0 u1 u2|} := Pack {
      sort : Type@{u0};
      class : class_of@{s|u0 u1 u2} sort
    }.
  Module t_conventions.
    Coercion sort : t >-> Sortclass.
    Arguments Pack [sort].
  End t_conventions.
  Import t_conventions.

  Definition to2graph@{s|u0 u1 u2|}
    (A : t@{s|u0 u1 u2}) : TwoGraph.t@{s|u0 u1 u2}
    := TwoGraph.Pack (is2graph (class A)).
  Module to2graph_coercion.
    Coercion to2graph : t >-> TwoGraph.t.
    Canonical to2graph.
  End to2graph_coercion.
  Import to2graph_coercion.

  Definition is_preorder_mixin@{s|u0 u1 u2|}
    (A : t@{s|u0 u1 u2})
    : PreOrder.mixin_of A
    := is_preorder (mixin (class A)).

  Module Exports.
    Export class_of_conventions.
    Export t_conventions.
    Export to2graph_coercion.
  End Exports.
End OneBicat.
Export OneBicat.Exports.
