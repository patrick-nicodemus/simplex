From Simplex Require Import Basics Graph TwoGraph PreOrder.
Local Set Implicit Arguments.
Local Open Scope morphism_scope.

Definition Associative@{s|u0 u1 u2|} (A : TwoGraph.t@{s|u0 u1 u2})
  (t : Transitive@{Type|u0 u1} (Hom (t:=A)))
  := forall (w x y z : A) (f : w ~> x) (g : x ~> y) (h : y ~> z),
    Couple@{s|u1 u2} (* (TwoGraph.two_hom _ _) *) _ ((f · g) · h) (f · (g · h)).
(* two_hom@{s | u0 u1 u2} = *)
(* fun (A : t) (x y : sort A) => *)
(* @Graph.Pack (@Graph.Hom (@Graph.Pack (sort A) (@base _ (class A))) x y) (@is2graph _ (class A) x y) *)
(*      : forall {A : t} (_ : sort A) (_ : sort A), Graph.t *)
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
        is_vpreorder : forall (x y: A),
          PreOrder.mixin_of@{s|u1 u2} (TwoGraph.two_hom0 x y);
        assoc : Associative@{s|u0 u1 u2} A
                  (PreOrder.trans (mixin_of:=is_preorder));
        lu : LeftUnitor@{s|u0 u1 u2} is_preorder;
        ru : RightUnitor@{s|u0 u1 u2} is_preorder;
        hcomp2 : forall (x y z : A) (f f' : x ~> y) (g g' : y ~> z),
          f ⇒ f' -> g ⇒ g' -> f · g ⇒ f' · g'
      }.

  Module mixin_of_conventions.
    Arguments Mixin [A] & [is_preorder].
  End mixin_of_conventions.
  Import mixin_of_conventions.

  Definition mixin_op@{s|u0 u1 u2|}
    (A : TwoGraph.t@{s|u0 u1 u2})
    : mixin_of A -> mixin_of (TwoGraph.co A)
    := fun m =>
         {|
           is_preorder := _;
           is_vpreorder x y := PreOrder.mixin_op (is_vpreorder m x y);
           assoc w x y z f g h := Graph.couple_op (assoc m w x y z f g h);
           lu x y f := Graph.couple_op (lu m x y f);
           ru x y f := Graph.couple_op (ru m x y f);
           hcomp2 x y z f f' g g' := hcomp2 m x y z f' f g' g
         |}.

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

  Definition to_vpreorder@{s|u0 u1 u2|} (A : t@{s|u0 u1 u2})
    : forall (x y : A), PreOrder.t@{s|u1 u2}
    := fun x y => PreOrder.Pack (PreOrder.Class (is_vpreorder (mixin (class A)) x y)).
  
  Definition to_graph@{s|u0 u1 u2|}
    (A : t@{s|u0 u1 u2}) : Graph.t@{Type|u0 u1}
    := @Graph.Pack (sort A)
         (to_vpreorder A).
  Module to_graph_exports.
    Canonical to_graph.
  End to_graph_exports.
  Import to_graph_exports.

  Definition to2graph@{s|u0 u1 u2|}
    (A : t@{s|u0 u1 u2}) : TwoGraph.t@{s|u0 u1 u2}
    := @TwoGraph.Pack (sort A) (is2graph (class A)).

  Module to2graph_coercion.
    Coercion to2graph : t >-> TwoGraph.t.
    Canonical to2graph.
  End to2graph_coercion.
  Import to2graph_coercion.

  Definition to_hom_graph@{s|u0 u1 u2|}
    (A:t@{s|u0 u1 u2}) :
    forall (x y : A), Graph.t@{s|u1 u2}
    := fun x y =>
      @Graph.Pack (x ~> y)
        (TwoGraph.is2graph (is2graph (class A)) x y).
  Module to_hom_graph_exports.
    Canonical to_hom_graph.
  End to_hom_graph_exports.

  Definition is_preorder_mixin@{s|u0 u1 u2|}
    (A : t@{s|u0 u1 u2})
    : PreOrder.mixin_of@{Type|u0 u1} A
    := is_preorder (mixin (class A)).

  Definition to_preorder@{s|u0 u1 u2|} (A : t@{s|u0 u1 u2})
    : PreOrder.t@{Type|u0 u1}
    := @PreOrder.Pack A ({| PreOrder.rel := _;
                        PreOrder.mixin := is_preorder_mixin A|}).

  Definition is_vpreorder_instance (A: t) (x y : A) : PreOrder.mixin_of (TwoGraph.two_hom0 x y)
    := is_vpreorder (mixin (class A)) x y.

  Definition co@{s|+|} : t@{s|_ _ _} -> t@{s|_ _ _}
    := fun x =>
         match x with
         | @Pack sort class =>
             {| sort := sort;
               class := {|
                         is2graph := _;
                         mixin :=
                           @mixin_op
                             (TwoGraph.Pack (is2graph class))
                             (mixin class)
                       |}
             |}
         end.

  Module Exports.
    Export class_of_conventions.
    Export t_conventions.
    Export to_graph_exports.
    Export to2graph_coercion.
    Export to_hom_graph_exports.
    Existing Instance is_preorder_mixin.
    Coercion to_preorder : t >-> PreOrder.t.
    Canonical to_preorder.
    Existing Instance is_vpreorder_instance.
  End Exports.
End OneBicat.
Export OneBicat.Exports.
