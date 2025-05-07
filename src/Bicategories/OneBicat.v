From Simplex Require Import Basics Graph TwoGraph PreOrder.Core.
Local Set Implicit Arguments.
Local Open Scope morphism_scope.

Definition Associative@{s|u0 u1 u2|} (A : TwoGraph.t@{s|u0 u1 u2})
  (t : Transitive@{Type|u0 u1} (@TwoGraph.Hom A))
  := forall (w x y z : A)
       (f : TwoGraph.Hom w x) (g : TwoGraph.Hom x y) (h : TwoGraph.Hom y z),
    Couple@{s|u1 u2} _ ((f · g) · h) (f · (g · h)).

Definition LeftUnitor@{s|u0 u1 u2|}
  (A : TwoGraph.t@{s|u0 u1 u2 })
  (t : PreOrder.class_of@{Type|u0 u1} (@TwoGraph.Hom A))
  := forall (x y : A) (f : A x y), Couple@{s|u1 u2} _ ((1 x) · f) f.

Definition RightUnitor@{s|u0 u1 u2|}
  (A : TwoGraph.t@{s|u0 u1 u2})
  (t : PreOrder.class_of@{Type|u0 u1} (@TwoGraph.Hom A))
  := forall (x y : A) (f : A x y), Couple _ (f · (1 y)) f.

Module OneBicat.
  Import TwoGraph.Notations.
  Record class_of@{s|u0 u1 u2|}
    (A : Type@{u0})
    (R : A -> A -> Type@{u1})
    (two_graph : TwoGraph.class_of@{s|u0 u1 u2} R)
    (G := TwoGraph.Pack two_graph) := {
        is_preorder : PreOrder.class_of@{Type|u0 u1} R;
        is_vpreorder : forall (x y: A),
          PreOrder.class_of@{s|u1 u2} (two_graph x y);
        assoc : Associative@{s|u0 u1 u2} G
                  (PreOrder.trans (class_of:=is_preorder));
        lu : LeftUnitor@{s|u0 u1 u2} G is_preorder;
        ru : RightUnitor@{s|u0 u1 u2} G is_preorder;
      hcomp2 : forall (x y z : A)
                 (f f' : TwoGraph.Hom (t:=G) x y)
                 (g g' : TwoGraph.Hom (t:=G) y z),
          f ⇒ f' -> g ⇒ g' -> f · g ⇒ f' · g'
    }.

  Definition co_class@{s|u0 u1 u2|}
    (A : Type@{u0})
    (R : A -> A -> Type@{u1})
    (two_graph : TwoGraph.class_of@{s|u0 u1 u2} R)
    : class_of two_graph -> class_of (TwoGraph.co_class two_graph)
    := fun m =>
         {|
           is_preorder := _;
           is_vpreorder x y := PreOrder.op_class (is_vpreorder m x y);
           assoc w x y z f g h := Graph.couple_op (assoc m w x y z f g h);
           lu x y f := Graph.couple_op (lu m x y f);
           ru x y f := Graph.couple_op (ru m x y f);
           hcomp2 x y z f f' g g' := hcomp2 m x y z f' f g' g
         |}.

  Record t@{s|u0 u1 u2|} :=
    Pack {
        sort : Type@{u0};
        Hom : sort -> sort -> Type@{u1};
        two_cells : TwoGraph.class_of@{s|u0 u1 u2} Hom;
        class : class_of@{s|u0 u1 u2} two_cells
    }.
  Module t_conventions.
    Coercion sort : t >-> Sortclass.
    Arguments Hom [t].
    Arguments two_cells [t x y].
  End t_conventions.
  Import t_conventions.

  Definition to_vpreorder@{s|u0 u1 u2|} (A : t@{s|u0 u1 u2})
    : forall (x y : A), PreOrder.t@{s|u1 u2}
    := fun x y => PreOrder.Pack (is_vpreorder (class A) x y).
  Module to_vpreorder_exports.
    Coercion to_vpreorder : t >-> Funclass.
    Canonical to_vpreorder.
  End to_vpreorder_exports.
  Import to_vpreorder_exports.

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
    := TwoGraph.Pack (@two_cells A).

  Module to2graph_coercion.
    Coercion to2graph : t >-> TwoGraph.t.
    Canonical to2graph.
  End to2graph_coercion.
  Import to2graph_coercion.

  Definition to_hom_graph@{s|u0 u1 u2|}
    (A:t@{s|u0 u1 u2}) :
    forall (x y : A), Graph.t@{s|u1 u2}
    := fun (x y : A) =>
      @Graph.Pack (Hom x y) (@two_cells _ x y).
  Module to_hom_graph_exports.
    Canonical to_hom_graph.
  End to_hom_graph_exports.

  Definition is_preorder_class@{s|u0 u1 u2|}
    (A : t@{s|u0 u1 u2})
    : PreOrder.class_of@{Type|u0 u1} (@Hom A)
    := is_preorder (class A).

  (** The horizontal preorder, i.e. 0-cells ordered by 1-cells as relations *)
  Definition to_preorder@{s|u0 u1 u2|} (A : t@{s|u0 u1 u2})
    : PreOrder.t@{Type|u0 u1}
    := @PreOrder.Pack _ _ (is_preorder_class A).

  Definition is_vpreorder_instance (A: t) (x y : A)
    : PreOrder.class_of (A x y)
    := is_vpreorder (class A) x y.

  Definition co@{s|+|} : t@{s|_ _ _} -> t@{s|_ _ _}
    := fun x =>
         match x with
         | @Pack sort Hom two_cells class =>
             {| sort := sort;
               Hom := Hom;
               two_cells x y f g := two_cells x y g f;
               class := co_class class
             |}
         end.

  Module Exports.
    Export t_conventions.
    Export to_graph_exports.
    Export to2graph_coercion.
    Export to_hom_graph_exports.
    Existing Instance is_preorder_class.
    Coercion to_preorder : t >-> PreOrder.t.
    Canonical to_preorder.
    Existing Instance is_vpreorder_instance.
  End Exports.
  Module Notations.
    Local Set Warnings "-notation-overridden".
    Infix "~>" := Hom (at level 41).
    Infix "⇒" := two_cells (at level 39).
  End Notations.
End OneBicat.
Export OneBicat.Exports.
