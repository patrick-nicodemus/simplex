From Simplex Require Import Basics Graph.
Local Set Implicit Arguments.
Module TwoGraph.
  Definition class_of@{s|u0 u1 u2|} (A : Type@{u0}) (R : A -> A -> Type@{u1})
    := forall (x y : A) (f g : R x y), Type@{s|u2}.

  Structure t@{s|u0 u1 u2|} :=
    Pack {
        sort : Type@{u0};
        Hom : sort -> sort -> Type@{u1};
        class : class_of@{s|u0 u1 u2} Hom
      }.

  Module t_conventions.
    Coercion sort : t >-> Sortclass.
    (* Coercion Hom : t >-> Funclass. *)
    Arguments Pack [sort Hom].
    Arguments Hom [t].
    Arguments class [t x y].
  End t_conventions.
  Import t_conventions.

  Definition to_graph@{s|u0 u1 u2|} (A: t@{s|u0 u1 u2})
    : Graph.t@{Type|u0 u1}
    := Graph.Pack (@Hom A).

  Definition two_hom@{s|u0 u1 u2|} {A : t@{s|u0 u1 u2}} (x y : A)
    : Graph.t@{s|u1 u2}
    := Graph.Pack (@class _ x y).

  Module two_hom_exports.
    Canonical two_hom.
    Coercion two_hom : t >-> Funclass.
  End two_hom_exports.
  Import two_hom_exports.

  Definition co_class@{s|u0 u1 u2|} (A : Type@{u0}) (R : A -> A -> Type@{u1})
    : class_of@{s|u0 u1 u2} R -> class_of@{s|u0 u1 u2} R
    := fun P (x y : A) (f g : R x y) => P x y g f.

  Definition co@{s|+|} (A : t@{s|_ _ _}) : t@{s|_ _ _}
    := {|
      sort := sort A;
      Hom := @Hom A;
      class := co_class (@class A)
    |}.
  
  Module ForExport.
    Export t_conventions.
    Coercion to_graph : t >-> Graph.t.
    Canonical to_graph.
    Export two_hom_exports.
  End ForExport.
  Module Notations.
    Infix "~>" := (@Hom _ ) (at level 41, right associativity).
    Infix "⇒" := (@class _ _ _) (at level 39, right associativity).
  End Notations.
End TwoGraph.
Export TwoGraph.ForExport.

Module TwoGraphHom.
  Class mixin_of@{s1 s2|+|} {A : TwoGraph.t@{s1|_ _ _}} {B : TwoGraph.t@{s2|_ _ _}}
    (F : GraphHom.t A B)
    := ffmap : forall (x y : A), GraphHom.class_of (GraphHom.fmap F (x:=x) (y:=y)).

  Class class_of@{s1 s2|+|} {A : TwoGraph.t@{s1|_ _ _}} {B : TwoGraph.t@{s2|_ _ _}}
    (F : A -> B)
    := Class {
           is_graph_hom : GraphHom.class_of F;
           is_2graph_hom : mixin_of (GraphHom.Pack is_graph_hom)
         }.
  Module class_of_conventions.
    Arguments is_graph_hom [A B F].
    Coercion is_graph_hom : class_of >-> GraphHom.class_of.
  End class_of_conventions.
  Import class_of_conventions.
  Structure t@{s1 s2|+|} (A : TwoGraph.t@{s1|_ _ _}) (B : TwoGraph.t@{s2|_ _ _})
    := Pack {
      map : A -> B;
      class : class_of map
    }.
  Module t_conventions.
    Arguments class [A B].
    Arguments Pack [A B] & [map].
    Coercion map : t >-> Funclass.
  End t_conventions.
  Import t_conventions.
  
  Definition to_graph_hom @{s1 s2|+|} [A B] (F : t@{s1 s2|_ _ _ _ _ _} A B)
    : GraphHom.t@{Type Type|_ _ _ _} A B
    := GraphHom.Pack (is_graph_hom (class F)).

  Module Exports.
    Export t_conventions.
    Export class_of_conventions.
    Coercion to_graph_hom : t >-> GraphHom.t.
  End Exports.
End TwoGraphHom.
Export TwoGraphHom.Exports.
