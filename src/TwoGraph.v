From Simplex Require Import Basics Graph.
Local Set Implicit Arguments.
Module TwoGraph.
  Definition mixin_of@{s|u0 u1 u2|} (A : Graph.t@{Type|u0 u1})
    := forall (x y : A), Graph.class_of@{s|u1 u2} (Hom x y).

  Record class_of@{s|u0 u1 u2|} (A : Type@{u0}) := Class {
    base : Graph.class_of@{Type|u0 u1} A;
    is2graph : mixin_of@{s|u0 u1 u2} (Graph.Pack base)
  }.  

  Module class_of_exports.
  End class_of_exports.

  Structure t@{s|u0 u1 u2|} := Pack {
      sort : Type@{u0};
      class : class_of@{s|u0 u1 u2} sort;
  }.
  Module t_conventions.
    Coercion sort : t >-> Sortclass.
    Arguments Pack [sort] &.
  End t_conventions.
  Import t_conventions.

  Definition to_graph@{s|u0 u1 u2|} (A: t@{s|u0 u1 u2})
    : Graph.t@{Type|u0 u1}
    := Graph.Pack (base (class A)).

  Definition two_hom@{s|u0 u1 u2|} {A : t@{s|u0 u1 u2}} (x y : A) :=
    Graph.Pack (is2graph@{s|u0 u1 u2} (class A) x y).

  Module two_hom_exports.
    Canonical two_hom.
  End two_hom_exports.
  Import two_hom_exports.

  Definition co@{s|+|} (A : t@{s|_ _ _}) : t@{s|_ _ _}
    := {|
      sort := sort A;
      class :=
        {|
          base := base (class A);
          is2graph x y f g := Hom g f
       |}
    |}.
  
  Module ForExport.
    Export t_conventions.
    Coercion to_graph : t >-> Graph.t.
    Export two_hom_exports.    
    Canonical to_graph.
    Infix "⇒" := (Hom (t:=@two_hom _ _ _ )) (at level 39, right associativity).
  End ForExport.
End TwoGraph.
Export TwoGraph.ForExport.

(* Section test. *)
(*   Set Printing All. *)
(*   Set Typeclasses Debug. *)
(*   Require Unicoq.Unicoq. *)
(*   Set Unicoq Debug. *)
(*   Context (A : TwoGraph.t). *)
(*   Context (x y : A). *)
(*   Print TwoGraph.to_graph. *)
(*   Set Printing Coercions. *)
(*   Print Canonical Projections. *)

(*   Check (@Graph.Hom _ x y). *)


Module TwoGraphHom.
  Class mixin_of@{s1 s2|+|} {A : TwoGraph.t@{s1|_ _ _}} {B : TwoGraph.t@{s2|_ _ _}}
    (F : GraphHom.t A B)
    := ffmap : forall (x y : A), GraphHom.class_of (fmap F (x:=x) (y:=y)).

  Class class_of@{s1 s2|+|} {A : TwoGraph.t@{s1|_ _ _}} {B : TwoGraph.t@{s2|_ _ _}}
    (F : A -> B)
    := Class {
           is_graph_hom : GraphHom.class_of F;
           is_2graph_hom : mixin_of (GraphHom.Pack is_graph_hom)
         }.
  Module class_of_conventions.
    Arguments is_graph_hom [A B F].
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
  End t_conventions.
  Import t_conventions.
  
  Definition to_graph_hom @{s1 s2|+|} [A B] (F : t@{s1 s2|_ _ _ _ _ _} A B)
    : GraphHom.t@{Type Type|_ _ _ _} A B
    := GraphHom.Pack (is_graph_hom (class F)).
  Module Exports.
    Export t_conventions.
    Export class_of_conventions.
  End Exports.
End TwoGraphHom.
Export TwoGraphHom.Exports.
