From Simplex Require Import Basics.
Local Set Implicit Arguments.

(** Defines a Graph. Definitions in this file are qualified, except for [Reflexive], [Transitive] and [Symmetric]. *)
Module Graph.
  Definition class_of@{s|u0 u1|} (A : Type@{u0}) := A -> A -> Type@{s|u1}.
  Record t@{s|u0 u1|} : Type@{max(u0+1,u1+1)}:= Pack {
      sort : Type@{u0};
      Hom : class_of@{s|u0 u1} sort
                                                  }.
  Definition op@{s|+|} (A : t@{s|_ _}) : t@{s|_ _}
    := {|
      sort := sort A;
      Hom a b := Hom A b a
    |}.

  Module ForExport.
    Arguments Hom [_].
    Arguments Pack [sort].
    Coercion sort : t >-> Sortclass.
    Infix "~>" := Hom (at level 41) : type_scope.
    Declare Scope morphism_scope.
    Delimit Scope morphism_scope with hom.
    Bind Scope morphism_scope with Hom.
    Notation Hom := Hom.
  End ForExport.
End Graph.
Export Graph.ForExport.

(* #[mode="+ -"] *)
Class Reflexive@{s | u0 u1 |}
  [A : Type@{u0}] (R : A -> A -> Type@{s | u1})
  : Type@{s|max(u0+1,u1+1)}
  := reflexive : forall (x : A), R x x.

Notation "1" := (@reflexive _ _ _) : morphism_scope.

Class Transitive@{s |u0 u1|}
  {A : Type@{u0}} (R : A -> A -> Type@{s | u1})
  : Type@{s|max(u0+1,u1+1)}
  := transitive : forall (x y z : A), R x y -> R y z -> R x z.

Infix "·" := (@transitive _ _ _ _ _ _) (at level 39).

Class Symmetric@{s | u0 u1|} {A : Type@{u0}} (R : A -> A -> Type@{s | u1})
  : Type@{s|max(u0+1,u1+1)}
  := symmetry : forall (x y: A), R x y -> R y x.

Record Couple@{s|u0 u1|} (A: Graph.t@{s|u0 u1}) (x y : A)
  : Type@{s|max(u0+1,u1+1)}
  := {
    Rxy : x ~> y;
    Ryx : y ~> x
  }.

Arguments Couple A &.

Definition couple_op@{s|u0 u1|} (A: Graph.t@{s|u0 u1}) (x y : A)
  (p : Couple A x y)
  : Couple (Graph.op A) x y
  := Build_Couple (Graph.op A) _ _ (Ryx p) (Rxy p).

Module GraphHom.
  Class class_of@{s1 s2|+|} {A : Graph.t@{s1|_ _}} {B : Graph.t@{s2|_ _}}
    (F : A -> B)
    := fmap : forall {x y  : A}, x ~> y -> F x ~> F y.

  Structure t@{s1 s2|+|} (A : Graph.t@{s1|_ _}) (B : Graph.t@{s2|_ _})
    := Pack {
           map : A -> B;
           class : class_of map
         }.
  Module Exports.
    Coercion map : t >-> Funclass.
    Notation fmap := fmap.
    Arguments fmap [A B] F {class_of} [x y].
    Arguments Pack [A B map].
    Existing Instance class.
  End Exports.
End GraphHom.
Export GraphHom.Exports.

Module Graph_of_Graphs.
  (* Definition Graph. *)
End Graph_of_Graphs.
