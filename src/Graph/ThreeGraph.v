From Simplex Require Import Basics Graph TwoGraph.
Local Set Implicit Arguments.
Module ThreeGraph.
  Definition class_of@{s|u0 u1 u2 u3|}
    (A : Type@{u0}) (R : A -> A -> Type@{u1})
    (RR : TwoGraph.class_of@{Type|u0 u1 u2} R)
    := forall (x y : A) (f g : R x y) (s t : RR x y f g), Type@{s|u3}.
  Structure t@{s|u0 u1 u2 u3|} := {
      sort : Type@{u0};
      Hom : sort -> sort -> Type@{u1};
      TwoHom : TwoGraph.class_of Hom;
      ThreeHom : class_of@{s|u0 u1 u2 u3} TwoHom
    }.
  Definition local_two_hom@{s|u0 u1 u2 u3|} (A:  t@{s|u0 u1 u2 u3})
    : forall (x y : sort A), TwoGraph.t@{s|u1 u2 u3}
    := fun x y =>
         {|
           TwoGraph.sort := Hom A x y;
           TwoGraph.Hom := TwoHom A x y;
           TwoGraph.class := ThreeHom A x y;
         |}.

  Module Exports.
    Coercion sort : t >-> Sortclass.
    Coercion local_two_hom : t >-> Funclass.
  End Exports.
End ThreeGraph.
Export ThreeGraph.Exports.
