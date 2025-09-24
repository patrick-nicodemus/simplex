From Simplex Require Import Basics Relations Graph.
Local Set Implicit Arguments.
Module PreOrder.
  Class class_of@{s;u0 u1|} (A : Type@{u0}) (R : A -> A -> Type@{s;u1})
    : Type@{s;max(u0+1,u1+1)}
    := Class {
      refl : Reflexive@{s;u0 u1} R;
      trans : Transitive@{s;u0 u1} R
  }.

  Module class_of_exports.
    Arguments Class [A R] &.
    Existing Instance refl.
    Existing Instance trans.
  End class_of_exports.
  Import class_of_exports.

  Record t@{s;u0 u1|} :=
    Pack {
        sort : Type@{u0};
        Hom : sort -> sort -> Type@{s;u1};
        class : class_of@{s;u0 u1} Hom
      }.

  Module t_conventions.
    Arguments Pack & [sort Hom].
    #[reversible] Coercion sort : t >-> Sortclass.
    Coercion Hom : t >-> Funclass.
    Arguments Hom [t].
    Existing Instance class.
  End t_conventions.
  Import t_conventions.
  
  Definition op_class@{s;u0 u1|} (A : Type@{u0}) (R : A -> A -> Type@{s;u1})
                     (P :class_of@{s;u0 u1} R)
    : class_of@{s;u0 u1} (Graph.op_class R)
    := Class (@refl _ _ P) (fun x y z f g => trans z y x g f).

  Definition to_graph@{s;u0 u1|} (A : t@{s;u0 u1}) : Graph.t@{s;u0 u1}
    := Graph.Pack (@Hom A).

  Module to_graph_conventions.
    Canonical to_graph.
    Coercion to_graph : t >-> Graph.t.
  End to_graph_conventions.
  Import to_graph_conventions.

  Definition is_refl@{s;u0 u1|} (A : t@{s;u0 u1})
    : Reflexive@{s;u0 u1} (@Hom A)
    := @refl _ _ (class A).
  Module is_refl_conventions.
    Existing Instance is_refl.
  End is_refl_conventions.

  Definition is_trans@{s;u0 u1 |} (A : t@{s;u0 u1})
    : Transitive@{s;u0 u1} (@Hom A)
    := @trans _ _ (class A).
  Module is_trans_conventions.
    Existing Instance is_trans.
  End is_trans_conventions.
  Import is_trans_conventions.

  Definition op@{s;u0 u1|} (A : t@{s;u0 u1}) : t@{s;u0 u1}
    := Pack (op_class (class A)).

  Abbreviation compose := transitive.

  Module ForExport.
    Export class_of_exports.
    Export t_conventions.
    Export to_graph_conventions.
    Export is_refl_conventions.
    Export is_trans_conventions.
  End ForExport.
  Module Notations.
    Infix "<=" := Hom (at level 70).
    Abbreviation IsPreOrder := class_of.
  End Notations.
End PreOrder.
Export PreOrder.ForExport.
Export PreOrder.Notations.
