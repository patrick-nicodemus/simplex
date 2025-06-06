From Simplex Require Import Basics Basics.Datatypes Basics.List Basics.Nat Graph Graph.Path.
Local Set Implicit Arguments.
Module TwoGraph.
  Definition class_of@{s;u0 u1 u2|} (A : Type@{u0}) (R : A -> A -> Type@{u1})
    := forall (x y : A) (f g : R x y), Type@{s|u2}.

  Structure t@{s;u0 u1 u2|} :=
    Pack {
        sort : Type@{u0};
        Hom : sort -> sort -> Type@{u1};
        class : class_of@{s|u0 u1 u2} Hom
      }.

  Module t_conventions.
    Coercion sort : t >-> Sortclass.
    Arguments Pack [sort Hom].
    Arguments Hom [t].
    Arguments class [t x y].
  End t_conventions.
  Import t_conventions.

  Definition to_graph@{s;u0 u1 u2|} (A: t@{s;u0 u1 u2})
    : Graph.t@{Type;u0 u1}
    := Graph.Pack (@Hom A).

  Definition two_hom@{s;u0 u1 u2|} {A : t@{s;u0 u1 u2}} (x y : A)
    : Graph.t@{s;u1 u2}
    := Graph.Pack (@class _ x y).

  Module two_hom_exports.
    Canonical two_hom.
    Coercion two_hom : t >-> Funclass.
  End two_hom_exports.
  Import two_hom_exports.

  Definition co_class@{s;u0 u1 u2|} (A : Type@{u0}) (R : A -> A -> Type@{u1})
    : class_of@{s;u0 u1 u2} R -> class_of@{s;u0 u1 u2} R
    := fun P (x y : A) (f g : R x y) => P x y g f.

  Definition co@{s;u0 u1 u2|} (A : t@{s;u0 u1 u2}) : t@{s;u0 u1 u2}
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
  Class mixin_of@{s1 s2;uA0 uA1 uA2 uB0 uB1 uB2|}
    {A : TwoGraph.t@{s1|uA0 uA1 uA2}} {B : TwoGraph.t@{s2|uB0 uB1 uB2}}
    (F : GraphHom.t A B)
    := ffmap : forall (x y : A), GraphHom.class_of (GraphHom.fmap F (x:=x) (y:=y)).

  Class class_of@{s1 s2;uA0 uA1 uA2 uB0 uB1 uB2} {A : TwoGraph.t@{s1|uA0 uA1 uA2}} {B : TwoGraph.t@{s2|uB0 uB1 uB2}}
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
  Structure t@{s1 s2;uA0 uA1 uA2 uB0 uB1 uB2} (A : TwoGraph.t@{s1|uA0 uA1 uA2}) (B : TwoGraph.t@{s2|uB0 uB1 uB2})
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
  
  Definition to_graph_hom @{s1 s2;uA0 uA1 uA2 uB0 uB1 uB2|} [A B] (F : t@{s1 s2;uA0 uA1 uA2 uB0 uB1 uB2} A B)
    : GraphHom.t@{Type Type|_ _ _ _} A B
    := GraphHom.Pack (is_graph_hom (class F)).

  Module Exports.
    Export t_conventions.
    Export class_of_conventions.
    Coercion to_graph_hom : t >-> GraphHom.t.
  End Exports.
End TwoGraphHom.
Export TwoGraphHom.Exports.

(** If [G] is a [TwoGraph.t], and [p, q] are two paths in [G] from
    node [x] to [y] along the same list of nodes, then there
    is a natural binary relation betwen [p] and [q],
    namely, whether their paths are related. *)
Fixpoint path_rel@{s;u0 u1 u2} (A : TwoGraph.t@{s|u0 u1 u2})
  (a : A) (l : list A) : Relation@{s;_ _} (path_on@{Type;u0 u1} (@TwoGraph.Hom A) a l)
  :=
  match l return forall p q : path_on (@TwoGraph.Hom A) a l, Type@{s|u2} with
  | List.nil => fun _ _ => unit@{s|}
  | hd :: tl => fun p q =>
                ((TwoGraph.class (fst p) (fst q)) /\
                  path_rel _ hd tl (snd p) (snd q))%type
  end.

Canonical path_graph@{s;u0 u1 u2}
  (A : TwoGraph.t@{s|u0 u1 u2})
  (a : A) (l : list A)
  : Graph.t@{s;u1 u2}
  := Graph.Pack (path_rel A a l).

Definition take_on@{s; u0 u1 u2} (A : TwoGraph.t@{s|u0 u1 u2}) (a : A) (l : list A)
  (k : nat) (p q: Graph.Path.path_on (TwoGraph.Hom (t:=A)) a l) (s : Graph.Hom p q)
  : Graph.Hom (Path.take_on@{Type|u0 u1} A a l k p)
      (Graph.Path.take_on@{Type|u0 u1} A a l k q).
Proof.
  revert l a k p q s.
  refine '(fix IH l := match l with | hd :: tl => _ | List.nil => _ end).
  - clear l.
    intros a k p q s.
    simpl. destruct k.
    + exact tt.
    + simpl. refine '({| fst := fst s; |}).
      apply IH.
      exact (snd s).
  - intros a k p q s.
    destruct k; exact tt.
Defined.
