From Simplex Require Import Basics.
Local Set Implicit Arguments.
Definition Relation@{s ; u0 u1|} (A : Type@{u0}) := A -> A -> Type@{s|u1}.

Class Reflexive@{s;u0 u1 |}
  [A : Type@{u0}] (R : A -> A -> Type@{s|u1})
  : Type@{s|max(u0+1,u1+1)}
  := reflexive : forall (x : A), R x x.

Class Transitive@{s;u0 u1|}
  {A : Type@{u0}} (R : A -> A -> Type@{s|u1})
  : Type@{s|max(u0+1,u1+1)}
  := transitive : forall (x y z : A), R x y -> R y z -> R x z.
Arguments transitive [A R] {Transitive} [x y z].

Class Symmetric@{s;u0 u1|} {A : Type@{u0}} (R : A -> A -> Type@{s|u1})
  : Type@{s|max(u0+1,u1+1)}
  := symmetry : forall (x y: A), R x y -> R y x.
Arguments symmetry {A R Symmetric x y}.

Notation "f ^" := (symmetry f).
