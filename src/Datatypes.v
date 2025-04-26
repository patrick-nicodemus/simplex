Require Corelib.Init.Datatypes.
From Simplex Require Import Basics.
Local Set Implicit Arguments.

Notation unit := Datatypes.unit.

Inductive sUnit : SProp := stt.
Inductive sEmpty : SProp := .

Inductive prod@{s|u1 u2|} (A : Type@{s|u1}) (B : Type@{s|u2})
  : Type@{s|max(u1,u2)}
  := { fst : A; snd : B}.

Infix "*" := prod (at level 40, left associativity)
    : type_scope.
Infix "/\" := prod (at level 80, right associativity)
    : type_scope.

Definition not@{s|u|} (A : Type@{s|u}) := A -> sEmpty.
Inductive sig@{s|u0 u1|} (A : Type@{u0})
  (P : A -> Type@{s|u1}) : Type@{max(u0,u1)}
  := exist : forall (a : A), P a -> sig P.

Notation "{ x | P }" := (sig (fun x => P)) (at level 0, x at level 99) : type_scope.
Notation "{ x : A | P }" :=
  (sig (fun x : A => P)) (at level 0, x at level 99) : type_scope.

Inductive sig2@{s1 s2|u0 u1 u2|} (A : Type@{u0})
  (P : A -> Type@{s1|u1})
  (Q : A -> Type@{s2|u2})
  : Type@{max(u0,u1,u2)}
  := exist2 : forall (a : A), P a -> Q a -> sig2 P Q.
#[warnings="-w -notation-overridden"]
Notation "~ x" := (not x) (at level 75, right associativity) : type_scope.
