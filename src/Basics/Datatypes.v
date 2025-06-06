Require Corelib.Init.Datatypes.
From Simplex Require Import Basics Eq.
Local Set Implicit Arguments.

Notation unit := Datatypes.unit.

Inductive sUnit : SProp := stt.
Inductive sEmpty : SProp := .

Record prod@{s|u1 u2|} (A : Type@{s|u1}) (B : Type@{s|u2})
  : Type@{s|max(u1,u2)}
  := { fst : A; snd : B}.

Infix "*" := prod (at level 40, left associativity)
    : type_scope.
Infix "/\" := prod (at level 80, right associativity)
    : type_scope.

Theorem prod_eq (A B : Type) (p q : A * B)
  : fst p = fst q -> snd p = snd q -> p = q.
Proof.
  destruct p, q; simpl in *.
  intros fsteq sndeq.
  destruct fsteq.
  destruct sndeq.
  reflexivity.
Defined.

Definition prod_unary@{s|+|+}
  (A : Type) (PA : A -> Type@{s|_})
  (B : Type) (PB : B -> Type@{s|_})
  : A * B -> Type@{s|_}
  := fun ab => (PA (fst ab) /\ PB (snd ab))%type.

Definition prod_binary@{s|+|+}
  (A : Type) (RA : A -> A -> Type@{s|_})
  (B : Type) (RB : B -> B -> Type@{s|_})
  : A * B -> A * B -> Type@{s|_}
  := fun ab ab' => (RA (fst ab) (fst ab') /\ RB (snd ab) (snd ab'))%type.

Definition uncurry@{s1 s2|u0 u1 u2|} (A : Type@{s1|u0})
  (B : Type@{s1|u1}) (C : Type@{s2|u2}) (f : A -> B -> C)
  : A * B -> C
  := fun x => f (fst x) (snd x).

Definition curry@{s1 s2 | u0 u1 u2|} (A : Type@{s1|u0})
  (B : Type@{s1|u1}) (C : Type@{s2|u2}) (f : A * B -> C)
  : A -> B -> C
  := fun a b => f {| fst := a; snd := b |}.

Definition not@{s|u|} (A : Type@{s|u}) := A -> sEmpty.

Record sig@{s|u0 u1|} (A : Type@{u0})
  (P : A -> Type@{s|u1}) : Type@{max(u0,u1)}
  := {
    ex_val : A;
    ex_pf : P ex_val
  }.

Definition sig_trans@{s|u0 u1|}
  (A : Type@{u0})
  (P : A -> Type@{s|u1})
  (a : A)
  (p : sig P) :
  a = ex_val p -> P a
  := fun eqp => transport _ eqp (ex_pf p).

Notation "{ x | P }" := (sig (fun x => P)) (at level 0, x at level 99) : type_scope.
Notation "{ x : A | P }" :=
  (sig (fun x : A => P)) (at level 0, x at level 99) : type_scope.

Record sig2@{s1 s2|u0 u1 u2|} (A : Type@{u0})
  (P : A -> Type@{s1|u1})
  (Q : A -> Type@{s2|u2})
  : Type@{max(u0,u1,u2)}
  := {
    ex2 : A;
    exP : P ex2;
    exQ : Q ex2
  }.

(* Inductive sig2@{s1 s2|u0 u1 u2|} (A : Type@{u0}) *)
(*   (P : A -> Type@{s1|u1}) *)
(*   (Q : A -> Type@{s2|u2}) *)
(*   : Type@{max(u0,u1,u2)} *)
(*   := exist2 : forall (a : A), P a -> Q a -> sig2 P Q. *)
#[warnings="-w -notation-overridden"]
Notation "~ x" := (not x) (at level 75, right associativity) : type_scope.
