From Simplex Require Import Basics.Basics.
Local Set Implicit Arguments.

Inductive unit@{s;} : Type@{s;Set} := tt : unit.
Inductive empty@{s;} : Type@{s;Set} := .

Record prod@{s;u1 u2|} (A : Type@{s;u1}) (B : Type@{s;u2})
  : Type@{s;max(u1,u2)}
  := { fst : A; snd : B}.

Infix "*" := prod (at level 40, left associativity)
    : type_scope.
Infix "/\" := prod (at level 80, right associativity)
    : type_scope.

Definition not@{sA sn;u|} (A : Type@{sA;u}) := A -> empty@{sn;}.
Notation "~ A" := (not A) (at level 39).

Record sig@{s;u0 u1|} (A : Type@{u0})
  (P : A -> Type@{s;u1}) : Type@{max(u0,u1)}
  := {
    ex_val : A;
    ex_pf : P ex_val
  }.

Notation "{ x | P }" := (sig (fun x => P)) (at level 0, x at level 99) : type_scope.
Notation "{ x : A | P }" :=
  (sig (fun x : A => P)) (at level 0, x at level 99) : type_scope.

Record sig2@{s1 s2;u0 u1 u2|} (A : Type@{u0})
  (P : A -> Type@{s1;u1})
  (Q : A -> Type@{s2;u2})
  : Type@{max(u0,u1,u2)}
  := { ex2val : A; ex2P : P ex2val; ex2Q : Q ex2val }.

Definition prod_unary@{s;uA uPA uB uPB uPAB|uPA<=uPAB,uPB<=uPAB}
  (A : Type@{uA}) (PA : A -> Type@{s;uPA})
  (B : Type@{uB}) (PB : B -> Type@{s;uPB})
  : A * B -> Type@{s;uPAB}
  := fun ab => (PA (fst ab) /\ PB (snd ab))%type.

Definition prod_binary@{s;uA uPA uB uPB uPAB|uPA<=uPAB,uPB<=uPAB}
  (A : Type@{uA}) (RA : A -> A -> Type@{s;uPA})
  (B : Type@{uB}) (RB : B -> B -> Type@{s;uPB})
  : A * B -> A * B -> Type@{s;uPAB}
  := fun ab ab' => (RA (fst ab) (fst ab') /\ RB (snd ab) (snd ab'))%type.

Definition uncurry@{s1 s2;u0 u1 u2|} (A : Type@{s1;u0})
  (B : Type@{s1;u1}) (C : Type@{s2;u2}) (f : A -> B -> C)
  : A * B -> C
  := fun x => f (fst x) (snd x).

Definition curry@{s1 s2;u0 u1 u2|} (A : Type@{s1;u0})
  (B : Type@{s1;u1}) (C : Type@{s2;u2}) (f : A * B -> C)
  : A -> B -> C
  := fun a b => f {| fst := a; snd := b |}.
