From Simplex Require Import Basics Relations.

Class Comm@{s;u0 u1 u2|}
  {A : Type@{u1}}
  {B : Type@{u0}}
  (R : Relation@{s;u1 u2} A)
  (f : B -> B -> A)
  := comm x y : R (f x y) (f y x).

Class LeftId@{s;u0 u1|} {A : Type@{u0}} (R : Relation@{s;u0 u1} A)
  (i : A) (f : A -> A -> A)
  :=  left_id x : R (f i x) x.

Class RightId@{s;u0 u1|} {A : Type@{u0}} (R : Relation@{s;u0 u1} A)
  (i : A) (f : A -> A -> A)
  :=  right_id x : R (f x i) x.
