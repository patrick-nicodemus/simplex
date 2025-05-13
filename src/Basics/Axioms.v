From Simplex Require Import Basics Eq.
Class Funext := funext : forall (A : Type) (B : A -> Type) (f g : forall (a : A), B a), (forall (x : A), f x = g x) -> f = g.
