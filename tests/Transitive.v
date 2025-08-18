(* From Simplex Require Import Basics. *)
(* From Simplex Require Import Tactics.Transitivity. *)
(* From Simplex Require Import Basics.Nat. *)
From Simplex Require Import Category.Category Category.Functor.
From elpi Require Import elpi.

Set Universe Polymorphism.

Inductive box@{u} (A : Type@{u}) : Type@{u} := unbox (a : A) : box A.
From Ltac2 Require Import Ltac2.

Elpi Tactic null.
Elpi Accumulate lp:{{
      solve G GS :- refine _ G GS.
      }}.

(* Goal forall (A : Type) (a : A), A. *)
(* Proof. *)
(*   intros A a. *)
(*   ltac1:(elpi null (box a)). *)
(*   (* intros n m k p q. *) *)
(*   (* ltac1:(elpi transitivity (m)). *) *)
(* Abort. *)

Goal forall (C D: Category.t)
            (F: Functor.t C D)
            (x y z : Category.sort C)
            (f : Category.Hom x y)
            (g : Category.Hom y z)
            , Category.Hom (Functor.map F x) (Functor.map F z).
Proof.
  intros C D F x y z f g.
  Fail ltac1:(elpi null (Functor.map F y)).
Abort.
