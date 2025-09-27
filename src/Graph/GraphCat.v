(** The category of graphs. *)
From Simplex Require Import Basics.
From Simplex.Graph Require Import Graph.
From Simplex.PreOrder Require Import Core.
From Simplex.Category Require Import Category.
From Simplex Require Import Tactics.

Instance IsPreOrderGraph : IsPreOrder GraphHom.t.
Proof.
  unshelve econstructor; exact _.
Defined.

Definition GraphCat : Category.t.
Proof.
  refine ({| Category.sort := Graph.t ; Category.Hom G H := GraphHom.t G H |}).
  eapply Category.Of_Preorder.Builder.
  (* TODO *)
  Abort.
