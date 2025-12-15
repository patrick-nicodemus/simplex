(** The category of graphs. *)
From Simplex Require Import Basics.Basics Basics.Datatypes_core.
From Simplex.Graph Require Import Graph.
From Simplex.PreOrder Require Import Core.
From Simplex.Category Require Import Category CategoricalProduct.
From Simplex Require Import Tactics.
From Simplex Require Import ElpiTactics.
From elpi Require Import elpi.

Instance IsPreOrderGraph : IsPreOrder GraphHom.t.
Proof.
  unshelve econstructor; exact _.
Defined.

Canonical GraphPreOrder := PreOrder.Pack IsPreOrderGraph.

Definition GraphCat : Category.t.
Proof.
  refine ({| Category.sort := Graph.t ; Category.Hom G H := GraphHom.t G H |}).
  eapply Category.Of_Preorder.Builder.
  unshelve econstructor;
  firstorder.
Defined.

Canonical GraphCat.

Instance ProductGraph (G1 G2 : Graph.t) : Product G1 G2 (Prod G1 G2).
Proof.
  ltac1:(elpi next_valid).
  {
      ltac1:(elpi next_valid). {
        ltac1:(elpi next_valid).
        firstorder.
    }
    ltac1:(elpi next_valid).
    simpl.

    Set Printing All.
    unfold GraphHom.class_of.
    
    unshelve econstructor.
    ltac1:(elpi next_valid).

 

  encap(). {
    ltac1:(elpi next_valid). {
      ltac1:(elpi next_valid). {
        ltac1:(elpi next_valid).
        firstorder.
    }
    ltac1:(elpi next_valid).
  }
  ltac1:(elpi next_valid).
  ltac1:(elpi next_valid).
  ltac1:(elpi next_valid).
  - Set Printing All.

  (*
    Options:
    - whd in type of H at the time it's introduced.
    - whd *and* destruct H at the time it's introduced.
    - Forward reasoning: destruct H.
  *)
  hnf in H.

    Set Printing All. 
  ltac1:(elpi next_valid).
  ltac1:(elpi next_valid).
  ltac1:(elpi next_valid).

Abort.