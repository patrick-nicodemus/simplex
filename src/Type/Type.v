From Simplex Require Import
  Basics
  Basics.Datatypes_core
  Basics.SEq
  PreOrder.Core
  PreOrder.Instances
  Category.Category
  Category.CategoricalProduct
  Tactics
.

Definition TypeIsCat@{u} : Category.class_of (fun A B : Type@{u} => A -> B).
Proof.
  naive().
Defined.

Definition TypeCat@{u} : Category.t@{;u+1 u} := Category.Pack TypeIsCat@{u}.

Definition univ_prod_map (A X Y: Type) (f : A -> X) (g : A->Y)
  : A -> X * Y
  := fun a => (f a, g a).

Instance TypeHasProducts : HasProducts TypeCat.
Proof.
  unshelve econstructor.
  - exact (fun A B => (A * B)%type).
  - intros X Y; unshelve econstructor.
    + exact (@fst X Y).
    + exact (@snd X Y).
    + intros A f g; unshelve econstructor.
      * unshelve econstructor.
        { exact (univ_prod_map A X Y f g). }
        { reflexivity. }
        { reflexivity. }
      * intros [h eqf eqg].
        simpl.
        apply eq_implies_seq.
        refine (sig2_eq _ _ _ _ _).
        { destruct eqf, eqg; reflexivity. }
        { destruct eqf, eqg; reflexivity. }
        { destruct eqf, eqg; reflexivity. }
Defined.
