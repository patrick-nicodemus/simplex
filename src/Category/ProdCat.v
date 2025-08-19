From Simplex Require Import
  Basics.Basics
  Basics.Eq
  Datatypes
  PreOrder.Instances
  PreOrder.Compose
  OneBicat
  Category.Category
  Category.Functor
  Graph.Graph
  Category.CategoricalProduct
.

From Simplex Require Tactics.

Import Graph.Notations.

Definition product@{;uAob uAarr uBob uBarr +|+}
  (A : Category.t@{; uAob uAarr})
  (B : Category.t@{; uBob uBarr})
  : Category.t@{;_ _}.
Proof.
  unshelve refine '(Category.Build _) > [
      exact ((A * B)%type)
    | apply prod_binary > [ apply Category.Hom | apply Category.Hom ]
    | unshelve econstructor
    ].
  constructor; simpl.
  - intros [w w'] [x x'] [y y'] [z z'] [f f'] [g g'] [h h'];
      simpl in *.
    apply prod_eq; apply Category.assoc.
  - intros [x0 x1] [y0 y1] [f0 f1]; simpl in *; apply prod_eq; apply Category.lu.
  - intros [x0 x1] [y0 y1] [f0 f1]; simpl in *; apply prod_eq; apply Category.ru.
Defined.

Canonical product.
Infix "×" := product (at level 70).

Definition univ_map (A X Y : Category.t)
  (F : Functor.t A X)
  (G : Functor.t A Y)
  : Functor.t A (X × Y).
Proof.
  unshelve econstructor.
  Abort.

Definition arrow_pair {C D : Category.t} {c c' : C} {d d' : D}
  (f : Category.Hom c c') (g : Category.Hom d d') :
  @Category.Hom (product C D) (c,d) (c',d') := (f,g).

Notation "⟨ f , g ⟩" := (arrow_pair f g) (at level 90).

Definition left_specialize (C D E : Category.t) (F : Functor.t (C × D) E) (c : C)
  : Functor.t D E.
Proof.
  unshelve econstructor.
  - exact (fun d => (F (c, d))).
  - intros a b f; simpl. refine '(fmap F _ ). exact ( 1 c , f )%hom.
  - constructor.
    + reflexivity.
    + simpl. intros x y z f g.
      refine '(match (Category.lu (1%hom c)) in eq _ zz
                    return
                    (Functor.fmap F (c,x) (c,z) (zz, f · g)) =
                      _ with eq_refl _ => _ end).
      refine '(transitive
                 (y:=((Functor.fmap F _ _ ((⟨ id c , f ⟩) · (⟨ id c, g ⟩)))
                 )) _ _ ) ; try(exact _).
      * reflexivity.
      * apply (Functor.F_comp (c,x) (c,y) (c,z)).
Defined.
