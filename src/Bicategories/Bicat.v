From Simplex Require Import Basics Datatypes Graph PreOrder.Core PreOrder.Instances OneBicat Category Functor FunctorCat.

Module Bicategory.
  (* Notation EG := ExponentialGraph. *)
  (* Definition left_assoc_graph_hom (A : OneBicat.t) (w x y z : A) : *)
  (*   GraphHom.t (OneBicat.vpreorder w x) *)
  (*     (EG (OneBicat.vpreorder x y) *)
  (*        (EG (OneBicat.vpreorder y z) (OneBicat.vpreorder w z))). *)
  (* Proof. *)
  (*   unshelve econstructor. *)
  (*   - intros f g h. simpl in *. exact ((f · g) · h). *)
  (*   - intros f f' sigma g g' tau h h' rho; simpl in *. *)
  (*     apply OneBicat.hcomp2. *)
  (*     + apply OneBicat.hcomp2. *)
  (*       * exact sigma. *)
  (*       * exact tau. *)
  (*     + exact rho. *)
  (* Defined. *)

  (* Definition right_assoc_graph_hom (A : OneBicat.t) (w x y z : A) : *)
  (*   GraphHom.t (OneBicat.vpreorder w x) *)
  (*     (EG (OneBicat.vpreorder x y) *)
  (*        (EG (OneBicat.vpreorder y z) (OneBicat.vpreorder w z))). *)
  (* Proof. *)
  (*   unshelve econstructor. *)
  (*   - intros f g h. simpl in *. exact (f · (g · h)). *)
  (*   - intros f f' sigma g g' tau h h' rho; simpl in *. *)
  (*     apply OneBicat.hcomp2 > [exact sigma|]. *)
  (*     apply OneBicat.hcomp2 > [exact tau | exact rho]. *)
  (* Defined. *)
  Record mixin_of@{u0 u1 u2} (A : OneBicat.t@{Type|u0 u2 u2}) := {
      is_vcat (x y : A) : Category.Mixin.mixin_of (OneBicat.vpreorder x y);
      vcat (x y : A) :=
        (@Category.Build _ _  
           (Category.Build_class_minimal
              (is_vcat x y)));
      assoc_inv (w x y z : A)
        (f : vcat w x)
        (g : vcat x y)
        (h : vcat y z) :
      @Category.AreInverse
        (vcat w z)
        _ _
        (Rxy (OneBicat.assoc f g h) :
          (@Graph.Hom (OneBicat.to_hom_graph A w z) _ _))
        (Ryx (OneBicat.assoc f g h));
      lu_inv (x y : A) (f : vcat x y) : @Category.AreInverse (vcat x y) _ _ (Rxy (OneBicat.lu f)) (Ryx (OneBicat.lu f));
      ru_inv (x y : A) (f : vcat x y) : @Category.AreInverse (vcat x y) _ _ (Rxy (OneBicat.ru f)) (Ryx (OneBicat.ru f));
      (* hcomp2_functor : forall (x y z : A), *)
      (*   Functor.is_functor (F:=uncurry (OneBicat.compose x y z)) _ *)
      (* assoc_nat : (??) ; *)
      (* lu_nat : (??) ; *)
      (* ru_nat : (??) ; *)
      (* pentagon : (??) ; *)
      (* triangle : (??) *)
    }.

  Structure t@{u0 u1 u2} := {
      sort : Type@{u0};
      Hom : sort -> sort -> Type@{u1};
      TwoHom : forall (x y : sort), Hom x y -> Hom x y -> Type@{u2};
    }.

(** N. b. - to convince yourself that the definition of a bicategory is
    correct, it would make sense to take a standard presentation and
    show that all the axioms and components of that standard presentation
    are provable/definable using the presentation given here. *)
End Bicategory.
