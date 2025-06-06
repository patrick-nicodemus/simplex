From Simplex Require Import Basics Datatypes Graph PreOrder.Core PreOrder.Instances OneBicat Category Functor FunctorCat Category.NatTrans.

Module Bicategory.
  Import OneBicat.Notations.
      
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
      lu_inv (x y : A) (f : vcat x y)
      : @Category.AreInverse
          (vcat x y) _ _ (Rxy (OneBicat.lu f)) (Ryx (OneBicat.lu f));
      ru_inv (x y : A) (f : vcat x y)
      : @Category.AreInverse
          (vcat x y) _ _ (Rxy (OneBicat.ru f)) (Ryx (OneBicat.ru f));
      hcomp2_functor : forall (x y z : A),
        Functor.is_functor (F:=uncurry (OneBicat.compose x y z)) _;
      assoc_nat (w x y z : A) :
      NatTrans.mixin_of
        (OneBicat.left_assoc A w x y z)
        (OneBicat.right_assoc A w x y z)
        (fun (fgh: (w ~> x) * (x ~> y) * (y ~> z)%type) 
         => Rxy (OneBicat.assoc (fst (fst fgh)) (snd (fst fgh)) (snd fgh)));
      (* lu_nat (x y : A) : *)
      (* NatTrans.mixin_of *)
      (*   (OneBicat.lid A x y) *)
      (*   _ *)
      (*   (fun (f : x ~> y) => Rxy (OneBicat.lu f)) *)
        
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
