From Simplex Require Import Basics Datatypes Relations Eq List Graph PreOrder.Core PreOrder.Instances OneBicat Category Functor Category.ProdCat FunctorCat Category.NatTrans.

Local Set Implicit Arguments.
Open Scope morphism_scope.
Module Bicategory.
  Import OneBicat.Notations.

  Class pre_bicat (A : Type) (Hom : A -> A -> Category.t)
    (Equiv : forall (C D : Category.t) (F G : Functor.t C D), Type)
    (IsPreOrder : forall (C D : Category.t), PreOrder.class_of (Equiv C D))
    := {
      compose (a b c : A) : Functor.t ((Hom a b) × (Hom b c)) (Hom a c);
      unit (a : A) : Hom a a;
      (* lu (a b : A), Equiv  *)
      (* ru,
         assoc
         pentagon
         triangle
       *)
    }.

  Record mixin_of@{u0 u1 u2} (A : OneBicat.t@{Type;u0 u1 u2}) := {
      (** 2-cells form a category under vertical composition. *)
      is_vcat (x y : A) : Category.Mixin.mixin_of (OneBicat.vpreorder x y);
      (** The vertical category of 2-cells associated to two 0-cells. *)
      vcat (x y : A) :=
        (@Category.Build _ _ 
           (Category.Build_class_minimal
              (is_vcat x y)));
      (** The left-to-right associator and the right-to-left associator are inverse. *)
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
      (** The left-to-right left unitor and the right-to-left
      component of the left unitor are inverse. *)
      lu_inv (x y : A) (f : vcat x y)
      : @Category.AreInverse
          (vcat x y) _ _ (Rxy (OneBicat.lu f)) (Ryx (OneBicat.lu f));
      (** The left-to-right right unitor and the right-to-left
      component of the right unitor are inverse. *)      
      ru_inv (x y : A) (f : vcat x y)
      : @Category.AreInverse
          (vcat x y) _ _ (Rxy (OneBicat.ru f)) (Ryx (OneBicat.ru f));
      (* The composition Hom(x,y) x Hom(y,z) -> Hom(x,z) is a functor. *)
      hcomp2_functor : forall (x y z : A),
        Functor.is_functor (F:=uncurry (OneBicat.compose x y z)) _;
      (** The associator is a natural transformation between functors
          Hom(w,x) x Hom(x,y) x Hom(y,z) -> Hom(w,z) *)
      assoc_nat (w x y z : A) :
      NatTrans.mixin_of
        (OneBicat.left_assoc w x y z)
        (OneBicat.right_assoc w x y z)
        (fun (fgh: TwoGraph.path_graph A w [x; y; z]) 
         => Rxy (OneBicat.assoc (fst fgh) (fst (snd fgh)) (fst (snd (snd fgh)))));
      (** The left unitor is a natural transformation between functors
          Hom(x,y) -> Hom(x,y). *)
      lu_nat (x y : A) :
      NatTrans.mixin_of
        (OneBicat.lid x y)
        (OneBicat.id_graph_hom x y)
        (fun f => Rxy (OneBicat.lu (fst f)));
      (** The right unitor is a natural transformation between functors
          Hom(x,y) -> Hom(x,y) *)
      ru_nat (x y : A) :
      NatTrans.mixin_of
        (OneBicat.rid x y)
        (OneBicat.id_graph_hom x y)
        (fun f => Rxy (OneBicat.ru (fst f)));
      (** Mac Lane's pentagon axiom *)
      pentagon (v w x y z : A) (f : vcat v w) (g : vcat w x)
        (h: vcat x y) (k : vcat y z)
        (* ((fg)h)k -> (f(gh))k -> f((gh)k) -> f(g(hk)) *)
      : (OneBicat.hcomp2 (Rxy (OneBicat.assoc f g h)) (1 k))
          · (Rxy (OneBicat.assoc f (g·h) k))
          · (OneBicat.hcomp2 (1 f) (Rxy (OneBicat.assoc g h k)))
        = (* ((fg)h)k -> (fg)(hk) -> f(g(hk))*)
          (Rxy (OneBicat.assoc (f · g) h k))
            · (Rxy (OneBicat.assoc f g (h · k)));
      (** The triangle axiom *)
      triangle (x y z : A) (f : vcat x y) (g : vcat y z):
      OneBicat.hcomp2 (Rxy (OneBicat.ru f)) (1 g)
      = Rxy (OneBicat.assoc f (1 y) g) ·
            OneBicat.hcomp2 (1 f) (Rxy (OneBicat.lu g))
    }.

  Class class_of@{u0 u1 u2} (A : Type@{u0})
    (R : A -> A -> Type@{u1})
    (RR : forall (x y : A), R x y -> R x y -> Type@{u2})
    := Class {
      isOneBicat : OneBicat.class_of RR;
      mixin : mixin_of (OneBicat.Pack isOneBicat)
    }.

  Structure t@{u0 u1 u2} := {
      sort : Type@{u0};
      Hom : sort -> sort -> Type@{u1};
      TwoHom : forall (x y : sort), Hom x y -> Hom x y -> Type@{u2};
      class : class_of Hom TwoHom
    }.

(** N. b. - to convince yourself that the definition of a bicategory is
    correct, it would make sense to take a standard presentation and
    show that all the axioms and components of that standard presentation
    are provable/definable using the presentation given here. *)
End Bicategory.
