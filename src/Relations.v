From Simplex Require Import Basics Nat.

Module Rel.
  Definition class_of@{s|u0 u1|} (A : Type@{u0}) := A -> A -> Type@{s|u1}.
  Record t@{s|u0 u1|} := Pack {
      sort : Type@{u0};
      Hom : class_of@{s|u0 u1} sort
    }.

  Module ForExport.
    Arguments Hom [_].
    Arguments Pack [sort].
    Coercion sort : t >-> Sortclass.
    Infix "~>" := Hom (at level 41) : type_scope.
    Declare Scope morphism_scope.
    Delimit Scope morphism_scope with hom.
    Bind Scope morphism_scope with Hom.
    Notation Hom := Hom.
  End ForExport.
End Rel.
Export Rel.ForExport.

Definition Reflexive@{s | u0 u1 |} {A : Type@{u0}} (R : A -> A -> Type@{s | u1})
  := forall (x : A), R x x.

Definition Transitive@{s | u0 u1|} {A : Type@{u0}} (R : A -> A -> Type@{s | u1})
  := forall (x y z : A), R x y -> R y z -> R x z.

Definition Symmetric@{s | u0 u1|} {A : Type@{u0}} (R : A -> A -> Type@{s | u1})
  := forall (x y: A), R x y -> R y x.

Module PreOrder.
  Record mixin_of@{s|u0 u1|} (A : Rel.t@{s|u0 u1}) := Mixin {
      refl : Reflexive (Hom (t:=A));
      trans : Transitive (Hom (t:=A))
    }.
  Record class_of@{s|u0 u1|} (A : Type@{u0}) := Class {
      rel : Rel.class_of A;
      mixin : mixin_of@{s|u0 u1} (Rel.Pack rel)
    }.
  Record t@{s|u0 u1|} := Pack {
      sort : Type@{u0};
      class : class_of@{s|u0 u1} sort
    }.
  Definition to_rel@{s|u0 u1|} (A : t@{s|u0 u1}) : Rel.t@{s|u0 u1}
    := Rel.Pack (rel _ (class A)).

  Definition is_refl@{s|u0 u1|} (A : t) : Reflexive@{s|u0 u1} (rel _ (class A))
    := refl _ ((mixin _ (class A))).

  Definition is_trans@{s|u0 u1|} (A : t) : Transitive@{s|u0 u1} (rel _ (class A))
    := trans _ ((mixin _ (class A))).

  Module ForExport.
    Coercion sort : t >-> Sortclass.
    Canonical to_rel.
    Arguments refl [A].
    Arguments trans [A m x y z].
    Arguments Pack [sort].
    Infix "·" := (@is_trans _ _ _ _) (at level 39) : morphism_scope.
    Notation "1" := (is_refl _) : morphism_scope.    
  End ForExport.
End PreOrder.
Export PreOrder.ForExport.

Module Example1.
  Canonical nat_rel := Rel.Pack le.
  Check (0 ~> 1 : SProp).
  
  Canonical nat_preorder : PreOrder.t
    := PreOrder.Pack
         (PreOrder.Class _ _
            (PreOrder.Mixin nat_rel Nat.le_refl (@Nat.le_trans))).

  (* This depends on Canonical to_rel above. *)
  Goal forall (A : PreOrder.t) (x y : A), x ~> y.
  Abort.

  Ltac2 reflexivity () :=
    exact (PreOrder.is_refl _ _).

  Set Printing All.
  Goal forall x : nat, x ~> x.
  Proof.
    intro x.
    reflexivity ().
  Defined.
  Definition ff : forall x y : nat, x ~> y -> x ~> y := fun x y f => f.
  Definition fmi : forall x y z : nat, x ~> y -> y ~> z -> x ~> z :=
    fun x y z f g => ff x z (f · g).
  Goal forall x y z: nat, x ~> y -> y ~> z -> x ~> z.
  Proof.
    intros x y z f g.
    Fail Check ((fun (s : x ~> z) => s) (f · g)).
    exact (f · g)%hom.
  Defined.

  Goal forall x : nat, le x x.
    exact (fun x => (1 x)%hom).
  Defined.
End Example1.

Definition Is2Graph@{s|u0 u1 u2|} (A : Rel.t@{Type|u0 u1})
  := forall (x y : A), Rel.class_of@{s|u1 u2} (Hom x y).

Module TwoGraph.
  Definition mixin_of@{s|u0 u1 u2|} (A : Rel.t@{Type|u0 u1})
    := forall (x y : A), Rel.class_of@{s|u1 u2} (Hom x y).

  Record class@{s|u0 u1 u2|} (A : Type@{u0}) := Class {
    base : Rel.class_of@{Type|u0 u1} A;
    is2graph : mixin_of@{s|u0 u1 u2} (Rel.Pack base)
  }.  

  Structure t@{s|u0 u1 u2|} := Pack {
      sort :> Type@{u0};
      class_of : class@{s|u0 u1 u2} sort;
    }.

  Definition to_graph@{s|u0 u1 u2|} (A: t@{s|u0 u1 u2})
    : Rel.t@{Type|u0 u1}
    := Rel.Pack (base _ (class_of A)).

  Definition two_hom@{s|u0 u1 u2|} (A : t@{s|u0 u1 u2}) (x y : A) :=
    Rel.Pack (is2graph@{s|u0 u1 u2} _ (class_of A) x y).

  Module ForExport.
    Coercion to_graph : t >-> Rel.t.
    Canonical to_graph.
    Canonical two_hom.
    Infix "=>" := (Hom (t:=two_hom _ _ _)) (at level 41, right associativity).
  End ForExport.
End TwoGraph.
Export TwoGraph.ForExport.

Record Couple@{s|u0 u1|} (A: Rel.t@{s|u0 u1}) (x y : A) := {
    Rxy : x ~> y;
    Ryx : y ~> x
  }.

Definition Associative@{s|u0 u1 u2|} (A : TwoGraph.t@{s|u0 u1 u2})
  (t : Transitive@{Type|u0 u1} (Hom (t:=A)))
  := forall (w x y z  : A) (f : w ~> x) (g : x ~> y) (h : y ~> z),
    Couple@{s|u1 u2} (TwoGraph.two_hom A w z)
      (t _ _ _ (t _ _ _ f g) h) (t _ _ _ f (t _ _ _ g h)).

Definition LeftUnitor@{s|u0 u1 u2|}
  (A : TwoGraph.t@{s|u0 u1 u2})
  (t : PreOrder.mixin_of@{Type|u0 u1} A)
  := forall (x y : A) (f : x ~> y), Couple (TwoGraph.two_hom A x y) (PreOrder.trans (m:=t) (PreOrder.refl t x) f) f.

Definition RightUnitor@{s|u0 u1 u2|}
  (A : TwoGraph.t@{s|u0 u1 u2})
  (t : PreOrder.mixin_of@{Type|u0 u1} A)
  := forall (x y : A) (f : x ~> y), Couple (TwoGraph.two_hom A x y) (PreOrder.trans (m:=t) f (PreOrder.refl t y)) f.

Open Scope morphism_scope.
Module ZeroBicat.
  Record mixin@{s|u0 u1 u2|} (A : TwoGraph.t@{s|u0 u1 u2}) :=
    Mixin {
        is_preorder : PreOrder.mixin_of@{Type|u0 u1} A;
        assoc : Associative@{s|u0 u1 u2} A (PreOrder.trans (m:=is_preorder));
        lu : LeftUnitor@{s|u0 u1 u2} A is_preorder;
        ru : LeftUnitor@{s|u0 u1 u2} A is_preorder;
        hcomp2 : forall (x y z : A) (f f' : x ~> y) (g g' : y ~> z),
          f => f' -> g => g' ->
                       (PreOrder.trans (m:=is_preorder) f g) =>
               (PreOrder.trans (m:=is_preorder) f' g')
    }.

  Record class@{s|u0 u1 u2|} (A : Type@{u0}) := {
      is2graph : TwoGraph.class @{s|u0 u1 u2} A;
      mixin_of : TwoGraph.Pack _ is2graph
    }.

  Record t@{s|u0 u1 u2|} := {
      sort : Type@{u0};
      class_of : class@{s|u0 u1 u2} sort
    }.
End ZeroBicat.
