From Simplex Require Import Basics.
From HB Require Import structures.

Local Set Implicit Arguments.

HB.mixin Record Rel A := {
    Hom : A -> A -> Type
  }.

HB.structure Definition Graph := {A & Rel A}.

Declare Scope morphism_scope.
Infix "~>" := Hom (right associativity, at level 41) : morphism_scope.
Open Scope morphism_scope.

HB.mixin Record Reflexive (A : Type) of Graph A := {
    refl : forall x : A, x ~> x
  }.

HB.mixin Record Symmetric (A : Type) of Graph A := {
    symmetry : forall x y : A, x ~> y -> y ~> x
  }.

HB.mixin Record Transitive (A : Type) of Graph A := {
    trans : forall x y z : A, x ~> y -> y ~> z -> x ~> z
  }.

HB.structure Definition PreOrder := { A of Graph A & Reflexive A & Transitive A }.

HB.mixin Record IsTwoGraph (A : Type) of Graph A := {
    hom_hom : forall x y : A, Rel (x ~> y)
  }.

HB.structure Definition TwoGraph := { A of Graph A & IsTwoGraph A }.

Module Graph.
  Definition class_of@{s|u0 u1|} (A : Type@{u0}) := A -> A -> Type@{s|u1}.
  Record t@{s|u0 u1|} := Pack {
      sort : Type@{u0};
      Hom : class_of@{s|u0 u1} sort
    }.

  Definition op@{s|+|} (A : t@{s|_ _}) : t@{s|_ _}
    := {|
      sort := sort A;
      Hom a b := Hom A b a
    |}.
  
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
End Graph.
Export Graph.ForExport.

Class Reflexive@{s | u0 u1 |} [A : Type@{u0}] (R : A -> A -> Type@{s | u1})
  := reflexive : forall (x : A), R x x.

Notation "1" := (@reflexive _ _ _) : morphism_scope.

Class Transitive@{s | u0 u1|} {A : Type@{u0}} (R : A -> A -> Type@{s | u1})
  := transitive : forall (x y z : A), R x y -> R y z -> R x z.

Infix "·" := (@transitive _ _ _ _ _ _) (at level 39) : morphism_scope.

Class Symmetric@{s | u0 u1|} {A : Type@{u0}} (R : A -> A -> Type@{s | u1})
  := symmetry : forall (x y: A), R x y -> R y x.

Module PreOrder.

  Class mixin_of@{s|u0 u1|} (A : Graph.t@{s|u0 u1}) := Mixin {
      refl : Reflexive (Hom (t:=A));
      trans : Transitive (Hom (t:=A))
  }.

  Module mixin_of_conventions.
    Arguments Mixin A &.
    Arguments refl [A].
    Arguments trans [A mixin_of x y z].
    Existing Instance refl.
    Existing Instance trans.
  End mixin_of_conventions.
  Import mixin_of_conventions.

  Class class_of@{s|u0 u1|} (A : Type@{u0})
    := Class {
           rel : Graph.class_of A;
           mixin : mixin_of@{s|u0 u1} (Graph.Pack rel)
         }.
  Module class_of_conventions.
    Arguments Class [A rel] &.
    Arguments rel : clear implicits.
    Arguments mixin : clear implicits.
  End class_of_conventions.
  Import class_of_conventions.

  Record t@{s|u0 u1|} := Pack {
      sort : Type@{u0};
      class : class_of@{s|u0 u1} sort
  }.

  Module t_conventions.
    Arguments Pack [sort].
    Coercion sort : t >-> Sortclass.
  End t_conventions.
  Import t_conventions.
    
  Definition to_graph@{s|u0 u1|} (A : t@{s|u0 u1}) : Graph.t@{s|u0 u1}
    := Graph.Pack (rel _ (class A)).
  Module to_graph_conventions.
    Canonical to_graph.    
    Coercion to_graph : t >-> Graph.t.
  End to_graph_conventions.
  Import to_graph_conventions.
  
  Definition is_refl@{s|u0 u1|} (A : t) : Reflexive@{s|u0 u1} (rel _ (class A))
    := @refl _ ((mixin _ (class A))).
  Module is_refl_conventions.
    Existing Instance is_refl.
  End is_refl_conventions.

  Definition is_trans@{s|u0 u1|} (A : t) : Transitive@{s|u0 u1} (rel _ (class A))
    := @trans _ ((mixin _ (class A))).
  Module is_trans_conventions.
    Existing Instance is_trans.
  End is_trans_conventions.
  Import is_trans_conventions.
  
  Definition op@{s|+|} (A : t@{s|_ _ }) : t@{s| _ _ }
    := Pack (Class (rel:=(fun (a b : sort A) => Hom b a))
         {| refl x := is_refl _ x; trans x y z f g := is_trans _ z y x g f |}).
  
  Module ForExport.
    Export to_graph_conventions.
    Export is_refl_conventions.
    Export is_trans_conventions.
    Export mixin_of_conventions.
    Export t_conventions.
  End ForExport.
End PreOrder.
Export PreOrder.ForExport.

Module TwoGraph.
  Definition mixin_of@{s|u0 u1 u2|} (A : Graph.t@{Type|u0 u1})
    := forall (x y : A), Graph.class_of@{s|u1 u2} (Hom x y).

  Record class@{s|u0 u1 u2|} (A : Type@{u0}) := Class {
    base : Graph.class_of@{Type|u0 u1} A;
    is2graph : mixin_of@{s|u0 u1 u2} (Graph.Pack base)
  }.  

  Structure t@{s|u0 u1 u2|} := Pack {
      sort : Type@{u0};
      class_of : class@{s|u0 u1 u2} sort;
  }.
  Module t_conventions.
    Coercion sort : t >-> Sortclass.
    Arguments Pack [sort] &.
  End t_conventions.
  Import t_conventions.

  Definition to_graph@{s|u0 u1 u2|} (A: t@{s|u0 u1 u2})
    : Graph.t@{Type|u0 u1}
    := Graph.Pack (base (class_of A)).

  Definition two_hom@{s|u0 u1 u2|} {A : t@{s|u0 u1 u2}} (x y : A) :=
    Graph.Pack (is2graph@{s|u0 u1 u2} (class_of A) x y).

  Canonical two_hom.

  Definition co@{s|+|} (A : t@{s|_ _ _}) : t@{s|_ _ _}
    := {|
      sort := sort A;
      class_of :=
        {|
          base := base (class_of A);
          is2graph x y f g := Hom g f
       |}
    |}.
  
  Module ForExport.
    Export t_conventions.
    Coercion to_graph : t >-> Graph.t.
    Canonical to_graph.
    #[warnings="-w -redundant-canonical-projection"]
    Canonical two_hom.
    Infix "=>" := (Hom (t:=@two_hom _ _ _)) (at level 41, right associativity).
  End ForExport.
End TwoGraph.
Export TwoGraph.ForExport.

Record Couple@{s|u0 u1|} (A: Graph.t@{s|u0 u1}) (x y : A) := {
    Rxy : x ~> y;
    Ryx : y ~> x
  }.

Local Open Scope morphism_scope.

Definition Associative@{s|u0 u1 u2|} (A : TwoGraph.t@{s|u0 u1 u2})
  (t : Transitive@{Type|u0 u1} (Hom (t:=A)))
  := forall (w x y z  : A) (f : w ~> x) (g : x ~> y) (h : y ~> z),
    Couple@{s|u1 u2} _ ((f · g) · h) (f · (g · h)).

Definition LeftUnitor@{s|u0 u1 u2|}
  (A : TwoGraph.t@{s|u0 u1 u2})
  (t : PreOrder.mixin_of@{Type|u0 u1} A)
  := forall (x y : A) (f : x ~> y), Couple _ ((1 x) · f) f.

Definition RightUnitor@{s|u0 u1 u2|}
  (A : TwoGraph.t@{s|u0 u1 u2})
  (t : PreOrder.mixin_of@{Type|u0 u1} A)
  := forall (x y : A) (f : x ~> y), Couple _ (f · (1 y)) f.

Module OneBicat.
  Record mixin_of@{s|u0 u1 u2|} (A : TwoGraph.t@{s|u0 u1 u2}) :=
    Mixin {
        is_preorder : PreOrder.mixin_of@{Type|u0 u1} A;
        assoc : Associative@{s|u0 u1 u2} A
                  (PreOrder.trans (mixin_of:=is_preorder));
        lu : LeftUnitor@{s|u0 u1 u2} is_preorder;
        ru : LeftUnitor@{s|u0 u1 u2} is_preorder;
        hcomp2 : forall (x y z : A) (f f' : x ~> y) (g g' : y ~> z),
          f => f' -> g => g' -> f · g => f' · g'
      }.

  Record class_of@{s|u0 u1 u2|} (A : Type@{u0}) := {
      is2graph : TwoGraph.class @{s|u0 u1 u2} A;
      mixin : mixin_of (TwoGraph.Pack is2graph)
    }.

  Module class_of_conventions.
    Arguments is2graph [A].
    Arguments mixin [A].
  End class_of_conventions.
  Import class_of_conventions.

  Record t@{s|u0 u1 u2|} := Pack {
      sort : Type@{u0};
      class : class_of@{s|u0 u1 u2} sort
    }.
  Module t_conventions.
    Coercion sort : t >-> Sortclass.
    Arguments Pack [sort].
  End t_conventions.
  Import t_conventions.

  Definition to2graph@{s|u0 u1 u2|} (A : t@{s|u0 u1 u2}) : TwoGraph.t@{s|u0 u1 u2}
    := TwoGraph.Pack (is2graph (class A)).
  Module to2graph_coercion.
    Coercion to2graph : t >-> TwoGraph.t.
    Canonical to2graph.
  End to2graph_coercion.
  Import to2graph_coercion.

  Definition is_preorder_mixin@{s|u0 u1 u2|} (A : t@{s|u0 u1 u2})
    : PreOrder.mixin_of A
    := is_preorder (mixin (class A)).

  Module Exports.
    Export class_of_conventions.
    Export t_conventions.
    Export to2graph_coercion.
  End Exports.
End OneBicat.
Export OneBicat.Exports.

Module GraphHom.
  Class class_of@{s1 s2|+|} {A : Graph.t@{s1|_ _}} {B : Graph.t@{s2|_ _}}
    (F : A -> B)
    := fmap :> forall {x y  : A}, x ~> y -> F x ~> F y.

  Structure t@{s1 s2|+|} (A : Graph.t@{s1|_ _}) (B : Graph.t@{s2|_ _})
    := Pack {
           map : A -> B;
           class : class_of map
         }.
  Module Exports.
    Coercion map : t >-> Funclass.
    Notation fmap := fmap.
    Arguments fmap [A B] F {class_of} [x y].
    Arguments Pack [A B map].
    Existing Instance class.
  End Exports.
End GraphHom.
Export GraphHom.Exports.

Module TwoGraphHom.
  Class mixin_of@{s1 s2|+|} {A : TwoGraph.t@{s1|_ _ _}} {B : TwoGraph.t@{s2|_ _ _}}
    (F : GraphHom.t A B)
    := ffmap : forall (x y : A), GraphHom.class_of (fmap F (x:=x) (y:=y)).

  Class class_of@{s1 s2|+|} {A : TwoGraph.t@{s1|_ _ _}} {B : TwoGraph.t@{s2|_ _ _}}
    (F : A -> B)
    := Class {
           is_graph_hom : GraphHom.class_of F;
           is_2graph_hom : mixin_of (GraphHom.Pack is_graph_hom)
         }.
  Module class_of_conventions.
    Arguments is_graph_hom [A B F].
  End class_of_conventions.
  Import class_of_conventions.
  Structure t@{s1 s2|+|} (A : TwoGraph.t@{s1|_ _ _}) (B : TwoGraph.t@{s2|_ _ _})
    := Pack {
      map : A -> B;
      class : class_of map
    }.
  Module t_conventions.
    Arguments class [A B].
    Arguments Pack [A B] & [map].
  End t_conventions.
  Import t_conventions.
  
  Definition to_graph_hom @{s1 s2|+|} [A B] (F : t@{s1 s2|_ _ _ _ _ _} A B)
    : GraphHom.t@{Type Type|_ _ _ _} A B
    := GraphHom.Pack (is_graph_hom (class F)).
  Module Exports.
    Export t_conventions.
    Export class_of_conventions.
  End Exports.
End TwoGraphHom.
Export TwoGraphHom.Exports.

Module Lax1Functor.
  Class mixin_of@{s1 s2|+|}
    (A : PreOrder.t@{s1|_ _})
    (B : TwoGraph.t@{s2|_ _ _}) {Bp: PreOrder.mixin_of B}
    (F : GraphHom.t A B)
    := Mixin {
      luc : forall (x : A), 1 (F x) => fmap F (1 x);
      lfc : forall (x y z: A) (f : x ~> y) (g : y ~> z),
        (fmap F f) · (fmap F g) => fmap F (f · g)
    }.
  Class class_of@{s1 s2|+|}
    (A : TwoGraph.t@{s1|_ _ _ }) (Ap : PreOrder.mixin_of A)
    (B : TwoGraph.t@{s2|_ _ _}) (Bp : PreOrder.mixin_of B) (F: A -> B)
    := Class {
      is2graph_hom: TwoGraphHom.class_of F;
      mixin : mixin_of (A:=PreOrder.Pack (PreOrder.Class Ap)) (Bp:=Bp) 
               (TwoGraphHom.to_graph_hom (TwoGraphHom.Pack is2graph_hom))
         }.
  Local Existing Instance OneBicat.is_preorder_mixin.
  Structure t@{s1 s2|+|} (A : OneBicat.t@{s1|_ _ _}) (B : OneBicat.t@{s1|_ _ _})
    := Pack {
           map : A -> B;
           class: class_of _ _ map
         }.
End Lax1Functor.
