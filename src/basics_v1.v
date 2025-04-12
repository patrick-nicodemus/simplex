From Simplex Require Import Basics Eq.
Require Export Ltac2.Ltac2.
Set Universe Polymorphism.
Global Set Typeclasses Strict Resolution.

Inductive eq {A : Type} (a : A) : A -> Type :=
  eq_refl : eq a a.

Local Set Warnings "-notation-overridden".
Notation "x = y" := (eq x y)
                      (at level 70, y at next level, no associativity) : type_scope.
Notation "x = y" := (eq x y)
    (at level 70, y at next level, no associativity).
Register eq as core.identity.type.
Register eq_refl as core.identity.refl.
Register eq_rect as core.identity.ind.

Require Import Classes.CRelationClasses.

(** The Corelib defines a notion of Relation, so this is perhaps
    unnecessary. But the one in the Corelib isn't a Class,
    so if we want to write "f : a ~> b" it's necessary to
    declare a class. *)

Class Rel (A : Type) := Hom : A -> A -> Type.
#[global] Typeclasses Transparent Rel.

Declare Scope morphism_scope.

Infix "·" := transitivity (at level 39) : morphism_scope.


Open Scope morphism_scope.

Infix "~>" := Hom (at level 40) : type_scope.

Arguments Hom {A Rel} a b.

(* an example of a relation *)
Instance eq_isgraph (A : Type) : Rel A := { Hom a b := a = b }.

Class Is2Graph (A : Type) {IsGraph : Rel A} :=
  hom_hom :: forall (x y : A), Rel (Hom x y).

(** Reflexivity and transitivity are also defined in the Corelib. *)

(** A kind of parametricity translation of transitivity. *)
Class Trans2 (A : Type) {IsGraph : Rel A} {Is2Graph : Is2Graph A}
  (Trans : Transitive IsGraph)
  := trans_pmet
    : forall [x y z : A] [f f' : x ~> y] (p : f ~> f') [g g' : y ~> z] (q : g ~> g'),
      f · g ~> f' · g'.

(* Print Implicit reflexivity. *)
Notation "1" := reflexivity : morphism_scope.

(** A kind of parametricity translation of reflexivity. *)
Class Refl2 (A : Type) {IsGraph : Rel A} {Is2Graph : Is2Graph A}
  (Refl : Reflexive IsGraph)
  := refl_pmet : forall (x : A), (1 x ~> 1 x).

Class PreOrder2 {A : Type} {IsGraph : Rel A} (Is2Graph : Is2Graph A)
  `{!PreOrder IsGraph} := {
    preorder2_trans2 : Trans2 A (PreOrder_Transitive);
    preorder2_refl2 : Refl2 A (PreOrder_Reflexive);
  }.

Instance eq_reflexive (A : Type) : Reflexive (eq (A:=A))
  := eq_refl. 

Instance eq_transitive (A : Type) : Transitive (eq (A:=A))
  := fun x y z p =>
       (match p in eq _ y' return eq y' z -> eq x z
       with | eq_refl _ => fun z => z end).

(** What the HoTT library calls a [01Cat] is defined in the Corelib as
   a [Preorder]. *)

(** What the HoTT library calls a [0Gpd] is defined in the Corelib as an
   [Equivalence]. *)

Class Associative (A : Type) {IsGraph : Rel A}
  {Is2Graph : Is2Graph A}
  {is_transitive : Transitive IsGraph} := {
    assoc_ltr : forall {a b c d: A} (f : a ~> b) (g : b ~> c) (h : c ~> d),
      (f · g) · h ~> f · (g · h);
    assoc_rtl : forall {a b c d: A} (f : a ~> b) (g : b ~> c) (h : c ~> d),
      f · (g · h) ~> (f · g) · h
  }.


Class LeftUnitor (A : Type) {IsGraph : Rel A}
  {Is2Graph : Is2Graph A}
  {PreOrder : PreOrder IsGraph} := {
    lu : forall {a b: A} (f : a ~> b),
      (1 a · f ~> f);
    lu_opp : forall {a b: A} (f : a ~> b),
      (f ~> 1 a · f)
  }.

Class RightUnitor (A : Type) {IsGraph : Rel A}
  {Is2Graph : Is2Graph A}
  {PreOrder : PreOrder IsGraph} := {
    ru : forall {a b: A} (f : a ~> b),
      (f · 1 b ~> f);
    ru_opp : forall {a b: A} (f : a ~> b),
      (f ~> f · 1 b)
  }.

Class Is1Bicat (A : Type) {IsGraph : Rel A}
  {is_preorder : PreOrder IsGraph}
  {Is2Graph : Is2Graph A } := {
    hom_ispreorder :: forall (x y : A), PreOrder (Is2Graph x y);
    is_2trans :: Trans2 A PreOrder_Transitive;
    bicat_assoc :: Associative A;
    bicat_lu :: LeftUnitor A;
    bicat_ru :: RightUnitor A
  }.
