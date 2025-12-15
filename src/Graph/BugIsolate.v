(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-native-compiler" "ondemand" "-R" "_build/default/src" "Simplex" "-top" "src.Graph.GraphCat") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 84 lines to 37 lines, then from 50 lines to 161 lines, then from 166 lines to 82 lines, then from 95 lines to 149 lines, then from 154 lines to 94 lines, then from 107 lines to 301 lines, then from 305 lines to 133 lines, then from 146 lines to 649 lines, then from 653 lines to 191 lines, then from 204 lines to 373 lines, then from 378 lines to 203 lines, then from 216 lines to 320 lines, then from 325 lines to 224 lines, then from 237 lines to 421 lines, then from 425 lines to 288 lines, then from 301 lines to 483 lines, then from 488 lines to 301 lines, then from 314 lines to 354 lines, then from 359 lines to 300 lines, then from 306 lines to 301 lines, then from 315 lines to 274 lines, then from 287 lines to 324 lines, then from 330 lines to 283 lines, then from 289 lines to 284 lines *)
(* coqc version 9.1.0 compiled with OCaml 5.3.0
   coqtop version 9.1.0
   Modules that could not be inlined: Simplex.Basics.Datatypes_core
   Expected coqc runtime on this file: 0.322 sec *)
Require Simplex.Basics.Datatypes_core.
Require Import Simplex.Basics.Eq.
Require elpi.elpi.

Import Simplex.Basics.Basics.
Definition Relation@{s ; u0 u1} (A : Type@{u0}) := A -> A -> Type@{s;u1}.

Class Reflexive@{s;u0 u1}
  [A : Type@{u0}] (R : A -> A -> Type@{s;u1})
  : Type@{s;max(u0+1,u1+1)}
  := reflexive : forall (x : A), R x x.

Class Transitive@{s;u0 u1}
  {A : Type@{u0}} (R : A -> A -> Type@{s;u1})
  : Type@{s;max(u0+1,u1+1)}
  := transitive : forall (x y z : A), R x y -> R y z -> R x z.

Export Simplex.Basics.Datatypes_core.

Ltac2 refine0 (x : preterm) :=
  Control.enter
    (fun () =>
       Control.refine (fun () =>
       let g := Control.goal () in
       Constr.Pretype.pretype
         Constr.Pretype.Flags.open_constr_flags_with_tc
         (Constr.Pretype.expected_oftype g)
         x
    )).

Ltac2 Notation "refine" x(preterm) := refine0 x.
Ltac2 Notation "firstorder" := ltac1:(firstorder).
Module Export Graph.
Local Set Implicit Arguments.
  Notation class_of := Relation.
  Record t@{s;u0 u1} : Type@{max(u0+1,u1+1)}:=
    Pack {
        sort : Type@{u0};
        Hom : class_of@{s;u0 u1} sort
      }.
    Arguments Hom [_].
    #[reversible] Coercion sort : t >-> Sortclass.
    Infix "~>" := Hom (at level 41).

Notation "1" := (@reflexive _ _ _) : morphism_scope.

Infix "·" := (@transitive _ _ _ _ _ _) (at level 39).

Record Couple@{s;u0 u1} (A: Graph.t@{s;u0 u1}) (x y : A)
  : Type@{s;max(u0+1,u1+1)}
  := {
    Rxy : x ~> y;
    Ryx : y ~> x
  }.

Module Export GraphHom.
  Class class_of@{s1 s2;uA0 uA1 uB0 uB1}
    {A : Graph.t@{s1;uA0 uA1}} {B : Graph.t@{s2;uB0 uB1}}
    (F : A -> B)
    := fmap' : forall {x y  : A}, x ~> y -> F x ~> F y.

  Structure t@{s1 s2;uA0 uA1 uB0 uB1}
    (A : Graph.t@{s1;uA0 uA1}) (B : Graph.t@{s2;uB0 uB1})
    := Pack {
           map : A -> B;
           class : class_of map
         }.

  Definition id@{s;+} (A : Graph.t@{s;_ _}) : t A A.
  Proof.
    unshelve refine '(Pack _).
    -
 exact (fun x => x).
    -
 exact (fun x y f => f).
  Defined.
  Instance compose@{s;+} : Transitive GraphHom.t.
    intros [Ao Ah] [Bo Bh] [Co Ch] [Fm Fh] [Gm Gh].
    simpl in *.
    unshelve refine '(Pack _); simpl.
    1:{
 auto.
}
    simpl.
unfold class_of.
simpl.
    unfold Graph.class_of in *.
     unfold class_of in *.
    simpl in *.
    auto.
  Defined.
Instance ReflexiveGraphHom : Reflexive GraphHom.t.
exact (id).
Defined.
Definition Prod@{s;uA0 uA1 uB0 uB1 +|+}
  (A : Graph.t@{s;uA0 uA1}) (B : Graph.t@{s;uB0 uB1})
  : Graph.t@{s;_ _}.
exact (@Graph.Pack (sort A * sort B)
       (fun ab ab' => ((Hom (fst ab) (fst ab')) /\ (Hom (snd ab) (snd ab')))%type)).
Defined.
Module Export PreOrder.
  Class class_of@{s;u0 u1|} (A : Type@{u0}) (R : A -> A -> Type@{s;u1})
    : Type@{s;max(u0+1,u1+1)}
    := Class {
      refl : Reflexive@{s;u0 u1} R;
      trans : Transitive@{s;u0 u1} R
  }.
    Existing Instance refl.
    Existing Instance trans.

  Record t@{s;u0 u1|} :=
    Pack {
        sort : Type@{u0};
        Hom : sort -> sort -> Type@{s;u1};
        class : class_of@{s;u0 u1} Hom
      }.
    #[reversible] Coercion sort : t >-> Sortclass.
    Arguments Hom [t].
    Existing Instance class.
    Infix "<=" := Hom (at level 70).
    Notation IsPreOrder := class_of.
Module Export TwoGraph.
  Definition class_of@{s;u0 u1 u2|} (A : Type@{u0}) (R : A -> A -> Type@{u1})
    := forall (x y : A) (f g : R x y), Type@{s;u2}.

  Structure t@{s;u0 u1 u2|} :=
    Pack {
        sort : Type@{u0};
        Hom : sort -> sort -> Type@{u1};
        class : class_of@{s;u0 u1 u2} Hom
      }.
    Coercion sort : t >-> Sortclass.
    Arguments Hom [t].
Definition two_hom@{s;u0 u1 u2|} {A : t@{s;u0 u1 u2}} (x y : A)
    : Graph.t@{s;u1 u2}.
exact (Graph.Pack (@class _ x y)).
Defined.
    Canonical two_hom.
    Coercion two_hom : t >-> Funclass.
    Infix "⇒" := (@class _ _ _) (at level 39, right associativity).
Module Export OneBicat.
Local Open Scope morphism_scope.

Definition Associative@{s;u0 u1 u2|} (A : TwoGraph.t@{s;u0 u1 u2})
  (t : Transitive@{Type;u0 u1} (@TwoGraph.Hom A))
  := forall (w x y z : A)
       (f : TwoGraph.Hom w x) (g : TwoGraph.Hom x y) (h : TwoGraph.Hom y z),
    Couple@{s;u1 u2} _ ((f · g) · h) (f · (g · h)).

Definition LeftUnitor@{s;u0 u1 u2|}
  (A : TwoGraph.t@{s;u0 u1 u2 })
  (t : PreOrder.class_of@{Type;u0 u1} (@TwoGraph.Hom A))
  := forall (x y : A) (f : A x y), Couple@{s;u1 u2} _ ((1 x) · f) f.

Definition RightUnitor@{s;u0 u1 u2|}
  (A : TwoGraph.t@{s;u0 u1 u2})
  (t : PreOrder.class_of@{Type;u0 u1} (@TwoGraph.Hom A))
  := forall (x y : A) (f : A x y), Couple _ (f · (1 y)) f.

  Module Export Class_of.
    Class t@{s;u0 u1 u2|}
      (A : Type@{u0})
      (R : A -> A -> Type@{u1})
      (two_graph : TwoGraph.class_of@{s;u0 u1 u2} R)
      (G := TwoGraph.Pack two_graph) := {
        is_preorder : PreOrder.class_of@{Type;u0 u1} R;
        is_vpreorder : forall (x y: A),
          PreOrder.class_of@{s;u1 u2} (two_graph x y);
        assoc : Associative@{s;u0 u1 u2} G
                   (PreOrder.trans (class_of:=is_preorder));
        lu : LeftUnitor@{s;u0 u1 u2} G is_preorder;
        ru : RightUnitor@{s;u0 u1 u2} G is_preorder;
        hcomp2 : forall (x y z : A)
                   (f f' : TwoGraph.Hom (t:=G) x y)
                   (g g' : TwoGraph.Hom (t:=G) y z),
          f ⇒ f' -> g ⇒ g' -> f · g ⇒ f' · g'
      }.
  End Class_of.
  Notation class_of := Class_of.t.
Module Export Category.
  Definition class_of@{u0 u1} (A : Type@{u0}) (R : A -> A -> Type@{u1}) :=
    @OneBicat.class_of@{Type;u0 u1 u1} A R (fun (x y : A) => @eq (R x y)).

  Structure t := Pack {
      sort : Type;
      Hom : sort -> sort -> Type;
      class : class_of Hom
   }.
    Coercion sort : t >-> Sortclass.

  Module Export Of_Preorder.
  Record factory (A : PreOrder.t) := Factory {
      assoc : forall (w x y z : A) (f : w <= x) (g : x <= y) (h : y <= z),
        ((f · g) · h) = f · (g · h);
      lu : forall (x y : A) (f : x <= y), (1 x · f) = f;
      ru : forall (x y : A) (f : x <= y), (f · 1 y) = f
  }.

  Definition Builder (A : Type) (R : A -> A -> Type) (C : PreOrder.class_of R)
    (fac : factory (PreOrder.Pack C)) : class_of R.
Admitted.
Definition to_graph (A : t) : Graph.t.
exact ({|
      Graph.sort := sort A;
      Graph.Hom := @Hom A
  |}).
Defined.
    Canonical to_graph.

Class Product {C : Category.t} (x y z : C) := {
    pi_x : z ~> x;
    pi_y : z ~> y;

  }.
Export elpi.elpi.

Elpi Db core_hint.db lp:{{
    kind tag type. % A tag is just a category for a hint.
    % Instead of having many hint databases, we have one hint database with many tags.
    type core tag.
% Our replacement for the core auto database.
    pred mysolve i:goal o:list sealed-goal.
    pred applicable o:tag i:goal o:open-tactic.
}}.

Elpi Tactic construc.
Elpi Accumulate lp:{{
    solve (goal _ _ Ty _ _ as G) GL :-
      whd Ty [] Ty' _,
      pglobal (indt GR) U = Ty',
      coq.env.indt GR _ _ _ _ Ks Kt,
        std.exists2 Ks Kt (k\ t\ sigma P\
           coq.saturate t (pglobal (indc k) U) P,
           refine P G GL).
 }}.

Instance IsPreOrderGraph : IsPreOrder GraphHom.t.
Proof.
  unshelve econstructor; exact _.
Defined.

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
  unshelve econstructor.
  {
    unshelve econstructor.
{
      intro.
      firstorder.
    }
    ltac1:(elpi construc).

