From Simplex Require Import
                     Basics Basics.Datatypes Basics.List
                     Basics.Eq
                     Nat
                     Tactics
  Relations Graph TwoGraph
  PreOrder.Core PreOrder.Compose .
Local Set Implicit Arguments.
Local Open Scope morphism_scope.

Definition Associative@{s;u0 u1 u2|} (A : TwoGraph.t@{s|u0 u1 u2})
  (t : Transitive@{Type|u0 u1} (@TwoGraph.Hom A))
  := forall (w x y z : A)
       (f : TwoGraph.Hom w x) (g : TwoGraph.Hom x y) (h : TwoGraph.Hom y z),
    Couple@{s|u1 u2} _ ((f · g) · h) (f · (g · h)).

Definition LeftUnitor@{s;u0 u1 u2|}
  (A : TwoGraph.t@{s|u0 u1 u2 })
  (t : PreOrder.class_of@{Type|u0 u1} (@TwoGraph.Hom A))
  := forall (x y : A) (f : A x y), Couple@{s|u1 u2} _ ((1 x) · f) f.

Definition RightUnitor@{s;u0 u1 u2|}
  (A : TwoGraph.t@{s|u0 u1 u2})
  (t : PreOrder.class_of@{Type|u0 u1} (@TwoGraph.Hom A))
  := forall (x y : A) (f : A x y), Couple _ (f · (1 y)) f.

Module OneBicat.
  Import TwoGraph.Notations.

  Module Class_of.
    Class t@{s;u0 u1 u2|}
      (A : Type@{u0})
      (R : A -> A -> Type@{u1})
      (two_graph : TwoGraph.class_of@{s|u0 u1 u2} R)
      (G := TwoGraph.Pack two_graph) := {
        is_preorder : PreOrder.class_of@{Type|u0 u1} R;
        is_vpreorder : forall (x y: A),
          PreOrder.class_of@{s|u1 u2} (two_graph x y);
        assoc : Associative@{s|u0 u1 u2} G
                   (PreOrder.trans (class_of:=is_preorder));
        lu : LeftUnitor@{s|u0 u1 u2} G is_preorder;
        ru : RightUnitor@{s|u0 u1 u2} G is_preorder;
        hcomp2 : forall (x y z : A)
                   (f f' : TwoGraph.Hom (t:=G) x y)
                   (g g' : TwoGraph.Hom (t:=G) y z),
          f ⇒ f' -> g ⇒ g' -> f · g ⇒ f' · g'
      }.
  End Class_of.
  Notation class_of := Class_of.t.
  Import Class_of.

  Definition co_class@{s;u0 u1 u2|}
    (A : Type@{u0})
    (R : A -> A -> Type@{u1})
    (two_graph : TwoGraph.class_of@{s|u0 u1 u2} R)
    : class_of two_graph -> class_of (TwoGraph.co_class two_graph)
    := fun m =>
         {|
           Class_of.is_preorder := _;
           is_vpreorder x y := PreOrder.op_class (is_vpreorder (t:=m) x y);
           assoc w x y z f g h := Graph.couple_op (assoc (t:=m) w x y z f g h);
           lu x y f := Graph.couple_op (lu (t:=m) x y f);
           ru x y f := Graph.couple_op (ru (t:=m) x y f);
           hcomp2 x y z f f' g g' := hcomp2 (t:=m) x y z f' f g' g
         |}.

  Record t@{s;u0 u1 u2|} :=
    Pack {
        sort : Type@{u0};
        Hom : sort -> sort -> Type@{u1};
        two_cells : TwoGraph.class_of@{s|u0 u1 u2} Hom;
        class : class_of@{s|u0 u1 u2} two_cells
      }.

  Module t_conventions.
    Coercion sort : t >-> Sortclass.
    Arguments Hom [t].
    Arguments two_cells [t x y].
  End t_conventions.
  Import t_conventions.

  Definition is_vpreorder@{s;u0 u1 u2|} {A: t@{s|u0 u1 u2}} (x y : A)
    : PreOrder.class_of (@two_cells A x y)
    := is_vpreorder (t:=(class A)) x y.

  Definition vpreorder@{s;u0 u1 u2|} {A : t@{s|u0 u1 u2}}
    : forall (x y : A), PreOrder.t@{s|u1 u2}
    := fun x y => PreOrder.Pack (is_vpreorder x y).

  Module vpreorder_exports.
    Canonical vpreorder.
    Existing Instance is_vpreorder.
    Arguments vpreorder {A}.
  End vpreorder_exports.
  Import vpreorder_exports.

  Definition to_graph@{s;u0 u1 u2|}
    (A : t@{s|u0 u1 u2}) : Graph.t@{Type|u0 u1}
    := @Graph.Pack (sort A)
         (@vpreorder A).
  Module to_graph_exports.
    Canonical to_graph.
  End to_graph_exports.
  Import to_graph_exports.

  Definition to2graph@{s;u0 u1 u2|}
    (A : t@{s|u0 u1 u2}) : TwoGraph.t@{s|u0 u1 u2}
    := TwoGraph.Pack (@two_cells A).

  Module to2graph_coercion.
    Coercion to2graph : t >-> TwoGraph.t.
    Canonical to2graph.
  End to2graph_coercion.
  Import to2graph_coercion.

  Definition to_hom_graph@{s;u0 u1 u2|}
    (A:t@{s|u0 u1 u2}) :
    forall (x y : A), Graph.t@{s|u1 u2}
    := fun (x y : A) =>
      @Graph.Pack (Hom x y) (@two_cells _ x y).
  Module to_hom_graph_exports.
    Canonical to_hom_graph.
  End to_hom_graph_exports.

  Definition is_preorder_class@{s;u0 u1 u2|}
    (A : t@{s|u0 u1 u2})
    : PreOrder.class_of@{Type|u0 u1} (@Hom A)
    := is_preorder (t:=class A).

  (** The horizontal preorder, i.e. 0-cells ordered by 1-cells as relations *)
  Definition to_preorder@{s;u0 u1 u2|} (A : t@{s|u0 u1 u2})
    : PreOrder.t@{Type|u0 u1}
    := @PreOrder.Pack _ _ (is_preorder_class A).

  Module preorder_exports.
    Existing Instance is_preorder_class.
    Coercion to_preorder : t >-> PreOrder.t.
    Canonical to_preorder.
  End preorder_exports.
  Import preorder_exports.

  Definition co@{s;uA0 uA1 uA2|} : t@{s|uA0 uA1 uA2} -> t@{s|uA0 uA1 uA2}
    := fun x =>
         match x with
         | @Pack sort Hom two_cells class =>
             {| sort := sort;
               Hom := Hom;
               two_cells x y f g := two_cells x y g f;
               class := co_class class
             |}
         end.

  Record AreInverse {A : t} (x y : A)
    (f : Hom x y) (g : Hom y x)
    := {
      fg_id : Couple (vpreorder x x) (f · g) (1 x);
      gf_id : Couple (vpreorder y y) (g · f) (1 y)
    }.

  Definition assoc@{s;+|} {A : t@{s|_ _ _}}
    : Associative@{s|_ _ _} A _
    := assoc (t:=class A).
  
  Definition lu@{s;+|} {A : t@{s|_ _ _}}
    : LeftUnitor@{s|_ _ _} A _
    := lu (t:=class A).

  Definition ru@{s;+|} {A : t@{s|_ _ _}}
    : RightUnitor@{s|_ _ _} A _
    := ru (t:=class A).

  Definition hcomp2@{s;+|} {A : t@{s|_ _ _}}
    := hcomp2 (t:=class A).

  Definition is_preorder@{s;+|} (A : t@{s|_ _ _})
    := is_preorder (t:=class A).  

  Module coherence_exports.
    Arguments assoc [A w x y z] f g h.
    Arguments lu [A x y] f.
    Arguments ru [A x y] f.
    Arguments hcomp2 {A} [x y z f f' g g'].
  End coherence_exports.
  Import coherence_exports.

  Definition compose_path_fmap_indices@{s;u0 u1 u2}[A : t@{s|_ _ _}] (a : A)
    (l : list A)
    (btree : unitBtree)
    (p : Path.path_on@{_|u0 u1} (OneBicat.Hom@{_|u0 u1 u2} (t:=A)) a l)
    (n1 n2: nat)
    (pf : n1 + length btree <= n2)
    : nth n1 a l <= nth n2 a l
    := compose_path_on_indices A a l btree p n1 n2 pf.

  (* Definition hcompose_path_from_hd_right_assoc_nonempty@{s;u0 u1 u2|} *)
  (*   (A : OneBicat.t@{s|u0 u1 u2}): *)
  (*   forall (a b: A) (f g: Hom a b) (tau : two_cells f g) (l : list A) (n : nat), *)
  (*     GraphHom.class_of *)
  (*       (fun p : path_graph A a (b :: l) => *)
  (*          compose_path_from_hd_right_assoc_nonempty *)
  (*            (OneBicat.to_preorder A) a b f l (snd p) n :> *)
  (*            Graph.sort (OneBicat.to_hom_graph A a (nth n b l))). *)
  (* Proof. *)
  (*   intros a b f g tau l; revert l a b f g tau. *)
  (*   Control.refine (fun () => '(fix IHl l := match l with | hd :: tl => _ | List.nil => _ end)). *)
  (*   - intros a b f g tau [|n] [p0 p] [q0 q] [r0 r]; simpl in *. *)
  (*     + reflexivity. *)
  (*     + apply hcomp2 >[ reflexivity | ]. *)
  (* Defined. *)

  Definition hcompose_path_from_hd_right_assoc@{s;u0 u1 u2}
    (A : OneBicat.t@{s|u0 u1 u2}):
    forall (a : A) (l : list A) (n : nat),
      GraphHom.class_of
        (fun p : path_graph A a l =>
           compose_path_from_hd_right_assoc
             (OneBicat.to_preorder A) a l p n :>
             Graph.sort (OneBicat.to_hom_graph A a (nth n a l))).
  Proof.
    intros a l; destruct l.
    - simpl. intro n.
      destruct n.
      + intros ? ? ?; reflexivity.
      + simpl.
        revert l a hd n; Control.refine (fun () =>
                    '(fix IHl l := match l with
                                  | hd :: tl => _
                                  | List.nil => _
                                  end)).
        * clear l. intros a hd0; simpl; destruct n.
          { intros ? ? [r0 ?]. exact r0. }
          { intros [p0 p] [q0 q] [r0 r]; apply hcomp2.
            { exact r0. }
            { simpl in *. apply IHl. exact r. }
          } 
        * clear l. intros a hd n; destruct n; intros ? ? [r0 ?]; exact r0. 
    - intros [|n] ? ? _ ; reflexivity.
  Defined.

  Definition hcompose_path_right_assoc@{s;u0 u1 u2}
  (A : OneBicat.t@{s|u0 u1 u2})
  (a: A)
  (l : list A)
  (n1 n2 : nat)
  (ineq : n1 <= n2)
    : GraphHom.class_of
      (fun (p : TwoGraph.path_graph A a l) => 
         (compose_path_right_assoc A a l p n1 n2 ineq :>
            Graph.sort (to_hom_graph A (List.nth n1 a l) (List.nth n2 a l)))).
  Proof.
    revert n1 a l n2 ineq.
    Control.refine (fun () => '(fix IHn n1 := match n1 with | O => _ | S n1' => _ end)).
    - simpl.
      intros ?  ? ? _;
        apply (hcompose_path_from_hd_right_assoc A).
    - intros a l n2 ineq.
      destruct l.
      + simpl. intros [p0 p] [q0 q] [r0 r]. destruct n2.
        * Tactics.contradiction.
        * simpl. apply IHn. exact r.
      + destruct n2.
        * Tactics.contradiction.
        * exact (fun _ _ _ => 1 _).
  Defined.

  Instance compose_path_on_indices@{s;u0 u1 u2} (A : OneBicat.t@{s;u0 u1 u2})
    (a : A)
    (l : list A)
    (btree : unitBtree)
    (n1 n2 : nat)
    (pf : n1 + length btree <= n2) :
    GraphHom.class_of
      (fun (p : TwoGraph.path_graph A a l) => 
         (compose_path_fmap_indices a l btree p n1 n2 pf :>
            Graph.sort (to_hom_graph A (List.nth n1 a l)(List.nth n2 a l)))).
  Proof.
    revert btree a l n1 n2 pf.
    Control.refine (fun () => '(fix IH btree :=
              match btree with
              | Compose.Unit => _
              | Compose.Morphism => _
              | Compose.Comp s1 s2 => _
              end)).
    1,2: intros a l n1 n2 pf; apply hcompose_path_right_assoc.
    intros a l n1 n2 pf p q r.
    apply hcomp2; apply IH; exact r.
  Defined.

  (** The most general composition operation for chains of morphisms
  in a [OneBicat.t]. *)
  Definition compose_graph_hom@{s;u0 u1 u2} (A : OneBicat.t@{s;u0 u1 u2})
    (a : A) (l : list A) (btree : unitBtree) (pf : length btree <= List.length l)
    : GraphHom.t (TwoGraph.path_graph A a l) 
        (to_hom_graph A a (List.last a l))
    := GraphHom.Pack (compose_path_on_indices A a l btree 0 (List.length l) pf).

  (** Binary composition (Hom a b) × (Hom b c) -> Hom a c,
      as a graph homomorphism. *)
  Definition binary_compose_graph_hom@{s;u0 u1 u2} (A : OneBicat.t@{s;u0 u1 u2})
    (a b c : A)
    :=
    compose_graph_hom A a [b;c] (Compose.Comp Compose.Morphism Compose.Morphism)
      (le_refl _).

  Definition left_assoc@{s;u0 u1 u2} {A : OneBicat.t@{s;u0 u1 u2}}
    (a b c d: A)
    :=
    compose_graph_hom A a [b;c;d]
      (Compose.Comp (Compose.Comp Compose.Morphism Compose.Morphism)
         Compose.Morphism)
      (le_refl _).

  Definition right_assoc@{s;u0 u1 u2} {A : OneBicat.t@{s;u0 u1 u2}}
    (a b c d: A)
    :=
    compose_graph_hom A a [b;c;d]
      (Compose.Comp
         Compose.Morphism
         (Compose.Comp Compose.Morphism Compose.Morphism))
      (le_refl _).

  Definition lid@{s;u0 u1 u2} {A : OneBicat.t@{s;u0 u1 u2}}
    (a b: A)
    :=
    compose_graph_hom A a [b]
      (Compose.Comp Compose.Unit Compose.Morphism)
      (le_refl _).

  Definition id_graph_hom@{s;u0 u1 u2} {A : OneBicat.t@{s;u0 u1 u2}}
    (a b: A)
    :=
    compose_graph_hom A a [b] Compose.Morphism (le_refl _).

  Definition rid@{s;u0 u1 u2} {A : OneBicat.t@{s;u0 u1 u2}}
    (a b: A)
    :=
    compose_graph_hom A a [b]
      (Compose.Comp Compose.Morphism Compose.Unit)
      (le_refl _).

  (* needs TwoGraph.take_on *)
  Definition compose_path_fmap@{s;u0 u1 u2}[A : t@{s;_ _ _}] (a : A)
    (l : list A)
    (btree : unitBtree)
    (p : Path.path_on@{_|u0 u1} (OneBicat.Hom@{_|u0 u1 u2} (t:=A)) a l)
    (eq_pf : length btree == List.length l)
    : a ~> List.last a l
    := compose_path_on A a l btree p eq_pf.

  Definition compose@{s;+|} [A : t@{s;_ _ _}] :=
    PreOrder.is_trans (to_preorder A).

  Section composition_graph_hom.
    Sort s.
    Universes u0 u1 u2.
    Variable A : t@{s;u0 u1 u2}.
  End composition_graph_hom.

  (* (* Graph homomorphism (f, g, h) |-> (f \cdot g) \cdot h *) *)
  (* Definition left_assoc_map@{s;u0 u1 u2} (A : OneBicat.t@{s|u0 u1 u2}) *)
  (*   (w x y z : A) *)
  (*   := fun fgh : ((w ~> x) * (x ~> y) * (y ~> z))%type => *)
  (*          fst (fst fgh) · snd (fst fgh) · snd fgh. *)

  (* Instance left_assoc_graph_hom@{s;u0 u1 u2} (A : OneBicat.t@{s|u0 u1 u2}) : *)
  (*   forall (w x y z : A), GraphHom.class_of (left_assoc_map A w x y z). *)
  (* Proof. *)
  (*   intros w x y z. *)
  (*   intros fgh fgh' str. *)
  (*   apply OneBicat.hcomp2. *)
  (*   - apply OneBicat.hcomp2. *)
  (*     + exact (fst (fst str)). *)
  (*     + exact (snd (fst str)).  *)
  (*   - exact (snd str). *)
  (* Defined. *)

  (* Definition left_assoc@{s;u0 u1 u2} (A : OneBicat.t@{s|u0 u1 u2}) *)
  (*   (w x y z : A) *)
  (*   : GraphHom.t *)
  (*       ((w ~> x) * *)
  (*          (x ~> y) * (y ~> z))%type *)
  (*       (w ~> z)%type *)
  (*   := GraphHom.Pack (map:=left_assoc_map _ w x y z) _. *)
  (* Canonical left_assoc.   *)

  (* (* Graph homomorphism (f, g, h) |-> (f \cdot g) \cdot h *) *)
  (* Definition right_assoc_map@{s;u0 u1 u2} (A : OneBicat.t@{s|u0 u1 u2}) *)
  (*   (w x y z : A) *)
  (*   := fun fgh : ((w ~> x) * (x ~> y) * (y ~> z))%type => *)
  (*          fst (fst fgh) · (snd (fst fgh) · snd fgh). *)

  (* Instance right_assoc_graph_hom@{s;u0 u1 u2} (A : OneBicat.t@{s|u0 u1 u2}) : *)
  (*   forall (w x y z : A), GraphHom.class_of (right_assoc_map A w x y z). *)
  (* Proof. *)
  (*   intros w x y z. *)
  (*   intros fgh fgh' str. *)
  (*   apply OneBicat.hcomp2. *)
  (*   - exact (fst (fst str)). *)
  (*   - apply OneBicat.hcomp2. *)
  (*     + exact (snd (fst str)).  *)
  (*     + exact (snd str). *)
  (* Defined. *)

  (* Definition right_assoc@{s;u0 u1 u2} (A : OneBicat.t@{s|u0 u1 u2}) *)
  (*   (w x y z : A) *)
  (*   : GraphHom.t *)
  (*       ((w ~> x) * *)
  (*          (x ~> y) * (y ~> z))%type *)
  (*       (w ~> z)%type *)
  (*   := *)
  (*   GraphHom.Pack (map:=right_assoc_map _ w x y z) _. *)
  (* Canonical right_assoc. *)

  (* Definition lid_map@{s;?|} (A : OneBicat.t@{s|_ _ _}) (x y :A) (f : x ~> y) *)
  (*   := (1 x) · f. *)

  (* Instance lid_graph_hom@{s;?|} (A : OneBicat.t@{s|_ _ _}) (x y :A) *)
  (*   : GraphHom.class_of (lid_map A x y). *)
  (* Proof. *)
  (*   intros f g s. *)
  (*   apply hcomp2. *)
  (*   - apply reflexive. *)
  (*   - exact s. *)
  (* Defined. *)

  (* Definition lid@{s;?|} (A : OneBicat.t@{s|_ _ _}) (x y :A) *)
  (*   := GraphHom.Pack (lid_graph_hom A x y). *)

  (* Definition rid_map@{s;?|} (A : OneBicat.t@{s|_ _ _}) (x y :A) (f : x ~> y) *)
  (*   := f · (1 y). *)

  (* Instance rid_graph_hom@{s;?|} (A : OneBicat.t@{s|_ _ _}) (x y :A) *)
  (*   : GraphHom.class_of (rid_map A x y). *)
  (* Proof. *)
  (*   intros f g s. *)
  (*   apply hcomp2. *)
  (*   - exact s. *)
  (*   - apply reflexive. *)
  (* Defined. *)

  (* Definition rid@{s;?|} (A : OneBicat.t@{s|_ _ _}) (x y :A) *)
  (*   := GraphHom.Pack (rid_graph_hom A x y). *)
  
  Module Exports.
    Export t_conventions.
    Export to_graph_exports.
    Export to2graph_coercion.
    Export to_hom_graph_exports.
    Export preorder_exports.
    Export vpreorder_exports.
    Export coherence_exports.
  End Exports.
  Module Notations.
    Local Set Warnings "-notation-overridden".
    Infix "~>" := Hom (at level 41).
    Infix "⇒" := two_cells (at level 39).
  End Notations.
End OneBicat.
Export OneBicat.Exports.
Export (hints) OneBicat.

Instance hcomp2_uncurry (A : OneBicat.t) (x y z : A) :
  GraphHom.class_of (uncurry (OneBicat.compose x y z)).
Proof.
  intros [f g] [f' g'] [s t]; simpl in *.
  apply OneBicat.hcomp2; assumption.
Defined.

