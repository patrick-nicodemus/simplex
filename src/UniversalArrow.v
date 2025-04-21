From Simplex Require Import Basics Graph PreOrder TwoGraph Bicat Pseudofunctor.

Module UniversalArrow0.
  Class mixin_of
    [P Q : Graph.t]
    (x : P)
    (G : Q -> P)
    (univ_object : Q) := Mixin {
      univ_arrow : x ~> G univ_object ;
      factoring : forall y, (x ~> G y) -> univ_object ~> y
    }.
  Module mixin_of_conventions.
    Arguments univ_arrow [P Q] x G {univ_object mixin_of}.
    Arguments factoring [P Q] x G {univ_object mixin_of}.
  End mixin_of_conventions.

  Class t
    [P Q : Graph.t]
    (x : P)
    (G : Q -> P)
    := Pack {
      univ_object : Q ;
      is_univ : mixin_of x G univ_object
         }.
  Module t_conventions.
    Arguments univ_object [P Q] x G {t}.    
    Arguments is_univ [P Q x G] t.
    Arguments Pack [P Q x G univ_object].
  End t_conventions.

  Definition eta {P Q : Graph.t} (x : P) (G : Q -> P) {t : t x G}
    := univ_arrow x G (mixin_of:=is_univ t).
  Definition alpha {P Q : Graph.t} (x : P) (G : Q -> P) {t : t x G}
    := factoring x G (mixin_of:=is_univ t).
  
  Module Exports.
    Export mixin_of_conventions.
    Export t_conventions.
    Arguments univ_object [P Q] x G {t}.
    Arguments eta [P Q] x G {t}.
    Arguments alpha [P Q x G] {t} [y].
  End Exports.
End UniversalArrow0.
Export UniversalArrow0.Exports.

Module Is1Universal.
  Local Open Scope morphism_scope.
  Import UniversalArrow0.
  Class mixin_of
    {P Q : TwoGraph.t}
    {trans : Transitive (Hom (t:=P))}
    (x : P)
    (G : GraphHom.t Q P)
    {univ0 : UniversalArrow0.t x G}
    := lift : forall (z : Q) (f : x ~> G z),
        UniversalArrow0.mixin_of
          (P:=TwoGraph.two_hom x (G z))
          (Q:=TwoGraph.two_hom (univ_object x G) z)
          f
          (fun (g : (univ_object x G) ~> z)  => ((eta x G) · fmap G g))
          (alpha f)
  .

  Module mixin_of_conventions.
  End mixin_of_conventions.

  Class t
    {P Q : TwoGraph.t}
    {trans : Transitive (Hom (t:=P))}
    (x : P)
    (G : GraphHom.t Q P)
    := {
      univ_object : Q;
      is0universal : UniversalArrow0.mixin_of x G univ_object;
      is1universal : mixin_of _ _ (univ0:=UniversalArrow0.Pack is0universal)
    }
  .

  Module t_conventions.
    Arguments univ_object [P Q] {trans} x G {t}.
    Arguments is0universal [P Q] {trans} {x G} t.
    Arguments is1universal [P Q] {trans} {x G} t.
  End t_conventions.
  Import t_conventions.

  Definition to_universal0
    {P Q : TwoGraph.t} {trans: Transitive (Hom(t:=P))}
    {x : P} {G : GraphHom.t Q P}
    : t x G -> UniversalArrow0.t x G
    := fun a => {| UniversalArrow0.univ_object := univ_object x G;
               is_univ := is0universal a
             |}.

  Module Exports.
    Export t_conventions.
    Typeclasses Transparent mixin_of.
    Coercion to_universal0 : t >-> UniversalArrow0.t.
  End Exports.
End Is1Universal.
Export Is1Universal.Exports.

Module ColaxLeftAdjoint.
  (** In this section we prove that a lax functor [Q -> P] with universal arrows x->Q for all x in P has a colax left adjoint.*)
  Import GraphHom UniversalArrow0.
  Local Open Scope morphism_scope.
  Section graph_hom.
    Context [P Q : Graph.t].
    Context {trans : Transitive (Hom (t:=P))}.
    Context (G : Q -> P).
    Context (F_univ : forall (x : P), UniversalArrow0.t x G).
    Definition F1 : GraphHom.t P Q
      := {|
        map x := univ_object x G;
        class x y f := alpha (f · (eta y G))
      |}.
  End graph_hom.
  (* Section test. *)
  (*   Set Printing All. *)
  (*   Set Typeclasses Debug. *)
  (*   (* Require Unicoq.Unicoq. *) *)
  (*   (* Set Unicoq Debug. *) *)
  (*   Context (A : TwoGraph.t). *)
  (*   Context (x y : A). *)
  (*   Print TwoGraph.to_graph. *)
  (*   Set Printing Coercions. *)
  (*   Print Canonical Projections. *)
  (*   Check (@Graph.Hom _ x y). *)
  (*   Check (@Graph.Hom (TwoGraph.to_graph _) x y). *)


  (*   Ltac2 Eval unify (Graph.sort _) . *)
  (* End test. *)
  
  Section colax_unitor.
    Context {P : OneBicat.t} {Q : TwoGraph.t}
      {rrefl : Reflexive (Hom(t:=Q))}
      (G : GraphHom.t Q P).
    Context (F_univ1 : forall (x : P), Is1Universal.t x G).
    Definition F_id : forall (x : P), (fmap (F1 G F_univ1) (1 x)) ⇒ 1 (F1 G F_univ1 x).
    Proof.
      intro x.
      apply (factoring _ _
               (mixin_of:=
                  Is1Universal.is1universal
                    (F_univ1 x) (univ_object x G) _)).
      refine '(transitive _ (eta x G) _ _ _).
    Abort.
  
      (* 1: { *)
      (*   (* Std.unify '(TwoGraph.to_graph _) *) *)
      (*   (*   '(OneBicat.to_graph P). *) *)
      (*   Std.unify '(Graph.sort _) *)
      (*     '(@Graph.Hom (OneBicat.to_graph P) x *)
      (*         (G(univ_object x G))). *)

      (*   Set Printing All. *)
      (*   refine '(@PreOrder.trans _ _). *)
      (*   exact (@PreOrder.trans _ (OneBicat.is_vpreorder_instance _ _ _)). *)
      (* }  *)
      (* 1: apply lu. *)
      (* refine '(transitive _ (eta x G · (1 (G (univ_object x G)))) _ _ _); *)
      (*   try (exact _). *)
      (* 1: apply ru. *)
      (* Unset Solve Unification Constraitns *)
      (* refine '(OneBicat.hcomp2 _ _ _ _ (eta x G) (eta x G) _ _ _ _). *)
      (* Abort. *)
  End colax_unitor.
  
  Section left_adjoint.
  End left_adjoint.
End ColaxLeftAdjoint.
