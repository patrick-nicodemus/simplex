From Simplex Require Import Basics Graph PreOrder.Core TwoGraph OneBicat Pseudofunctor.

Module UniversalArrow0.
  #[mode="! ! ! ! -"]
  Class mixin_of
    [P Q : Graph.t]
    (x : P)
    (G : Q -> P)
    (univ_object : Q) := Mixin {
      univ_arrow : Graph.Hom x (G univ_object) ;
      factoring : forall y, (Graph.Hom x (G y)) -> Graph.Hom univ_object y
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

  #[mode="! ! - ! ! -"]
  Class mixin_of
    {P Q : TwoGraph.t}
    {trans : Transitive (@TwoGraph.Hom P)}
    (x : P)
    (G : GraphHom.t Q P)
    {univ0 : UniversalArrow0.t x G}
    := lift : forall (z : Q) (f : TwoGraph.Hom x (G z)),
        UniversalArrow0.mixin_of
          (P:=TwoGraph.two_hom x (G z))
          (Q:=TwoGraph.two_hom (univ_object x G) z)
          f
          (fun (g : TwoGraph.Hom (univ_object x G) z) =>
             ((eta x G) · fmap G g))
          (alpha f)
  .

  Module mixin_of_conventions.
  End mixin_of_conventions.

  #[mode="! ! - ! !"]
  Class t
    [P Q : TwoGraph.t]
    {trans : Transitive (@TwoGraph.Hom P)}
    (x : P)
    (G : GraphHom.t Q P)
    := {
      univ_object : Q;
      is0universal : UniversalArrow0.mixin_of x G univ_object;
      is1universal : mixin_of _ _ (univ0:=UniversalArrow0.Pack is0universal)
    }.
  Module t_conventions.
    Arguments univ_object [P Q] {trans} x G {t}.
    Arguments is0universal [P Q] {trans} {x G} t.
    Arguments is1universal [P Q] {trans} {x G} t.
  End t_conventions.
  Import t_conventions.

  Definition to_universal0
    {P Q : TwoGraph.t} {trans: Transitive (@TwoGraph.Hom P)}
    {x : P} {G : GraphHom.t Q P}
    : t x G -> UniversalArrow0.t x G
    := fun a => {| UniversalArrow0.univ_object := univ_object x G;
               is_univ := is0universal a
             |}.
  Existing Instance to_universal0.
  
  Definition universal_2cell [P Q : TwoGraph.t]
    {trans : Transitive (@TwoGraph.Hom P)}
    (x : P) (G : GraphHom.t Q P) {universal_arrow : t x G}
    (y : Q)
    (f : TwoGraph.Hom x (G y))
    : TwoGraph.class f (eta x G · fmap G (alpha f))
    := (univ_arrow _ _ (mixin_of:=(is1universal universal_arrow y f))).

  Module Exports.
    Export t_conventions.
    Typeclasses Transparent mixin_of.
    Coercion to_universal0 : t >-> UniversalArrow0.t.
    Existing Instance to_universal0.
    Canonical to_universal0.
  End Exports.
End Is1Universal.
Export Is1Universal.Exports.

Module ColaxLeftAdjoint.
  (** In this section we prove that a lax functor [Q -> P] with universal arrows x->Q for all x in P has a colax left adjoint.*)
  Import UniversalArrow0.
  Import Tactics.

  Local Open Scope morphism_scope.
  Section graph_hom.
    Context [P Q : Graph.t].
    Context {trans : Transitive (Graph.Hom (t:=P))}.
    Context (G : Q -> P).
    Context (F_univ : forall (x : P), UniversalArrow0.t x G).
    Definition F1 : GraphHom.t P Q
      := {|
        GraphHom.map x := univ_object x G;
        fmap x y f := alpha (f · (eta y G))
      |}.
  End graph_hom.

  Module colax_constraints.
  Import OneBicat.Notations.
  Section colax_constraints_ctx.
    Context {P Q: OneBicat.t}
      (G : Lax1Functor.t Q P).
    Context (F_univ1 : forall (x : P), Is1Universal.t x G).
    Definition F_id : forall (x : P),
        (fmap (F1 G F_univ1) (1 x)) ⇒
          1 (F1 G F_univ1 x).
    Proof.
      intro x.
      apply (factoring _ _
               (mixin_of:=
                  Is1Universal.is1universal
                    (F_univ1 x) (univ_object x G) _)).
      apply (transitive _ (eta x G)) > [ apply OneBicat.lu |].
      apply (transitive _ (eta x G · (1 _))) > [ apply OneBicat.ru |].
      apply OneBicat.hcomp2 >  [exact (reflexive _)|].
      apply (Lax1Functor.luc).
    Defined.

    Definition F_comp : forall (x y z : P) (f : x ~> y) (g : y ~> z),
        fmap (F1 G F_univ1) (f · g) ⇒
          (fmap (F1 G F_univ1) f) · (fmap (F1 G F_univ1) g).
    Proof.
      intros x y z f g.
      apply (factoring _ _
               (mixin_of:=
                  Is1Universal.is1universal
                    (F_univ1 x) (univ_object z G) _)).
      apply (transitive _ (f · (g · eta z G))) > [apply OneBicat.assoc|].
      apply (transitive _ (f · (eta y G · (fmap G (fmap (F1 G F_univ1) g))))).
      1: apply OneBicat.hcomp2 > 
                [ apply reflexive
                | apply Is1Universal.universal_2cell]. 
      apply (transitive _ 
               (f · (eta y G) · fmap G (fmap (F1 G (fun x0 : OneBicat.to_graph P => F_univ1 x0)) g)))
            > [ apply OneBicat.assoc |].
      apply (transitive _ 
               ((eta x G · fmap G (fmap (F1 G _) f)) · fmap G (fmap (F1 G (fun x0 : OneBicat.to_graph P => F_univ1 x0)) g))).
      1: apply OneBicat.hcomp2 > [  apply Is1Universal.universal_2cell | apply reflexive]. 
      apply (transitive _ (eta x G · (fmap G (fmap (F1 G _) f) · (fmap G (fmap (F1 G _) g)))))
            > [apply OneBicat.assoc|].
      apply OneBicat.hcomp2 > [ apply reflexive |].
      apply Lax1Functor.lfc.
    Defined.
  End colax_constraints_ctx.
  End colax_constraints.
End ColaxLeftAdjoint.
