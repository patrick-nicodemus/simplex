From Simplex Require Import Basics Graph.
Local Set Implicit Arguments.
Module PreOrder.
  Class mixin_of@{s|u0 u1|}
    (A : Graph.t@{s|u0 u1})
    : Type@{s|max(u0+1,u1+1)}
    := Mixin {
      refl : Reflexive@{s|u0 u1} (Hom (t:=A));
      trans : Transitive@{s|u0 u1} (Hom (t:=A))
  }.

  Module mixin_of_conventions.
    Arguments Mixin A &.
    Arguments refl [A] {mixin_of}.
    Arguments trans [A mixin_of x y z].
    Existing Instance refl.
    Existing Instance trans.
  End mixin_of_conventions.
  Import mixin_of_conventions.

  Class class_of@{s|u0 u1|} (A : Type@{u0})
    : Type@{max(u0+1,u1+1)}
    := Class {
           rel : Graph.class_of@{s|u0 u1} A;
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
    
  Definition mixin_op@{s|u0 u1|}
    (A : Graph.t@{s|u0 u1}) (P : mixin_of A) :
    mixin_of (Graph.op A) :=
    {|
      refl x := refl (mixin_of:=P) x;
      trans x y z f g := trans (mixin_of:=P) g f
    |}.

  Definition to_graph@{s|u0 u1|} (A : t@{s|u0 u1}) : Graph.t@{s|u0 u1}
    := Graph.Pack (rel _ (class A)).

  Module to_graph_conventions.
    Canonical to_graph.
    Coercion to_graph : t >-> Graph.t.
  End to_graph_conventions.
  Import to_graph_conventions.
  
  Definition is_refl@{s|u0 u1 +|+} (A : t) : Reflexive@{s|u0 u1} (rel _ (class A))
    := @refl _ ((mixin _ (class A))).
  Module is_refl_conventions.
    Existing Instance is_refl.
  End is_refl_conventions.

  Definition is_trans@{s|u0 u1 +| +} (A : t) : Transitive@{s|u0 u1} (rel _ (class A))
    := @trans _ ((mixin _ (class A))).
  Module is_trans_conventions.
    Existing Instance is_trans.
  End is_trans_conventions.
  Import is_trans_conventions.
  
  Definition op@{s|+|+} (A : t@{s|_ _}) : t@{s| _ _}
    := Pack (Class (rel:=(fun (a b : sort A) => Hom b a))
         {| refl x := is_refl _ x; trans x y z f g := is_trans _ z y x g f |}).
  
  Module ForExport.
    Export t_conventions.
    Export to_graph_conventions.
    Export is_refl_conventions.
    Export is_trans_conventions.
    Export mixin_of_conventions.
  End ForExport.
End PreOrder.
Export PreOrder.ForExport.
