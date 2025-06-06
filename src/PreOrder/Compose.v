From Simplex Require Import Basics Basics.List Graph Eq
  Nat Tactics Path PreOrder.Core.
Local Set Implicit Arguments.

Inductive unitBtree :=
| Unit
| Morphism
| Comp : unitBtree -> unitBtree -> unitBtree.

Fixpoint length : unitBtree -> nat :=
  fun t => match t with
        | Unit => 0
        | Morphism => Nat.S 0
        | Comp x y => Nat.add (length x) (length y)
        end.

Definition compose_path@{s;u0 u1|}
  (A : PreOrder.t@{s|u0 u1})
  (a b : A)
  (p : Path.path A a b)
  (t : unitBtree)
  (eq_pf : length t == Path.length p)
  : A a b.
Proof.
  revert a b p eq_pf.
  refine ((fix rec_t (s : unitBtree) := _ ) t).
  clear t. destruct s.
  - intros a b p h.
    destruct (Path.length0 _ (symmetry h)).
    reflexivity.
  - intros a b p e. simpl length in e. symmetry in e. apply Path.length1 in e. exact e.
  - intros a b p e. simpl in e.
    apply (transitive (y:=Path.nth_vertex (length s2) p)).
    + apply (rec_t s1 a _ (Path.drop (length s2) p)).
      apply SEqType.seq_only_if.
      apply SEqType.seq_if in e.
      rewrite Path.drop_length
              > [apply symmetry, add_sub_eq_r; exact e|].
      destruct e.
      apply Nat.le_add_l.
    + apply (rec_t s2 _ _ (Path.take (length s2) p)).
      apply SEqType.seq_only_if.
      apply SEqType.seq_if in e.
      apply symmetry.
      apply take_length.
      destruct e.
      apply Nat.le_add_l.
Defined.

(** Very similar to [compose_path], but
    with an alternate design: that the list of nodes
    is provided separately from the path.
 *)
Definition compose_path_on@{s;u0 u1|}
  (A : PreOrder.t@{s|u0 u1})
  (a: A)
  (l : list A)
  (p : Path.path_on@{s|u0 u1} A a l)
  (t : unitBtree)
  (eq_pf : length t == List.length l)
  : A a (List.last a l).
Proof.
  revert a l p eq_pf.
  refine ((fix rec_t (s : unitBtree) := _ ) t).
  clear t. destruct s.
  - intros a; destruct l.
    + simpl. intros. contradiction.
    + simpl; intros; reflexivity.
  - intros a; destruct l.
    + intros [k s] h.
      simpl in h.
      change _ with (0 == List.length l) in h.
      apply List.length0 in h; destruct (symmetry h).
      exact k.
    + simpl. intros ? ?; contradiction.
  - simpl; intros a l p h.
    apply (@transitive _ _ _ _ (List.last a (List.take (length s1) l)) _).
    + apply (rec_t s1).
      * 
Abort.    
