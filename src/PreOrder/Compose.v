From Simplex Require Import Basics Graph Eq Nat Tactics Path PreOrder.Core.
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

Definition compose@{s;u0 u1|}
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
    destruct (Path.length0 _ (symmetry _ _ h)).
    reflexivity.
  - intros a b p e. simpl length in e. symmetry in e. apply Path.length1 in e. exact e.
  - intros a b p e. simpl in e. apply (transitive _ (Path.nth_vertex (length s2) p)).
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
