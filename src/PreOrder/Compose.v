From Simplex Require Import Basics Basics.Datatypes Basics.List Graph Eq SEq
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
  (A : PreOrder.t@{s;u0 u1})
  (a b : A)
  (t : unitBtree)
  (p : Path.path A a b)
  (eq_pf : length t == Path.length p)
  : A a b.
Proof.
  revert a b p eq_pf.
  refine ((fix rec_t (s : unitBtree) := _ ) t).
  clear t. destruct s.
  - intros a b p h.
    destruct (Path.length0 _ (symmetry h)).
    reflexivity.
  - intros a b p e. simpl length in e. symmetry in e. apply Path.length1 in e.
    exact e.
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

(** Takes a path with at least one edge, and composes the path
    in a right associative way. (There is no trailing multiplication by the
    identity at the end, so this function can be used with
    any graph with an associative composition, even if it is not unital. *)
Definition compose_path_from_hd_right_assoc_nonempty@{s;u0 u1|}
  (A : PreOrder.t@{s;u0 u1})
  (a: A)
  (b : A)
  (f : A a b)
  (l : list A)
  (p : Path.path_on@{s;u0 u1} A b l)
  (n : nat)
  : A a (List.nth n b l)
  :=
  (fix IHl (l : list A):
    forall (a b :A) (f : A a b) (p : Path.path_on@{s;u0 u1} A b l) (n : nat), A a (List.nth n b l)
      := match l return forall (a b :A) (f : A a b) (p : Path.path_on@{s;u0 u1} A b l) (n : nat), A a (List.nth n b l) with
         | hd :: tl => fun a b f p n =>
                       match n return A a (List.nth n b (hd::tl)) with
                       | 0 => f
                       | S n' => transitive f (IHl tl b hd (fst p) (snd p) n')
                       end
         | List.nil => fun a b f p n => match n with | 0 => f | S n' => f end
         end) l a b f p n.

(** A right-associative composition of paths, defined by case analysis
    on whether the path is empty: if the path is empty, it returns the
    identity morphism, otherwise it recursively composes all the
    morphisms in the non-empty list. *)
Definition compose_path_from_hd_right_assoc@{s;u0 u1|}
  (A : PreOrder.t@{s;u0 u1})
  (a: A)
  (l : list A)
  (p : Path.path_on@{s;u0 u1} A a l)
  (n : nat)
  : A a (List.nth n a l)
  :=
  match l return forall (p : Path.path_on@{s;u0 u1} A a l), A a (List.nth n a l) with
  | hd :: tl =>
      match n with
      | 0 => fun p => reflexive a
      | S n' => fun p => compose_path_from_hd_right_assoc_nonempty A a hd (fst p) tl (snd p) n'
      end
  | List.nil => fun p => match n with | 0 => reflexive a | S _ => reflexive a end
  end p.

(** Like [compose_path_from_hd_right_assoc]
    but drops a prefix. *)
Definition compose_path_right_assoc@{s;u0 u1|}
  (A : PreOrder.t@{s;u0 u1})
  :
  forall (a : A) (l : list A),
  path_on@{s;u0 u1} A a l ->
  forall n1 n2 : nat, Nat.le n1 n2 -> nth n1 a l <= nth n2 a l :=
  (fix compose_path_right_assoc a l p n1 n2 ineq {struct n1} :=
     match n1 return (forall (ineq : Nat.le n1 n2),
                         PreOrder.Hom@{s;u0 u1}(nth n1 a l) (nth n2 a l)) with
  | O =>  fun _ => compose_path_from_hd_right_assoc A a l p n2
  | S n1' =>
      (match l return
             (forall (p : path_on A a l) (ineq : Nat.le (S n1') n2),
                 PreOrder.Hom@{s;u0 u1} (nth (S n1') a l) (nth n2 a l))
       with
       | hd :: tl =>
           fun p =>
             (match n2 with
              | S n2' => fun ineq =>
                          compose_path_right_assoc hd tl (snd p) n1' n2' ineq
              | O => fun ineq => match ineq with end
              end)
       | List.nil => fun p => match n2
                          with
                          | S n2' => fun _ => reflexive a
                          | O => fun ineq => match ineq with end
                          end 
       end p)
  end ineq).

(** This is a modified version of [compose_path_on]
    defined later in the file. This
    function is very important to be able to reason about
    effectively, because we want to define common things
    using it.
    Ideally I do not want to use reindexing along an equality
    between indices, because reasoning inside an equality
    pattern match is harder; my hope is that
    the stronger induction hypothesis given by this theorem
    will allow me to prove this without using
    any pattern matching on equality.
    TODO: Redefine "List.last a l" as "List.nth (List.length l) a l"
    so that we can use this on an arbitrary path without indices
 *)

Fixpoint compose_path_on_indices@{s;u0 u1|}
  (A : PreOrder.t@{s;u0 u1})
  (a: A)
  (l : list A)
  (t : unitBtree)
  (p : Path.path_on@{s;u0 u1} A a l)
  (n1 n2 : nat)
  (h : Nat.le (n1 + length t) n2)
  : A (List.nth n1 a l) (List.nth n2 a l).
Proof.
  destruct t as [ | | s1 s2].
  - apply compose_path_right_assoc > [ exact p| ].
    revert h; exact (match (Nat.add_comm 0 n1) in eq _ y return
                 forall (p :Nat.le y n2), Nat.le n1 n2
           with eq_refl _ => fun x => x end).
  - apply compose_path_right_assoc > [ exact p| ].
    apply (@transitive@{SProp;_ _}  _ Nat.le _ _ (n1 + length Morphism)).
    + apply Nat.le_add_r.
    + exact h.
  -
    intros. apply (@transitive _ _ _ _ (nth (n1 + length s1) a l)).
    + apply (compose_path_on_indices A a l s1 p n1 (n1 + length s1)); reflexivity.
    + apply (compose_path_on_indices A a l s2 p (n1 + length s1) n2).
      destruct (SEqType.seq_if _ _ (Nat.assoc n1 (length s1) (length s2)))^.
      exact h.
Defined.

(** Very similar to [compose_path], but
    with an alternate design: that the list of nodes
    is provided separately from the path. *)
Definition compose_path_on@{s;u0 u1|}
  (A : PreOrder.t@{s;u0 u1})
  (a: A)
  (l : list A)
  (t : unitBtree)  
  (p : Path.path_on@{s;u0 u1} A a l)
  (eq_pf : length t == List.length l)
  : A a (List.last a l).
Proof.
  revert a l p eq_pf.
  refine ((fix rec_t (s : unitBtree) := _ ) t).
  clear t. destruct s; intro a.
  - destruct l.
    + intros; contradiction.
    + intros; reflexivity.
  - destruct l.
    + intros [k s] h.
      simpl in h.
      simpl.
      change _ with (0 == List.length l) in h.
      apply List.length0 in h; destruct (symmetry h).
      exact k.
    + simpl. intros ? ?; contradiction.
  - intros l p h.
    apply (@transitive _ _ _ _ (List.last a (List.take (length s1) l)) _).
    + apply (rec_t s1).
      * apply take_on. exact p.
      * apply SEqType.seq_only_if. symmetry. apply List.take_length.
        apply SEqType.seq_if in h.
        destruct h.
        apply le_add_r.
    + destruct (List.nth_last_take a l (length s1)).
      destruct (List.nth_last_drop a l (length s1)).
      apply (rec_t s2).
      * simpl. apply Graph.Path.drop_on. exact p.
      * apply SEqType.seq_only_if.
        apply SEqType.seq_if in h.
        apply (transitive (y:=(List.length l)-(length s1))).
        { 
          destruct h.
          symmetry. simpl.
          rewrite add_comm.
          apply add_sub.
        }
        symmetry.
        apply (List.drop_length l (length s1)).
        destruct h.
        apply le_add_r.
Defined.
