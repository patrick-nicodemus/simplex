From Simplex Require Import Basics Basics.Datatypes Basics.List Graph Eq
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

(** The obvious right-associative composition function
   on paths, generalized so that it can operate on
   a prefix of the list if necessary.
   (Set [n = List.length l] to compose the full path.) *)
Definition compose_path_from_hd_right_assoc@{s;u0 u1|}
  (A : PreOrder.t@{s|u0 u1})
  (a: A)
  (l : list A)
  (p : Path.path_on@{s|u0 u1} A a l)
  (n : nat)
  : A a (List.nth n a l)
  :=
  (fix IHl (l : list A)
    : forall (a : A) (p : Path.path_on A a l) (n : nat), A a (List.nth n a l)
   := match l with
      | hd :: tl => fun a p n =>
                    match n with
                    | O => reflexive a
                    | S n' => transitive (fst p) (IHl tl hd (snd p) n')
                    end
      | List.nil => fun a p n => match n with
                   | O => reflexive a
                   | S n' => reflexive a
                   end
      end
  ) l a p n.

(** Like [compose_path_from_hd_right_assoc]
    but drops a prefix. *)
Definition compose_path_right_assoc@{s;u0 u1|}
  (A : PreOrder.t@{s|u0 u1})
  :
  forall (a : A) (l : list A),
  path_on@{s|u0 u1} A a l ->
  forall n1 n2 : nat, n1 <= n2 -> nth n1 a l <= nth n2 a l :=
  (fix compose_path_right_assoc a l p n1 n2 ineq {struct n1} :=
  match n1 return (forall (ineq : n1 <= n2), (nth n1 a l <= nth n2 a l)) with
  | O =>  fun _ => compose_path_from_hd_right_assoc A a l p n2
  | S n1' =>
      (match l return
             (forall (p : path_on A a l) (ineq : S n1' <= n2),
                 (nth (S n1') a l <= nth n2 a l))
       with
       | hd :: tl =>
           fun p =>
             (match n2 with
              | S n2' => fun ineq =>
                          compose_path_right_assoc hd tl (snd p) n1' n2' ineq
              | O => fun ineq => match ineq with end
              end )
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
Definition compose_path_on_indices@{s;u0 u1|}
  (A : PreOrder.t@{s|u0 u1})
  (a: A)
  (l : list A)
  (t : unitBtree)
  (p : Path.path_on@{s|u0 u1} A a l)
  (n1 n2 : nat)
  (h : n1 + length t <= n2)
  : A (List.nth n1 a l) (List.nth n2 a l).
Proof.
  revert a l p n1 n2 h.
  revert t.
  refine (fix IH t :=
             match t with
             | Compose.Unit => _
             | Compose.Morphism => _
             | Compose.Comp s1 s2 => _
             end
         ).
  - (* Unit btree. We only care about this
       in the case where n1 = n2, as this is the only time it should be defined. *)
    clear t IH.
    intros a l; revert l a.
    
    refine (fix IHl l := match l with hd :: tl => _ | List.nil => _ end).
    + (* If l = hd :: tl, do a case analysis on whether n = 0 or n = S n'.
         If n = 0 then any definition is valid so long as it
         returns the identity morphism in the case n' = 0
         (which [compose_path_from_hd_right_assoc] does.)
         If n = S n', then just induct,
         recursively reducing it to the case where
         either l is empty or n = 0. *)
      intros a [f1 p] [|n'].
      * simpl. intros n2 _. apply compose_path_from_hd_right_assoc.
        exact ({| fst:= f1; snd:= p |}).
      * simpl. destruct n2 > [intros ?; contradiction| intro le].
        simpl. apply IHl; assumption.
    + (* If l = nil then this is just reflexivity,
         but we need to pattern match for this to be obvious. *)
      intros a _ [|n1] [|n2]; intros; reflexivity.
  - (* Morphism btree. We only care about this being correct in the
      case n2 = n1 + 1, so we can return junk outside of that. *)
    clear t.
    intros a l; revert l a.
    refine (fix IHl l := match l with hd :: tl => _ | List.nil => _ end).
    + intros a [f p] [|n1].
      * (* Case: n=0. In this case we only really care about n2=1.
           Return junk otherwise. *)
        intros n2 _. simpl. destruct n2 > [ reflexivity |]. simpl.
        (* The only important line *)
        destruct n2 > [exact f|].
        apply (@transitive _ _ _ _ hd) >
                [ exact f|
                  apply compose_path_from_hd_right_assoc; exact p].
      * (* Case: n = S n'. Induct as before. *)
        intros [|n2] > [intros; contradiction| simpl; intro le].
        apply IHl > [ exact p |
                      let h := Control.hyp (ident:(le)) in exact ($h)].
    + intros a _ [|n1] [|n2]; intros; reflexivity.
  - intros. apply (@transitive _ _ _ _ (nth (n1 + length s1) a l)).
    + apply (IH s1) > [ exact p | reflexivity ].
    + apply (IH s2) > [ exact p | simpl in h ].
      destruct (SEqType.seq_if _ _ (Nat.assoc n1 (length s1) (length s2))).
      exact h.
Defined.

(** Very similar to [compose_path], but
    with an alternate design: that the list of nodes
    is provided separately from the path. *)
Definition compose_path_on@{s;u0 u1|}
  (A : PreOrder.t@{s|u0 u1})
  (a: A)
  (l : list A)
  (t : unitBtree)  
  (p : Path.path_on@{s|u0 u1} A a l)
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
      simpl.
      change _ with (0 == List.length l) in h.
      apply List.length0 in h; destruct (symmetry h).
      exact k.
    + simpl. intros ? ?; contradiction.
  - simpl; intros a l p h.
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
          symmetry.
          rewrite add_comm.
          apply add_sub.
        }
        symmetry.
        apply (List.drop_length l (length s1)).
        destruct h.
        apply le_add_r.
Defined.
