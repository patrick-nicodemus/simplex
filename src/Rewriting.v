From Simplex Require Import Basics Eq Nat.
Module Rewriting.
  Ltac2 Notation "pattern" x(pattern) := x.
  (** Stream of all subterms *)
  Ltac2 all_closed_subterms (t : constr) : constr :=
    let (_, a) := Pattern.matches_subterm (pattern ?a) t in
    match a with
    |[(_,c)] => c
    | _ => Control.zero Not_found
    end.

  (** Create an evar of the given type. *)
  Ltac2 create_evar (type : constr) :=
    Constr.Pretype.pretype
      Constr.Pretype.Flags.open_constr_flags_no_tc
      (Constr.Pretype.expected_oftype type)
      preterm:(_).

  (** Given a type of the form forall x1....xn, T,
      return the term T[x1/?y1, x2/?y2,...xn/?yn]
      where all the ?y_i are freshly created evars. *)
  Ltac2 to_holes (tm : constr) (type : constr) :=
    let rec helper (tm : constr) (type : constr) (depth : int) (evars : constr list) :=
    match Constr.Unsafe.kind type with
    | Constr.Unsafe.Prod binder type' =>
        let btype := Constr.Binder.type binder in
        let new_evar := create_evar btype in
        helper '($tm $new_evar) type' (Int.add depth 1) (new_evar :: evars)
    | _ => (tm, Constr.Unsafe.substnl evars 0 type)
    end
    in
    let (tm, type) := helper tm type 0 [] in
    match Constr.Unsafe.check type with
    | Val v => (tm, v)
    | Err e => Control.zero e
    end.

  Ltac2 rewrite (hyp : ident) :=
    let eq_hyp := Control.hyp hyp in
    let eq_hyp_type := Constr.type eq_hyp in
    let goal := match! goal with | [|- ?g] => g end in
    let (holey_pf, holey_eq_hyp) := to_holes eq_hyp eq_hyp_type in
    let (_, y) := match! holey_eq_hyp with (@eq _ ?x ?y) => (x,y) end in
    let goal_subterm := (all_closed_subterms goal) in
    Std.unify y goal_subterm;
    Control.refine (fun () => '(match $holey_pf return $goal with eq_refl _ => _ end)).

  Goal (forall (x y : nat), x + y = y + x) -> (forall (x y z : nat), (x + y) = (y + x)).
  Proof.
    intro h.
    intros x y z.
    rewrite @h.
    exact (eq_refl _).
  Defined.
End Rewriting.
