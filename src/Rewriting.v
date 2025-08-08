From Simplex Require Import Basics Eq Nat.
Module Rewriting.
  Ltac2 Notation "pattern" x(pattern) := x.

  (** Stream of all subterms *)
  Ltac2 all_closed_subterms (t : constr) : Pattern.context * constr :=
    let (ctx, a) := Pattern.matches_subterm (pattern ?a) t in
    match a with
    |[(_,c)] => (ctx,c)
    | _ => Control.zero Not_found
    end.

  (** Create an evar of the given type. *)
  (* Ltac2 create_evar (type : constr) := *)
  (*   Constr.Pretype.pretype *)
  (*     Constr.Pretype.Flags.open_constr_flags_no_tc *)
  (*     (Constr.Pretype.expected_oftype type) *)
  (*     preterm:(_). *)
  Ltac2 create_evar (type : constr) := '(_ :> $type).

  (** Given a term [tm] of type [type], where [type] is
      of the form [forall (x1 : A1) (x2 : A2) ... (xn : An), B],
      create new metavariables ?y1 : A1, ?y2 : A2[y1/?y2],...
      and return
      (tm ?y1 ?y2 ... ?yn,
       B[x1/?y1,x2/?y2,...xn/?yn],
       [?yn;?yn-1;...?y1]) *)
  Ltac2 to_holes (tm : constr) (type : constr)
    : constr * constr * constr list :=
    let rec helper (tm : constr) (type : constr)
          (evars : constr list) :=
    match Constr.Unsafe.kind type with
    | Constr.Unsafe.Prod binder type' =>
        let btype := Constr.Binder.type binder in
        Message.print (Message.of_constr tm);
        let new_evar := create_evar btype in
        Message.print (Message.of_constr tm);
        Message.print (Message.of_constr type');
        let ell := new_evar::evars in
        helper '($tm $new_evar) (Constr.Unsafe.substnl [new_evar] 0 type') ell
    | _ =>
        (tm, type, evars)
    end
    in
    let (tm, type, evars) := helper tm type [] in
    match Constr.Unsafe.check type with
    | Val v => (tm, v, evars)
    | Err e => Control.zero e
    end.

  (**
     Variants of rewrite we could imagine:
     - rewrite the first unification
     - skip to the n-th and rewrite that
     - "greedy" - rewrite all disjoint occurrences,
       where rewrite at pos c is ignored if c is
       at a subterm of another rewrite discovered first.
     - rewrite repeatedly
     Let's implement 1, 2, and 3.
   *)

   Ltac2 relevance (in_sprop : bool) :=
      if in_sprop then Constr.Binder.Irrelevant else Constr.Binder.Relevant.

   Ltac2 context_to_lambda (c : Pattern.context) (binder_type: constr): constr :=
     '(fun abc : $binder_type => 
         ltac2:(Control.refine (fun () => Pattern.instantiate c &abc))).

   Module What.
     Import Constr.Unsafe.
     Ltac2 what_is_it (tm : constr) :=
       match Constr.Unsafe.kind tm with
       | Rel _ => "Rel"
       | Var _ => "Var"
       | Meta _ => "Meta"
       | Evar _ _ => "Evar"
       | Sort _ => "Sort"
       | Cast _ _ _ => "Cast"
       | Prod _ _ => "Prod"
       | Lambda _ _ => "Lambda"
       | LetIn _ _ _ => "LetIn"
       | App _ _ => "App"
       | Constant _ _ => "Constant"
       | Ind _ _ => "Ind"
       | Constructor _ _ => "Constructor"
       | Case _ _ _ _ _ => "Case"
       | Fix _ _ _ _ => "Fix"
       | CoFix _ _ _ => "CoFix"
       | Proj _ _ _=> "Proj"
       | Uint63 _ =>"Uint"
       | Float _ => "Float"
       | String _=> "String"
       | Array _ _ _ _  => "array"
       end.
   End What.

   (** [type] is of the form
       [forall x1 x2.... xn, I u1... um];
       gets the inductive I
    *)
   Ltac2 rec inductive_head (type : constr) : inductive * instance
     :=
     match Constr.Unsafe.kind type with
     | Constr.Unsafe.Lambda _ arg => inductive_head arg
     | Constr.Unsafe.LetIn _ _ arg => inductive_head arg
     | Constr.Unsafe.App hd _ =>
         match Constr.Unsafe.kind hd with
         | Constr.Unsafe.Ind inductive instance => inductive, instance
         | _ =>
             Control.zero Not_found
         end
     | _ => Control.zero Not_found
     end.

   Ltac2 print_ctx ctx :=
     Message.print (Message.of_constr (Pattern.instantiate ctx '_)).

   Locate Relations.Symmetric.
   (** [tm : forall x1...xn, t1 = t2] =>
      [reverse_term tm : forall x1...xn, t2 = t1]
    *)

   Ltac2 reverse_term tm :=
     let type := Constr.type tm in
     let (holey_tm, holey_type, evar) := to_holes tm type in
     ().

  (* Rewrite the *first* unification of the RHS of the
     head of [tm] with the goal. *)
   Ltac2 rewrite_fst (tm : constr) :=
     let context_to_lambda_eq (c : Pattern.context)
     (binder_type: constr)
     (equality_type : constr)
     : constr :=
     '(fun (abc : $binder_type) (_ : $equality_type) => 
         ltac2:(Control.refine (fun () => Pattern.instantiate c &abc)))
     in
    let tm_type := Constr.type tm in
    let goal := Control.goal () in
    Control.refine (fun ()=> 
                      let (holey_pf, holey_type, _) := to_holes tm tm_type in
    let (eqtype, _, y) :=
      match! holey_type with (@eq ?eqtype ?x ?y) => (eqtype,x,y) end in
    let (goal_ctx, _) :=
      Control.once (fun () =>
                      let (ctx, goal_subterm) := all_closed_subterms goal
                      in (ctx,Std.unify y goal_subterm))
    in
    let case :=
      let (inductive, _) := inductive_head holey_type in
      Constr.Unsafe.case inductive
    in
    let raw_tm := Constr.Unsafe.make (
              Constr.Unsafe.Case case
                (context_to_lambda_eq goal_ctx eqtype holey_type,
                  (if Constr.equal (Constr.type holey_pf) 'SProp then
                     Constr.Binder.Irrelevant
                   else
                     Constr.Binder.Relevant
                ))
                Constr.Unsafe.NoInvert
                holey_pf
                [| '_  |])
    in
    Message.print (Message.of_constr raw_tm);

    match Constr.Unsafe.check(raw_tm)
    with
    | Val tm => tm
    | Err exn => Control.zero exn
    end).

  Goal (forall (x y : Datatypes.bool), Datatypes.andb x y = Datatypes.andb y x) ->
       (forall (x y z : Datatypes.bool), Datatypes.andb x y = Datatypes.andb y x).
  Proof.
    intro h.
    intros x y z.
    rewrite_fst (Control.hyp @h).
    reflexivity.
  Qed.

  Goal (forall (x y : nat), x + y = y + x) -> (forall (x y z : nat), (x + y) = (y + x)).
  Proof.
    intro h.
    intros x y z.
    rewrite_fst (Control.hyp @h).
    reflexivity.
  Qed.

  (* Ltac2 rewriter (hyp : ident) := *)
  (*   let eq_hyp := Control.hyp hyp in *)
  (*   let eq_hyp_type := Constr.type eq_hyp in *)
  (*   (* Fails if there is not exactly one goal under focus. *) *)
  (*   let goal := Control.goal () in  *)
  (*   let (holey_pf, holey_eq_hyp) := to_holes eq_hyp eq_hyp_type in *)
  (*   let (_, y) := match! holey_eq_hyp with (@eq _ ?x ?y) => (x,y) end in *)
  (*   let goal_subterm := (all_closed_subterms goal) in *)
  (*   Std.unify y goal_subterm; *)
  (*   Control.refine (fun () => '(match $holey_pf return $goal with eq_refl _ => _ end)). *)


End Rewriting.
