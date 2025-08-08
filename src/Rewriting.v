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

  (* Inductive s1 : SProp := stt . *)
  (* Inductive s2 : SProp := stt2 . *)
  
  (* Inductive unit : Type := tt. *)
  (* Inductive unit2 : Type := tt2.   *)
  
  (* Ltac2 abc (type : constr) := *)
  (*   let f := '(fun (x : $type) => x) in *)
  (*   let b := *)
  (*         let a := Constr.Unsafe.kind f in *)
  (*         match a with *)
  (*         | Constr.Unsafe.Lambda binder _ => binder *)
  (*         | _ => Control.zero Not_found *)
  (*         end *)
  (*   in *)
  (*   Constr.Binder.relevance b. *)

  (* Goal unit. *)
  (*   if abc s1 = abc s2 then *)
  (*     Message.print (Message.of_string "Same") *)
  (*   else *)
  (*     Message.print (Message.of_string "Diff"). *)

  (** Create an evar of the given type. *)
  Ltac2 create_evar (type : constr) :=
    Constr.Pretype.pretype
      Constr.Pretype.Flags.open_constr_flags_no_tc
      (Constr.Pretype.expected_oftype type)
      preterm:(_).

  (* Ltac2 to_holes (tm : constr) (type : constr) := *)
  (*   let rec helper (tm : constr) (type : constr) (depth : int) (evars : constr list) := *)
  (*    match Constr.Unsafe.kind type with *)
  (*    | Constr.Unsafe.Prod binder type' => *)
  (*        let btype := Constr.Binder.type binder in *)
  (*        let new_evar := create_evar btype in *)
  (*       helper '($tm $new_evar) type' (Int.add depth 1) (new_evar :: evars) *)
  (*   | _ => (tm, Constr.Unsafe.substnl evars 0 type) *)

  (*    end *)
  (*    in *)
  (*   let (tm, type) := helper tm type 0 [] in *)

  (*    match Constr.Unsafe.check type with *)
  (*   | Val v => (tm, v) *)

  (*    | Err e => Control.zero e *)
  (*    end. *)
  
  (* Given a type of the form [forall x1....xn, T], *)
  (*   return a pair *)
  (*   [( [?yn;?yn-1;...;?y1], T[x1/?y1, x2/?y2,...xn/?yn] )] *)
  (*   where all the ?y_i are freshly created evars. *)

  (** Given a term [tm] of type [type], where [type] is
      of the form [forall (x1 : A1) (x2 : A2) ... (xn : An), B],
      create new metavariables ?y1 : A1, ?y2 : A2[y1/?y2],...
      and return
      (tm ?y1 ?y2 ... ?yn,
       B[x1/?y1,x2/?y2,...xn/?yn],
       [?yn;?yn-1;...?y1])
   *)
  Ltac2 to_holes (tm : constr) (type : constr)
    : constr * constr * constr list :=
    let rec helper (tm : constr) (type : constr)
          (evars : constr list) :=
    match Constr.Unsafe.kind type with
    | Constr.Unsafe.Prod binder type' =>
        (* Message.print (Message.of_constr type'); *)
        let btype := Constr.Binder.type binder in
        let new_evar := create_evar btype in
        helper '($tm $new_evar) type' (new_evar :: evars)
    | _ =>
        (* Message.print (Message.of_constr tm); *)
        (* Message.print (Message.of_constr type); *)
        (tm, Constr.Unsafe.substnl evars 0 type, evars)
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

  (* | Case (case, (constr * Binder.relevance), case_invert, constr, constr array) *)
  (** [Case case (fun u1 u2 ... un v => rettype, _) ci scrut
          [|(fun x1 x2 => t1);(fun y1 y2 y3 => t2));...|]]
      corresponds to
      [match scrut in I u1 u2 ... as v return rettype with
       | c0 _ _ x1 x2 => t1
       | c1 _ _ y1 y2 y3 => t2
       | (...)
      end].
      [ci] is of interest when [scrut] inhabits an [SProp], see comments on the type
      [case_invert] above. [case] contains a reference to the inductive type of the scrutinee.*)
   Ltac2 relevance (in_sprop : bool) :=
      if in_sprop then Constr.Binder.Irrelevant else Constr.Binder.Relevant.

   Ltac2 context_to_lambda (c : Pattern.context) (binder_type: constr): constr :=
     '(fun abc : $binder_type => 
         ltac2:(Control.refine (fun () => Pattern.instantiate c &abc))).

   Module What.
     Import Constr.Unsafe.
   Ltac2 what_is_it (tm : constr) :=
  match Constr.Unsafe.kind tm with
  | Rel (int) => "Rel"
  | Var (ident) => "Var"
  | Meta (meta) => "Meta"
  | Evar _ _ => "Evar"
  | Sort (sort) => "Sort"
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
  | Uint63 (uint63) =>"Uint"
  | Float (float) => "Float"
  | String (pstring)=> "String"
  | Array _ _ _ _  => "array"
  end.

   (** Given a type which is of the form
        (binders) I ....;
        get the inductive associated to I
    *)

   Ltac2 case_eq () :=
     match Constr.Unsafe.kind '@eq with
     | Ind i  _ => case i
     | _ => Control.zero Not_found
     end.

   Goal (forall (x y : Datatypes.bool), Datatypes.andb x y = Datatypes.andb y x) ->
        (forall (x y z : Datatypes.bool),
            Datatypes.andb x y = Datatypes.andb y x).
   Proof.
     intro h.
     intros x y z.
     Constr.Unsafe.make(
              Constr.Unsafe.Case (case_eq ())
                ( '(fun abc _ => abc = Datatypes.andb y x),
                  Constr.Binder.Relevant)
                Constr.Unsafe.NoInvert
                '(h y x)
                [| '_  |]).
     
     let t := '(
                  match (h _ _ ) in eq _ b return b = Datatypes.andb y x with
                  | eq_refl _ => _
                  end
                )
     in
     match Constr.Unsafe.kind t with
     | Case _ (c1, _) _ c2 arr => Message.print(Message.of_constr c1);
                                  Message.print(Message.of_constr c2);
                                  Message.print(Message.of_constr
                                                  (Array.get arr 0))
                                  (* Control.refine (fun ()=> t) *)
     | _ => Control.zero Not_found
     end.
     Unshelve.
     
     rewrite_fst (Control.hyp @h) false.
  Abort.

   (* Ltac2 next_step () := *)
     
   
   (* . *)

   (* Goal (forall (x y : Datatypes.bool), Datatypes.andb x y = Datatypes.andb y x) -> *)
   (*      (forall (x y z : Datatypes.bool), Datatypes.andb x y = Datatypes.andb y x). *)
   (* Proof. *)
   (*   intro h. *)
   (*   intros x y z. *)
   (*   rewrite_fst (Control.hyp @h) false. *)
   (* Abort. *)

   Ltac2 rec inductive_head (type : constr) : inductive * instance
     :=
     match Constr.Unsafe.kind type with
     | Constr.Unsafe.Lambda _ arg => inductive_head arg
     | Constr.Unsafe.LetIn _ _ arg => inductive_head arg
     | Constr.Unsafe.App hd _ =>
         match Constr.Unsafe.kind hd with
         | Constr.Unsafe.Ind inductive instance => inductive, instance
         | _ =>
             Message.print (Message.of_string (What.what_is_it hd));
             Control.zero Not_found
         end
     | _ => Control.zero Not_found
     end.

   (** Do not use! This only has use in the following functions,
       note the dummy argument _. *)
   Ltac2 print_ctx ctx :=
     Message.print (Message.of_constr (Pattern.instantiate ctx '_)).
   
   Ltac2 context_to_lambda_eq (c : Pattern.context) (binder_type: constr)
     : constr :=
     Message.print (Message.of_constr binder_type);
     '(fun (abc : $binder_type) _ => 
         ltac2:(Control.refine (fun () => Pattern.instantiate c &abc))).
   
  (* Rewrite the *first* unification of the RHS of the
     head of [tm] with the goal. *)
   Ltac2 rewrite_fst (tm : constr) (in_sprop : bool) :=
    let tm_type := Constr.type tm in
    let goal := Control.goal () in
    let (holey_pf, holey_type, _) := to_holes tm tm_type in
    (* I'm happy with the code up to here. *)
    (* Message.print (Message.of_constr holey_pf); *)
    (* Message.print (Message.of_constr holey_type); *)
    let (eqtype, _, y) :=
      match! holey_type with (@eq ?eqtype ?x ?y) => (eqtype,x,y) end in
    (* Message.print (Message.of_constr y); *)
    let (goal_ctx, _) :=
      Control.once (fun () =>
                      let (ctx, goal_subterm) := all_closed_subterms goal
                      in (ctx,Std.unify y goal_subterm))
    in
    (* Message.print (Message.of_constr holey_type); *)
    let case :=
      let (inductive, _) := inductive_head holey_type in
      Constr.Unsafe.case inductive
    in
    let zz:=context_to_lambda_eq goal_ctx eqtype in
    Message.print (Message.of_constr zz);
    Control.plus ( fun () => 
    let raw_tm := (* Constr.Unsafe.make *)(
              Constr.Unsafe.Case case
                (zz, relevance in_sprop)
                Constr.Unsafe.NoInvert
                holey_pf
                [| '(_:$goal)  |])
                  in
    ()) (fun _ => Message.print (Message.of_string "Failure.")).
    (* Control.plus (fun () => *)
    (* in *)
    (* ()) (fun _ => Message.print (Message.of_string "Failure")). *)
    (* in  *)

    (* match Constr.Unsafe.check(raw_tm ) *)
    (* with *)
    (* | Val tm => Control.refine (fun () => tm) *)
    (* | Err exn => Control.zero exn *)
    (* end) (fun _ => Message.print (Message.of_string "Failure")). *)

  Goal (forall (x y : Datatypes.bool), Datatypes.andb x y = Datatypes.andb y x) ->
       (forall (x y z : Datatypes.bool), Datatypes.andb x y = Datatypes.andb y x).
  Proof.
    intro h.
    intros x y z.
    rewrite_fst (Control.hyp @h) false.
  Abort.
  
  Ltac2 rewriter (hyp : ident) :=
    let eq_hyp := Control.hyp hyp in
    let eq_hyp_type := Constr.type eq_hyp in
    (* Fails if there is not exactly one goal under focus. *)
    let goal := Control.goal () in 
    let (holey_pf, holey_eq_hyp) := to_holes eq_hyp eq_hyp_type in
    let (_, y) := match! holey_eq_hyp with (@eq _ ?x ?y) => (x,y) end in
    let goal_subterm := (all_closed_subterms goal) in
    Std.unify y goal_subterm;
    Message.print (Message.of_constr holey_pf);    
    Control.refine (fun () => '(match $holey_pf return $goal with eq_refl _ => _ end)).


  (* Needs work. *)

  Goal (forall (x y : nat), x + y = y + x) -> (forall (x y z : nat), (x + y) = (y + x)).  
  Proof.
    intro h.
    intros x y z.
    (* Control.refine (fun () => '(match h y x as pfeq in eq _ b return eq b (y+x) with *)
    (*                               eq_refl _ => _ end)). *)
    rewriter @h.
    (* exact (eq_refl _). *)    
  Abort.

End Rewriting.
