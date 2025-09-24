From Simplex Require Import Basics Relations Datatypes.

Require Import Ltac2.Ltac2.

Module Open_Constr_tc.
  Import Init.
  (* otc is a shorthand notation for "open_constr, elaborated *with typeclass resolution* enabled" *)
  Ltac2 Notation "otc" t(preterm) :=
    Constr.Pretype.pretype
      Constr.Pretype.Flags.open_constr_flags_with_tc
      Constr.Pretype.expected_without_type_constraint
      t.
End Open_Constr_tc.
Export Open_Constr_tc.

Ltac2 refine0 (x : preterm) :=
  Control.enter
    (fun () =>
       Control.refine (fun () =>
       let g := Control.goal () in
       Constr.Pretype.pretype
         Constr.Pretype.Flags.open_constr_flags_with_tc
         (Constr.Pretype.expected_oftype g)
         x
    )).

Ltac2 Notation "refine" x(preterm) := refine0 x.

Ltac2 contradiction0 () :=
  match! goal with
  | [ h : ?c |- ?g ] =>
      unify $c empty;
      let h := Control.hyp h in
      exact (match $h return $g with end)
  end.

Ltac2 Abbreviation contradiction := contradiction0 ().

Ltac2 reflexivity () :=
  try (exact (@reflexive _ _ _ _));
  try reflexivity;
  fail.

Ltac2 failwith s := Control.zero (Tactic_failure (Some (Message.of_string s))).

Ltac2 hyp_type (h : ident) :=
  Constr.type (Control.hyp h).

Module Symmetry.
    Ltac2 sym_pf (pf : constr) (typ : constr) : constr :=
    let rec helper pf typ (depth : int) : constr :=
      match Constr.Unsafe.kind typ with
      | Constr.Unsafe.Prod b con =>
          let name := Constr.Binder.name b in
          let btype := Constr.Binder.type b in
          match name with
          | Some ident =>
              Constr.in_context ident btype
                (fun () => let c := Control.hyp ident in
                        let typ' := Constr.Unsafe.substnl [c] depth con in
                        Control.refine (fun () => (helper constr:($pf $c) typ' depth)))
          | None => helper '($pf _) con depth
          end
      | _ =>
          match! typ with
          | ?r ?x ?y => constr:(@symmetry _ $r _ $x $y $pf)
          end
      end
    in
    helper pf typ 0.
    (* let pf' := helper pf typ 0 in *)
    (* Std.eval_red pf'. *)

  (** typ is forall x1 ... xn, R t1 t2; pf : typ. Returns (pf', typ')
      where typ' = forall x1,... xn and pf' : typ'. *)
  (* Ltac2 sym_pf (pf : constr) (typ : constr) : constr * constr := *)
  (*   let rec helper pf typ : constr * constr := *)
  (*     match Constr.Unsafe.kind typ with *)
  (*     | Constr.Unsafe.Prod b con => *)
  (*         let name := Constr.Binder.name b in *)
  (*         let btype := Constr.Binder.type b in *)
  (*         let pf_term := match name with *)
  (*                        | Some ident => *)
  (*                            Constr.in_context ident btype *)
  (*                              (fun () => let c := Control.hyp ident in exact ($pf $c)) *)
  (*                        | None => '($pf _) *)
  (*                        end *)
  (*         in  *)
  (*         let (pf', typ') := helper pf_term con in *)
  (*         (Constr.Unsafe.make (Constr.Unsafe.Lambda b pf'), *)
  (*           Constr.Unsafe.make (Constr.Unsafe.Prod b typ')) *)
  (*     | _ => (Message.print (Message.of_constr typ); *)
  (*           match! typ with *)
  (*           | ?r ?x ?y => *)
  (*               (Message.print (Message.of_constr r); *)
  (*                Message.print (Message.of_constr x); *)
  (*                Message.print (Message.of_constr y); *)
  (*                ('(@symmetry _ $r _ $x $y $pf), constr:($r $y $x))) *)
  (*           end) *)
  (*     end *)
  (*   in *)
  (*   let (pf, typ) := helper pf typ in *)
  (*   let pf := Constr.Unsafe.check (Std.eval_red pf) in *)
  (*   let typ := Constr.Unsafe.check typ in *)
  (*   match pf with *)
  (*   | Val pf => match typ with *)
  (*              | Val typ => (pf,typ) *)
  (*              | Err e => Control.zero e *)
  (*              end *)
  (*   | Err e => Control.zero e *)
  (*   end. *)
End Symmetry.

(* Ltac2 term_symmetry (t : constr) := *)
(*   let rec helper t args := *)
(*     match Constr.Unsafe.kind t with *)
(*     | Constr.Unsafe.Prod b con => Constr.Unsafe.make (Constr.Unsafe.Prod b (helper con)) *)
(*     | _ => match! t with *)
(*           | ?r ?x ?y => *)
(*               let t1 := constr:($r $y $x) in *)
(*               let sym := constr:(symmetry (R:=$r) $x $y) in *)
(*           end  *)
(*     end *)
(*   in *)
(*   match Constr.Unsafe.check (helper t) with *)
(*   | Val t => t *)
(*   | Err e => Control.zero e *)
(*   end. *)

Ltac2 symmetry_lookup (r : constr) := constr:(symmetry (R:=$r)).
      
(* Ltac2 under_binders (tac : constr -> constr option) (t : constr) := *)
(*   let t' := tac t in *)
(*   match t' with *)
(*   | Some t' => t' *)
(*   | None => *)
(*       match Constr.Unsafe.kind t with *)
(*       | Constr.Unsafe.Lambda b con => t *)
(*       | _ => t *)
(*       end *)
(*   end. *)

From Ltac2 Require Import Printf.
Ltac2 symmetry0 (cl : Std.clause) : unit :=
  match cl with
  | { Std.on_hyps := on_hyps; Std.on_concl := on_concl} =>
      (match on_hyps with
       | Some hyps =>
           List.iter
             (fun (ident, _, hyp_loc_flag) =>
                match hyp_loc_flag with
                | Std.InHyp | Std.InHypTypeOnly =>
                let t0 := Control.hyp ident in
                let t1 := Constr.type t0 in
                (* (Message.print (Message.of_constr t0); *)
                (*  Message.print (Message.of_constr t1)); *)
                let a := Symmetry.sym_pf t0 t1 in
                Std.clear [ident]; Std.pose (Some ident) a
                | Std.InHypValueOnly => failwith "Not implemented"
                end
             ) hyps
       | None => Control.zero Not_found
       end);
      match on_concl with
      | Std.AllOccurrences =>
          match! goal with
          | [|- ?r ?x ?y] =>
              refine (@symmetry _ $r _ $y $x _)
          end
      | Std.AllOccurrencesBut (_int_list) => Control.zero Not_found
      | Std.NoOccurrences => ()
      | Std.OnlyOccurrences (_int_list) => Control.zero Not_found
      end
  end.

Module Notations.
  Ltac2 Abbreviation reflexivity := reflexivity().
  Ltac2 Notation "symmetry" cl(opt(clause))
    :=
    let cl := (Notations.default_on_concl cl) in
    Control.plus (fun () => symmetry0 cl)
      (fun _ => Std.symmetry cl).
End Notations.
Export Notations.

Ltac2 destruct_intro () :=
  match! goal with
  | [ |- forall a, _ ] => intro fresh; destruct fresh
  end.

Ltac2 naive
  () :=
  repeat (
      first
        [ destruct_intro ()|
          intro|
          progress(simpl in *)|
          unshelve econstructor|
          reflexivity
        ]
    ).
