From Simplex Require Import Basics Relations Datatypes.

Require Import Ltac2.Ltac2.
Ltac2 Notation "ue" := unshelve econstructor.

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

Ltac2 Notation contradiction := contradiction0 ().

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
End Symmetry.

Ltac2 symmetry_lookup (r : constr) := constr:(symmetry (R:=$r)).
      
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
  Ltac2 Notation reflexivity := reflexivity().
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

Ltac2 naive () :=
  repeat (
      first
        [ destruct_intro ()|
          intro|
          progress(simpl in *)|
          ue|
          reflexivity
        ]
    ).

Ltac2 z() := try (exact _).
Ltac2 Notation "firstorder" := ltac1:(firstorder).
