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
