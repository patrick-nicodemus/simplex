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
