Require Corelib.Init.Datatypes.
Inductive eq {A : Type} (a : A) : forall x : A, Prop
  := eq_refl : eq a a.
                                      
Require Import Ltac2.Ltac2.
Ltac2 case_eq () :=
  match Constr.Unsafe.kind '@eq with
  | Constr.Unsafe.Ind i  _ => Constr.Unsafe.case i
  | _ => Control.zero Not_found
  end.

Goal
  forall H :
  (forall (x y : Datatypes.bool), eq (Datatypes.andb x y) (Datatypes.andb y x)),
  (forall (x y : Datatypes.bool), eq (Datatypes.andb x y) (Datatypes.andb y x)).
Proof.
  intros h x y.
  Set Debug "backtrace".
  let _ := Constr.Unsafe.make
       (Constr.Unsafe.Case
          (match Constr.Unsafe.kind '@eq with
              | Constr.Unsafe.Ind i  _ => Constr.Unsafe.case i
              | _ => Control.zero Not_found
              end)
          ( '(fun abc
                  (_ : eq (Datatypes.andb x y)
                         (Datatypes.andb y x)) =>
                eq abc (Datatypes.andb y x)), Constr.Binder.Relevant)
          Constr.Unsafe.NoInvert
          '(h y x)
          [| '_  |])
       in ().
Abort.
