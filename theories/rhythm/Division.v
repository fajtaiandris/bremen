Require Import QArith PArith.

Inductive division : Type :=
    | whole
    | half : division -> division
    | third : division -> division
  .

Notation "'Half'"     := ((half whole)) (at level 80, right associativity).
Notation "'Quarter'"  := ((half (half whole))) (at level 80, right associativity).
Notation "'Eights'"   := ((half (half (half whole)))) (at level 80, right associativity).
Notation "'QTriplet'"  := ((third (half (half whole)))) (at level 80, right associativity).
Notation "'ETriplet'" := ((third (half (half (half whole))))) (at level 80, right associativity).

(*This is would not be needed if Q.eqb existed to write eqb_division.*)
Fixpoint fraction_inverse (x : division) : nat := 
  match x with
  | whole => 1
  | half d => 2 * fraction_inverse d
  | third d => 3 * fraction_inverse d
  end.

Fixpoint fraction (x : division) : Q :=
  match x with
  | whole => 1
  | half d => ((fraction d) / 2)
  | third d => ((fraction d) / 3)
  end.

