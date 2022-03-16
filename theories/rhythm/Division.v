Require Import QArith PArith Nat.

Inductive division : Type :=
    | whole
    | half : division -> division
    | third : division -> division
  .

Notation "'Half'"     := ((half whole)) (at level 80, right associativity).
Notation "'Quarter'"  := ((half (half whole))) (at level 80, right associativity).
Notation "'Eighth'"   := ((half (half (half whole)))) (at level 80, right associativity).
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

Fixpoint half_count (x : division) : nat :=
  match x with
  | whole => 0
  | half d => S (half_count d)
  | third d => half_count d
  end.

Fixpoint third_count (x : division) : nat :=
  match x with
  | whole => 0
  | third d => S (third_count d)
  | half d => third_count d
  end.

Fixpoint nth_half (h : nat) (base : division) : division :=
  match h with
  | O => base
  | S n => half (nth_half n base )
  end.

Fixpoint nth_third (h : nat) (base : division) : division :=
  match h with
  | O => base
  | S n => third (nth_third n base )
  end.
