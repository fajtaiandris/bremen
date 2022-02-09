Require Import QArith PArith.

Inductive division : Type :=
    | whole
    | half : division -> division
    | third : division -> division
  .

Inductive duration : Type :=
  | dur : division -> duration
  | tie : duration -> duration -> duration.

Notation "'Whole'"    := (dur whole) (at level 80, right associativity).
Notation "'Half'"     := (dur (half whole)) (at level 80, right associativity).
Notation "'Quarter'"  := (dur (half (half whole))) (at level 80, right associativity).
Notation "'Eights'"   := (dur (half (half (half whole)))) (at level 80, right associativity).
Notation "'QTriplet'"  := (dur (third (half (half whole)))) (at level 80, right associativity).
Notation "'ETriplet'" := (dur (third (half (half (half whole))))) (at level 80, right associativity).

(*This is would not be needed if Q.eqb existed to write eqb_division.*)
Fixpoint division_fraction_number (x : division) : nat := 
  match x with
  | whole => 1
  | half d => 2 * division_fraction_number d
  | third d => 3 * division_fraction_number d
  end.

Definition eqb_division (x y : division) : bool :=
  Nat.eqb (division_fraction_number x) (division_fraction_number y).

Fixpoint size_of_division (x : division) : Q :=
  match x with
  | whole => 1
  | half d => ((size_of_division d) / 2)
  | third d => ((size_of_division d) / 3)
  end.

Fixpoint size_of_duration (x : duration) : Q :=
  match x with
  | dur d   => size_of_division d
  | tie a b => size_of_duration a + size_of_duration b
  end.

Definition same_size (x y : duration) : Prop :=
  size_of_duration x = size_of_duration y.

Inductive meter : Type :=
  | meter_from : positive -> division -> meter.

(*TODO innen folytatni. txt-ben leírtam.
Definition length_of_division (x : division) (m : meter) (bpm : nat) :=
  match m with
  | meter_from n d => Q.multi (size_of_division x) (division_fraction_number d)
  end.*)
