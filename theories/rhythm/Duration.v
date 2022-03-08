Require Import QArith.
From Bremen.theories.rhythm Require Import Division.

Inductive duration : Type :=
  | dur : division -> duration
  | tie : duration -> duration -> duration.

Notation "'Whole_'"    := (dur whole) (at level 80, right associativity).
Notation "'Half_'"     := (dur (half whole)) (at level 80, right associativity).
Notation "'Quarter_'"  := (dur (half (half whole))) (at level 80, right associativity).
Notation "'Eighth_'"   := (dur (half (half (half whole)))) (at level 80, right associativity).
Notation "'Sixteenth_'"   := (dur (half (half (half (half whole))))) (at level 80, right associativity).
Notation "'QTriplet_'"  := (dur (third (half (half whole)))) (at level 80, right associativity).
Notation "'ETriplet_'" := (dur (third (half (half (half whole))))) (at level 80, right associativity).

Notation "'DottedHalf_'"     := (tie (Half_) (Quarter_)) (at level 80, right associativity).
Notation "'DottedQuarter_'"     := (tie (Quarter_) (Eighth_)) (at level 80, right associativity).
Notation "'DottedEighth_'"     := (tie (Eighth_) (Sixteenth_)) (at level 80, right associativity).

Fixpoint fraction (x : duration) : Q :=
  match x with
  | dur d   => Division.fraction d
  | tie a b => fraction a + fraction b
  end.

Definition same_fraction (x y : duration) : Prop :=
  fraction x = fraction y.

Definition longer_equal (x y : duration) : bool :=
   Qle_bool (fraction y) (fraction x).

(*Az eltelt idő reprezentálására*)
Inductive optionalDuration : Type :=
  | no_time
  | some_time : duration -> optionalDuration.

