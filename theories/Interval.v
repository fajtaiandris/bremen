Require Import ZArith.
From Bremen.theories Require Export Pitch.

(*TODO find out the right names*)
Inductive interval_category : Type :=
  | perfect
  | majorminor
.

Inductive interval_quality : Type :=
  | iqual : interval_category -> Z -> interval_quality.

Definition P     := iqual perfect     0.
Definition Aug   := iqual perfect     1.
Definition Dim   := iqual perfect  (- 1).
Definition major := iqual majorminor    0.
Definition minor := iqual majorminor (- 1).
Definition aug   := iqual majorminor    1.
Definition dim   := iqual majorminor (- 2).

Definition modifier (q : interval_quality) : Z :=
  match q with 
  | iqual category modifier => modifier
  end.

Inductive interval_name : Type :=
  | iname : interval_quality -> nat -> interval_name.

(*TODO what about iname P 2 ? Also P 0*)
(*TODO ez kell?*)
Notation "! Q N" := (iname Q N) (at level 80, right associativity).

Definition size (i : interval_name) : Z :=
  match i with
  | iname q n => 
    Z.of_nat (Letter.upward_distance Letter.C (Letter.nextN Letter.C (n - 1)))
    + modifier q 
    + 12 * (Z.div (Z.of_nat n) 8)
  end.

Definition apply_upward (p : pitch) (i : interval_name) : pitch := 
  match p, i with
  | l # m ' o , iname q n =>
  (*Letter*)   Letter.nextN l (n - 1)
  (*Modifier*) # m + size i 
               - Z.of_nat (PitchClass.upward_distance (l # 0) (Letter.nextN l (n - 1) # 0))
  (*Octave*)   ' o + 0 (*TODO*)
  end.

Eval compute in apply_upward (Letter.B # 1 ' 0) (iname Aug 1).

Definition enharmonic_eq (x y : interval_name) : Prop :=
  size x = size y.