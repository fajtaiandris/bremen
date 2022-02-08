Require Import ZArith.
From Bremen.theories Require Import Letter PitchClass Pitch.

(*TODO find out the right names*)
Inductive intervalCategory : Type :=
  | perfect
  | majorminor
.

Inductive intervalQuality : Type :=
  | iqual : intervalCategory -> Z -> intervalQuality.

Definition P     := iqual perfect     0.
(*TODO constantok helyett notation?*)
Notation "'Perfect'" := (iqual perfect 0) (at level 80, right associativity).
Definition Aug   := iqual perfect     1.
Definition Dim   := iqual perfect  (- 1).
Definition major := iqual majorminor    0.
Definition minor := iqual majorminor (- 1).
Definition aug   := iqual majorminor    1.
Definition dim   := iqual majorminor (- 2).

Definition modifier (q : intervalQuality) : Z :=
  match q with 
  | iqual category modifier => modifier
  end.

Inductive intervalName : Type :=
  | iname : intervalQuality -> nat -> intervalName.

(*TODO what about iname P 2 ? Also P 0*)
(*TODO ez kell?*)
Notation "! Q N" := (iname Q N) (at level 80, right associativity).

Definition size (i : intervalName) : Z :=
  match i with
  | iname q n => 
    Z.of_nat (Letter.upward_distance C (nextN C (n - 1)))
    + modifier q 
    + 12 * (Z.div (Z.of_nat n) 8)
  end.

Definition between_pitchClasses (x y : pitchClass) : intervalName :=
  match x, y with
  | l1 # m1 , l2 # m2 =>
    iname (iqual perfect 0) (Letter.upward_distance l1 l2)
  end.

Eval compute in between_pitchClasses (C # 0) (G # 0).

(*
Definition apply_to_pitchClass (p : pitchClass) (i : interval_name) : pitchClass := 
  match p, i with
  | l # m , iname q n =>
  (*Letter*)   nextN l (n - 1)
  (*Modifier*) # m + (size i - size (iname
            (*   - Z.of_nat (PitchClass.upward_distance (l # 0) (nextN l (n - 1) # 0))*)
  end.
Eval compute in apply_to_pitchClass (A # 0) (iname major 18).

Definition apply_to_pitch (p : pitch) (i : interval_name) : pitch := 
  match p, i with
  | l # m ' o , iname q n =>
  (*Letter*)   nextN l (n - 1)
  (*Modifier*) # m + size i 
               - Z.of_nat (PitchClass.upward_distance (l # 0) (nextN l (n - 1) # 0))
  (*Octave*)   ' o + 0 (*TODO*)
  end.

Eval compute in apply_to_pitch (B # 1 ' 0) (iname Aug 1).
*)
Definition enharmonic_eq (x y : intervalName) : Prop :=
  size x = size y.