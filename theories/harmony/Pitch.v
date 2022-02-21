Require Import ZArith.
From Bremen.theories.harmony Require Import Letter PitchClass.

Inductive pitch : Set :=
  p : pitchClass -> nat -> pitch.

Notation "PC ' O" := (p PC O) (at level 85, right associativity).

Example Cb4 := (C # - 1) ' 4.

Definition class (x : pitch) : pitchClass :=
  match x with
  | pc ' o => pc
  end.

Definition octave (x : pitch) : nat :=
  match x with
  | pc ' o => o
  end.

Definition sharpen (x : pitch) : pitch :=
  sharpen (class x) ' (octave x).

Definition flatten (x : pitch) : pitch :=
  flatten (class x) ' (octave x).

(*Does not work for pitches below C0, (Cb0, Cbb0, ..)*)
Definition distance_C0 (x : pitch) : Z :=
 Z.of_nat(PitchClass.upward_distance (C # 0) (class x)) + (Z.of_nat(octave x) * 12).

Definition enharmonic_eq (x y : pitch) : Prop :=
  distance_C0 x = distance_C0 y.

(*TODO átnevezni e=-re*)
Notation "X ee= Y" := (enharmonic_eq X Y) (at level 90, right associativity).

Definition halfstep_up (x : pitch) : pitch :=
  match x with
  | B # m ' o => halfstep_up (B # m) ' o + 1
  | l # m ' o => halfstep_up (l # m) ' o
  end.

Notation "> X" := (halfstep_up X) (at level 90, right associativity).

Definition wholestep_up (x : pitch) : pitch :=
  sharpen (> x).

Notation ">> X" := (wholestep_up X) (at level 90, right associativity).
