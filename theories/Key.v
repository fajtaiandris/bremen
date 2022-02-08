Require Import ZArith List.
From Bremen.theories Require Export Chord.

Inductive key_quality : Type :=
| major
| minor.

Inductive key : Type :=
  key_of : pitchClass -> key_quality -> key.

Check key_of (Letter.G # 0) major.

(*TODO*)
Definition pitches (k : key) : chord :=
  pitches nil.