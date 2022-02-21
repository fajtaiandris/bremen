Require Import ZArith List.
From Bremen.theories.harmony Require Import Letter PitchClass Pitch Interval Chord.

Inductive key_quality : Type :=
  | majorkey
  | minorkey.

Inductive key : Type :=
  key_of : pitchClass -> key_quality -> key.

Check key_of (Letter.G # 0) majorkey.

(*
(*TODO*)
Definition pitches (k : key) : chord :=
  pitches nil.*)