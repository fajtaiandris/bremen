Require Import ZArith List.
From Bremen.theories Require Import Letter PitchClass Pitch.

Inductive chord : Type :=
   | base : pitch -> chord
   | following : chord -> pitch -> chord.

Notation ">>>> A" := (base A) (at level 80, right associativity).
Notation "A >>>> B"    := (following (A) B) (at level 81, left associativity).

Inductive chordName : Type :=
  | Major.