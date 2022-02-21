Require Import ZArith List.
From Bremen.theories.harmony Require Import Letter PitchClass Pitch.

Inductive chord : Type :=
   | base : pitch -> chord
   | following : chord -> pitch -> chord.

Notation ">>>> A" := (base A) (at level 80, right associativity).
Notation "A >>>> B"    := (following (A) B) (at level 81, left associativity).

Fixpoint base_pitch (c : chord) : pitch :=
  match c with
  | base x => x
  | following c x => base_pitch c
  end.

Inductive chordName : Type :=
  | Major.