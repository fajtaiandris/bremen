Require Import ZArith.
From Bremen.theories.harmony Require Import Letter PitchClass Pitch Chord Key Note.
From Bremen.theories.rhythm Require Import Duration.
From Bremen.theories.physics Require Import Dynamics.

(*=melody*)
Inductive melodic_part : Type :=
  | melodic_part_of : note -> melodic_part
  | longer : note -> melodic_part -> melodic_part.

Definition example_note := note_of (A # 0 ' 4) (Quarter_) (mf).
Definition example_rest := rest_of (Half_) (f).

Definition example_melody1 := longer example_note (
                              longer example_rest (
                              longer example_note (
                              melodic_part_of example_note))).

Definition example_melody2 := longer example_note (
                              melodic_part_of example_note).