Require Import ZArith List.
From Bremen.theories.harmony Require Import Letter PitchClass Pitch Chord.
From Bremen.theories.physics Require Import Dynamics.
From Bremen.theories.rhythm Require Import Duration.

(*TODO nagyon átgondolni a restet is*)
Inductive note : Type :=
  | note_of : pitch -> duration -> dynamic -> note
  | rest_of : duration -> dynamic -> note.

