Require Import ZArith List.
From Bremen.theories Require Import Letter PitchClass Pitch Chord Rhythm Dynamics.

(*TODO add dynamic quality, nagyon átgondolni a restet is*)
Inductive note : Type :=
  | note_of : pitch -> duration -> dynamic -> note
  | rest_of : duration -> dynamic -> note.
