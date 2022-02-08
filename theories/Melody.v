Require Import ZArith List.
From Bremen.theories Require Import Letter PitchClass Pitch Chord Key Note.

Inductive melody : Type :=
  melody_of : list note -> melody.