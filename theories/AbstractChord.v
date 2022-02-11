From Bremen.theories Require Import PitchClass Letter.
Require Import ZArith.

Inductive abstractChord : Type :=
   | base : pitchClass -> abstractChord
   | following : abstractChord -> pitchClass -> abstractChord.


Notation ">>> A" := (base A) (at level 80, right associativity).
Notation "A >>> B"    := (following (A) B) (at level 81, left associativity).



