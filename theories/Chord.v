Require Import ZArith List.
From Bremen.theories Require Export Pitch.

(*TODO listával valahogy*)

Inductive abstractChord : Type :=
  pitchClasses : list pitchClass -> abstractChord.

Inductive chord : Type :=
  pitches : list pitch -> chord.

Check pitches ((Letter.A # 0 ' 1) :: (Letter.C # 0 ' 2) :: (Letter.E # 0 ' 2) :: nil).

(*TODO*)
Inductive chordName : Type :=
  | Major.