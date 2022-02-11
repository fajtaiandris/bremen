From Bremen.theories Require Import Interval PitchClass Pitch AbstractChord Chord Letter.
Require Import ZArith.

Inductive intervalStructure : Type :=
  | first : intervalName -> intervalStructure
  | next  : intervalStructure -> intervalName -> intervalStructure.

Notation "-- A" := (first A) (at level 80, right associativity).
Notation "A -- B"    := (next (A) B) (at level 81, left associativity).

(*TODO P1-et nem kellene beírni*)
Definition major_scale := -- P1_ -- M2_ -- M3_ -- P4_ -- P5_ -- M6_ -- M7_ -- P8_ .
Definition natural_minor_scale := -- P1_ -- M2_ -- m3_ -- P4_ -- P5_ -- m6_ -- m7_ -- P8_ .

Definition major_triad := -- P1_ -- M3_ -- P5_ .

Fixpoint apply_to_pitch_class (pc : pitchClass) (is : intervalStructure) : abstractChord :=
  match is with
  | first i => AbstractChord.base (Interval.apply_to_pitch_class pc i)
  | next is i => AbstractChord.following (apply_to_pitch_class pc is) (Interval.apply_to_pitch_class pc i)
  end.

Fixpoint apply_to_pitch (p : pitch) (is : intervalStructure) : chord :=
  match is with
  | first i => base (Interval.apply_to_pitch p i)
  | next is i => following (apply_to_pitch p is) (Interval.apply_to_pitch p i)
  end.

(*TODO
Fixpoint from_abstract_chord (ac : abstractChord) : intervalStructure :=
  match ac with
  | base pc => first *)

Eval compute in apply_to_pitch_class (A # 0) major_triad.