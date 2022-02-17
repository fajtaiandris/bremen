From Bremen.theories Require Import Interval PitchClass Pitch AbstractChord Chord Letter.
Require Import ZArith.

Inductive intervalStructure : Type :=
  | first : intervalName -> intervalStructure
  | next  : intervalStructure -> intervalName -> intervalStructure.

Notation "-- A" := (first A) (at level 80, right associativity).
Notation "A -- B"    := (next (A) B) (at level 81, left associativity).

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

Fixpoint from_abstract_chord (ac : abstractChord) : intervalStructure :=
  match ac with
  | AbstractChord.base pc => first (P1_)
  | AbstractChord.following ac' pc =>
    next (from_abstract_chord ac') (between_pitch_classes (base_pitch_class ac') pc)
  end.

Inductive directionalIntervalStructure : Type :=
  | first_di : directionalIntervalName -> directionalIntervalStructure
  | next_di : directionalIntervalStructure -> directionalIntervalName -> directionalIntervalStructure.

Notation "--- A" := (first_di A) (at level 80, right associativity).
Notation "A --- B"    := (next_di (A) B) (at level 81, left associativity).

Definition example_cadence_line := --- upward (P1_) --- upward (P5_) --- downward(m2_) --- upward (P1_).

Fixpoint from_chord (c : chord) : directionalIntervalStructure :=
  match c with
  | Chord.base x => first_di (upward (P1_))
  | Chord.following c' x =>
    next_di (from_chord c') (between_pitches (base_pitch c) x)
  end.

Fixpoint directionally_apply_to_pitch (p : pitch) (dis : directionalIntervalStructure) : chord :=
  match dis with
  | first_di i => base (Interval.directionally_apply_to_pitch p i)
  | next_di dis i => 
  following (directionally_apply_to_pitch p dis) 
            (Interval.directionally_apply_to_pitch p i)
  end.

Eval compute in directionally_apply_to_pitch (C # 0 ' 1) example_cadence_line.