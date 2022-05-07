Require Import ZArith.
From Bremen.theories.harmony Require Import 
  Letter PitchClass Pitch Chord Interval IntervalStructure AbstractChord Note.
From Bremen.theories.rhythm Require Import Duration.
From Bremen.theories.structure Require Import MelodicPart.

Inductive triadName : Type :=
  | majorTriad : pitchClass -> triadName
  | minorTriad : pitchClass -> triadName.

Definition major_structure := -- P1_ -- M3_ -- P5_ .
Definition minor_structure := -- P1_ -- m3_ -- P5_ .

Definition triadNotes (n : triadName) : abstractChord :=
  match n with
  | majorTriad pc => apply_to_pitch_class pc major_structure
  | minorTriad pc => apply_to_pitch_class pc minor_structure
  end.

(*Very restrictive formalization, but should be enough for now.*)
Inductive tensionNote : Type :=
  | T2 | T4 | T6 | T7 .

Inductive quadratonicName : Type :=
  | quad : triadName -> tensionNote -> quadratonicName.

Definition quadratonicNotes (n : quadratonicName) : abstractChord :=
  match n with | quad triad tension => 
    following (triadNotes triad) 
      (match tension, triad with
        | T2, majorTriad pc => Interval.apply_to_pitch_class pc (M2_)
        | T4, majorTriad pc => Interval.apply_to_pitch_class pc (P4_)
        | T6, majorTriad pc => Interval.apply_to_pitch_class pc (M6_)
        | T7, majorTriad pc => Interval.apply_to_pitch_class pc (M7_)
        | T2, minorTriad pc => Interval.apply_to_pitch_class pc (M2_)
        | T4, minorTriad pc => Interval.apply_to_pitch_class pc (P4_)
        | T6, minorTriad pc => Interval.apply_to_pitch_class pc (M6_)
        | T7, minorTriad pc => Interval.apply_to_pitch_class pc (M7_)
      end)
  end.

Inductive quadratonicProgression : Type :=
  | first : quadratonicName -> duration -> quadratonicProgression
  | next : quadratonicName -> duration -> quadratonicProgression -> quadratonicProgression.
(*
(*TODO*)
Fixpoint first_quad_assumption (melody : melodic_part) (qn : quadratonicName)
  : option quadratonicName :=
  
  None.

Fixpoint first_quadratonic_of (melody : melodic_part) : option quadratonicName :=
  match melody with
  | melodic_part_of note => 
    match (pitch_class_of note) with
    | Some pc => Some (quad (majorTriad pc) T2)
    | None => None
    end
  | longer note remaining =>
    match (pitch_class_of note) with
    | Some pc => first_quad_assumption melody (quad (majorTriad pc) T2)
    | None => first_quadratonic_of remaining
    end
  end.

(*TODO*)
Fixpoint quadratonic_progression_of (melody : melodic_part) : quadratonicProgression :=
  match melody with
  | melodic_part_of note => first (quad (majorTriad (C # 0)) T2) (Whole_)
  | longer note remaining => next (quad (majorTriad (C # 0)) T2) (Whole_)
                              (quadratonic_progression_of remaining)
  end.

Eval compute in first_quadratonic_of example_melody1.
*)