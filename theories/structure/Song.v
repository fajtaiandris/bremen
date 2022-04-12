From Bremen.theories.structure Require Import HarmonicPart.
From Bremen.theories.rhythm Require Import Duration.
From Bremen.theories.physics Require Import Instrument.
Require Import List.
Import ListNotations.

(* A section consist of a main part and the rest of the parts *)
Inductive section :=
  | sect : (instrument * harmonic_part) -> list (instrument * harmonic_part) -> section.


Fixpoint part_durations (parts : list (instrument * harmonic_part)) : list duration :=
  match parts with
    | [] => []
    | (inst, part) :: rest => concat [[duration_of part]; part_durations rest]
  end.

Definition section_duration (s : section) : duration :=
  match s with
  | sect (inst, h) ss => match (duration_of h), (max_duration (part_durations ss) (Quarter_)) with
    | a, b => if longer_equal a b then a else b
    end
  end.

Fixpoint section_durations (sl : list section) : list duration :=
  match sl with
  | [] => []
  | x :: xs => concat [[section_duration x]; section_durations xs]
  end.

Fixpoint durations_sum (dl : list duration) (default : duration) : duration :=
  match dl with
  | [] => default (*irrelevant case *)
  | x :: [] => x
  | x :: y :: [] => tie x y
  | x :: xs => tie x (durations_sum (xs) default)
  end.

(* A song consists of an AVERAGE bpm and sections. The first section is a workaround to avoid empty section list. *)
Inductive song :=
  | song_ : nat -> section -> list section -> song.

Definition duration_of (s : song) : duration :=
  match s with
  | song_ bpm s1 ss => tie (section_duration s1) (durations_sum (section_durations ss) (Quarter_))
  end.

Example section1 : section := sect (trumpet, harmonic_part1) [].
Example section2 : section := sect (trumpet, harmonic_part1) [(matthew_caws_voice, harmonic_part1)].
Example s1 : song := song_ 120 section1 [section2].