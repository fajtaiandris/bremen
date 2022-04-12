From Bremen.theories.rhythm Require Import Duration.
From Bremen.theories.physics Require Import Dynamics.
From Bremen.theories.structure Require Import MelodicPart.
Require Import List.
Import ListNotations.

Inductive harmonic_part : Type :=
  | first_melodic_part_at_start : melodic_part -> harmonic_part
  | melodic_part_at_start       : melodic_part -> harmonic_part -> harmonic_part
  | melodic_part_later          : duration -> melodic_part -> harmonic_part -> harmonic_part.

Definition harmonic_part1 := 
  melodic_part_later (Whole_) melody1 (
  melodic_part_at_start melody1 (
  first_melodic_part_at_start (melody1))).


Fixpoint part_durations (h : harmonic_part) : list duration :=
  match h with
  | first_melodic_part_at_start x => match duration_of x with
    | None => []
    | Some z => [z]
    end
  | melodic_part_at_start x y => match duration_of x with
    | None => part_durations y
    | Some z => concat [[z]; part_durations y]
    end
  | melodic_part_later d x y =>  match duration_of x with
    | None => part_durations y
    | Some z => concat [[tie z d]; part_durations y]
    end
  end.

Fixpoint max_duration (dl : list duration) (default : duration ): duration :=
  match dl with
  | [] => default
  | x :: rest => match max_duration rest default with | y =>
    if longer_equal x y then x else y end
  end.

Definition duration_of (h : harmonic_part) : duration :=
  max_duration (part_durations h) (Quarter_).

Eval compute in duration_of harmonic_part1.
