Require Import ZArith.
From Bremen.theories.harmony Require Import Letter PitchClass Pitch Chord Key Note.
From Bremen.theories.rhythm Require Import Duration.
From Bremen.theories.physics Require Import Dynamics.

(*=melody*)
Inductive melodic_part : Type :=
  | melodic_part_of : note -> melodic_part
  | longer : note -> melodic_part -> melodic_part.

Fixpoint duration_of (m : melodic_part) : duration :=
  match m with
  | melodic_part_of n => Note.duration_of n
  | longer n remaining => tie (Note.duration_of n) (duration_of remaining)
  end.


(*TODO*)
(*
Definition is_variation (a av : melodic_part) : Prop :=
  .
*)
Definition A_note := note_of (A # 0 ' 4) (Quarter_) (emphasized).
Definition C_note := note_of (C # 0 ' 5) (Quarter_) (mf).
Definition E_note := note_of (E # 0 ' 5) (Quarter_) (mf).
Definition quarter_rest := rest_of (Quarter_) (f).

Definition example_melody1 := 
  longer quarter_rest (
  longer C_note (
  longer A_note (
  longer quarter_rest (
  longer C_note (
  longer A_note (
  melodic_part_of E_note
  )))))).

Definition example_melody2 := 
  longer quarter_rest (
  longer C_note (
  longer A_note (
  longer quarter_rest (
  longer C_note (
  melodic_part_of A_note
  ))))).

Definition example_melody3 := 
  longer quarter_rest(
  melodic_part_of E_note).