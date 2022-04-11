From Bremen.theories.structure Require Import HarmonicPart.
From Bremen.theories.physics Require Import Instrument.

(* A section consist of a main part and the rest of the parts *)
Inductive section :=
  | sect : (instrument * harmonic_part) -> list (instrument * harmonic_part) -> section.

(* A song consists of an AVERAGE bpm and sections. The first section is a workaround to avoid empty section list. *)
Inductive song :=
  | song_ : nat -> section -> list section -> song.

Definition song_length_in_msec (s : song) : nat :=
  (*TODO*)
.