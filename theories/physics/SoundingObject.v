Require Import QArith PArith.
Require Import List.
From Bremen.theories.physics Require Import Frequency FrequencySample Instrument.
From Bremen.theories.harmony Require Import Pitch Letter.
Import ListNotations.

Definition sampling_rate := N.

Inductive sounding_object : Type :=
  sounding_obj : sampling_rate -> list frequency_sample -> sounding_object.

Example so1 := sounding_obj 10%N [s1; s1; s1; []; [(5Hz 1.0dB); (10Hz 0.9dB); (15Hz 0.2dB)]; s1].
Example so2 := sounding_obj 10%N [s1].

Definition maximum_one_pitch (s : sounding_object) : bool :=
  match s with | sounding_obj rate samples =>
    forallb maximum_one_pitch samples
  end.

Definition maximum_one_pitch_with_instrument (s : sounding_object) (i : instrument) : bool :=
  match s with | sounding_obj rate samples =>
    forallb (maximum_one_pitch_with_instrument i) samples
  end.

Definition lowest_frequency_within (s : sounding_object) (f1 f2 : frequency) : bool :=
  match s with | sounding_obj rate samples =>
    forallb (lowest_frequency_within f1 f2) samples
  end.

Eval compute in maximum_one_pitch_with_instrument so1 trumpet.
Eval compute in lowest_frequency_within so2 8.5 12.0.

(* rounded up to next integer *)
Definition length_in_msec (so : sounding_object) : nat :=
  match so with
  | sounding_obj rate samples => Nat.div (length samples * 1000) (N.to_nat rate) + 1
  end.

Eval compute in length_in_msec so2.

(* Noodling is not music *)
Definition is_music (so : sounding_object) : bool :=
  Nat.ltb 3000 (length_in_msec so).
(*
 - van benne egyértelmű hangsúly, legalább két ütem egy
 - van benne zenei hang
*)


Definition is_pop_song (so : sounding_object) : bool :=
  is_music so.
(*
Teljesülnie kell:
 - stabilan ütemekre bontható
 - van benne tetőpont, refrén, valami
*)


(* EXAMPLE: The trumpet plays a note in the C2 - Cb4 register *)
Definition example (so : sounding_object) : bool :=
  andb (maximum_one_pitch_with_instrument so trumpet)
  (lowest_frequency_within so (from_pitch C2) (from_pitch Cb4)).
