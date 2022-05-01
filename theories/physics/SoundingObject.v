Require Import QArith PArith.
Require Import List.
From Bremen.theories.physics Require Import Frequency FrequencySample Instrument.
From Bremen.theories.harmony Require Import Pitch Letter.
Import ListNotations.

Definition sampling_rate := N.

Inductive sounding_object : Type :=
  sounding_obj : sampling_rate -> list frequency_sample -> sounding_object.

Example so1 := sounding_obj 10%N [[]; [(5Hz 1.0dB); (10Hz 0.9dB); (15Hz 0.2dB)]].
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

Fixpoint sum_strength (ls: list frequency_sample) : Q :=
  match ls with
  | [] => 0.0
  | s :: ss => Qplus (strength s) (sum_strength ss)
  end.

Definition average_strength (so : sounding_object) : Q :=
  match so with
  | sounding_obj rate samples => Qdiv (sum_strength samples) (Z.of_nat (length samples) # 1)
  end.

Definition above_average_strength (so: sounding_object) (s : frequency_sample) : bool :=
  Qle_bool (average_strength so) (strength s).

Definition is_music (so : sounding_object) : bool :=
  andb(
    andb
      (*Van hossza*)
      (Nat.ltb 3000 (length_in_msec so))
      (*Van benne hangsúly*)
      (match so with
        | sounding_obj rate samples => (existsb (above_average_strength so) samples)
      end))
  (*van benne zenei minta*)
  (match so with
     | sounding_obj rate samples => (existsb is_musical samples)
   end)
  .

Definition is_pop_song (so : sounding_object) : bool :=
  andb
    (is_music so)
    (**)
    (true)
.


(* EXAMPLE: The trumpet plays a note in the C2 - Cb4 register *)
Definition example (so : sounding_object) : bool :=
  andb (maximum_one_pitch_with_instrument so trumpet)
  (lowest_frequency_within so (from_pitch C2) (from_pitch Cb4)).
