From Bremen.theories.structure Require Import Song.
Require Import QArith.

Inductive frequency_amplitude : Type :=
  freq_amp : Q -> Q -> frequency_amplitude.

Notation "A 'hz' - B 'dB'" := (freq_amp A B) (at level 85, right associativity).

Inductive frequency_sample : Type :=
  sample : list frequency_amplitude -> frequency_sample.

Inductive sounding_object : Type :=
  sounding_obj : nat -> list frequency_sample -> sounding_object.

(* EXAMPLE: The trumpet plays a note in the C2 - C3 register *)



Inductive signal_transcription : Type :=
  transcription : sounding_object -> song -> signal_transcription.

(* wellformedness rules *)