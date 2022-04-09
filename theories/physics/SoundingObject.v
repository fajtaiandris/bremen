Require Import QArith PArith.
Require Import List.
Import ListNotations.

Inductive frequency_amplitude : Type :=
  freq_amp : Q -> Q -> frequency_amplitude.

Notation "A 'hz' - B 'dB'" := (freq_amp A B) (at level 85, right associativity).

Inductive frequency_sample : Type :=
  sample : list frequency_amplitude -> frequency_sample.

Inductive sounding_object : Type :=
  sounding_obj : nat -> list frequency_sample -> sounding_object.

(* DEFINÍCIÓK:
 - egy hang szól a mintában
 - végig egy hang szól a sounding objectben
 - az adott hangot ez az adott hangszer adja
*)

(* Noodling is not music *)
Definition is_music (so : sounding_object) : bool :=
(*
 - van benne egyértelmű hangsúly, legalább két ütem egy
 - van benne zenei hang
*)
true.


Definition is_pop_song (so : sounding_object) : bool :=
(*
Teljesülnie kell:
 - stabilan ütemekre bontható
 - van benne tetőpont, refrén, valami
*)
true.

Example s1 : frequency_sample := sample [(440.0 hz - 13 dB); (880.0 hz - 9.0 dB)].