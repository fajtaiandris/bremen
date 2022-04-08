Require Import QArith.
Require Import List.
Import ListNotations.

(* represents the relative strength of the first 8 overtones to the fundamental note *)
Inductive harmonic_quality :=
  harmonics : Q -> Q -> Q -> Q -> Q -> Q -> Q -> Q -> harmonic_quality.

(* represents harmonic samples at given frequencies.
Between the frequency range of two samples, the higher frequency's sample
will be assumed to represent the instruments harmonic quality. *)
Inductive complex_harmonic_quality :=
  complex_harmonics : list (Q * harmonic_quality) -> complex_harmonic_quality.

(* well formedness szabályok kellenek *)

Definition ch1 : complex_harmonic_quality := 
  complex_harmonics [
    (1000.0, harmonics 0.9 0.8 0.7 0.6 0.5 0.4 0.3 0.2);
    (1000.0, harmonics 0.9 0.8 0.5 0.7 0.5 0.4 0.3 0.3)
  ].

Inductive instrument :=
  instrument_of : complex_harmonic_quality -> instrument.

Definition trumpet := instrument_of ch1.
Definition matthew_caws_voice := instrument_of ch1.