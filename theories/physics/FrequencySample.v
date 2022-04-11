Require Import QArith PArith.
Require Import List.
From Bremen.theories.physics Require Import Frequency.
Import ListNotations.

(* measured in decibel *)
Definition amplitude := Q.

Inductive frequency_amplitude :=
  freq_amp : frequency -> amplitude -> frequency_amplitude.

Notation "A 'Hz' B 'dB'" := (freq_amp A B) (at level 85, right associativity).

Definition frequency_sample := list frequency_amplitude.

Example s1 : frequency_sample := [(10.0 Hz 10 dB); (20.0 Hz 9.0 dB); (30.0 Hz 2 dB)].

Definition is_harmonic (a b : frequency_amplitude) : bool :=
  match a, b with
  | f1 Hz _ dB , f2 Hz _ dB => is_harmonic f1 f2
  end.

(* Noise and overlapping harmonics are not considered, but should be. *)
Definition maximum_one_pitch (s : frequency_sample) : bool :=
  match s with
    | [] => true
    | a :: b => forallb (is_harmonic a) b
  end
.

Definition lowest_frequency_within (f1 f2 : frequency) (s : frequency_sample) : bool :=
  match s with
  | [] => true
  | (f Hz _ dB) :: _ => andb (Qle_bool f1 f) (Qle_bool f f2)
  end.

Eval compute in lowest_frequency_within 9.0 8.0 s1.
