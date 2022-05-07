Require Import QArith.
Require Import List.
Import ListNotations.
From Bremen.theories.physics Require Import Frequency FrequencySample.

(* represents the relative strength of the first 8 overtones to the fundamental note *)
Inductive harmonic_quality :=
  harmonics : Q -> Q -> Q -> Q -> Q -> Q -> Q -> Q -> harmonic_quality.

Example h1 : harmonic_quality := harmonics 0.9 0.8 0.7 0.6 0.5 0.4 0.3 0.2.

Definition l0 := [0.0; 0.0; 0.0; 0.0; 0.0; 0.0; 0.0; 0.0].

Definition hempty := harmonics 0.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0.

Definition from_list (l : list Q) : option harmonic_quality :=
  match l with
  | h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: h7 :: h8 :: rest => match rest with
    | [] => Some (harmonics h1 h2 h3 h4 h5 h6 h7 h8)
    | _ => None
    end
  | _ => None
  end.

(* helper *)
Definition T (a : bool) : bool :=
  a.

(* helper *)
Definition eqb (x y : harmonic_quality) : bool :=
  match x, y with
  | harmonics x1 x2 x3 x4 x5 x6 x7 x8,
    harmonics y1 y2 y3 y4 y5 y6 y7 y8 =>
    forallb T
    [(Qeq_bool x1 y1); (Qeq_bool x2 y2); (Qeq_bool x3 y3); (Qeq_bool x4 y4); (Qeq_bool x5 y5); (Qeq_bool x6 y6); (Qeq_bool x7 y7); (Qeq_bool x8 y8)]
  end.

(* helper *)
Definition list_replace (l : list Q) (index : nat) (new : Q) : list Q :=
  concat [(firstn (index - 2) l); [new]; (skipn (index - 1) l)].

Example fa1 := 10 Hz 10 dB.
Example fa2 := 30 Hz 8 dB.

Eval compute in match fa1, fa2 with
  | x1 Hz y1 dB, x2 Hz y2 dB => match (harmonic_number x1 x2) with
    | None => None
    | Some n => Some (list_replace l0 (N.to_nat n) (Qdiv y2 y1))
    end
  end.

(* this is a helper for from_frequency_sample *)
Fixpoint func1 (fs : frequency_sample) (l : list Q) (fund : frequency_amplitude) : list Q :=
  match fs with
  | [] => l
  | h :: rest => func1 rest (match fund, h with
    | x1 Hz y1 dB, x2 Hz y2 dB => 
      match (harmonic_number x1 x2) with
      | None => l (* unimportant case *)
      | Some n => (list_replace l (N.to_nat n) (Qdiv y2 y1))
      end
    end) fund
  end.

Definition from_frequency_sample (s : frequency_sample) : option harmonic_quality :=
  if negb (maximum_one_pitch s) then None else 
  match s with
  | [] => None
  | fund :: harms => from_list (func1 harms l0 fund)
  end.

Eval compute in from_frequency_sample s1.

(* represents harmonic samples at given frequencies.*)
Inductive complex_harmonic_quality :=
  complex_harmonics : list (Q * harmonic_quality) -> complex_harmonic_quality.

(* well formedness szabályok kellenek *)

Definition ch1 : complex_harmonic_quality := 
  complex_harmonics [
    (1000.0, harmonics 0.9 0.8 0.7 0.6 0.5 0.4 0.3 0.2);
    (2000.0, harmonics 0.9 0.8 0.5 0.7 0.5 0.4 0.3 0.3)
  ].

Inductive instrument :=
  instrument_of : complex_harmonic_quality -> instrument.

Fixpoint harmonic_quality_for_frequency (l : list (Q * harmonic_quality)) (f : frequency) : harmonic_quality :=
  match l with
  | (freq, hq) :: rest => match (Qle_bool f freq) with
    | true => hq
    | false => harmonic_quality_for_frequency rest f
    end
  | [] => hempty
  end.

Definition inst_harmonic_quality_for_frequency (i : instrument) (f : frequency) : harmonic_quality :=
  match i with
  | instrument_of (complex_harmonics chl) => harmonic_quality_for_frequency chl f
  end.

Definition matthew_caws_voice := instrument_of ch1.
Definition trumpet := instrument_of 
  (complex_harmonics [
    (20000.0, harmonics 0.9 0.2 0.0 0.0 0.0 0.0 0.0 0.0)
  ]).


Definition maximum_one_pitch_with_instrument (i : instrument) (s : frequency_sample) : bool :=
  andb (maximum_one_pitch s)
  (match s with
    | [] => true
    | (f Hz a dB) :: harms =>
      match (from_frequency_sample s) with
      | None => false
      | Some sample_harmonics => 
      (eqb sample_harmonics (inst_harmonic_quality_for_frequency i f))
      end
    end)
.



