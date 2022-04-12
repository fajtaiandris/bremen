(* THIS IS A GENERATED FILE *)
From Bremen.theories.physics Require Import FrequencySample Frequency Instrument SoundingObject.
From Bremen.theories.harmony Require Import Pitch.
Require Import QArith PArith List.
Import ListNotations.

Definition so1 : sounding_object := sounding_obj
    5%N [[(440.0 Hz 10.0 dB);(880 Hz 9.0 dB)];[(440.0 Hz 10.0 dB);(880 Hz 9.0 dB)]].

Definition criteria (so : sounding_object) : bool :=
  andb (maximum_one_pitch_with_instrument so trumpet)
  (lowest_frequency_within so (from_pitch C2) (from_pitch Cb4)).
Eval compute in criteria so1.