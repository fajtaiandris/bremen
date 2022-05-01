From Bremen.theories.structure Require Import Song.
From Bremen.theories.physics Require Import SoundingObject Time.
Require Import QArith PArith.
Require Import List.
Import ListNotations.

Inductive transcription : Type :=
  transcript : sounding_object -> song -> transcription.

Definition is_right (t : transcription) : bool :=
  match t with | transcript so song =>
  andb 
  (is_music so) 
  (*nagyjából megegyezik a hossz *)
  (andb (Nat.leb (N.to_nat (song_duration_in_sec song) * 800) (length_in_msec so))
        (Nat.leb ((length_in_msec so) * 800) (N.to_nat (song_duration_in_sec song))))
  (*az egyek hangsúlyosak*)
  (*ugyanazok a dolgok szólnak időben ugyanott*)
  end.
