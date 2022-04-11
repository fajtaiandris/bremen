From Bremen.theories.structure Require Import Song.
From Bremen.theories.physics Require Import SoundingObject.
Require Import QArith PArith.
Require Import List.
Import ListNotations.

Inductive transcription : Type :=
  transcript : sounding_object -> song -> transcription.


Definition is_right (t : transcription) : bool :=
  match t with | transcript so song =>
  is_music so
  end.
(* Teljesülnie kell:
   - a sounding object zene
   - egyezik a hossz
   - ugyanazok a dolgok szólnak időben ugyanott (kb ??)
   - az egyek hangsúlyosabbak, mint a többi dolog
*)

