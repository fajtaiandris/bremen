From Bremen.theories.structure Require Import Song.
From Bremen.theories.physics Require Import SoundingObject.
Require Import QArith PArith.
Require Import List.
Import ListNotations.

Inductive transcription : Type :=
  transcript : sounding_object -> song -> transcription.

Definition is_right (t : transcription) : bool :=
(* Teljesülnie kell:
   - a sounding object zene
   - egyezik a hossz
   - ugyanazok a dolgok szólnak időben ugyanott (kb ??)
   - az egyek hangsúlyosabbak, mint a többi dolog
*)
  true.

(* EXAMPLE: The trumpet plays a note in the C2 - C3 register *)
