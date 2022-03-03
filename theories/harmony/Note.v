Require Import ZArith List.
From Bremen.theories.harmony Require Import Letter PitchClass Pitch Chord.
From Bremen.theories.physics Require Import Dynamics.
From Bremen.theories.rhythm Require Import Duration.

(*TODO nagyon átgondolni a restet is*)
Inductive note : Type :=
  | note_of : pitch -> duration -> dynamic -> note
  | rest_of : duration -> dynamic -> note.

Definition pitch_class_of (n : note) : option pitchClass :=
  match n with
  | note_of (Pitch.p pc _) _ _ => Some pc
  | rest_of _ _ => None
  end.

Definition emphasized (n : note) : option bool := 
  match n with
  | note_of _ _ emphasized => Some true
  | note_of _ _ _ => Some false
  | rest_of _ _ => None
  end.

Definition duration_of (n : note) : duration :=
  match n with
  | note_of _ d _ => d
  | rest_of d _ => d
  end.