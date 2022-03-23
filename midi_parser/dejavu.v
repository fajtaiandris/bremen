Require Import ZArith.
From Bremen.theories.harmony Require Import Letter PitchClass Pitch Chord Key Note.
From Bremen.theories.rhythm Require Import Duration Division Meter.
From Bremen.theories.physics Require Import Dynamics.
From Bremen.theories.structure Require Import MelodicPart.
Require Import List.
Import ListNotations.

Definition melody1 := [
( note_of (C # 1 ' 4) (tie (Sixteenth_) (Sixteenth_)) (mf))
; ( note_of (C # 1 ' 4) (tie (Sixteenth_) (Sixteenth_)) (emphasized))
; ( note_of (C # 1 ' 4) (tie (tie (tie (Sixteenth_) (Sixteenth_)) (Sixteenth_)) (Sixteenth_)) (mf))
; ( note_of (B # 0 ' 3) (tie (tie (tie (Sixteenth_) (Sixteenth_)) (Sixteenth_)) (Sixteenth_)) (mf))
; ( note_of (C # 1 ' 4) (tie (Sixteenth_) (Sixteenth_)) (mf))
; ( note_of (A # 0 ' 3) (tie (Sixteenth_) (Sixteenth_)) (mf))
; ( note_of (A # 0 ' 3) (tie (Sixteenth_) (Sixteenth_)) (mf))
; ( note_of (C # 1 ' 4) (tie (tie (tie (tie (tie (tie (tie (Sixteenth_) (Sixteenth_)) (Sixteenth_)) (Sixteenth_)) (Sixteenth_)) (Sixteenth_)) (Sixteenth_)) (Sixteenth_)) (emphasized))
; ( note_of (A # 0 ' 3) (tie (tie (tie (Sixteenth_) (Sixteenth_)) (Sixteenth_)) (Sixteenth_)) (mf))
; ( rest_of (tie (Sixteenth_) (Sixteenth_)) (mf))
; ( note_of (E # 0 ' 3) (tie (Sixteenth_) (Sixteenth_)) (mf))
; ( note_of (C # 1 ' 4) (tie (Sixteenth_) (Sixteenth_)) (emphasized))
; ( note_of (C # 1 ' 4) (tie (tie (tie (Sixteenth_) (Sixteenth_)) (Sixteenth_)) (Sixteenth_)) (mf))
].

Definition constant_meter := constant_meter_in_the_middle melody1.
Eval compute in constant_meter.