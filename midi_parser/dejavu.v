Require Import ZArith.
From Bremen.theories.harmony Require Import Letter PitchClass Pitch Chord Key Note.
From Bremen.theories.rhythm Require Import Duration Division Meter.
From Bremen.theories.physics Require Import Dynamics.
From Bremen.theories.structure Require Import MelodicPart.
Require Import List.
Import ListNotations.

Definition melody1 := [
( note_of (C # 1 ' 4) (dur (Quarter)) (emphasized) )
; ( note_of (B # 0 ' 3) (dur (Quarter)) (mf))
; ( rest_of (dur (Quarter)) (mf))
; ( note_of (C # 1 ' 4) (dur (Quarter)) (mf))
; ( note_of (C # 1 ' 4) (dur (Quarter)) (emphasized))
; ( note_of (C # 1 ' 4) (dur (Quarter)) (mf))
; ( note_of (B # 0 ' 3) (dur (Quarter)) (mf))
; ( note_of (C # 1 ' 4) (dur (Quarter)) (mf))
; ( note_of (A # 0 ' 3) (dur (Quarter)) (mf))
; ( note_of (A # 0 ' 3) (dur (Quarter)) (mf))
; ( note_of (C # 1 ' 4) (dur (Quarter)) (emphasized))
; ( note_of (A # 0 ' 3) (dur (Quarter)) (mf))
; ( rest_of (dur (Quarter)) (mf))
; ( note_of (E # 0 ' 3) (dur (Quarter)) (mf))
; ( note_of (C # 1 ' 4) (dur (Quarter)) (emphasized))
; ( note_of (C # 1 ' 4) (dur (Quarter)) (mf))
; ( note_of (B # 0 ' 3) (dur (Quarter)) (mf))
; ( note_of (B # 0 ' 3) (dur (Quarter)) (mf))
; ( note_of (B # 0 ' 3) (dur (Quarter)) (mf))
; ( note_of (A # 0 ' 3) (dur (Quarter)) (mf))
; ( note_of (C # 1 ' 4) (dur (Quarter)) (emphasized))
; ( note_of (F # 1 ' 3) (dur (Quarter)) (mf))
; ( rest_of (dur (Quarter)) (emphasized))
; ( note_of (B # 0 ' 3) (dur (Quarter)) (emphasized))
; ( note_of (A # 0 ' 3) (dur (Quarter)) (mf))
; ( note_of (B # 0 ' 3) (dur (Quarter)) (mf))
; ( note_of (A # 0 ' 3) (dur (Quarter)) (mf))
; ( note_of (C # 1 ' 4) (dur (Quarter)) (mf))
; ( note_of (B # 0 ' 3) (dur (Quarter)) (mf))
; ( note_of (A # 0 ' 3) (dur (Quarter)) (mf))
; ( note_of (B # 0 ' 3) (dur (Quarter)) (mf))
; ( note_of (A # 0 ' 3) (dur (Quarter)) (emphasized))
].

Definition constant_meter := constant_meter_in_the_middle melody1.
Eval compute in constant_meter.