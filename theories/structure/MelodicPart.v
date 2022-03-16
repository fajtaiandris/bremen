Require Import ZArith.
From Bremen.theories.harmony Require Import Letter PitchClass Pitch Chord Key Note.
From Bremen.theories.rhythm Require Import Duration Division.
From Bremen.theories.physics Require Import Dynamics.
Require Import List.
Import ListNotations.

(*=melody*)
Inductive melodic_part : Type :=
  | melodic_part_of : note -> melodic_part
  | longer : note -> melodic_part -> melodic_part.

Inductive melodic_part2 : Type :=
  melody : list note -> melodic_part2.

Definition note_list (m : melodic_part2) : list note :=
  match m with
  | melody l => l
  end.

Fixpoint duration_of (m : melodic_part) : duration :=
  match m with
  | melodic_part_of n => Note.duration_of n
  | longer n remaining => tie (Note.duration_of n) (duration_of remaining)
  end.


(*TODO*)
(*
Definition is_variation (a av : melodic_part) : Prop :=
  .
*)
Definition A_note := note_of (A # 0 ' 4) (Quarter_) (emphasized).
Definition C_note := note_of (C # 0 ' 5) (Quarter_) (mf).
Definition E_note := note_of (E # 0 ' 5) (Quarter_) (mf).
Definition quarter_rest := rest_of (Quarter_) (f).

Definition ex_melody := [ E_note ; quarter_rest ; A_note ; C_note ; A_note ; A_note ; E_note ; E_note ; E_note] .

Fixpoint size (m : list note) : nat :=
  match m with
  | [] => 0
  | _ :: remaining => S ( size remaining )
  end.

Fixpoint first_measure (m : list note) : list note :=
  match m with
  | [] => []
  | n1 :: n1_remaining => match n1_remaining with
    | [] => [n1]
    | n2 :: n2_remaining => match (Note.emphasized n2) with
      | Some true => [n1]
      | _ => (concat [[n1] ; (first_measure n1_remaining)])
      end
    end
  end.

Fixpoint beat_ones (m : list note) : list bool :=
  match m with
  | [] => []
  | n1 :: n1_remaining => match (Note.emphasized n1) with 
    | Some true => concat [ [true] ; (beat_ones n1_remaining)]
    | _         => concat [ [false] ; (beat_ones n1_remaining)]
    end
  end.

Fixpoint measures (m : list note) (bl : list bool) : list (list note) :=
  match m, bl with
  | [], [] => [[]]
  | n1 :: n1_remaining, true :: bl_remaining => 
  (* ütem egy, tehát a legfrissebb ütemhez konkatenáljuk és létrehozunk egy új üres ütemet *)
    match (hd [] (measures n1_remaining bl_remaining)) with
    | bar => [] :: (n1 :: bar) :: (skipn 1 (measures n1_remaining bl_remaining))
    end
  | n1 :: n1_remaining, false :: bl_remaining =>
  (* nem ütem egy, tehát a legfrissebb ütemhez konkatenáljuk *)
    match (hd [] (measures n1_remaining bl_remaining)) with
    | bar => (n1 :: bar) :: (skipn 1 (measures n1_remaining bl_remaining))
    end
  | _, _ => [[]]
  end.


Definition example_melody1 := 
  longer quarter_rest (
  longer C_note (
  longer A_note (
  longer quarter_rest (
  longer C_note (
  longer A_note (
  melodic_part_of E_note
  )))))).

Definition example_melody2 := 
  longer quarter_rest (
  longer C_note (
  longer A_note (
  longer quarter_rest (
  longer C_note (
  melodic_part_of A_note
  ))))).

Definition example_melody3 := 
  longer quarter_rest(
  melodic_part_of E_note).

Definition example_melody4 := 
  longer quarter_rest (
  longer C_note (
  longer A_note (
  longer quarter_rest (
  melodic_part_of C_note
)))).

(*Az elejéről leszedi azokat a hangokat, amik még beleférnek a megadott hosszba*)
Fixpoint head (m : melodic_part) (d : duration) : option melodic_part :=
  match (longer_equal d (duration_of m)) with
  | true => Some m
  | false => match m with
    | melodic_part_of n  => None
    | longer n remaining => head remaining d
    end
  end.



Fixpoint first_note (m : melodic_part) : note :=
  match m with
  | melodic_part_of n => n
  | longer _ remaining => first_note remaining
  end.

Fixpoint second_note (m : melodic_part) : option note :=
  match m with
  | melodic_part_of n => None
  | longer second_n (melodic_part_of n) => Some second_n
  | longer _ remaining => second_note remaining
  end.