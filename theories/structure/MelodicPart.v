Require Import ZArith.
From Bremen.theories.harmony Require Import Letter PitchClass Pitch Chord Key Note.
From Bremen.theories.rhythm Require Import Duration Division.
From Bremen.theories.physics Require Import Dynamics.
Require Import List.
Import ListNotations.

Definition melodic_part := list note.

Example A_note := note_of (A # 0 ' 4) (Quarter_) (emphasized).
Example C_note := note_of (C # 0 ' 5) (Quarter_) (mf).
Example E_note := note_of (E # 0 ' 5) (Quarter_) (mf).
Example quarter_rest := rest_of (Quarter_) (f).
Example melody1 : melodic_part :=
  [ E_note ; quarter_rest ; A_note ; C_note ; A_note ; A_note ; E_note ; E_note ; E_note] .

Fixpoint duration_of (m : melodic_part) : option duration :=
  match m with
  | [] => None
  | x :: rest => match duration_of rest with
    | None => Some (Note.duration_of x)
    | Some restd => Some (tie (Note.duration_of x) restd)
    end
  end.

Fixpoint size (m : melodic_part) : nat :=
  match m with
  | [] => 0
  | _ :: remaining => S ( size remaining )
  end.

Fixpoint first_measure (m : melodic_part) : melodic_part :=
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

Fixpoint beat_ones (m : melodic_part) : list bool :=
  match m with
  | [] => []
  | n1 :: n1_remaining => match (Note.emphasized n1) with 
    | Some true => concat [ [true] ; (beat_ones n1_remaining)]
    | _         => concat [ [false] ; (beat_ones n1_remaining)]
    end
  end.

Fixpoint measures (m : melodic_part) (bl : list bool) : list melodic_part :=
  match m, bl with
  | [], [] => []
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
  | _, _ => []
  end.

Definition whats_the_measures (m : melodic_part) :=
  measures m (beat_ones m).