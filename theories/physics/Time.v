From Bremen.theories.rhythm Require Import Division Duration Meter.
From Bremen.theories.structure Require Import Song.
Require Import QArith PArith.

Definition Q_of_nat (n : nat) : Q :=
  Z.of_nat n # 1.

Definition sec_division (x : division) (m : meter) (bpm : nat) : Q :=
  match m with
  | meter_from n d => 
    (60 / (Q_of_nat bpm )) /
    ((Q_of_nat (Division.fraction_inverse x) ) /
      (Q_of_nat (Division.fraction_inverse d)))
  end.

Fixpoint sec_duration (x : duration) (m : meter) (bpm : nat) : Q :=
  match x with
  | dur d => (sec_division d m bpm)
  | tie a b => (sec_duration a m bpm) + (sec_duration b m bpm)
  end.

(*TODO*)
Definition song_duration_in_sec (s : song) : N :=
  match s with | song_ bpm s1 ss =>
   match ( sec_duration (duration_of s) (meter_from 4 (Quarter)) bpm) with
    | a # b => match a with
      | Zneg _ => 0
      | Z0 => 0
      | Zpos ap => (N.modulo (N.of_nat (Pos.to_nat ap)) (N.of_nat (Pos.to_nat b)))
      end
    end
  end.
(*
Eval compute in song_duration_in_sec s1.*)