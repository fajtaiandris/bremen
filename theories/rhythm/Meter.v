From Bremen.theories.rhythm Require Import Division Duration.
From Bremen.theories.structure Require Import MelodicPart.
From Bremen.theories.harmony Require Import Note.
Require Import PArith QArith.
Require Import List.
Import ListNotations.

Inductive meter : Type :=
  | meter_from : positive -> division -> meter.

Eval compute in Qplus (Division.fraction (QTriplet)) (Division.fraction (Eighth)) .

Definition meter_plus (m1 m2 : meter) : meter :=
  match m1, m2 with
  | meter_from p1 div1 , meter_from p2 div2 =>
    match half_count div1, third_count div1, half_count div2, third_count div2  with
    | h1, t1, h2, t2 =>
      match (Nat.eqb h1 h2), (Nat.eqb t1 t2) with
      | true, true => meter_from (Pplus p1 p2) div1
      | false, false =>
        match (Nat.ltb h2 h1), (Nat.ltb t2 t1) with
        | true, true => meter_from (
          p1 + p2 * (Pos.of_nat (Nat.pow 3 (t1 - t2))) * (Pos.of_nat (Nat.pow 2 (h1 - h2)))) div1
        | true, false => meter_from (
          p1 * (Pos.of_nat (Nat.pow 3 (h2 - h1))) + p2 * (Pos.of_nat (Nat.pow 2 (h1 - h2))))
          (nth_third t2 (nth_half h1 whole))
        | false, true => meter_from (
          p2 * (Pos.of_nat (Nat.pow 3 (h1 - h2))) + p1 * (Pos.of_nat (Nat.pow 2 (h2 - h1))))
          (nth_third t1 (nth_half h2 whole))
        | false, false => meter_from (
          p2 + p1 * (Pos.of_nat (Nat.pow 3 (t2 - t1))) * (Pos.of_nat (Nat.pow 2 (h2 - h1)))) div2
        end
      | true, false =>
        match (Nat.ltb t2 t1) with
        | true => meter_from (p1 + p2 * (Pos.of_nat (Nat.pow 3 (t1 - t2)))) div1
        | false => meter_from (p2 + p1 * (Pos.of_nat (Nat.pow 3 (t2 - t1)))) div2
        end
      | false, true =>
        match (Nat.ltb h2 h1) with
        | true => meter_from (p1 + p2 * (Pos.of_nat (Nat.pow 2 (h1 - h2)))) div1
        | false => meter_from (p2 + p1 * (Pos.of_nat (Nat.pow 2 (h2 - h1)))) div2
        end
      end
    end
  end.

Fixpoint meter_from_duration (d : duration) : meter :=
  match d with
  | dur div => meter_from 1 div
  | tie dur1 dur2 =>
    (meter_plus (meter_from_duration dur1) (meter_from_duration dur2))
  end.

Eval compute in meter_from_duration (tie (Quarter_) (Quarter_)).

Fixpoint measure_duration (measure : list note) : option duration :=
  match measure with
  | [] => None
  | n1 :: n1_remaining =>
    match (measure_duration n1_remaining) with
    | None => Some (duration_of n1)
    | Some remaining_duration => Some (tie (duration_of n1) remaining_duration)
    end
  end.

Definition measure_meter (measure : list note) : option meter :=
  match measure_duration measure with
  | None => None
  | Some d => Some (meter_from_duration d)
  end.

Eval compute in measure_meter (hd [] (measures melody1 (beat_ones melody1))).


Fixpoint meters_for_measures (ml : list (list note)) : list meter :=
  match ml with
  | [] => []
  | bar1 :: remaining =>  match (measure_meter bar1) with 
    | None => meters_for_measures remaining
    | Some meter1 => meter1 :: (meters_for_measures remaining)
    end
  end.

Definition whats_the_meter (melody : list note) : list meter :=
  meters_for_measures (measures melody (beat_ones melody)).

Definition eq_meter (m1 m2 : meter) : bool :=
  match m1, m2 with
  | meter_from p1 d1 , meter_from p2 d2 => andb (Pos.eqb p1 p2) (Division.eqb d1 d2)
  end.

Definition constant_meter (melody : list note) : option meter :=
  match whats_the_meter melody with
  | [] => None
  | meters => match hd (meter_from 1 (Quarter)) meters with
    | first_meter => if forallb (eq_meter first_meter) meters then Some first_meter else None
    end
  end.

Definition constant_meter_in_the_middle (melody : list note) : option meter :=
  match whats_the_meter melody with
  | [] => None
  | meters => match skipn 1 (firstn ((length meters) - 1) meters) with
    | middle_meters => match hd (meter_from 1 (Quarter)) middle_meters with
      | first_meter => if forallb (eq_meter first_meter) middle_meters then Some first_meter else None
      end
    end
  end.
