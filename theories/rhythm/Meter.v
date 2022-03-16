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
        (*A true, false és a false true sor hibás, példa lent*)
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

(*EZ ITT ROSSZUL MŰKÖDIK, bejelöltem, hol lesz a hiba*)
Eval compute in meter_plus (meter_from 1 (QTriplet)) (meter_from 1 (Eighth)).

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

Eval compute in measure_meter (hd [] (measures ex_melody (beat_ones ex_melody))).


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

Eval compute in whats_the_meter ex_melody.

(*TODO azt jelenti az ütemmutató, hogy hol kell hangsúlyozni a dallamot,
  , tehát egy dallamra meg lehet hívni az ütemmutatót, hogy behangsúlyozza.*)

Fixpoint first_emphasis (m : melodic_part) : option optionalDuration :=
  match m with
  | melodic_part_of n =>
    match (emphasized n) with
    | Some true => Some (no_time)
    | _ => None
    end
  | longer n remaining =>
    match first_emphasis remaining with
    | Some d => Some d
    | None =>
      match (emphasized n) with
      | Some true => Some (some_time (MelodicPart.duration_of remaining))
      | _ => None
      end
    end
  end.
(*
Definition second_emphasis (m : melodic_part) : option duration :=
  match (first_emphasis m) with
  | None => None
  | Some no_time =>
    match first_emphasis( head m (duration_of (first_note m))) with
    | None => None
    | Some no_time => (*Az első két hang hangsúlyos, az első két hang hosszát kell összeadni*)
      match (second_note m) with (*A mintaillesztés csak a kicsomagolás miatt kell*)
      | None => None
      | Some second => Some (tie
           (duration_of (first_note m))
           (duration_of (second)))
    | Some some_time => (*Az első hang hangsúlyos, aztán később van még egy hangsúly*)
    *)
(*
    match m with
    | melodic_part_of n => None
    | longer n remaining =>
      match (first_emphasis remaining) with
      | None => None
      | Some no_time => match remaining with
        | melodic_part_of second_note => Some (tie (duration_of n) (duration_of second_note))
        | longer second_note still_remaining => Some (tie (duration_of n) (duration_of second_note))
        end
      | Some (some_time d) => Some (tie (tie (duration_of n) d) (duration_of n))
      end
    end
  | Some (some_time d) =>
    match m with
    | melodic_part_of n => None
    | longer n remaining =>
      match (first_emphasis remaining) with
      | None => None
      | Some no_time => match remaining with
        | melodic_part_of second_note => Some (tie (d) (duration_of second_note))
        | longer second_note still_remaining => Some (tie (d) (duration_of second_note))
        end
      | Some (some_time d2) => Some (tie (tie d d2) (duration_of n))
      end
    end
  end.
*)

Eval compute in first_emphasis example_melody2.
(*

Fixpoint bars (m : melodic_part) : list melodic_part :=
  match first_emphasis m with
  | None => m :: nil
  | Some no_time => (*első hang hangsúlyos, hozzá kell adni az első ütemet és rekurzívan hívni*)
    match m with
    | melodic_part_of n => m :: nil
    | longer n remaining => 
  | Some some_time d => (*le kell vágni a dallam elejét*) head d m
  end.


Definition meter_of (m : melodic_part) : option meter := 
(* megkeresem az első hangsúlyt, megnézem milyen messze van a második hangsúly.
  ilyen távolságokra a dal végéig kell, hogy legyen hangsúly*)
  match (first_emphasis m) with
  | None => None
  | Some no_time =>
    match m with
    | melodic_part_of n => Some (*Egy hang alapján mi az ütemmutató?*)
    | longer n remaining =>
    (*meg kell keresni a következő emphasist*)
      match (first_emphasis remaining) with
      |
  | Some some_time d => (*meg kell keresni a következő emphasist*)
  end.
*)