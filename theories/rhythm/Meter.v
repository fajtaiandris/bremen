From Bremen.theories.rhythm Require Import Division Duration.
From Bremen.theories.structure Require Import MelodicPart.
From Bremen.theories.harmony Require Import Note.
Require Import PArith.

Inductive meter : Type :=
  | meter_from : positive -> division -> meter.


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