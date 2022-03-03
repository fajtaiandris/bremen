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

Eval compute in first_emphasis example_melody2.

Definition meter_of (m : melodic_part) : option meter := 
(* megkeresem az első hangsúlyt, megnézem milyen messze van a második hangsúly.
  ilyen távolságokra a dal végéig kell, hogy legyen hangsúly*)
  match (first_emphasis m) with
  | None => None
  | Some no_time =>
    match m with
    | melodic_part_of n => Some (*Egy hang alapján mi az ütemmutató?*)
    | longer n remaining => (*meg kell keresni a következő emphasist*)
  | Some some_time d => (*meg kell keresni a következő emphasist*)
  end.
