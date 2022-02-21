From Bremen.theories.rhythm Require Import Division Duration.
Require Import PArith.

Inductive meter : Type :=
  | meter_from : positive -> division -> meter.


(*TODO azt jelenti az ütemmutató, hogy hol kell hangsúlyozni a dallamot,
  , tehát egy dallamra meg lehet hívni az ütemmutatót, hogy behangsúlyozza.*)

(*TODO ugyanígy meg is lehet állapítani egy dallamról az ütemmutatót*)
