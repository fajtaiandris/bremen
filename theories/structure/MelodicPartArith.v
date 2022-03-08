Require Import QArith.
From Bremen.theories.structure Require Import MelodicPart.
From Bremen.theories.rhythm Require Import Duration.
From Bremen.theories.harmony Require Import Note.

Fixpoint tail_with_fraction (m : melodic_part) (df : Q) : option melodic_part :=
  match m with
    | melodic_part_of n => 
      match (orb (Qle_bool (fraction (duration_of n)) df ) (Qeq_bool df (fraction (duration_of n))))with
      | true => Some m
      | false => None
      end
    | longer n remaining =>
      match (orb (Qle_bool (fraction (duration_of n)) df ) (Qeq_bool df (fraction (duration_of n)))) with
      | true => tail_with_fraction remaining (Qminus df (fraction (duration_of n)))
      | false => None
      end
  end.

(*A végéről leszedi azokat a hangokat, amik még beleférnek a megadott hosszba*)
Definition tail (m : melodic_part) (d : duration) : option melodic_part :=
  tail_with_fraction m (fraction d).

Definition melody1 := 
  longer A_note (
  melodic_part_of E_note).

Eval compute in tail melody1 (Quarter_).
Eval compute in orb (Qle_bool (fraction (duration_of A_note)) (fraction(Quarter_)) ) (Qeq_bool (fraction(Quarter_)) (fraction (duration_of A_note))).