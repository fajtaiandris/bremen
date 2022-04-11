From Bremen.theories.harmony Require Import Pitch.
From Bremen.theories.physics Require Import A440.
Require Import QArith ZArith PArith.
From Coq.PArith Require Import Pnat.
From Coq.NArith Require Import BinNatDef.
Require Import List.
Import ListNotations.

Definition frequency := Q.

Definition A_constant := 440.0.

(*could be computed, but the stdlib doesnt include functinos for Q^Q*)
Definition from_pitch (p : pitch) : Q :=
  nth (Z.to_nat (distance_C0 p)) pitches_from_C0 0.0.

Eval compute in from_pitch Cb4.

(* This mess could be avoided with modulo defined over Q *)
(* also this causes stack overflow *)
Definition is_harmonic (f1 f2 : Q) : bool :=
  match (Qdiv f2 f1) with 
  | a # b =>
    match a with
    | Zneg _ => false
    | Z0 => false
    | Zpos ap => N.eqb 0 (N.modulo (N.of_nat (Pos.to_nat ap)) (N.of_nat (Pos.to_nat b)))
    end
  end.

(* based on is_harmonic *)
Definition harmonic_number (f1 f2 : Q) : option N :=
  match (Qdiv f2 f1) with 
  | a # b =>
    match a with
    | Zneg _ => None
    | Z0 => None
    | Zpos ap => match (N.of_nat (Pos.to_nat ap)), (N.of_nat (Pos.to_nat b)) with
      | x, y => if negb (N.eqb 0 (N.modulo x y)) then None (*isn't even a harmonic*)
                else Some (N.div x y)
      end
    end
  end.

Eval compute in harmonic_number 10.1 80.8.
Eval compute in is_harmonic 40.0 80.0.