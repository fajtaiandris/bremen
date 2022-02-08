Require Import ZArith.
From Bremen.theories Require Export Letter.

Inductive pitchClass : Type :=
  pitch_class : Letter.letter -> Z -> pitchClass.

Notation "L # M" := (pitch_class L M) (at level 80, right associativity).

Definition letter (x : pitchClass) : Letter.letter :=
  match x with
  | l # m => l
  end.

Definition modifier (x : pitchClass) : Z :=
  match x with
  | l # m => m
  end.

Definition upward_distance (x y : pitchClass) : nat :=
  match x, y with
  | l # m, l' # m' => Z.to_nat (Zmod (Z.of_nat (Letter.upward_distance l l') - m + m') 12)
  end.

Definition enharmonic_eq (x y : pitchClass) : Prop :=
  upward_distance (Letter.A # 0) x = upward_distance (Letter.A # 0) y.

Notation "X e= Y" := (enharmonic_eq X Y) (at level 80, right associativity).

Definition sharpen (x : pitchClass) : pitchClass :=
  match x with
  | l # m => l # m + 1
  end.

Definition flatten (x : pitchClass) : pitchClass :=
  match x with
  | l # m => l # m - 1
  end.

Definition halfstep_up (x : pitchClass) : pitchClass :=
    match x with | l # m => 
    Letter.next l # (m - Z.of_nat(upward_distance (l # 0) (Letter.next l # 0)) + 1)
  end.

(*
Definition apply_upward (p : pitchClass) (i : interval_name) : pitch := 
  match p, i with
  | l # m , iname q n =>
  (*Letter*)   nextN l (n - 1)
  (*Modifier*) # m + size i 
               - Z.of_nat (PitchClass.upward_distance (l # 0) (nextN l (n - 1) # 0))
  end.*)

