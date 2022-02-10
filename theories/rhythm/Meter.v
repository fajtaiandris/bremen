Require Import QArith PArith.
From Bremen.theories.rhythm Require Import Division Duration.

Inductive meter : Type :=
  | meter_from : positive -> division -> meter.

Definition Q_of_nat (n : nat) : Q :=
  Z.of_nat n # 1.

Definition sec_division (x : division) (m : meter) (bpm : nat) : Q :=
  match m with
  | meter_from n d => 
    (60 / (Q_of_nat bpm )) /
    ((Q_of_nat (Division.fraction_inverse x) ) /
      (Q_of_nat (Division.fraction_inverse d)))
  end.

(*TODO*)
Fixpoint sec_duration (x : duration) (m : meter) (bpm : nat) : Q :=
  match x with
  | dur d => (sec_division d m bpm)
  | tie a b => (sec_duration a m bpm) + (sec_duration b m bpm)
  end.

Eval compute in sec_duration (DottedEighth_) (meter_from 3 (Quarter)) 60.
