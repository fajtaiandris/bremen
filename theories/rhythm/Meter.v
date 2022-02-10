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
Definition sec_duration (x : duration) (m : meter) (bpm : nat) : Q :=
  0.1
  .

