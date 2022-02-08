Require Import ZArith.

Inductive letter : Type := | A | B | C | D | E | F | G.

Definition next (x : letter) : letter :=
  match x with
  | A => B
  | B => C
  | C => D
  | D => E
  | E => F
  | F => G
  | G => A
  end.

Fixpoint nextN (x : letter) (n : nat) : letter :=
  match n with
  | 0 => x
  | S n => nextN (next x) n
  end.

Definition upward_distance_from_A (x : letter) : nat :=
  match x with
  | A => 0
  | B => 2
  | C => 3
  | D => 5
  | E => 7
  | F => 8
  | G => 10
  end.

Definition upward_distance (x y : letter) : nat :=
  Z.to_nat(
    Zmod
    (Zminus 
      (Z.of_nat (upward_distance_from_A y))
      (Z.of_nat (upward_distance_from_A x)))
    12)
.
