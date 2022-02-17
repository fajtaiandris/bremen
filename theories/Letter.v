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

Definition eqb (x y : letter) : bool :=
  match x, y with
  | A, A => true
  | B, B => true
  | C, C => true
  | D, D => true
  | E, E => true
  | F, F => true
  | G, G => true
  | _, _ => false
  end.

Fixpoint nextN (x : letter) (n : nat) : letter :=
  match n with
  | 0 => x
  | S n => nextN (next x) n
  end.

(*not very sophisticated*)
(*n is expected to be 6 to work properly.*)
Fixpoint next_count_rec (x y : letter) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n => if eqb (nextN x (S n)) (y)
           then (S n)
           else next_count_rec x y n
  end.

Definition next_count (x y : letter) : nat :=
  if eqb x y
  then 0
  else next_count_rec x y 6.

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

(*---------------------------------------------------------------*)

Lemma eqb_eq : forall (x y : letter), eqb x y = true -> x = y.
Proof. intros x y. unfold eqb. destruct x ; destruct y; try discriminate ; auto.
Qed.

Lemma upward_distance_xx : forall (x : letter), upward_distance x x = 0.
Proof. destruct x; try auto.
Qed.

Lemma upward_distance_0 : forall (x y : letter), 
  (upward_distance x y = 0) <-> (x = y).
Proof.
  intros.
  unfold upward_distance. unfold upward_distance_from_A. destruct y; destruct x;
     ( simpl; split; reflexivity )
  || ( simpl; unfold Pos.to_nat; unfold Pos.iter_op; simpl; split; discriminate).
Qed.

Lemma upward_distance_12 : forall (x y : letter), ~ x = y -> (upward_distance x y) = 12 - (upward_distance y x).
Proof.
intros.
unfold upward_distance. unfold upward_distance_from_A. unfold Z.to_nat. unfold Z.of_nat. unfold Pos.to_nat.
destruct x; destruct y; (simpl; contradiction) || auto.
Qed.