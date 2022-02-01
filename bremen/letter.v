Module Letter.

Inductive letter : Type := | A | B | C | D | E | F | G.

Definition eqB (x y : letter) : bool :=
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

Definition nextL (x : letter) : letter :=
  match x with
  | A => B
  | B => C
  | C => D
  | D => E
  | E => F
  | F => G
  | G => A
  end.

Definition upward_closer (x : letter) : bool :=
  match x with
  | A => false
  | B => true
  | C => false
  | D => false
  | E => true
  | F => false
  | G => false
  end.

Definition upward_distance_to_next (x : letter) : nat :=
  if upward_closer(x) then 1 else 2.

(*Igazából ez adódik az upward_distance_to_next és nextből*)
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

Require Import ZArith.

Definition upward_distance (x y : letter) : nat :=
  Z.to_nat(
    Zmod
    (Zminus 
      (Z.of_nat (upward_distance_from_A y))
      (Z.of_nat (upward_distance_from_A x)))
    12)
.

(* Valahogy így lenne szép...
Fixpoint upward_distance (x y : letter) : nat :=
  match x with
  | y => 0
  | z => upward_distance_to_next z + upward_distance (nextL z) y
  end.

*)

Lemma letter1 : forall (x y : letter), (upward_distance x y) = 0 <-> (x = y).
Proof.
  intros.
  unfold upward_distance. unfold upward_distance_from_A. destruct y.
  * destruct x.
  ** simpl. split. reflexivity. reflexivity.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  * destruct x.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. split. reflexivity. reflexivity.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  * destruct x.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. split. reflexivity. reflexivity.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  * destruct x.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. split. reflexivity. reflexivity.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  * destruct x.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. split. reflexivity. reflexivity.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  * destruct x.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. split. reflexivity. reflexivity.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  * destruct x.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. unfold Pos.to_nat. unfold Pos.iter_op. simpl. split. discriminate. discriminate.
  ** simpl. split. reflexivity. reflexivity.
Qed.

Lemma letter2 : forall (x y : letter), (upward_distance x y) > 0 <-> ~ x = y.
Proof.
intros. unfold upward_distance. unfold upward_distance_from_A.
destruct x. destruct y. 
* simpl. split.
  ** unfold gt. unfold not.

Admitted.

Compute upward_distance A A.

Lemma letter3 : forall (x y : letter), ~ x = y -> (upward_distance x y) = 12 - (upward_distance y x).
Proof.
intros.
unfold upward_distance. unfold upward_distance_from_A. unfold Z.to_nat. unfold Z.of_nat. unfold Pos.to_nat.
destruct x.
  * destruct y. 
    simpl. contradiction. auto. auto. auto. auto. auto. auto.
  * destruct y.
    simpl. auto. contradiction. auto. auto. auto. auto. auto.
  * destruct y.
    simpl. auto. auto. contradiction. auto. auto. auto. auto.
  * destruct y.
    simpl. auto. auto. auto. contradiction. auto. auto. auto.
  * destruct y.
    simpl. auto. auto. auto. auto. contradiction. auto. auto.
  * destruct y.
    simpl. auto. auto. auto. auto. auto. contradiction. auto.
  * destruct y.
    simpl. auto. auto. auto. auto. auto. auto. contradiction.
Qed.

Lemma letter4 : forall (x y : letter), x = y -> upward_distance x y = upward_distance y x.
Proof.
intros. rewrite -> H. reflexivity.
Qed.

