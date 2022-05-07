Require Import ZArith.
From Bremen.theories.harmony Require Import Letter.

Inductive pitchClass : Type :=
  pitch_class : letter -> Z -> pitchClass.

Notation "L # M" := (pitch_class L M) (at level 80, right associativity).

Definition letter (x : pitchClass) : letter :=
  match x with
  | l # m => l
  end.

Definition modifier (x : pitchClass) : Z :=
  match x with
  | l # m => m
  end.

Definition upward_distance (x y : pitchClass) : nat :=
  match x, y with
  | l # m, l' # m' => Z.to_nat (Zmod (Z.of_nat (upward_distance l l') - m + m') 12)
  end.

Definition eqb (x y : pitchClass) : bool :=
  match x, y with
  | (l1 # m1), (l2 # m2) => andb (Letter.eqb l1 l2) (Z.eqb m1 m2)
  end.

Definition enharmonic_eq (x y : pitchClass) : Prop :=
  upward_distance (A # 0) x = upward_distance (A # 0) y.

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
    next l # (m - Z.of_nat(upward_distance (l # 0) (next l # 0)) + 1)
end.

Lemma same_letter_same_pitch_class : forall (l1 l2 : Letter.letter) (m : Z), l1 = l2 -> (l1 # m) = (l2 # m).
Proof. intros l1 l2 m. intro H. rewrite -> H. reflexivity.
Qed.


Lemma different_pitch_classes : forall (l1 l2 : Letter.letter) (m1 m2 : Z),
  eqb (l1 # m1) (l2 # m2) = false <-> 
  orb (Bool.eqb (Letter.eqb l1 l2) false) (Bool.eqb (Z.eqb m1 m2) false) = true.
Proof.
intros. split.
  * unfold eqb. unfold Bool.eqb. unfold andb. unfold orb. destruct (Letter.eqb l1 l2) eqn:eqL1L2.
  ** destruct (Z.eqb m1 m2). auto. auto.
  ** auto.
  * destruct (Letter.eqb l1 l2) eqn:eqL1L2.
  ** destruct (Z.eqb m1 m2) eqn:eqM1M2.
  *** simpl. rewrite -> eqL1L2. rewrite -> eqM1M2. auto.
  *** simpl. rewrite -> eqL1L2. rewrite -> eqM1M2. auto.
  ** destruct (Z.eqb m1 m2) eqn:eqM1M2.
  *** simpl. rewrite -> eqM1M2. rewrite -> eqL1L2. auto.
  *** simpl. rewrite -> eqM1M2. rewrite -> eqL1L2. auto.
Qed.

Lemma pitchclass16 : forall (l1 l2 : Letter.letter) (m1 m2 : Z), 
  upward_distance (l1 # m1) (l2 # m1) = upward_distance (l1 # m2) (l2 # m2).
Proof. Admitted.


Lemma upward_distance_12 : forall (x y : pitchClass),
  eqb x y = false <->
  Nat.eqb (upward_distance x y) (12 - (upward_distance y x)) = true.
Proof. Admitted.

Lemma upward_distance_modifier : forall (l1 l2 : Letter.letter) (m1 m2 : Z), 
  upward_distance (l1 # m1) (l2 # m1) = upward_distance (l1 # m2) (l2 # m2).
Proof. Admitted.

(* A flatten és a sharpen kapcsolatára vonatkozó állítások *)
Lemma flatten_sharpen_1 : forall (x : pitchClass), flatten (sharpen x) = x.
Proof. Admitted.

Lemma flatten_sharpen_2 : forall (x y : pitchClass), sharpen x = y -> flatten y = x.
Proof. Admitted.

Lemma upward_distance_sharpen : forall (x y : pitchClass), upward_distance x y + 1 = upward_distance x (sharpen y).
Proof. Admitted.