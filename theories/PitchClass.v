Require Import ZArith.
From Bremen.theories Require Import Letter.

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

Lemma pitchclass1 : forall (l1 l2 : Letter.letter) (m : Z), l1 = l2 -> (l1 # m) = (l2 # m).
Proof. intros l1 l2 m. intro H. rewrite -> H. reflexivity.
Qed.
(*
Lemma pitchclass15 : forall (l1 l2 : Letter.letter) (m1 m2 : Z), (l1 # m1) = (l2 # m2) -> l1 = l2.
Proof. intros l1 l2 m1 m2. enough (l1 = l2 \/ ~ l1 = l2 ) as [H|H].
  - rewrite -> H. reflexivity.
  - 
 destruct (l1 = l2) eqn:LL. intro H. rewrite -> H. destruct (Z.eqb m1 m2) eqn:EM.
  -  destruct (Letter.eqb l1 l2) eqn:EL1L2. auto. auto.
  - destruct (Letter.eqb l1 l2) eqn:EL1L2. auto. auto.
Qed.

Lemma pitchclass2 : forall (l1 l2 : Letter.letter) (m1 m2 : Z),
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

Lemma pitchclass3 : forall (x y : pitchClass),
  eqb x y = false <->
  Nat.eqb (upward_distance x y) (12 - (upward_distance y x)) = true.
Proof.
intros x y. destruct (eqb x y) eqn:EXY. 
  * split.
  ** intro H. destruct (Nat.eqb (upward_distance x y) (12 - (upward_distance y x)) ).
  *** reflexivity.
  *** rewrite -> H. reflexivity.
  ** destruct x eqn:EX.
  *** destruct y eqn:EY. apply pitchclass15 in EXY. apply Letter.eqb_eq in EXY.
      rewrite EXY. unfold upward_distance. rewrite Letter.upward_distance_xx. simpl. 
      induction z eqn:ZZ.
  **** simpl. induction z0 eqn:ZZ0.
  *****  simpl. intro. rewrite H. reflexivity.
  *****  simpl. induction (Z.neg p) eqn:ZP.
  ******  simpl.
Admitted.

Lemma pitchclass16 : forall (l1 l2 : Letter.letter) (m1 m2 : Z), 
  upward_distance (l1 # m1) (l2 # m1) = upward_distance (l1 # m2) (l2 # m2).
Proof.
intros.
unfold upward_distance.
Admitted.

Theorem pitchclassx : forall (x y z : pitchClass),
  enharmonic_eqb x y = true <-> upward_distance z x = upward_distance z y.
Proof.
intros. split.
- unfold enharmonic_eqb.

Theorem pitchclass3 : forall (x : pitchlass), flatten (sharpen x) = x.
Theorem pitchclass4 : forall (x y : pitchlass), sharpen x = y -> flatten y = x.
Theorem pitchclass5 : forall (x y : pitchclass), upward_distance x y + 1 = upward_distance x (sharpen y).
*)