Require ZArith.

Module Letter.

  Import ZArith.
  Inductive letter : Type := | A | B | C | D | E | F | G.

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

(* Ezekre nincs szükség?
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
*)
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


  Definition upward_distance (x y : letter) : nat :=
    Z.to_nat(
      Zmod
      (Zminus 
        (Z.of_nat (upward_distance_from_A y))
        (Z.of_nat (upward_distance_from_A x)))
      12)
  .

  Lemma upward_distance_0 : forall (x y : letter), 
    (upward_distance x y) = 0 <-> (x = y).
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


  Lemma upward_distance_not_0 : forall (x y : letter), (0 =? (upward_distance x y)) = false <-> Letter.eqb x y = false.
  Proof.
    intros. split.
    - destruct y eqn:Ey.
      -- destruct x. auto. auto. auto. auto. auto. auto. auto.
      -- destruct x. auto. auto. auto. auto. auto. auto. auto.
      -- destruct x. auto. auto. auto. auto. auto. auto. auto.
      -- destruct x. auto. auto. auto. auto. auto. auto. auto.
      -- destruct x. auto. auto. auto. auto. auto. auto. auto.
      -- destruct x. auto. auto. auto. auto. auto. auto. auto.
      -- destruct x. auto. auto. auto. auto. auto. auto. auto.
    - unfold upward_distance. simpl. destruct x eqn:Ex.
      -- destruct y. auto. auto. auto. auto. auto. auto. auto.
      -- destruct y. auto. auto. auto. auto. auto. auto. auto.
      -- destruct y. auto. auto. auto. auto. auto. auto. auto.
      -- destruct y. auto. auto. auto. auto. auto. auto. auto.
      -- destruct y. auto. auto. auto. auto. auto. auto. auto.
      -- destruct y. auto. auto. auto. auto. auto. auto. auto.
      -- destruct y. auto. auto. auto. auto. auto. auto. auto.
Qed.

  Lemma upward_distance_12 : forall (x y : letter), ~ x = y -> (upward_distance x y) = 12 - (upward_distance y x).
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

  Lemma upward_distance_reflexivity : forall (x y : letter), x = y -> upward_distance x y = upward_distance y x.
  Proof.
  intros. rewrite -> H. reflexivity.
  Qed.

End Letter.

Module PitchClass.

Import ZArith.

Inductive pitchClass : Set :=
  pitch_class : Letter.letter -> Z -> pitchClass.

Notation "L # M" := (pitch_class L M) (at level 80, right associativity).

Definition eqb (x y : pitchClass) : bool :=
  match x, y with
  | l1 # m1, l2 # m2 => (Letter.eqb l1 l2) && (Z.eqb m1 m2)
  end.

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

Definition enharmonic_eqb (x y : pitchClass) : bool :=
  upward_distance (Letter.A # 0) x =? upward_distance (Letter.A # 0) y.

Definition sharpen (x : pitchClass) : pitchClass :=
  match x with
  | l # m => l # m + 1
  end.

Definition flatten (x : pitchClass) : pitchClass :=
  match x with
  | l # m => l # m - 1
  end.

Lemma pitchclass1 : forall (l1 l2 : Letter.letter) (m : Z), Letter.eqb l1 l2 = false -> eqb (l1 # m) (l2 # m) = false.
Proof. intros l1 l2 m. intro H. unfold eqb. unfold andb. rewrite -> H. reflexivity.
Qed.

Lemma pitchclass2 : forall (l1 l2 : Letter.letter) (m1 m2 : Z), eqb (l1 # m1) (l2 # m2) = false <-> orb (Bool.eqb (Letter.eqb l1 l2) false) (Bool.eqb (Z.eqb m1 m2) false) = true.
Proof.
intros. split.
  * unfold eqb. unfold Bool.eqb. unfold andb. unfold orb. give_up.
  * unfold not. give_up.
Admitted.

Lemma pitchclass1 : forall (x y : pitchClass), ~ x = y -> upward_distancePC x y = 12 - (upward_distancePC y x).
Proof.
intros x y. destruct x. destruct y. unfold not. 
unfold upward_distancePC.
Admitted.

Lemma pitchclass15 : forall (l1 l2 : letter) (m1 m2 : Z), 
  upward_distancePC (l1 # m1) (l2 # m1) = upward_distancePC (l1 # m2) (l2 # m2).
Proof.
intros.
unfold upward_distancePC. unfold Zminus.
Admitted.

Theorem pitchclass2 : forall (x y z : pitchClass),
  enharmonic_eqPC x y <-> upward_distancePC z x = upward_distancePC z y.
Proof.
intros.
unfold enharmonic_eqPC. split.
* destruct z. destruct l.
** 

Theorem pitchclass3 : forall (x : pitchlass), flatten (sharpen x) = x.
Theorem pitchclass4 : forall (x y : pitchlass), sharpen x = y -> flatten y = x.
Theorem pitchclass5 : forall (x y : pitchclass), upward_distance x y + 1 = upward_distance x (sharpen y).

(*-------------- PITCH ---------------*)
Inductive pitch : Set :=
  p : pitchClass -> nat -> pitch.

Notation "PC ' O" := (p PC O) (at level 85, right associativity).

Definition class (x : pitch) : pitchClass :=
  match x with
  | pc ' o => pc
  end.

Definition octave (x : pitch) : nat :=
  match x with
  | pc ' o => o
  end.

Definition sharpen (x : pitch) : pitch :=
  sharpenPC (class x) ' (octave x).

Definition flatten (x : pitch) : pitch :=
  flattenPC (class x) ' (octave x).

Definition fromC0 (x : pitch) : Z :=
 fromCPC (class x) + (Z.of_nat(octave x) * 12).

Eval compute in fromC0 (C # 0 ' 1).

Definition eqE (x y : pitch) : Prop :=
  fromC0 x = fromC0 y.

Notation "X e= Y" := (eqE X Y) (at level 90, right associativity).

Theorem eqE_comm : forall (x y : pitch), x e= y -> y e= x.
Proof.
intros.
unfold eqE.
auto.
Qed.

Theorem eqE_trans : forall (x y z : pitch), (x e= y) /\ (y e= z) -> (x e= z).
Proof.
intros x y z.
intros H.
destruct H as (HA & HB).
unfold eqE.
Admitted.

(*TODO A C-t szebben belefoglalni*)
Definition halfstep_up (x : pitch) : pitch :=
  match x with 
  | C # m ' o => D # m - 1 ' o + 1
  | l # m ' o =>
    if upward_closer l
    then  nextL l # m ' o
    else  nextL l # m - 1 ' o
  end.

Notation "> X" := (halfstep_up X) (at level 90, right associativity).

Definition wholestep_up (x : pitch) : pitch :=
  sharpen (> x).

Notation ">> X" := (wholestep_up X) (at level 90, right associativity).

(*---------------- INTERVAL --------------------*)
Inductive interval_quality : Set :=
  | iqual : bool -> Z -> interval_quality.

(*Nincs elrejtve a típus (true = P, false = m/M)*)
Definition P     := iqual true     0.
Definition Aug   := iqual true     1.
Definition Dim   := iqual true  (- 1).
Definition major := iqual false    0.
Definition minor := iqual false (- 1).
Definition aug   := iqual false    1.
Definition dim   := iqual false (- 2).


Definition perfect_type (q : interval_quality) : Prop :=
  match q with
  | iqual t m => t = true
  end.

(*
(*32:38 a videóban*)
Definition asd (q : interval_quality) : (perfect_type q )-> interval_quality :=
  q.
*)

Inductive interval_name : Set :=
  | interv : interval_quality -> nat -> interval_name.

(*
(* CDÚR skálán kell végig menni*)
Fixpoint halfstep_count (i : interval_name) : Z :=
  match i with
  | interv (iqual t m) 0 => m
  | interv (iqual t m) (S n) => 1 + halfstep_count(interv (iqual t m) n)
  end.

Eval compute in halfstep_count (interv major 2).
*)
Definition eqEInterval (x y : interval_quality) : Prop :=
  



(* így is lehetne...
Inductive interval : Set :=
  | interv : nat -> Z -> interval.

(*típus el van rejtve a p és mm-be*)
Definition p_perf : Z := 0.
Definition p_aug : Z := 1.
Definition p_dim : Z := -1.
Definition mm_min : Z := -1.
Definition mm_maj : Z := 0.
Definition mm_aug : Z := 1.
Definition mm_dim : Z := -2.

Definition P5 := interv 5 0.
Definition P5' (x : pitch) := >> > >> >> x.
Eval compute in P5' (P5' (D # -1 ' 3)).


Definition numberI (i : interval) : nat :=
  match i with
  | interv n m => n
  end.

Definition modifierI (i : interval) : Z :=
  match i with
  | interv n m => m
  end.

(*
Fixpoint apply_interval (x : pitch) (i : interval) : pitch :=
  match i with
  | interv 0 m => x
  | interv (S n) m => > apply_interval x (interv n m)
  end.
*)
*)
