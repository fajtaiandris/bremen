(*------- PITCH CLASS -------*)
Require Import ZArith.

Inductive pitchClass : Set :=
  pitch_class : letter -> Z -> pitchClass.

Notation "L # M" := (pitch_class L M) (at level 80, right associativity).

Definition letterPC (x : pitchClass) : letter :=
  match x with
  | l # m => l
  end.

Definition modifierPC (x : pitchClass) : Z :=
  match x with
  | l # m => m
  end.

Definition upward_distancePC (x y : pitchClass) : nat :=
  match x, y with
  | l # m, l' # m' => Z.to_nat (Zmod (Z.of_nat (upward_distance l l') - m + m') 12)
  end.

Definition enharmonic_eqPC (x y : pitchClass) : Prop :=
  upward_distancePC (A # 0) x = upward_distancePC (A # 0) y.

Definition sharpenPC (x : pitchClass) : pitchClass :=
  match x with
  | l # m => l # m + 1
  end.

Definition flattenPC (x : pitchClass) : pitchClass :=
  match x with
  | l # m => l # m - 1
  end.

Lemma aorb : forall (p1 p2 p3 : Prop), (p1 \/ p2 -> p3) = (p1 -> p3 \/ p2 -> p3).
Proof.
intros.
Admitted.

Lemma pitchclass0 : forall (l1 l2 : letter) (m1 m2 : Z), ~ (l1 # m1) = (l2 # m2) <-> ~ l1 = l2 \/ ~ m1 = m2.
Proof.
intros. split.
  * intro H. left. give_up.
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
