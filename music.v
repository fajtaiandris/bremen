(*------- LETTER -------*)
Inductive letter : Set :=
  A : letter
| B : letter
| C : letter
| D : letter
| E : letter
| F : letter
| G : letter.

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

Definition fromAPC (x : pitchClass) : Z :=
  match x with
  | A # m => 0 + m
  | B # m => 2 + m
  | C # m => 3 + m
  | D # m => 5 + m
  | E # m => 7 + m
  | F # m => 8 + m
  | G # m => 10 + m
  end.

Definition fromCPC (x : pitchClass) : Z :=
  match x with
  | C # m => 0 + m
  | D # m => 2 + m
  | E # m => 4 + m
  | F # m => 5 + m
  | G # m => 7 + m
  | A # m => 9 + m
  | B # m => 11 + m
  end.

Definition eqEPC (x y : pitchClass) : Prop :=
  Zmod (fromAPC x) 12 = Zmod (fromAPC y) 12.

Definition sharpenPC (x : pitchClass) : pitchClass :=
  match x with
  | l # m => l # m + 1
  end.

Definition flattenPC (x : pitchClass) : pitchClass :=
  match x with
  | l # m => l # m - 1
  end.

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


(*
Theorem noteqEPCsharp : forall (x: pitchClass),
  ~ (eqEPC x (sharpen(x))).
Proof.
intros.
unfold not.
induction x.
unfold sharpen.
unfold eqEPC.
intros H.
Qed.
*)

(*
Eval compute in pc A 3.

Eval compute in nextL(A).

Eval compute in C.
Check C.
Check letter.

Section Declaration.
Variable n : nat.
Hypothesis Pos_n : (gt n 0).
Definition one := (S 0).
Definition one' : nat := (S 0).
Definition one'' := (S 0) : nat.
Definition double (m : nat) := plus m m.


Section Minimal_logic.
Variables A B C : Prop.
Check (A -> B).

*) 