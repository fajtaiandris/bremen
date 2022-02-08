Require Import ZArith.
From Bremen.theories Require Import Letter PitchClass Pitch.

(*TODO find out the right names*)
Inductive intervalCategory : Type :=
  | perfect
  | majorminor
.

Inductive intervalQuality : Type :=
  | iqual : intervalCategory -> Z -> intervalQuality.

Notation "'Perfect'"    := (iqual perfect 0) (at level 80, right associativity).
Notation "'Augmented'"  := (iqual perfect 1) (at level 80, right associativity).
Notation "'Diminished'" := (iqual perfect (- 1)) (at level 80, right associativity).
Notation "'major'"      := (iqual majorminor 0) (at level 80, right associativity).
Notation "'minor'"      := (iqual majorminor (- 1)) (at level 80, right associativity).
Notation "'augmented'"  := (iqual majorminor 1) (at level 80, right associativity).
Notation "'diminished'" := (iqual majorminor (- 2)) (at level 80, right associativity).

Fixpoint category_from_number (n : nat) :=
  match n with
  | 0 => perfect
  | 1 => perfect
  | 2 => majorminor
  | 3 => majorminor
  | 4 => perfect
  | 5 => perfect
  | 6 => majorminor
  | 7 => majorminor
  | S(S(S(S(S(S(S n)))))) => category_from_number n
  end.

Definition modifier (q : intervalQuality) : Z :=
  match q with 
  | iqual category modifier => modifier
  end.

Inductive intervalName : Type :=
  | iname : intervalQuality -> nat -> intervalName.

(*TODO what about iname P 2 ? Also P 0*)

Definition size (i : intervalName) : Z :=
  match i with
  | iname q n => 
    Z.of_nat (Letter.upward_distance C (nextN C (n - 1)))
    + modifier q 
    + 12 * (Z.div (Z.of_nat n) 8)
  end.

Definition between_pitch_classes (x y : pitchClass) : intervalName :=
  match x, y with
  | l1 # m1 , l2 # m2 =>
    iname
    (iqual
    (*categoey*)
    (category_from_number (1 + next_count l1 l2))
    (*modifier*) 
    ((Z.of_nat(Letter.upward_distance l1 l2))
    -(Z.of_nat(Letter.upward_distance C (nextN C (next_count l1 l2))))
    + m2 - m1))
    (*number*)
    (1 + next_count l1 l2)
  end.

Inductive directionalIntervalName : Type :=
  | upward : intervalName -> directionalIntervalName
  | downward : intervalName -> directionalIntervalName.

Definition between_pitches (x y : pitch) : directionalIntervalName :=
  if Z.leb (distance_C0 x) (distance_C0 y)
  then match x, y with
    | l1 # m1 ' o1, l2 # m2 ' o2 => 
      match (between_pitch_classes (l1 # m1) (l2 # m2)) with
      | iname q n => 
        if (*We leaped over a C letter*)
        andb (Nat.ltb (Letter.upward_distance l1 C) (Letter.upward_distance l2 C))
        (negb (eqb l1 C))
        then upward (iname q (n + (o2 - o1 - 1) * 7))
        else if andb (eqb l2 C) (negb (eqb l1 C)) (*This could be simplified logically*)
          then upward (iname q (n + (o2 - o1 - 1) * 7))
          else upward (iname q (n + (o2 - o1) * 7))
      end
    end(*CODE BELOW IS COPIED FROM ABOVE*)
  else match x, y with
    | l2 # m2 ' o2, l1 # m1 ' o1 => 
      match (between_pitch_classes (l1 # m1) (l2 # m2)) with
      | iname q n => 
        if
        andb (Nat.ltb (Letter.upward_distance l1 C) (Letter.upward_distance l2 C))
        (negb (eqb l1 C))
        then downward (iname q (n + (o2 - o1 - 1) * 7))
        else if andb (eqb l2 C) (negb (eqb l1 C))
          then downward (iname q (n + (o2 - o1 - 1) * 7))
          else downward (iname q (n + (o2 - o1) * 7))
      end
    end
.

Eval compute in between_pitches (D # 0 ' 4) (B # 0 ' 3). 


(*TODO EEZT MEGÍRNI*)
Definition apply_to_pitchClass (p : pitchClass) (i : intervalName) : pitchClass := 
  match p, i with
  | l # m , iname q n =>
  (*Letter*)   nextN l (n - 1)
  (*Modifier*) # m
              - Z.of_nat (PitchClass.upward_distance (l # 0) (nextN l (n - 1) # 0))
  end.

Eval compute in apply_to_pitchClass (A # 0) (iname (major) 2).
(*
Definition apply_to_pitch (p : pitch) (i : interval_name) : pitch := 
  match p, i with
  | l # m ' o , iname q n =>
  (*Letter*)   nextN l (n - 1)
  (*Modifier*) # m + size i 
               - Z.of_nat (PitchClass.upward_distance (l # 0) (nextN l (n - 1) # 0))
  (*Octave*)   ' o + 0 (*TODO*)
  end.

Eval compute in apply_to_pitch (B # 1 ' 0) (iname Aug 1).
*)
Definition enharmonic_eq (x y : intervalName) : Prop :=
  size x = size y.