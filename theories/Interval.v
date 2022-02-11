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

Notation "'P1_'"    := (iname (Perfect) 1) (at level 80, right associativity).
Notation "'P4_'"    := (iname (Perfect) 4) (at level 80, right associativity).
Notation "'Aug4_'"    := (iname (Augmented) 4) (at level 80, right associativity).
Notation "'Dim4_'"    := (iname (Diminished) 4) (at level 80, right associativity).
Notation "'P5_'"    := (iname (Perfect) 5) (at level 80, right associativity).
Notation "'Aug5_'"    := (iname (Augmented) 5) (at level 80, right associativity).
Notation "'Dim5_'"    := (iname (Diminished) 5) (at level 80, right associativity).
Notation "'m2_'"    := (iname (minor) 2) (at level 80, right associativity).
Notation "'M2_'"    := (iname (major) 2) (at level 80, right associativity).
Notation "'m3_'"    := (iname (minor) 3) (at level 80, right associativity).
Notation "'M3_'"    := (iname (major) 3) (at level 80, right associativity).
Notation "'m6_'"    := (iname (minor) 6) (at level 80, right associativity).
Notation "'M6_'"    := (iname (major) 6) (at level 80, right associativity).
Notation "'m7_'"    := (iname (minor) 7) (at level 80, right associativity).
Notation "'M7_'"    := (iname (major) 7) (at level 80, right associativity).
Notation "'P8_'"    := (iname (Perfect) 8) (at level 80, right associativity).

(*Works within the octave*)
Definition invert (i : intervalName) : intervalName :=
  match i with 
  | iname (iqual perfect m) n    => iname (iqual perfect (- m))        (9 - n)
  | iname (iqual majorminor m) n => iname (iqual majorminor (- m - 1)) (9 - n)
  end.

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

(*Hibás: Eval compute in apply_to_pitch_class (A # 1) (iname (Diminished) 1).*)
Definition apply_to_pitch_class (p : pitchClass) (i : intervalName) : pitchClass := 
  match p, i with
  | l # m , iname q n =>
  (*Letter*)   nextN l (n - 1)
  (*Modifier*) # m + ((size i) mod 12) - (size (between_pitch_classes p (nextN l (n - 1) # m)))
  end.

Definition apply_to_pitch (p : pitch) (i : intervalName) : pitch := 
  match p, i with
  | l # m ' o , iname q n =>
    match apply_to_pitch_class (l # m) (iname q n) with
    | l2 # m2 => l2 # m2 ' o + (Nat.div n 7) + 
      match between_pitches (l # m ' o) (l2 # m2 ' o) with
      | upward x   => 0
      | downward (iname q 1) => 0
      | downward _ => 1
      end
    end
  end.

Definition enharmonic_eq (x y : intervalName) : Prop :=
  size x = size y.

Definition plus (x y : intervalName) : intervalName :=
  match x, y with
  | iname (iqual c1 m1) n1, iname (iqual c2 m2) n2
    => iname 
      (iqual
      (*category*) (category_from_number (n1 + n2 - 1))
      (*modifier*) (m1 + m2) )
      (*number*)   (n1 + n2 - 1)
   end.