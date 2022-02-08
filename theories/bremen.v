Require ZArith.
Require letter.

Module Letter.

  Import ZArith.
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

End Letter.

(*--------------------------------------------------------------------*)
Module PitchClass.

  Import ZArith.
  Import Interval.

  Inductive pitchClass : Type :=
    pitch_class : Letter.letter -> Z -> pitchClass.

  Notation "L # M" := (pitch_class L M) (at level 80, right associativity).

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

  Definition enharmonic_eq (x y : pitchClass) : Prop :=
    upward_distance (Letter.A # 0) x = upward_distance (Letter.A # 0) y.

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
      Letter.next l # (m - Z.of_nat(upward_distance (l # 0) (Letter.next l # 0)) + 1)
    end.

  Definition apply_upward (p : pitch) (i : interval_name) : pitch := 
    match p, i with
    | l # m ' o , iname q n =>
    (*Letter*)   nextN l (n - 1)
    (*Modifier*) # m + size i 
                 - Z.of_nat (PitchClass.upward_distance (l # 0) (nextN l (n - 1) # 0))
    end.

End PitchClass.

(*----------------------------------------------*)
Module Pitch.
  Import Letter.
  Import PitchClass.
  Import ZArith.

  Inductive pitch : Set :=
    p : pitchClass -> nat -> pitch.

  Notation "PC ' O" := (p PC O) (at level 85, right associativity).

  Example Cb4 := (C # - 1) ' 4.

  Definition class (x : pitch) : pitchClass :=
    match x with
    | pc ' o => pc
    end.

  Definition octave (x : pitch) : nat :=
    match x with
    | pc ' o => o
    end.

  Definition sharpen (x : pitch) : pitch :=
    sharpen (class x) ' (octave x).

  Definition flatten (x : pitch) : pitch :=
    flatten (class x) ' (octave x).

  (*Does not work for pitches below C0, (Cb0, Cbb0, ..)*)
  Definition distance_C0 (x : pitch) : Z :=
   Z.of_nat(PitchClass.upward_distance (C # 0) (class x)) + (Z.of_nat(octave x) * 12).

  Definition enharmonic_eq (x y : pitch) : Prop :=
    distance_C0 x = distance_C0 y.

  (*TODO átnevezni e=-re*)
  Notation "X ee= Y" := (enharmonic_eq X Y) (at level 90, right associativity).

  Definition halfstep_up (x : pitch) : pitch :=
    match x with
    | B # m ' o => halfstep_up (B # m) ' o + 1
    | l # m ' o => halfstep_up (l # m) ' o
    end.

  Notation "> X" := (halfstep_up X) (at level 90, right associativity).

  Definition wholestep_up (x : pitch) : pitch :=
    sharpen (> x).

  Notation ">> X" := (wholestep_up X) (at level 90, right associativity).

End Pitch.

(*------------------------------------------------------*)
Module Interval.

  Import ZArith.
  Import Pitch.
  Import Letter.
  Import PitchClass.

  (*TODO find out the right names*)
  Inductive interval_category : Type :=
    | perfect
    | majorminor
  .

  Inductive interval_quality : Type :=
    | iqual : interval_category -> Z -> interval_quality.

  Definition P     := iqual perfect     0.
  Definition Aug   := iqual perfect     1.
  Definition Dim   := iqual perfect  (- 1).
  Definition major := iqual majorminor    0.
  Definition minor := iqual majorminor (- 1).
  Definition aug   := iqual majorminor    1.
  Definition dim   := iqual majorminor (- 2).

  Definition modifier (q : interval_quality) : Z :=
    match q with 
    | iqual category modifier => modifier
    end.

  Inductive interval_name : Type :=
    | iname : interval_quality -> nat -> interval_name.

  (*TODO what about iname P 2 ? Also P 0*)
  (*TODO ez kell?*)
  Notation "! Q N" := (iname Q N) (at level 80, right associativity).

  Definition size (i : interval_name) : Z :=
    match i with
    | iname q n => 
      Z.of_nat (Letter.upward_distance C (nextN C (n - 1)))
      + modifier q 
      + 12 * (Z.div (Z.of_nat n) 8)
    end.

  Definition apply_upward (p : pitch) (i : interval_name) : pitch := 
    match p, i with
    | l # m ' o , iname q n =>
    (*Letter*)   nextN l (n - 1)
    (*Modifier*) # m + size i 
                 - Z.of_nat (PitchClass.upward_distance (l # 0) (nextN l (n - 1) # 0))
    (*Octave*)   ' o + 
    end.

  Eval compute in apply_upward (B # 1 ' 0) (iname Aug 1).

  Definition enharmonic_eq (x y : interval_name) : Prop :=
    size x = size y.

End Interval.

Module Chord.

  Import ZArith.
  Import List.
  Import Letter.
  Import PitchClass.
  Import Pitch.
  (*TODO listával valahogy*)

  Inductive abstractChord : Type :=
    pitchClasses : list pitchClass -> abstractChord.

  Inductive chord : Type :=
    pitches : list pitch -> chord.

  Check pitches ((A # 0 ' 1) :: (C # 0 ' 2) :: (E # 0 ' 2) :: nil).

  (*TODO*)
  Inductive chordName : Type :=
    | Major.

End Chord.

Module Key.
  Import ZArith.
  Import List.
  Import Letter.
  Import PitchClass.
  Import Pitch.
  Import Chord.

  Inductive key_quality : Type :=
  | major
  | minor.

  Inductive key : Type :=
    key_of : pitchClass -> key_quality -> key.

  Check key_of (G # 0) major.

  (*TODO*)
  Definition pitches (k : key) : chord :=
    pitches nil.

End Key.

Module Rhythm.

  Inductive division : Type :=
    | whole
    | half : division -> division
    | third : division -> division
  .

  Inductive duration : Type :=
    | simple_duration : division -> duration
    | complex_duration : duration -> duration -> duration.

  Definition quarter := half(half(whole)).
  Eval compute in complex_duration (simple_duration quarter) (simple_duration quarter).

End Rhythm.

Module Dynamics.

  (*TODO: Azt nem formalizálom, hogy ez mit jelent*)
  Inductive dynamic : Type :=
  | f
  | mf
  | p
  | pp
  | diminuendo
  | rubato .

End Dynamics.

Module Note.
  Import ZArith.
  Import List.
  Import Letter.
  Import PitchClass.
  Import Pitch.
  Import Chord.
  Import Rhythm.
  Import Dynamics.

  (*TODO add dynamic quality, nagyon átgondolni a restet is*)
  Inductive note : Type :=
    | note_of : pitch -> duration -> dynamic -> note
    | rest_of : duration -> dynamic -> note.

End Note.

Module Melody.
  Import ZArith.
  Import List.
  Import Letter.
  Import PitchClass.
  Import Pitch.
  Import Chord.
  Import Key.
  Import Note.

  Inductive melody : Type :=
    melody_of : list note -> melody.

End Melody.

Module Analysis.
End Analysis.

Module Song.
End Song.

