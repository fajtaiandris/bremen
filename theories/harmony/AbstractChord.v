From Bremen.theories.harmony Require Import PitchClass Letter Interval.
Require Import ZArith.

Inductive abstractChord : Type :=
   | base : pitchClass -> abstractChord
   | following : abstractChord -> pitchClass -> abstractChord.


Notation ">>> A" := (base A) (at level 80, right associativity).
Notation "A >>> B"    := (following (A) B) (at level 81, left associativity).

Definition before_last (ac : abstractChord) : pitchClass :=
  match ac with
  | base pc => pc
  | following ac pc => match ac with
    | base pc' => pc'
    | following ac' pc' => pc'
    end
  end.

Fixpoint base_pitch_class (ac : abstractChord) : pitchClass :=
  match ac with
  | base pc => pc
  | following ac pc => base_pitch_class ac
  end.

Fixpoint transpose (ac : abstractChord) (di : directionalIntervalName) : abstractChord :=
  match ac with
  | base pc => base (directionally_apply_to_pitch_class pc di)
  | following ac' pc => following (transpose ac' di) (directionally_apply_to_pitch_class pc di)
  end.