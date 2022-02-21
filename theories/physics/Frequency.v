From Bremen.theories.harmony Require Import Pitch.
Require Import QArith.

Definition A_constant := 440.0.

(*TODO*)
Definition frequency (p : pitch) : Q :=
  A_constant * 2.