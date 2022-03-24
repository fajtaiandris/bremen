From Bremen.theories.harmony Require Import Pitch.
Require Import QArith ZArith.

Definition A_constant := 440.0.

Definition frequency (p : pitch) : Q :=
  Qpower (Qdiv ((distance_C0 p) # 1) 12) 2 .

Eval compute in frequency Cb4.