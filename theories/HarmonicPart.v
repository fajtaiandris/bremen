From Bremen.theories Require Import Duration Dynamics MelodicPart.

(*this could be formalized many many ways, don't forget to mention in thesis*)
Inductive harmonic_part : Type :=
  | first_melodic_part_at_start : melodic_part -> harmonic_part
  | melodic_part_at_start       : melodic_part -> harmonic_part -> harmonic_part
  | melodic_part_later          : duration -> melodic_part -> harmonic_part -> harmonic_part.

Definition example_harmonic_part := 
  melodic_part_later (Whole_) example_melody2 (
  melodic_part_at_start example_melody2 (
  first_melodic_part_at_start (example_melody1))).

Print example_harmonic_part.