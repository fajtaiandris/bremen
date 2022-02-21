From Bremen.theories.structure Require Import HarmonicPart.
From Bremen.theories.physics Require Import Instrument.

Inductive section :=
  | first_instrument : instrument -> harmonic_part -> section
  | another_instrument : instrument -> harmonic_part -> section -> section.

Inductive song :=
  | first_section : section -> song
  | another_section : section -> song -> song.