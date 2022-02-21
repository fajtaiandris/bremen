Inductive harmonic_quality :=
  some_harmonic_quality.

Inductive instrument :=
  instrument_of : harmonic_quality -> instrument.

Definition piano := instrument_of some_harmonic_quality.
Definition guitar := instrument_of some_harmonic_quality.
Definition matthew_caws_voice := instrument_of some_harmonic_quality.