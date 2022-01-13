module music2 where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false; not)

data Letter : Set where
  A B C D E F G : Letter

data SharpLetter : Set where
  _♯ : Letter ⊎ SharpLetter → SharpLetter

data FlatLetter : Set where
  _♭ : Letter ⊎ FlatLetter → FlatLetter

PitchClass = Letter ⊎ SharpLetter ⊎ FlatLetter

_e=_ : PitchClass → PitchClass → Bool
x e= y = {!   !}

-- (inj₂ ((inj₁ C) ♯)) ♯
