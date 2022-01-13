module music where

open import Data.Bool using (Bool; true; false; not)

data PitchClass : Set where
  A : PitchClass
  _♯ : PitchClass → PitchClass

-- PitchClass constants
B C D E F G : PitchClass
B = A ♯ ♯
C = B ♯
D = C ♯ ♯
E = D ♯ ♯
F = E ♯
G = F ♯ ♯

_♭ : PitchClass → PitchClass
x ♯ ♭ = x
x ♭ = x ♯ ♯ ♯ ♯ ♯ ♯ ♯ ♯ ♯ ♯ ♯

-- Enharmonically equals
_e=_ : PitchClass → PitchClass → Bool
A                          e= A                         = true
x                          e= y ♯ ♯ ♯ ♯ ♯ ♯ ♯ ♯ ♯ ♯ ♯ ♯ = x e= y
x ♯ ♯ ♯ ♯ ♯ ♯ ♯ ♯ ♯ ♯ ♯ ♯  e= y                         = x e= y
A                          e= x ♯                       = false
x ♯                        e= A                         = false
x ♯                        e= y ♯                       = x e= y

infix 3 _e=_

-- Whole step
>> : PitchClass → PitchClass
>> x = x ♯ ♯

-- Azonos normálforma: C , B ♯
-- Amúgy meg, kell-e hogy külön dolog legyen?
-- Hallásban sincs különbség.
