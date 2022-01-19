module music3 where

open import Data.Integer
open import Data.Nat using (ℕ) renaming (_+_ to _ℕ+_; _≡ᵇ_ to _ℕ=_)
open import Data.Bool using (Bool; true; false; not; if_then_else_; _∧_)

-- ez csak benne val az stdlibben?
_ℤ=_ : ℤ → ℤ → Bool
a ℤ= b = (a ≤ᵇ b) ∧ (b ≤ᵇ a)

data Letter : Set where
  A B C D E F G : Letter

_l=_ : Letter → Letter → Bool
A l= A = true
B l= B = true
C l= C = true
D l= D = true
E l= E = true
G l= G = true
x l= y = false

nextLetter : Letter → Letter
nextLetter A = B
nextLetter B = C
nextLetter C = D
nextLetter D = E
nextLetter E = F
nextLetter F = G
nextLetter G = A

data PitchClass : Set where
  _#_ : Letter → (modifier : ℤ) → PitchClass

-- TODO ez kell, hogy mod 12-t is alkalmazza az eredményre
modSimpl : ℤ → ℕ
modSimpl (+ x ) = x
modSimpl x = ∣ + 12 + x ∣

distanceFromA : PitchClass → ℕ
distanceFromA (A # n) = modSimpl( + 0 + n )
distanceFromA (B # n) = modSimpl( + 2 + n )
distanceFromA (C # n) = modSimpl( + 3 + n )
distanceFromA (D # n) = modSimpl( + 5 + n )
distanceFromA (E # n) = modSimpl( + 7 + n )
distanceFromA (F # n) = modSimpl( + 8 + n )
distanceFromA (G # n) = modSimpl( + 10 + n )

_e=_ : PitchClass → PitchClass → Bool
x e= y = distanceFromA x ℕ= distanceFromA y

sharpen : PitchClass → PitchClass
sharpen (l # n) = l # n + (+ 1)

flatten : PitchClass → PitchClass
flatten (l # n) = l # n - + 1

data Pitch : Set where
  _^_ : PitchClass → (octave : ℕ) → Pitch

-- ez a distanceFromA-ből adódik
-- lehetne egyszerűbben?
hs : Pitch → Pitch
hs ((B # n) ^ o) = ((C # n) ^ (o ℕ+ 1))
hs ((E # n) ^ o) = ((F # n) ^ o )
hs ((l # n) ^ o) = ((nextLetter (l) # (n - + 1)) ^ o)

ws : Pitch → Pitch
ws ((l # n) ^ o) = hs ((l # (n + + 1)) ^ o)

m2 M2 m3 : Pitch → Pitch
interval : ℕ → ℕ → Pitch → Pitch
m2 = λ x → hs x
M2 = λ x → ws x
m3 = λ x → hs (ws x)

infix 5 _#_
infix 4 _e=_
