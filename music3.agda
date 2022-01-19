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

data PitchClass : Set where
  _#_ : Letter → (modifier : ℤ) → PitchClass

-- TODO ez kell, hogy mod 12-t is alkalmazza az eredményre
modSimpl : ℤ → ℕ
modSimpl (+ x ) = x
modSimpl x = ∣ + 12 + x ∣


hsFromA : PitchClass → ℕ
hsFromA (A # n) = modSimpl( + 0 + n )
hsFromA (B # n) = modSimpl( + 2 + n )
hsFromA (C # n) = modSimpl( + 3 + n )
hsFromA (D # n) = modSimpl( + 5 + n )
hsFromA (E # n) = modSimpl( + 7 + n )
hsFromA (F # n) = modSimpl( + 8 + n )
hsFromA (G # n) = modSimpl( + 10 + n )

_e=_ : PitchClass → PitchClass → Bool
x e= y = hsFromA x ℕ= hsFromA y

sharpen : PitchClass → PitchClass
sharpen (l # n) = l # n + (+ 1)

flatten : PitchClass → PitchClass
flatten (l # n) = l # n - + 1

infix 5 _#_
infix 4 _e=_
