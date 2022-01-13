module music3 where

open import Data.Product using (_×_; _,_)
open import Data.Integer
open import Data.Bool using (Bool; true; false; not; if_then_else_)

data Letter : Set where
  A B C D E F G : Letter

data PitchClass : Set where
  pc : Letter × ℤ → PitchClass

-- _♯ : PitchClass → PitchClass
-- pc (l , n) ♯ = pc (l , n + (+ 1))
--
-- _♭ : PitchClass → PitchClass
-- pc (l , n) ♭ = pc (l , n - + 1)

-- itt sincs Ciszesz végülis, mert a "pc (C , + 1) ♭" nem egy hang
-- de átnevezve már nem megtévesztő:

sharpen : PitchClass → PitchClass
sharpen (pc (l , n)) = pc (l , n + (+ 1))

flatten : PitchClass → PitchClass
flatten (pc (l , n)) = pc (l , n - + 1)

_l=_ : Letter → Letter → Bool
x l= y = {!   !}

_e=_ : PitchClass → PitchClass → Bool
pc (l1 , n1) e= pc (l2 , n2) = {! !}
