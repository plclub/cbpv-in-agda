open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)

module CBN.Base.Terms where

data Term (n : ℕ) : Set where
  #_ : Fin n → Term n
  unit : Term n
  ƛ_ : Term (suc n) → Term n
  _·_ : Term n → Term n → Term n
  _»_ : Term n → Term n → Term n

infix 5 ƛ_
infixl 7 _»_
infixl 7 _·_
infix 9 #_
