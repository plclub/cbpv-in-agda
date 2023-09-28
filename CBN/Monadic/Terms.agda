open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)

module CBN.Monadic.Terms where

data Term (n : ℕ) : Set where
  #_ : Fin n → Term n
  unit : Term n
  ƛ_ : Term (suc n) → Term n
  _·_ : Term n → Term n → Term n
  _»_ : Term n → Term n → Term n
  return_ : Term n → Term n
  $⟵_⋯_ : Term n → Term (suc n) → Term n
  tick : Term n

infix 5 ƛ_
infixl 7 _»_
infix 6 return_
infixl 7 _·_
infix 9 #_
infixr 5 $⟵_⋯_
