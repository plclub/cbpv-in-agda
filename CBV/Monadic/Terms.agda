open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)

module CBV.Monadic.Terms where

mutual
  data Value (n : ℕ) : Set where
    unit : Value n
    ƛ_ : Exp (suc n) → Value n
    #_ : Fin n → Value n

  data Exp (n : ℕ) : Set where
    val : Value n → Exp n
    _·_ : Exp n → Exp n → Exp n
    _»_ : Exp n → Exp n → Exp n
    return_ : Exp n → Exp n
    $⟵_⋯_ : Exp n → Exp (suc n) → Exp n
    tick : Exp n

infix 5 ƛ_
infixl 7 _»_
infix 6 return_
infixl 7 _·_
infix 9 #_
infixr 4 $⟵_⋯_
