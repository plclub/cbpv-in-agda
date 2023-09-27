open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)

module CBPV.Base.Terms where

mutual
  data Val (n : ℕ) : Set where
    #_ : Fin n → Val n
    unit : Val n
    ⟪_⟫ : Comp n → Val n

  data Comp (n : ℕ) : Set where
    ƛ_ : Comp (suc n) → Comp n
    _·_ : Comp n → Val n → Comp n
    _»_ : Val n → Comp n → Comp n
    _! : Val n → Comp n
    return_ : Val n → Comp n
    $⟵_⋯_ : Comp n → Comp (suc n) → Comp n

infix 5 ƛ_
infixl 7 _»_
infix 6 _!
infix 6 return_
infixl 7 _·_
infix 9 #_
infixr 5 $⟵_⋯_
infix 5 ⟪_⟫
