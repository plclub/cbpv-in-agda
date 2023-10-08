open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)

module CBV.Effects.Terms where

variable n : ℕ
variable m : Fin n

mutual
  data Value (n : ℕ) : Set where
    unit : Value n
    ƛ_ : Exp (suc n) → Value n
    ♯_ : Fin n → Value n
    inl : Value n → Value n
    inr : Value n → Value n
    ⟨_,_⟩ : Value n → Value n → Value n

  data Exp (n : ℕ) : Set where
    val : Value n → Exp n
    _·_ : Exp n → Exp n → Exp n
    _»_ : Exp n → Exp n → Exp n
    inl : Exp n → Exp n
    inr : Exp n → Exp n
    ⟨_,_⟩ : Exp n → Exp n → Exp n
    case_inl⇒_inr⇒_ : Exp n → Exp (suc n) → Exp (suc n) → Exp n
    $≔_⋯_ : Exp n → Exp (suc (suc n)) → Exp n
    tick : Exp n

variable v v₁ v₂ : Value n
variable e e′ e₁ e₂ : Exp n

infix 5 ƛ_
infixl 7 _»_
infixl 7 _·_
infix 9 ♯_
infixl 5 case_inl⇒_inr⇒_
infixr 5 $≔_⋯_
