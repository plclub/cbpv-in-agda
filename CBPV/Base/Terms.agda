open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)

module CBPV.Base.Terms where

variable n n′ : ℕ
variable m : Fin n

mutual
  data Val : ℕ → Set where
    #_ : Fin n → Val n
    unit : Val n
    ⟪_⟫ : Comp n → Val n
    ⟨_,_⟩ : Val n → Val n → Val n
    inl : Val n → Val n
    inr : Val n → Val n

  data Comp : ℕ → Set where
    ƛ_ : Comp (suc n) → Comp n
    _·_ : Comp n → Val n → Comp n
    _»_ : Val n → Comp n → Comp n
    _! : Val n → Comp n
    ⟨_,_⟩ : Comp n → Comp n → Comp n
    projl : Comp n → Comp n
    projr : Comp n → Comp n
    return_ : Val n → Comp n
    $⟵_⋯_ : Comp n → Comp (suc n) → Comp n
    $≔_⋯_ : Val n → Comp (suc (suc n)) → Comp n
    case_inl⇒_inr⇒_ : Val n → Comp (suc n) → Comp (suc n) → Comp n

variable V V′ V₁ V₂ : Val n
variable M N M′ M″ N′ M₁ M₂ : Comp n

infix 5 ƛ_
infixl 7 _»_
infix 6 _!
infix 6 return_
infixl 7 _·_
infix 9 #_
infixr 5 $⟵_⋯_
infixr 5 $≔_⋯_
infixl 5 case_inl⇒_inr⇒_
infix 5 ⟪_⟫
