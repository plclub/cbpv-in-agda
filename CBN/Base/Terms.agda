open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)

module CBN.Base.Terms where

variable n : ℕ
variable m : Fin n

data Term (n : ℕ) : Set where
  #_ : Fin n → Term n
  unit : Term n
  inl : Term n → Term n
  inr : Term n → Term n
  ⟨_,_⟩ : Term n → Term n → Term n
  ƛ_ : Term (suc n) → Term n
  _·_ : Term n → Term n → Term n
  _»_ : Term n → Term n → Term n
  fst : Term n → Term n
  snd : Term n → Term n
  case_inl⇒_inr⇒_ : Term n → Term (suc n) → Term (suc n) → Term n

variable e e′ e₁ e₂ : Term n

infix 5 ƛ_
infixl 7 _»_
infixl 7 _·_
infix 9 #_
infixl 5 case_inl⇒_inr⇒_
