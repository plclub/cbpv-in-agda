open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)

open import CBV.Base.Terms

module CBV.Base.Semantics where

mutual
  data ClosVal : Set where
    unit : ClosVal
    inl : ClosVal → ClosVal
    inr : ClosVal → ClosVal
    ⟨_,_⟩ : ClosVal → ClosVal → ClosVal
    clos⦅_,ƛ_⦆ : Env n → Exp (suc n) → ClosVal

  Env : ℕ → Set
  Env n = Fin n → ClosVal

variable a b d : ClosVal
variable ρ ρ′ : Env n

∅ᵨ : Env zero
∅ᵨ ()

_∷ᵨ_ : Env n → ClosVal → Env (suc n)
ρ ∷ᵨ w = λ where
             zero → w
             (suc n) → ρ n

infixl 5 _∷ᵨ_

data _⊩_⇓_ : Env n → Value n → ClosVal → Set where
  evalUnit : ρ ⊩ unit ⇓ unit

  evalVar : ρ ⊩ # m ⇓ ρ m

  evalAbs : ρ ⊩ ƛ e ⇓ clos⦅ ρ ,ƛ e ⦆

  evalInl : ρ ⊩ v ⇓ a
            -------------
          → ρ ⊩ inl v ⇓ a

  evalInr : ρ ⊩ v ⇓ a
            -------------
          → ρ ⊩ inr v ⇓ a

  evalPair : ρ ⊩ v₁ ⇓ a
           → ρ ⊩ v₂ ⇓ b
             ---------------------------
           → ρ ⊩ ⟨ v₁ , v₂ ⟩ ⇓ ⟨ a , b ⟩

infix 4 _⊩_⇓_

data _⊢_⇓_ : Env n → Exp n → ClosVal → Set where
  evalVal : ρ ⊩ v ⇓ a
            -------------
          → ρ ⊢ val v ⇓ a

  evalSeq : ρ ⊢ e₁ ⇓ unit
          → ρ ⊢ e₂ ⇓ a
            ---------------
          → ρ ⊢ e₁ » e₂ ⇓ a

  evalApp : ρ ⊢ e₁ ⇓ clos⦅ ρ′ ,ƛ e ⦆
          → ρ ⊢ e₂ ⇓ a
          → ρ′ ∷ᵨ a ⊢ e ⇓ b
            ------------------------
          → ρ ⊢ e₁ · e₂ ⇓ b

  evalInl : ρ ⊢ e ⇓ a
            -----------------
          → ρ ⊢ inl e ⇓ inl a

  evalInr : ρ ⊢ e ⇓ a
            -----------------
          → ρ ⊢ inr e ⇓ inr a

  evalPair : ρ ⊢ e₁ ⇓ a
           → ρ ⊢ e₂ ⇓ b
             ---------------------------
           → ρ ⊢ ⟨ e₁ , e₂ ⟩ ⇓ ⟨ a , b ⟩

  evalSplit : ρ ⊢ e₁ ⇓ ⟨ a , b ⟩
            → ρ ∷ᵨ a ∷ᵨ b ⊢ e₂ ⇓ d
              --------------------
            → ρ ⊢ $≔ e₁ ⋯ e₂ ⇓ d

  evalCaseInl : ρ ⊢ e ⇓ inl a
              → ρ ∷ᵨ a ⊢ e₁ ⇓ b
                ------------------------------
              → ρ ⊢ case e inl⇒ e₁ inr⇒ e₂ ⇓ b

  evalCaseInr : ρ ⊢ e ⇓ inr a
              → ρ ∷ᵨ a ⊢ e₂ ⇓ b
                ------------------------------
              → ρ ⊢ case e inl⇒ e₁ inr⇒ e₂ ⇓ b

infix 4 _⊢_⇓_
