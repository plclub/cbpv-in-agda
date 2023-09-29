open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)

open import CBPV.Effects.Terms
open import Effects

module CBPV.Effects.Semantics (E : Effect) where

open Effect E

mutual
  data ClosVal : Set where
    unit : ClosVal

    clos⦅_,⟪_⟫⦆ : ∀ {n : ℕ} → Env n → Comp n → ClosVal

  data ClosTerminal : Set where
    return_ : ClosVal → ClosTerminal

    clos⦅_,ƛ_⦆ : ∀ {n : ℕ} → Env n → Comp (suc n) → ClosTerminal

  Env : ℕ → Set
  Env n = Fin n → ClosVal

variable W W′ : ClosVal
variable T T′ : ClosTerminal
variable ρ ρ′ : Env n

∅ᵨ : Env zero
∅ᵨ ()

_∷ᵨ_ : ∀ {n : ℕ} → Env n → ClosVal → Env (suc n)
ρ ∷ᵨ W = λ where
          zero → W
          (suc n) → ρ n

infixl 5 _∷ᵨ_

data _⊢v_⇓_ : Env n → Val n → ClosVal → Set where
  evalVar : ρ ⊢v ♯ m ⇓ ρ m

  evalUnit : ρ ⊢v unit ⇓ unit

  evalThunk : ρ ⊢v ⟪ M ⟫ ⇓ clos⦅ ρ ,⟪ M ⟫⦆

data _⊢c_⇓_#_ : Env n → Comp n → ClosTerminal → Eff → Set where
  evalAbs : ρ ⊢c ƛ M ⇓ clos⦅ ρ ,ƛ M ⦆ # pure

  evalRet : ρ ⊢v V ⇓ W
            ------------------------------
          → ρ ⊢c return V ⇓ return W # pure

  evalSeq : ρ ⊢v V ⇓ unit
          → ρ ⊢c M ⇓ T # φ
            ------------------
          → ρ ⊢c V » M ⇓ T # φ

  evalApp : ρ ⊢c M ⇓ clos⦅ ρ′ ,ƛ M′ ⦆ # φ₁
          → ρ ⊢v V ⇓ W
          → ρ′ ∷ᵨ W ⊢c M′ ⇓ T # φ₂
            -----------------------------
          → ρ ⊢c M · V ⇓ T # φ₁ + φ₂

  evalForce : ρ ⊢v V ⇓ clos⦅ ρ′ ,⟪ M ⟫⦆
            → ρ′ ⊢c M ⇓ T # φ
              -----------------
            → ρ ⊢c V ! ⇓ T # φ

  evalLetin : ρ ⊢c M ⇓ return W # φ₁
            → ρ ∷ᵨ W ⊢c N ⇓ T # φ₂
              ---------------------------
            → ρ ⊢c $⟵ M ⋯ N ⇓ T # φ₁ + φ₂

  evalTick : ρ ⊢c tick ⇓ return unit # tock

infix 4 _⊢v_⇓_
infix 4 _⊢c_⇓_#_
