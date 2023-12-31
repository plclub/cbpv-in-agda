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

    ⟨_,_⟩ : ClosVal → ClosVal → ClosVal

    inl : ClosVal → ClosVal

    inr : ClosVal → ClosVal

  data ClosTerminal : Set where
    return_ : ClosVal → ClosTerminal

    clos⦅_,ƛ_⦆ : ∀ {n : ℕ} → Env n → Comp (suc n) → ClosTerminal

    clos⦅_,⟨_,_⟩⦆ : Env n → Comp n → Comp n → ClosTerminal

  Env : ℕ → Set
  Env n = Fin n → ClosVal

variable W W′ W₁ W₂ : ClosVal
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

  evalPair : ρ ⊢v V₁ ⇓ W₁
           → ρ ⊢v V₂ ⇓ W₂
             ------------------------------
           → ρ ⊢v ⟨ V₁ , V₂ ⟩ ⇓ ⟨ W₁ , W₂ ⟩

  evalInl : ρ ⊢v V ⇓ W
            ------------------
          → ρ ⊢v inl V ⇓ inl W

  evalInr : ρ ⊢v V ⇓ W
            ------------------
          → ρ ⊢v inr V ⇓ inr W

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

  evalCpair : ρ ⊢c ⟨ M₁ , M₂ ⟩ ⇓ clos⦅ ρ ,⟨ M₁ , M₂ ⟩⦆ # pure

  evalProjl : ρ ⊢c M ⇓ clos⦅ ρ′ ,⟨ M₁ , M₂ ⟩⦆ # φ₁
            → ρ′ ⊢c M₁ ⇓ T # φ₂
              ------------------------------------
            → ρ ⊢c projl M ⇓ T # φ₁ + φ₂

  evalProjr : ρ ⊢c M ⇓ clos⦅ ρ′ ,⟨ M₁ , M₂ ⟩⦆ # φ₁
            → ρ′ ⊢c M₂ ⇓ T # φ₂
              ------------------------------------
            → ρ ⊢c projr M ⇓ T # φ₁ + φ₂

  evalForce : ρ ⊢v V ⇓ clos⦅ ρ′ ,⟪ M ⟫⦆
            → ρ′ ⊢c M ⇓ T # φ
              -----------------
            → ρ ⊢c V ! ⇓ T # φ

  evalLetin : ρ ⊢c M ⇓ return W # φ₁
            → ρ ∷ᵨ W ⊢c N ⇓ T # φ₂
              ---------------------------
            → ρ ⊢c $⟵ M ⋯ N ⇓ T # φ₁ + φ₂

  evalSplit : ρ ⊢v V ⇓ ⟨ W₁ , W₂ ⟩
            → ρ ∷ᵨ W₁ ∷ᵨ W₂ ⊢c M ⇓ T # φ
              --------------------------
            → ρ ⊢c $≔ V ⋯ M ⇓ T # φ

  evalCaseInl : ρ ⊢v V ⇓ inl W
              → ρ ∷ᵨ W ⊢c M₁ ⇓ T # φ
                -----------------------------------
              → ρ ⊢c case V inl⇒ M₁ inr⇒ M₂ ⇓ T # φ

  evalCaseInr : ρ ⊢v V ⇓ inr W
              → ρ ∷ᵨ W ⊢c M₂ ⇓ T # φ
                -----------------------------------
              → ρ ⊢c case V inl⇒ M₁ inr⇒ M₂ ⇓ T # φ

  evalTick : ρ ⊢c tick ⇓ return unit # tock

infix 4 _⊢v_⇓_
infix 4 _⊢c_⇓_#_
