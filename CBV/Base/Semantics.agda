open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)

open import CBV.Base.Terms

module CBV.Base.Semantics where

mutual
  data ClosVal : Set where
    unit : ClosVal

    clos⦅_,⟪_⟫⦆ : Env n → Comp n → ClosVal

    ⟨_,_⟩ : ClosVal → ClosVal → ClosVal

    inl : ClosVal → ClosVal

    inr : ClosVal → ClosVal

  data ClosTerminal : Set where
    return_ : ClosVal → ClosTerminal

    clos⦅_,ƛ_⦆ : Env n → Comp (suc n) → ClosTerminal

    clos⦅_,⟨_,_⟩⦆ : Env n → Comp n → Comp n → ClosTerminal

  Env : ℕ → Set
  Env n = Fin n → ClosVal

variable W W′ W₁ W₂ : ClosVal
variable T T′ : ClosTerminal
variable ρ ρ′ : Env n

∅ᵨ : Env zero
∅ᵨ ()

_∷ᵨ_ : Env n → ClosVal → Env (suc n)
ρ ∷ᵨ W = λ where
             zero → W
             (suc n) → ρ n

infixl 5 _∷ᵨ_

data _⊩_⇓_ : Env n → Val n → ClosVal → Set where
  evalVar :  ρ ⊢v # m ⇓ ρ m

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

infix 4 _⊢v_⇓_

data _⊢_⇓_ : Env n → Comp n → Domain → Set where
  evalAbs : ρ ⊢c ƛ M ⇓ clos⦅ ρ ,ƛ M ⦆

  evalRet : ρ ⊢v V ⇓ W
            ------------------------
          → ρ ⊢c return V ⇓ return W

  evalSeq : ρ ⊢v V ⇓ unit
          → ρ ⊢c M ⇓ T
            --------------
          → ρ ⊢c V » M ⇓ T

  evalCpair : ρ ⊢c ⟨ M₁ , M₂ ⟩ ⇓ clos⦅ ρ ,⟨ M₁ , M₂ ⟩⦆

  evalProjl : ρ ⊢c M ⇓ clos⦅ ρ′ ,⟨ M₁ , M₂ ⟩⦆
            → ρ′ ⊢c M₁ ⇓ T
              -------------------------------
            → ρ ⊢c projl M ⇓ T

  evalProjr : ρ ⊢c M ⇓ clos⦅ ρ′ ,⟨ M₁ , M₂ ⟩⦆
            → ρ′ ⊢c M₂ ⇓ T
              -------------------------------
            → ρ ⊢c projr M ⇓ T

  evalApp : ρ ⊢c M ⇓ clos⦅ ρ′ ,ƛ M′ ⦆
          → ρ ⊢v V ⇓ W
          → ρ′ ∷ᵨ W ⊢c M′ ⇓ T
            ------------------------
          → ρ ⊢c M · V ⇓ T

  evalForce : ρ ⊢v V ⇓ clos⦅ ρ′ ,⟪ M ⟫⦆
            → ρ′ ⊢c M ⇓ T
              -------------------------
            → ρ ⊢c V ! ⇓ T

  evalLetin : ρ ⊢c M ⇓ return W
            → ρ ∷ᵨ W ⊢c N ⇓ T
              -----------------
            → ρ ⊢c $⟵ M ⋯ N ⇓ T

  evalSplit : ρ ⊢v V ⇓ ⟨ W₁ , W₂ ⟩
            → ρ ∷ᵨ W₁ ∷ᵨ W₂ ⊢c M ⇓ T
              ----------------------
            → ρ ⊢c $≔ V ⋯ M ⇓ T

  evalCaseInl : ρ ⊢v V ⇓ inl W
              → ρ ∷ᵨ W ⊢c M₁ ⇓ T
                -------------------------------
              → ρ ⊢c case V inl⇒ M₁ inr⇒ M₂ ⇓ T

  evalCaseInr : ρ ⊢v V ⇓ inr W
              → ρ ∷ᵨ W ⊢c M₂ ⇓ T
                -------------------------------
              → ρ ⊢c case V inl⇒ M₁ inr⇒ M₂ ⇓ T

infix 4 _⊢c_⇓_
