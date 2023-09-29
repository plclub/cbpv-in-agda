open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)

open import CBPV.Base.Terms

module CBPV.Base.Semantics where

mutual
  data ClosVal : Set where
    unit : ClosVal

    clos⦅_,⟪_⟫⦆ : Env n → Comp n → ClosVal

  data ClosTerminal : Set where
    return_ : ClosVal → ClosTerminal

    clos⦅_,ƛ_⦆ : Env n → Comp (suc n) → ClosTerminal

  Env : ℕ → Set
  Env n = Fin n → ClosVal

variable W W′ : ClosVal
variable T T′ : ClosTerminal
variable ρ ρ′ : Env n

∅ᵨ : Env zero
∅ᵨ ()

_∷ᵨ_ : Env n → ClosVal → Env (suc n)
ρ ∷ᵨ W = λ where
          zero → W
          (suc n) → ρ n

infixl 5 _∷ᵨ_

data _⊢v_⇓_ : Env n → Val n → ClosVal → Set where
  evalVar :  ρ ⊢v # m ⇓ ρ m

  evalUnit : ρ ⊢v unit ⇓ unit

  evalThunk : ρ ⊢v ⟪ M ⟫ ⇓ clos⦅ ρ ,⟪ M ⟫⦆

infix 4 _⊢v_⇓_

data _⊢c_⇓_ : Env n → Comp n → ClosTerminal → Set where
  evalAbs : ρ ⊢c ƛ M ⇓ clos⦅ ρ ,ƛ M ⦆

  evalRet : ρ ⊢v V ⇓ W
            ------------------------
          → ρ ⊢c return V ⇓ return W

  evalSeq : ρ ⊢v V ⇓ unit
          → ρ ⊢c M ⇓ T
            --------------
          → ρ ⊢c V » M ⇓ T

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

infix 4 _⊢c_⇓_
