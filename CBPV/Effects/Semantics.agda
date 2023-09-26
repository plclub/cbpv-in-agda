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

∅ᵨ : Env zero
∅ᵨ ()

_∷ᵨ_ : ∀ {n : ℕ} → Env n → ClosVal → Env (suc n)
ρ ∷ᵨ W = λ where
          zero → W
          (suc n) → ρ n

infixl 5 _∷ᵨ_

data _∣_⇓v_ {n : ℕ} (ρ : Env n) : Val n → ClosVal → Set where
  evalVar : ∀ {m : Fin n} {W : ClosVal}
            -------------
          → ρ ∣ ♯ m ⇓v ρ m

  evalUnit : ρ ∣ unit ⇓v unit

  evalThunk : ∀ {M : Comp n}
              --------------------------
            → ρ ∣ ⟪ M ⟫ ⇓v clos⦅ ρ ,⟪ M ⟫⦆

data _∣_⇓c_#_ {n : ℕ} (ρ : Env n) : Comp n → ClosTerminal → Eff → Set where
  evalAbs : ∀ {M : Comp (suc n)}
            ------------------------------
          → ρ ∣ ƛ M ⇓c clos⦅ ρ ,ƛ M ⦆ # pure

  evalRet : ∀ {V : Val n} {W : ClosVal}
          → ρ ∣ V ⇓v W
            ------------------------------
          → ρ ∣ return V ⇓c return W # pure

  evalSeq : ∀ {V : Val n} {M : Comp n} {T : ClosTerminal} {φ : Eff}
          → ρ ∣ V ⇓v unit
          → ρ ∣ M ⇓c T # φ
            ------------------
          → ρ ∣ V » M ⇓c T # φ

  evalApp : ∀ {m : ℕ} {M : Comp n} {ρ′ : Env m} {M′ : Comp (suc m)} {V : Val n}
              {W : ClosVal} {T : ClosTerminal} {φ₁ φ₂ : Eff}
          → ρ ∣ M ⇓c clos⦅ ρ′ ,ƛ M′ ⦆ # φ₁
          → ρ ∣ V ⇓v W
          → ρ′ ∷ᵨ W ∣ M′ ⇓c T # φ₂
            -----------------------------
          → ρ ∣ M · V ⇓c T # φ₁ + φ₂

  evalForce : ∀ {m : ℕ} {V : Val n} {ρ′ : Env m} {M : Comp m}
                {T : ClosTerminal} {φ : Eff}
            → ρ ∣ V ⇓v clos⦅ ρ′ ,⟪ M ⟫⦆
            → ρ′ ∣ M ⇓c T # φ
              -----------------
            → ρ ∣ V ! ⇓c T # φ

  evalLetin : ∀ {M : Comp n} {W : ClosVal} {T : ClosTerminal}
                {N : Comp (suc n)} {φ₁ φ₂ : Eff}
            → ρ ∣ M ⇓c return W # φ₁
            → ρ ∷ᵨ W ∣ N ⇓c T # φ₂
              ---------------------------
            → ρ ∣ $⟵ M ⋯ N ⇓c T # φ₁ + φ₂

  evalTick : ρ ∣ tick ⇓c return unit # tock

infix 4 _∣_⇓v_
infix 4 _∣_⇓c_#_
