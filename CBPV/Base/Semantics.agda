open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)

open import CBPV.Base.Terms

module CBPV.Base.Semantics where

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
  evalVar : ∀ {m : Fin n}
            --------------
          → ρ ∣ # m ⇓v ρ m

  evalUnit : ρ ∣ unit ⇓v unit

  evalThunk : ∀ {M : Comp n}
              --------------------------
            → ρ ∣ ⟪ M ⟫ ⇓v clos⦅ ρ ,⟪ M ⟫⦆

infix 4 _∣_⇓v_
infix 4 _∣_⇓c_

data _∣_⇓c_ {n : ℕ} (ρ : Env n) : Comp n → ClosTerminal → Set where
  evalAbs : ∀ {M : Comp (suc n)}
            -----------------------
          → ρ ∣ ƛ M ⇓c clos⦅ ρ ,ƛ M ⦆

  evalRet : ∀ {V : Val n} {W : ClosVal}
          → ρ ∣ V ⇓v W
            ------------------------
          → ρ ∣ return V ⇓c return W

  evalSeq : ∀ {V : Val n} {M : Comp n} {T : ClosTerminal}
          → ρ ∣ V ⇓v unit
          → ρ ∣ M ⇓c T
            --------------
          → ρ ∣ V » M ⇓c T

  evalApp : ∀ {m : ℕ} {M : Comp n} {ρ′ : Env m} {M′ : Comp (suc m)} {V : Val n}
              {W : ClosVal} {T : ClosTerminal}
          → ρ ∣ M ⇓c clos⦅ ρ′ ,ƛ M′ ⦆
          → ρ ∣ V ⇓v W
          → ρ′ ∷ᵨ W ∣ M′ ⇓c T
            ----------------
          → ρ ∣ M · V ⇓c T

  evalForce : ∀ {m : ℕ} {V : Val n} {ρ′ : Env m} {M : Comp m}
                {T : ClosTerminal}
            → ρ ∣ V ⇓v clos⦅ ρ′ ,⟪ M ⟫⦆
            → ρ′ ∣ M ⇓c T
              -----------
            → ρ ∣ V ! ⇓c T

  evalLetin : ∀ {M : Comp n} {W : ClosVal} {T : ClosTerminal}
                {N : Comp (suc n)}
            → ρ ∣ M ⇓c return W
            → ρ ∷ᵨ W ∣ N ⇓c T
              -----------------
            → ρ ∣ $⟵ M ⋯ N ⇓c T
