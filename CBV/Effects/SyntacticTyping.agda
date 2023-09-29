open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)

open import CBV.Effects.Terms
open import Effects

module CBV.Effects.SyntacticTyping (E : Effect) where

open import CBV.Effects.Types E
open Effect E

Ctx : ℕ → Set
Ctx n = Fin n → Type

variable Γ : Ctx n

∅ : Ctx zero
∅ ()

_∷_ : Ctx n → Type → Ctx (suc n)
Γ ∷ τ = λ where
          zero → τ
          (suc n) → Γ n

infixl 5 _∷_

mutual
  data _⊩_⦂_#_ : Ctx n → Value n → Type → Eff → Set where
    typeVar : Γ ⊩ ♯ m ⦂ Γ m # φ

    typeUnit : Γ ⊩ unit ⦂ 𝟙 # φ

    typeAbs : Γ ∷ τ ⊢ e ⦂ τ′ # φ′
              ------------------------
            → Γ ⊩ ƛ e ⦂ τ ─ φ′ ⟶ τ′ # φ

  data _⊢_⦂_#_ : Ctx n → Exp n → Type → Eff → Set where
    typeVal : Γ ⊩ v ⦂ τ # φ
              -----------------
            → Γ ⊢ val v ⦂ τ # φ

    typeApp : Γ ⊢ e₁ ⦂ τ′ ─ φ₃ ⟶ τ # φ₁
            → Γ ⊢ e₂ ⦂ τ′ # φ₂
            → φ₁ + φ₂ + φ₃ ≤ φ
              -------------------------
            → Γ ⊢ e₁ · e₂ ⦂ τ # φ

    typeSeq : Γ ⊢ e₁ ⦂ 𝟙 # φ₁
            → Γ ⊢ e₂ ⦂ τ # φ₂
            → φ₁ + φ₂ ≤ φ
              -------------------------
            → Γ ⊢ e₁ » e₂ ⦂ τ # φ

    typeTick : tock ≤ φ
               ----------------
             → Γ ⊢ tick ⦂ 𝟙 # φ

infix 4 _⊩_⦂_#_
infix 4 _⊢_⦂_#_
