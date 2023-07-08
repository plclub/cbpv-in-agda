open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)

open import CBV.Effects.Terms
open import Effects

module CBV.Effects.SyntacticTyping (E : Effect) where

open import CBV.Effects.Types E
open Effect E

Ctx : ℕ → Set
Ctx n = Fin n → Type

∅ : Ctx zero
∅ ()

_∷_ : ∀ {n : ℕ} → Ctx n → Type → Ctx (suc n)
Γ ∷ τ = λ where
          zero → τ
          (suc n) → Γ n

infixl 5 _∷_

mutual
  data _⊩_⦂_#_ {n : ℕ} (Γ : Ctx n) : Value n → Type → Eff → Set where
    typeVar : ∀ {m : Fin n} {φ : Eff}
              -----------------
            → Γ ⊩ ♯ m ⦂ Γ m # φ

    typeUnit : ∀ {φ : Eff}
               ----------------
             → Γ ⊩ unit ⦂ 𝟙 # φ

    typeAbs : {τ τ′ : Type} {e : Exp (suc n)} {φ φ′ : Eff}
            → Γ ∷ τ ⊢ e ⦂ τ′ # φ′
              ------------------------
            → Γ ⊩ ƛ e ⦂ τ ─ φ′ ⟶ τ′ # φ

  data _⊢_⦂_#_ {n : ℕ} (Γ : Ctx n) : Exp n → Type → Eff → Set where
    typeVal : ∀ {v : Value n} {τ : Type} {φ : Eff}
            → Γ ⊩ v ⦂ τ # φ
              -----------------
            → Γ ⊢ val v ⦂ τ # φ

    typeApp : ∀ {e₁ e₂ : Exp n} {τ τ′ : Type} {φ₁ φ₂ φ₃ φ : Eff}
            → Γ ⊢ e₁ ⦂ τ′ ─ φ₃ ⟶ τ # φ₁
            → Γ ⊢ e₂ ⦂ τ′ # φ₂
            → φ₁ + φ₂ + φ₃ ≤ φ
              -------------------------
            → Γ ⊢ e₁ · e₂ ⦂ τ # φ

    typeSeq : ∀ {e₁ e₂ : Exp n} {τ : Type} {φ₁ φ₂ φ : Eff}
            → Γ ⊢ e₁ ⦂ 𝟙 # φ₁
            → Γ ⊢ e₂ ⦂ τ # φ₂
            → φ₁ + φ₂ ≤ φ
              -------------------------
            → Γ ⊢ e₁ » e₂ ⦂ τ # φ

    typeTick : ∀ {φ : Eff}
             → tock ≤ φ
               ----------------
             → Γ ⊢ tick ⦂ 𝟙 # φ

infix 4 _⊩_⦂_#_
infix 4 _⊢_⦂_#_
