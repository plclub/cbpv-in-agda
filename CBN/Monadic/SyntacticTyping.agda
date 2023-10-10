open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)

open import CBN.Monadic.Terms
open import Effects

module CBN.Monadic.SyntacticTyping (E : Effect) where

open import CBN.Monadic.Types E
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

data _⊢_⦂_ : Ctx n → Term n → Type → Set where
  typeVar : Γ ⊢ # m ⦂ Γ m

  typeUnit : Γ ⊢ unit ⦂ 𝟙

  typeInl : Γ ⊢ e ⦂ τ₁
            -------------------
          → Γ ⊢ inl e ⦂ τ₁ ∪ τ₂

  typeInr : Γ ⊢ e ⦂ τ₂
            -------------------
          → Γ ⊢ inr e ⦂ τ₁ ∪ τ₂

  typePair : Γ ⊢ e₁ ⦂ τ₁
           → Γ ⊢ e₂ ⦂ τ₂
             -------------------------
           → Γ ⊢ ⟨ e₁ , e₂ ⟩ ⦂ τ₁ * τ₂

  typeAbs : Γ ∷ τ ⊢ e ⦂ τ′
            ----------------
          → Γ ⊢ ƛ e ⦂ τ ⇒ τ′

  typeApp : Γ ⊢ e₁ ⦂ τ′ ⇒ τ
          → Γ ⊢ e₂ ⦂ τ′
            ---------------
          → Γ ⊢ e₁ · e₂ ⦂ τ

  typeSeq : Γ ⊢ e₁ ⦂ 𝟙
          → Γ ⊢ e₂ ⦂ τ
            ---------------
          → Γ ⊢ e₁ » e₂ ⦂ τ

  typeFst : Γ ⊢ e ⦂ τ₁ * τ₂
            ---------------
          → Γ ⊢ fst e ⦂ τ₁

  typeSnd : Γ ⊢ e ⦂ τ₁ * τ₂
            ---------------
          → Γ ⊢ snd e ⦂ τ₂

  typeCase : Γ ⊢ e ⦂ τ₁ ∪ τ₂
           → Γ ∷ τ₁ ⊢ e₁ ⦂ τ
           → Γ ∷ τ₂ ⊢ e₂ ⦂ τ
             ------------------------------
           → Γ ⊢ case e inl⇒ e₁ inr⇒ e₂ ⦂ τ

  typeReturn : Γ ⊢ e ⦂ τ
               --------------------
             → Γ ⊢ return e ⦂ 𝑻 φ τ

  typeBind : Γ ⊢ e₁ ⦂ 𝑻 φ₁ τ′
           → Γ ∷ τ′ ⊢ e₂ ⦂ 𝑻 φ₂ τ
           → φ₁ + φ₂ ≤ φ
             -----------------------
           → Γ ⊢ $⟵ e₁ ⋯ e₂ ⦂ 𝑻 φ τ

  typeTick : tock ≤ φ
             ----------------
           → Γ ⊢ tick ⦂ 𝑻 φ 𝟙

infix 4 _⊢_⦂_
