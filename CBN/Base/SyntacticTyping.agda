open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)

open import CBN.Base.Terms
open import CBN.Base.Types

module CBN.Base.SyntacticTyping where

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

  typeCase : Γ ⊢ e ⦂ τ₁ ∪ τ₂
           → Γ ∷ τ₁ ⊢ e₁ ⦂ τ
           → Γ ∷ τ₂ ⊢ e₂ ⦂ τ
             ------------------------------
           → Γ ⊢ case e inl⇒ e₁ inr⇒ e₂ ⦂ τ

infix 4 _⊢_⦂_
