open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)

open import CBV.Base.Terms
open import CBV.Base.Types

module CBV.Base.SyntacticTyping where

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
  data _⊩_⦂_ : Ctx n → Value n → Type → Set where
    typeVar : Γ ⊩ # m ⦂ Γ m

    typeUnit : Γ ⊩ unit ⦂ 𝟙

    typeAbs : Γ ∷ τ ⊢ e ⦂ τ′
              ----------------
            → Γ ⊩ ƛ e ⦂ τ ⇒ τ′

    typePair : Γ ⊩ v₁ ⦂ τ₁
             → Γ ⊩ v₂ ⦂ τ₂
               -------------------------
             → Γ ⊩ ⟨ v₁ , v₂ ⟩ ⦂ τ₁ * τ₂

    typeInl : Γ ⊩ v ⦂ τ₁
              -------------------
            → Γ ⊩ inl v ⦂ τ₁ ∪ τ₂

    typeInr : Γ ⊩ v ⦂ τ₂
              -------------------
            → Γ ⊩ inr v ⦂ τ₁ ∪ τ₂

  data _⊢_⦂_ : Ctx n → Exp n → Type → Set where
    typeVal : Γ ⊩ v ⦂ τ
              -------------
            → Γ ⊢ val v ⦂ τ

    typeApp : Γ ⊢ e₁ ⦂ τ′ ⇒ τ
            → Γ ⊢ e₂ ⦂ τ′
              ---------------
            → Γ ⊢ e₁ · e₂ ⦂ τ

    typeSeq : Γ ⊢ e₁ ⦂ 𝟙
            → Γ ⊢ e₂ ⦂ τ
              ---------------
            → Γ ⊢ e₁ » e₂ ⦂ τ

    typePair : Γ ⊢ e₁ ⦂ τ₁
             → Γ ⊢ e₂ ⦂ τ₂
               -------------------------
             → Γ ⊢ ⟨ e₁ , e₂ ⟩ ⦂ τ₁ * τ₂

    typeInl : Γ ⊢ e ⦂ τ₁
              -------------------
            → Γ ⊢ inl e ⦂ τ₁ ∪ τ₂

    typeInr : Γ ⊢ e ⦂ τ₂
              -------------------
            → Γ ⊢ inr e ⦂ τ₁ ∪ τ₂

    typeCase : Γ ⊢ e ⦂ τ₁ ∪ τ₂
             → Γ ∷ τ₁ ⊢ e₁ ⦂ τ
             → Γ ∷ τ₂ ⊢ e₂ ⦂ τ
               ------------------------------
             → Γ ⊢ case e inl⇒ e₁ inr⇒ e₂ ⦂ τ

    typeSplit : Γ ⊢ e₁ ⦂ τ₁ * τ₂
              → Γ ∷ τ₁ ∷ τ₂ ⊢ e₂ ⦂ τ
                --------------------
              → Γ ⊢ $≔ e₁ ⋯ e₂ ⦂ τ

infix 4 _⊩_⦂_
infix 4 _⊢_⦂_
