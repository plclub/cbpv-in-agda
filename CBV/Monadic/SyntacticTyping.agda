open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)

open import CBV.Monadic.Terms
open import Effects

module CBV.Monadic.SyntacticTyping (E : Effect) where

open import CBV.Monadic.Types E
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
  data _⊩_⦂_ : Ctx n → Value n → Type → Set where
    typeVar : Γ ⊩ # m ⦂ Γ m

    typeUnit : Γ ⊩ unit ⦂ 𝟙

    typeAbs : Γ ∷ τ ⊢ e ⦂ τ′
              ----------------
            → Γ ⊩ ƛ e ⦂ τ ⇒ τ′

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

infix 4 _⊩_⦂_
infix 4 _⊢_⦂_
