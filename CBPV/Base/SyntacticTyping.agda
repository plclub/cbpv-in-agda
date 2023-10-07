import Relation.Binary.PropositionalEquality as Eq
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open Eq using (_≡_; refl)

open import CBPV.Base.Terms
open import CBPV.Base.Types

module CBPV.Base.SyntacticTyping where

Ctx : ℕ → Set
Ctx n = Fin n → ValType

variable Γ Δ : Ctx n

∅ : Ctx zero
∅ ()

_∷_ : Ctx n → ValType → Ctx (suc n)
Γ ∷ A = λ where
          zero → A
          (suc n) → Γ n

infixl 5 _∷_

mutual
  data _⊢v_⦂_ : Ctx n → Val n → ValType → Set where
    typeVar : Γ ⊢v # m ⦂ Γ m

    typeUnit : Γ ⊢v unit ⦂ 𝟙

    typeThunk : Γ ⊢c M ⦂ B
                ----------------
              → Γ ⊢v ⟪ M ⟫ ⦂ 𝑼 B

    typePair : Γ ⊢v V₁ ⦂ A₁
             → Γ ⊢v V₂ ⦂ A₂
               --------------------------
             → Γ ⊢v ⟨ V₁ , V₂ ⟩ ⦂ A₁ * A₂

    typeInl : Γ ⊢v V ⦂ A₁
              --------------------
            → Γ ⊢v inl V ⦂ A₁ ∪ A₂

    typeInr : Γ ⊢v V ⦂ A₂
              --------------------
            → Γ ⊢v inr V ⦂ A₁ ∪ A₂

  data _⊢c_⦂_ : Ctx n → Comp n → CompType → Set where
    typeAbs : Γ ∷ A ⊢c M ⦂ B
              ----------------
            → Γ ⊢c ƛ M ⦂ A ⇒ B

    typeApp : Γ ⊢c M ⦂ A ⇒ B
            → Γ ⊢v V ⦂ A
              --------------
            → Γ ⊢c M · V ⦂ B

    typeSequence : Γ ⊢v V ⦂ 𝟙
                 → Γ ⊢c M ⦂ B
                   --------------
                 → Γ ⊢c V » M ⦂ B

    typeForce : Γ ⊢v V ⦂ 𝑼 B
                ------------
              → Γ ⊢c V ! ⦂ B

    typeRet : Γ ⊢v V ⦂ A
              -------------------
            → Γ ⊢c return V ⦂ 𝑭 A

    typeLetin : Γ ⊢c M ⦂ 𝑭 A
              → Γ ∷ A ⊢c N ⦂ B
                ------------------
              → Γ ⊢c $⟵ M ⋯ N ⦂ B

    typeSplit : Γ ⊢v V ⦂ A₁ * A₂
              → Γ ∷ A₁ ∷ A₂ ⊢c M ⦂ B
                --------------------
              → Γ ⊢c $≔ V ⋯ M ⦂ B

    typeCase : Γ ⊢v V ⦂ A₁ ∪ A₂
             → Γ ∷ A₁ ⊢c M₁ ⦂ B
             → Γ ∷ A₂ ⊢c M₂ ⦂ B
               -------------------------------
             → Γ ⊢c case V inl⇒ M₁ inr⇒ M₂ ⦂ B

infix 4 _⊢v_⦂_
infix 4 _⊢c_⦂_
