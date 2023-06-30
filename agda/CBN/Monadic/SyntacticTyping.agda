import Relation.Binary.PropositionalEquality as Eq
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open Eq using (_≡_)

open import CBN.Monadic.Renaming
open import CBN.Monadic.Terms
open import Effects

module CBN.Monadic.SyntacticTyping (E : Effect) where

open import CBN.Monadic.Types E
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
  data _⊢_⦂_ {n : ℕ} (Γ : Ctx n) : Term n → Type → Set where
    typeVar : {m : Fin n}
              -------------
            → Γ ⊢ # m ⦂ Γ m

    typeUnit : Γ ⊢ unit ⦂ 𝟙

    typeAbs : {τ τ′ : Type} {e : Term (suc n)}
            → Γ ∷ τ ⊢ e ⦂ τ′
              ----------------
            → Γ ⊢ ƛ e ⦂ τ ⇒ τ′

    typeApp : ∀ {e₁ e₂ : Term n} {τ τ′ : Type}
            → Γ ⊢ e₁ ⦂ τ′ ⇒ τ
            → Γ ⊢ e₂ ⦂ τ′
              ---------------
            → Γ ⊢ e₁ · e₂ ⦂ τ

    typeSeq : ∀ {e₁ e₂ : Term n} {τ : Type}
            → Γ ⊢ e₁ ⦂ 𝟙
            → Γ ⊢ e₂ ⦂ τ
              ---------------
            → Γ ⊢ e₁ » e₂ ⦂ τ

    typeReturn : ∀ {e : Term n} {τ : Type} {φ : Eff}
               → Γ ⊢ e ⦂ τ
                 --------------------
               → Γ ⊢ return e ⦂ 𝑻 φ τ

    typeBind : ∀ {e₁ e₂ : Term n} {φ₁ φ₂ φ : Eff} {τ τ′ : Type}
             → Γ ⊢ e₁ ⦂ 𝑻 φ₁ τ′
             → Γ ⊢ e₂ ⦂ 𝑻 φ₂ τ
             → φ₁ + φ₂ ≤ φ
               -----------------------
             → Γ ⊢ $⇐ e₁ ⋯ e₂ ⦂ 𝑻 φ τ

    typeTick : ∀ {φ : Eff}
             → tock ≤ φ
               ----------------
             → Γ ⊢ tick ⦂ 𝑻 φ 𝟙

infix 4 _⊢_⦂_
