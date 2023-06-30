open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)

open import CBPV.Effects.Terms
open import Effects

module CBPV.Effects.SyntacticTyping (E : Effect) where

open import CBPV.Effects.Types E
open Effect E

Ctx : ℕ → Set
Ctx n = Fin n → ValType

∅ : Ctx zero
∅ ()

_∷_ : ∀ {n : ℕ} → Ctx n → ValType → Ctx (suc n)
Γ ∷ A = λ where
          zero → A
          (suc n) → Γ n

infixl 5 _∷_

mutual
  data _⊢v_⦂_ {n : ℕ} (Γ : Ctx n) : Val n → ValType → Set where
    typeVar : ∀ {m : Fin n}
              --------------
            → Γ ⊢v ♯ m ⦂ Γ m

    typeUnit : Γ ⊢v unit ⦂ 𝟙

    typeThunk : ∀ {M : Comp n} {B : CompType} {φ : Eff}
              → Γ ⊢c M ⦂ B # φ
                ----------------
              → Γ ⊢v ⟪ M ⟫ ⦂ 𝑼 φ B

  data _⊢c_⦂_#_ {n : ℕ} (Γ : Ctx n) : Comp n → CompType → Eff → Set where
    typeAbs : ∀ {A : ValType} {M : Comp (suc n)} {B : CompType}
                {φ : Eff}
            → Γ ∷ A ⊢c M ⦂ B # φ
              ----------------
            → Γ ⊢c ƛ M ⦂ A ⇒ B # φ

    typeApp : ∀ {M : Comp n} {A : ValType} {B : CompType} {V : Val n} {φ : Eff}
            → Γ ⊢c M ⦂ A ⇒ B # φ
            → Γ ⊢v V ⦂ A
              --------------
            → Γ ⊢c M · V ⦂ B # φ

    typeSequence : ∀ {V : Val n} {M : Comp n} {B : CompType} {φ : Eff}
                 → Γ ⊢v V ⦂ 𝟙
                 → Γ ⊢c M ⦂ B # φ
                   --------------
                 → Γ ⊢c V » M ⦂ B # φ

    typeForce : ∀ {V : Val n} {B : CompType} {φ₁ φ₂ : Eff}
              → Γ ⊢v V ⦂ 𝑼 φ₁ B
              → φ₁ ≤ φ₂
                ------------
              → Γ ⊢c V ! ⦂ B # φ₂

    typeRet : ∀ {V : Val n} {A : ValType} {φ : Eff}
            → Γ ⊢v V ⦂ A
              -------------------
            → Γ ⊢c return V ⦂ 𝑭 A # φ
    typeLetin : ∀ {M : Comp n} {A : ValType} {N : Comp (suc n)} {B : CompType}
                  {φ₁ φ₂ φ : Eff}
              → Γ ⊢c M ⦂ 𝑭 A # φ₁
              → Γ ∷ A ⊢c N ⦂ B # φ₂
              → φ₁ + φ₂ ≤ φ
                ------------------
              → Γ ⊢c $⇐ M ⋯ N ⦂ B # φ

    typeTick : ∀ {φ : Eff}
             → tock ≤ φ
               -----------------------
             → Γ ⊢c tick ⦂ 𝑭 𝟙 # φ

infix 4 _⊢v_⦂_
infix 4 _⊢c_⦂_#_

-- Subeffecting well-typed terms

type-subeff : ∀ {n : ℕ} {Γ : Ctx n} {M : Comp n} {B : CompType} {φ ψ : Eff}
            → Γ ⊢c M ⦂ B # φ
            → φ ≤ ψ
            → Γ ⊢c M ⦂ B # ψ
type-subeff (typeAbs pf) φ≤ψ = typeAbs (type-subeff pf φ≤ψ)
type-subeff (typeApp pf₁ pf₂) φ≤ψ = typeApp (type-subeff pf₁ φ≤ψ) pf₂
type-subeff (typeSequence pf₁ pf₂) φ≤ψ = typeSequence pf₁ (type-subeff pf₂ φ≤ψ)
type-subeff (typeForce pf φ₁≤φ₂) φ₂≤φ₃ = typeForce pf (≤-trans φ₁≤φ₂ φ₂≤φ₃)
type-subeff (typeRet pf) φ≤ψ = typeRet pf
type-subeff (typeLetin pf₁ pf₂ φ₁+φ₂≤φ) φ≤ψ =
  typeLetin pf₁ pf₂ (≤-trans φ₁+φ₂≤φ φ≤ψ)
type-subeff (typeTick tock) φ≤ψ = typeTick (≤-trans tock φ≤ψ)
