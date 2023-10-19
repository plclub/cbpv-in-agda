import Relation.Binary.PropositionalEquality as Eq
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open Eq using (_≡_; refl)

open import CBPV.Effects.Terms
open import Effects

module CBPV.Effects.SyntacticTyping (E : Effect) where

open import CBPV.Effects.Types E
open Effect E

Ctx : ℕ → Set
Ctx n = Fin n → ValType

variable Γ Δ : Ctx n

∅ : Ctx zero
∅ ()

_∷_ : ∀ {n : ℕ} → Ctx n → ValType → Ctx (suc n)
Γ ∷ A = λ where
          zero → A
          (suc n) → Γ n

infixl 5 _∷_

mutual
  data _⊢v_⦂_ : Ctx n → Val n → ValType → Set where
    typeVar : Γ ⊢v ♯ m ⦂ Γ m

    typeUnit : Γ ⊢v unit ⦂ 𝟙

    typeThunk : Γ ⊢c M ⦂ B # φ
                ------------------
              → Γ ⊢v ⟪ M ⟫ ⦂ 𝑼 φ B

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

  data _⊢c_⦂_#_ : Ctx n → Comp n → CompType → Eff → Set where
    typeAbs : Γ ∷ A ⊢c M ⦂ B # φ
              --------------------
            → Γ ⊢c ƛ M ⦂ A ⇒ B # φ

    typeApp : Γ ⊢c M ⦂ A ⇒ B # φ
            → Γ ⊢v V ⦂ A
              ------------------
            → Γ ⊢c M · V ⦂ B # φ

    typeSequence : Γ ⊢v V ⦂ 𝟙
                 → Γ ⊢c M ⦂ B # φ
                   ------------------
                 → Γ ⊢c V » M ⦂ B # φ

    typeCpair : Γ ⊢c M₁ ⦂ B₁ # φ
              → Γ ⊢c M₂ ⦂ B₂ # φ
                ------------------------------
              → Γ ⊢c ⟨ M₁ , M₂ ⟩ ⦂ B₁ & B₂ # φ

    typeProjl : Γ ⊢c M ⦂ B₁ & B₂ # φ
                ---------------------
              → Γ ⊢c projl M ⦂ B₁ # φ

    typeProjr : Γ ⊢c M ⦂ B₁ & B₂ # φ
                ---------------------
              → Γ ⊢c projr M ⦂ B₂ # φ

    typeForce : Γ ⊢v V ⦂ 𝑼 φ₁ B
              → φ₁ ≤ φ₂
                -----------------
              → Γ ⊢c V ! ⦂ B # φ₂

    typeRet : Γ ⊢v V ⦂ A
            → pure ≤ φ
              -----------------------
            → Γ ⊢c return V ⦂ 𝑭 A # φ

    typeLetin : Γ ⊢c M ⦂ 𝑭 A # φ₁
              → Γ ∷ A ⊢c N ⦂ B # φ₂
              → φ₁ + φ₂ ≤ φ
                ----------------------
              → Γ ⊢c $⟵ M ⋯ N ⦂ B # φ

    typeSplit : Γ ⊢v V ⦂ A₁ * A₂
              → Γ ∷ A₁ ∷ A₂ ⊢c M ⦂ B # φ
                ------------------------
              → Γ ⊢c $≔ V ⋯ M ⦂ B # φ

    typeCase : Γ ⊢v V ⦂ A₁ ∪ A₂
             → Γ ∷ A₁ ⊢c M₁ ⦂ B # φ
             → Γ ∷ A₂ ⊢c M₂ ⦂ B # φ
               -----------------------------------
             → Γ ⊢c case V inl⇒ M₁ inr⇒ M₂ ⦂ B # φ

    typeTick : tock ≤ φ
               -------------------
             → Γ ⊢c tick ⦂ 𝑭 𝟙 # φ

infix 4 _⊢v_⦂_
infix 4 _⊢c_⦂_#_

type-subeff : Γ ⊢c M ⦂ B # φ
            → φ ≤ ψ
              --------------
            → Γ ⊢c M ⦂ B # ψ
type-subeff (typeAbs pf) φ≤ψ = typeAbs (type-subeff pf φ≤ψ)
type-subeff (typeApp pf₁ pf₂) φ≤ψ = typeApp (type-subeff pf₁ φ≤ψ) pf₂
type-subeff (typeSequence pf₁ pf₂) φ≤ψ = typeSequence pf₁ (type-subeff pf₂ φ≤ψ)
type-subeff (typeForce pf φ₁≤φ₂) φ₂≤φ₃ = typeForce pf (≤-trans φ₁≤φ₂ φ₂≤φ₃)
type-subeff (typeRet pf pure≤φ) φ≤ψ = typeRet pf (≤-trans pure≤φ φ≤ψ)
type-subeff (typeLetin pf₁ pf₂ φ₁+φ₂≤φ) φ≤ψ =
  typeLetin pf₁ pf₂ (≤-trans φ₁+φ₂≤φ φ≤ψ)
type-subeff (typeSplit ⊢V ⊢M) φ≤ψ = typeSplit ⊢V (type-subeff ⊢M φ≤ψ)
type-subeff (typeCase ⊢V ⊢M₁ ⊢M₂) φ≤ψ =
  typeCase ⊢V (type-subeff ⊢M₁ φ≤ψ) (type-subeff ⊢M₂ φ≤ψ)
type-subeff (typeTick tock) φ≤ψ = typeTick (≤-trans tock φ≤ψ)
type-subeff (typeCpair ⊢M₁ ⊢M₂) φ≤ψ =
  typeCpair (type-subeff ⊢M₁ φ≤ψ) (type-subeff ⊢M₂ φ≤ψ)
type-subeff (typeProjl ⊢M) φ≤ψ = typeProjl (type-subeff ⊢M φ≤ψ)
type-subeff (typeProjr ⊢M) φ≤ψ = typeProjr (type-subeff ⊢M φ≤ψ)
