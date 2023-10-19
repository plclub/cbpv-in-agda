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
    typeVar : pure ≤ φ
              -----------------
            → Γ ⊩ ♯ m ⦂ Γ m # φ

    typeUnit : pure ≤ φ
               ---------------
             → Γ ⊩ unit ⦂ 𝟙 # φ

    typeAbs : Γ ∷ τ ⊢ e ⦂ τ′ # φ′
            → pure ≤ φ
              -------------------------
            → Γ ⊩ ƛ e ⦂ τ ─ φ′ ⟶ τ′ # φ

    typePair : Γ ⊩ v₁ ⦂ τ₁ # φ
             → Γ ⊩ v₂ ⦂ τ₂ # φ
               -----------------------------
             → Γ ⊩ ⟨ v₁ , v₂ ⟩ ⦂ τ₁ * τ₂ # φ

    typeInl : Γ ⊩ v ⦂ τ₁ # φ
              -----------------------
            → Γ ⊩ inl v ⦂ τ₁ ∪ τ₂ # φ

    typeInr : Γ ⊩ v ⦂ τ₂ # φ
              -----------------------
            → Γ ⊩ inr v ⦂ τ₁ ∪ τ₂ # φ

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

    typePair : Γ ⊢ e₁ ⦂ τ₁ # φ₁
             → Γ ⊢ e₂ ⦂ τ₂ # φ₂
             → φ₁ + φ₂ ≤ φ
               -----------------------------
             → Γ ⊢ ⟨ e₁ , e₂ ⟩ ⦂ τ₁ * τ₂ # φ

    typeInl : Γ ⊢ e ⦂ τ₁ # φ
              -----------------------
            → Γ ⊢ inl e ⦂ τ₁ ∪ τ₂ # φ

    typeInr : Γ ⊢ e ⦂ τ₂ # φ
              -----------------------
            → Γ ⊢ inr e ⦂ τ₁ ∪ τ₂ # φ

    typeCase : Γ ⊢ e ⦂ τ₁ ∪ τ₂ # φ₁
             → Γ ∷ τ₁ ⊢ e₁ ⦂ τ # φ₂
             → Γ ∷ τ₂ ⊢ e₂ ⦂ τ # φ₂
             → φ₁ + φ₂ ≤ φ
               ----------------------------------
             → Γ ⊢ case e inl⇒ e₁ inr⇒ e₂ ⦂ τ # φ

    typeSplit : Γ ⊢ e₁ ⦂ τ₁ * τ₂ # φ₁
              → Γ ∷ τ₁ ∷ τ₂ ⊢ e₂ ⦂ τ # φ₂
              → φ₁ + φ₂ ≤ φ
                -------------------------
              → Γ ⊢ $≔ e₁ ⋯ e₂ ⦂ τ # φ

    typeTick : tock ≤ φ
               ----------------
             → Γ ⊢ tick ⦂ 𝟙 # φ

infix 4 _⊩_⦂_#_
infix 4 _⊢_⦂_#_

type-val-eff-pure-≤ : Γ ⊩ v ⦂ τ₁ # φ
                      --------------
                    → pure ≤ φ
type-val-eff-pure-≤ (typeVar pure≤φ) = pure≤φ
type-val-eff-pure-≤ (typeUnit pure≤φ) = pure≤φ
type-val-eff-pure-≤ (typeAbs _ pure≤φ) = pure≤φ
type-val-eff-pure-≤ (typePair ⊩v₁ ⊩v₂) = type-val-eff-pure-≤ ⊩v₂
type-val-eff-pure-≤ (typeInl ⊩v) = type-val-eff-pure-≤ ⊩v
type-val-eff-pure-≤ (typeInr ⊩v) = type-val-eff-pure-≤ ⊩v

type-subeff-val : Γ ⊩ v ⦂ τ # φ
                → φ ≤ ψ
                  -------------
                → Γ ⊩ v ⦂ τ # ψ
type-subeff-val (typeVar pure≤φ) φ≤ψ = typeVar (≤-trans pure≤φ φ≤ψ)
type-subeff-val (typeUnit pure≤φ) φ≤ψ = typeUnit (≤-trans pure≤φ φ≤ψ)
type-subeff-val (typeAbs ⊢e pure≤φ) φ≤ψ = typeAbs ⊢e (≤-trans pure≤φ φ≤ψ)
type-subeff-val (typePair ⊩v₁ ⊩v₂) φ≤ψ =
  typePair (type-subeff-val ⊩v₁ φ≤ψ) (type-subeff-val ⊩v₂ φ≤ψ)
type-subeff-val (typeInl ⊩v) φ≤ψ = typeInl (type-subeff-val ⊩v φ≤ψ)
type-subeff-val (typeInr ⊩v) φ≤ψ = typeInr (type-subeff-val ⊩v φ≤ψ)

type-subeff : Γ ⊢ e ⦂ τ # φ
            → φ ≤ ψ
              -------------
            → Γ ⊢ e ⦂ τ # ψ
type-subeff (typeVal ⊩v) φ≤ψ = typeVal (type-subeff-val ⊩v φ≤ψ)
type-subeff (typeApp ⊢e₁ ⊢e₂ pf) φ≤ψ = typeApp ⊢e₁ ⊢e₂ (≤-trans pf φ≤ψ)
type-subeff (typeSeq ⊢e₁ ⊢e₂ pf) φ≤ψ = typeSeq ⊢e₁ ⊢e₂ (≤-trans pf φ≤ψ)
type-subeff (typePair ⊢e₁ ⊢e₂ pf) φ≤ψ = typePair ⊢e₁ ⊢e₂ (≤-trans pf φ≤ψ)
type-subeff (typeInl ⊢e) φ≤ψ = typeInl (type-subeff ⊢e φ≤ψ)
type-subeff (typeInr ⊢e) φ≤ψ = typeInr (type-subeff ⊢e φ≤ψ)
type-subeff (typeCase ⊢e ⊢e₁ ⊢e₂ x) φ≤ψ = typeCase ⊢e ⊢e₁ ⊢e₂ (≤-trans x φ≤ψ)
type-subeff (typeSplit ⊢e ⊢e₁ pf) φ≤ψ = typeSplit ⊢e ⊢e₁ (≤-trans pf φ≤ψ)
type-subeff (typeTick x) φ≤ψ = typeTick (≤-trans x φ≤ψ)
