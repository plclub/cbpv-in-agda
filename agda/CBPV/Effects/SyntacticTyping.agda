import Relation.Binary.PropositionalEquality as Eq
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open Eq using (_≡_; refl)

open import CBPV.Effects.Renaming
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

mutual
  val-typepres-renaming : ∀ {n n′ : ℕ} {Γ : Ctx n} {V : Val n′} {A : ValType}
                            {ρ : Ren n n′} {Δ : Ctx n′}
                         → Δ ⊢v V ⦂ A
                         → (∀ (m : Fin n′) → Δ m ≡ Γ (ρ m))
                           --------------------------------
                         → Γ ⊢v V [ ρ ]v ⦂ A
  val-typepres-renaming (typeVar {m}) pf rewrite pf m = typeVar
  val-typepres-renaming typeUnit _ = typeUnit
  val-typepres-renaming (typeThunk Δ⊢M⦂B) pf =
    typeThunk (comp-typepres-renaming Δ⊢M⦂B pf)

  comp-typepres-renaming : ∀ {n n′ : ℕ} {Γ : Ctx n} {M : Comp n′} {B : CompType}
                             {φ : Eff} {ρ : Ren n n′} {Δ : Ctx n′}
                         → Δ ⊢c M ⦂ B # φ
                         → (∀ (m : Fin n′) → Δ m ≡ Γ (ρ m))
                           --------------------------------
                         → Γ ⊢c M [ ρ ]c ⦂ B # φ
  comp-typepres-renaming (typeAbs Δ⊢M⦂A⇒B) pf =
    typeAbs (comp-typepres-renaming Δ⊢M⦂A⇒B ext-pf)
    where
      ext-pf = λ where
                   zero    → refl
                   (suc m) → pf m
  comp-typepres-renaming (typeApp Δ⊢M⦂B Δ⊢V⦂A) pf =
    typeApp (comp-typepres-renaming Δ⊢M⦂B pf) (val-typepres-renaming Δ⊢V⦂A pf)
  comp-typepres-renaming (typeSequence Δ⊢V⦂𝟙 Δ⊢M⦂B) pf =
    typeSequence
      (val-typepres-renaming Δ⊢V⦂𝟙 pf)
      (comp-typepres-renaming Δ⊢M⦂B pf)
  comp-typepres-renaming (typeForce Δ⊢V⦂𝑼φ′B φ′≤φ) pf =
    typeForce (val-typepres-renaming Δ⊢V⦂𝑼φ′B pf) φ′≤φ
  comp-typepres-renaming (typeRet Δ⊢V⦂A) pf =
    typeRet (val-typepres-renaming Δ⊢V⦂A pf)
  comp-typepres-renaming (typeLetin Δ⊢M⦂𝑭A Δ∷A⊢N⦂B φ₁+φ₂≤φ) pf =
    typeLetin
      (comp-typepres-renaming Δ⊢M⦂𝑭A pf)
      (comp-typepres-renaming Δ∷A⊢N⦂B ext-pf)
      φ₁+φ₂≤φ
    where
      ext-pf = λ where
                   zero    → refl
                   (suc m) → pf m
  comp-typepres-renaming (typeTick tock≤φ) _ = typeTick tock≤φ
