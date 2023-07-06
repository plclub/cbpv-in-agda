import Relation.Binary.PropositionalEquality as Eq
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)
open import Level using (0ℓ)
open Eq using (_≡_; refl; sym)

open import CBV.Monadic.Terms
open import CBPV.Effects.Renaming
open import CBPV.Effects.Terms
open import Effects

module CBV.Monadic.Translation (E : Effect) where

import CBPV.Effects.SyntacticTyping E as CBPV
open import CBPV.Effects.Types E
open import CBV.Monadic.SyntacticTyping E
open import CBV.Monadic.Types E
open import CBPV.Effects.Eagerlet E
open CBPV hiding (Ctx; _∷_)
open Effect E
open Effects.Properties E

postulate
  extensionality : Extensionality 0ℓ 0ℓ

record Translation (A B : Set) : Set where
  field
    ⟦_⟧ : A → B

open Translation ⦃...⦄ public

instance
  ⟦Type⟧ : Translation Type ValType
  Translation.⟦ ⟦Type⟧ ⟧ 𝟙 = 𝟙
  Translation.⟦ ⟦Type⟧ ⟧ (τ₁ ⇒ τ₂) = 𝑼 pure (⟦ τ₁ ⟧ ⇒ 𝑭 ⟦ τ₂ ⟧)
  Translation.⟦ ⟦Type⟧ ⟧ (𝑻 φ τ) = 𝑼 φ (𝑭 ⟦ τ ⟧)

  ⟦Ctx⟧ : ∀ {n : ℕ} → Translation (Ctx n) (CBPV.Ctx n)
  Translation.⟦ ⟦Ctx⟧ ⟧ Γ m = ⟦ Γ m ⟧

  mutual
    ⟦Value⟧ : ∀ {n : ℕ} → Translation (Value n) (Val n)
    Translation.⟦ ⟦Value⟧ ⟧ unit = unit
    Translation.⟦ ⟦Value⟧ ⟧ (ƛ e) = ⟪ ƛ ⟦ e ⟧ ⟫
    Translation.⟦ ⟦Value⟧ ⟧ (# x) = ♯ x

    ⟦Exp⟧ : ∀ {n : ℕ} → Translation (Exp n) (Comp n)
    Translation.⟦ ⟦Exp⟧ ⟧ (val v) = return ⟦ v ⟧
    Translation.⟦ ⟦Exp⟧ ⟧ (e₁ · e₂) =
      $⇐ ⟦ e₁ ⟧ ⋯
      $⇐ ⟦ e₂ ⟧ [ suc ]c ⋯
      (♯ suc zero !) · ♯ zero
    Translation.⟦ ⟦Exp⟧ ⟧ (e₁ » e₂) =
      $⇐ ⟦ e₁ ⟧ ⋯
      ♯ zero » ⟦ e₂ ⟧ [ suc ]c
    Translation.⟦ ⟦Exp⟧ ⟧ (return e) = return ⟪ ⟦ e ⟧ ⟫
    Translation.⟦ ⟦Exp⟧ ⟧ ($⟵ e₁ ⋯ e₂) =
      return ⟪ $⟵ $⟵ ⟦ e₁ ⟧ ⋯ ♯ zero ! ⋯ $⟵ ⟦ e₂ ⟧ ⋯ ♯ zero ! ⟫
    Translation.⟦ ⟦Exp⟧ ⟧ (tick) = return ⟪ $⟵ tick ⋯ return ♯ zero ⟫

⟦Γ∷τ⟧-expand : ∀ {n : ℕ} {Γ : Ctx n} {τ : Type}
               → ⟦ Γ ∷ τ ⟧ ≡ ⟦ Γ ⟧ CBPV.∷ ⟦ τ ⟧
⟦Γ∷τ⟧-expand = extensionality λ where
                                  zero    → refl
                                  (suc m) → refl

mutual
  translation-preservation-value : ∀ {n : ℕ} {Γ : Ctx n} {v : Value n}
                                     {τ : Type}
                                 → Γ ⊩ v ⦂ τ
                                   ----------------------
                                 → ⟦ Γ ⟧ ⊢v ⟦ v ⟧ ⦂ ⟦ τ ⟧
  translation-preservation-value typeVar = typeVar
  translation-preservation-value typeUnit = typeUnit
  translation-preservation-value {Γ = Γ} (typeAbs {τ = τ} Γ∷τ⊢e⦂τ′)
    with translation-preservation-exp Γ∷τ⊢e⦂τ′
  ...  | ⟦Γ∷τ⟧⊢⟦e⟧⦂𝑭⟦τ′⟧
    rewrite ⟦Γ∷τ⟧-expand {Γ = Γ} {τ} = typeThunk (typeAbs ⟦Γ∷τ⟧⊢⟦e⟧⦂𝑭⟦τ′⟧)

  translation-preservation-exp : ∀ {n : ℕ} {Γ : Ctx n} {e : Exp n}
                                     {τ : Type}
                               → Γ ⊢ e ⦂ τ
                                 -------------------------------
                               → ⟦ Γ ⟧ ⊢c ⟦ e ⟧ ⦂ 𝑭 ⟦ τ ⟧ # pure
  translation-preservation-exp (typeVal Γ⊩v⦂τ) =
    typeRet (translation-preservation-value Γ⊩v⦂τ)
  translation-preservation-exp (typeApp Γ⊢e₁⦂τ′→τ Γ⊢e₂⦂τ′) =
    typeEagerlet
      (translation-preservation-exp Γ⊢e₁⦂τ′→τ)
      (typeEagerlet
        (comp-typepres-renaming
          (translation-preservation-exp Γ⊢e₂⦂τ′)
          λ _ → refl)
        (typeApp (typeForce typeVar pure-≤) typeVar)
        (≡→≤ +-pure-idˡ))
      (≡→≤ +-pure-idˡ)
  translation-preservation-exp (typeSeq Γ⊢e₁⦂𝟙 Γ⊢e₂⦂τ) =
    typeEagerlet
      (translation-preservation-exp Γ⊢e₁⦂𝟙)
      (typeSequence
        typeVar
        (comp-typepres-renaming
          (translation-preservation-exp Γ⊢e₂⦂τ)
          λ _ → refl))
      (≡→≤ +-pure-idˡ)
  translation-preservation-exp (typeReturn Γ⊢e⦂τ) =
    typeRet (typeThunk (type-subeff (translation-preservation-exp Γ⊢e⦂τ) pure-≤))
  translation-preservation-exp {Γ = Γ} (typeBind {τ′ = τ′} Γ⊢e₁⦂𝑻φ₁τ′
    Γ∷τ′⊢e₂⦂𝑻φ₂τ φ₁+φ₂≤φ)
    with translation-preservation-exp Γ⊢e₁⦂𝑻φ₁τ′
  ...  | ⟦Γ⟧⊢⟦e₁⟧⦂⟦𝑻φ₁τ′⟧
    with translation-preservation-exp Γ∷τ′⊢e₂⦂𝑻φ₂τ
  ...  | ⟦Γ∷τ′⟧⊢⟦e₂⟧⦂𝑻φ₂τ
    rewrite ⟦Γ∷τ⟧-expand {Γ = Γ} {τ′} =
    typeRet
      (typeThunk
        (typeLetin
          (typeLetin
            ⟦Γ⟧⊢⟦e₁⟧⦂⟦𝑻φ₁τ′⟧
            (typeForce typeVar ≤-refl)
            (≡→≤ +-pure-idˡ))
          (typeLetin
            ⟦Γ∷τ′⟧⊢⟦e₂⟧⦂𝑻φ₂τ
            (typeForce typeVar ≤-refl)
            (≡→≤ +-pure-idˡ))
          φ₁+φ₂≤φ))
  translation-preservation-exp (typeTick tock≤φ) =
    typeRet
      (typeThunk
        (typeLetin (typeTick tock≤φ) (typeRet typeVar) (≡→≤ +-pure-idʳ)))
