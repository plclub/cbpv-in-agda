import Relation.Binary.PropositionalEquality as Eq
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)
open import Level using (0ℓ)
open Eq using (_≡_; refl; sym)

import CBPV.Base.SyntacticTyping as CBPV
open import CBV.Base.SyntacticTyping
open import CBV.Base.Terms
open import CBV.Base.Types
open import CBPV.Base.Eagerlet
open import CBPV.Base.Renaming
open import CBPV.Base.Terms
open import CBPV.Base.Types
open CBPV hiding (Ctx; _∷_)

module CBV.Base.Translation where

postulate
  extensionality : Extensionality 0ℓ 0ℓ

record Translation (A B : Set) : Set where
  field
    ⟦_⟧ : A → B

open Translation ⦃...⦄ public

instance
  ⟦Type⟧ : Translation Type ValType
  Translation.⟦ ⟦Type⟧ ⟧ 𝟙 = 𝟙
  Translation.⟦ ⟦Type⟧ ⟧ (τ₁ ⇒ τ₂) = 𝑼 (⟦ τ₁ ⟧ ⇒ 𝑭 ⟦ τ₂ ⟧)

  ⟦Ctx⟧ : ∀ {n : ℕ} → Translation (Ctx n) (CBPV.Ctx n)
  Translation.⟦ ⟦Ctx⟧ ⟧ Γ m = ⟦ Γ m ⟧

  mutual
    ⟦Value⟧ : ∀ {n : ℕ} → Translation (Value n) (Val n)
    Translation.⟦ ⟦Value⟧ ⟧ unit = unit
    Translation.⟦ ⟦Value⟧ ⟧ (ƛ e) = ⟪ ƛ ⟦ e ⟧ ⟫
    Translation.⟦ ⟦Value⟧ ⟧ (# x) = # x

    ⟦Exp⟧ : ∀ {n : ℕ} → Translation (Exp n) (Comp n)
    Translation.⟦ ⟦Exp⟧ ⟧ (val v) = return ⟦ v ⟧
    Translation.⟦ ⟦Exp⟧ ⟧ (e₁ · e₂) =
      $⇐ ⟦ e₁ ⟧ ⋯
      $⇐ ⟦ e₂ ⟧ [ suc ]c ⋯
      (# (suc zero) !) · # zero
    Translation.⟦ ⟦Exp⟧ ⟧ (e₁ » e₂) =
      $⇐ ⟦ e₁ ⟧ ⋯
      # zero » ⟦ e₂ ⟧ [ suc ]c

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
  ...  | ⟦Γ∷τ⟧⊢⟦e⟧⦂⟦τ′⟧
    rewrite ⟦Γ∷τ⟧-expand {Γ = Γ} {τ} = typeThunk (typeAbs ⟦Γ∷τ⟧⊢⟦e⟧⦂⟦τ′⟧)

  translation-preservation-exp : ∀ {n : ℕ} {Γ : Ctx n} {e : Exp n}
                                     {τ : Type}
                               → Γ ⊢ e ⦂ τ
                                 ----------------------
                               → ⟦ Γ ⟧ ⊢c ⟦ e ⟧ ⦂ 𝑭 ⟦ τ ⟧
  translation-preservation-exp (typeVal Γ⊩v⦂τ) =
    typeRet (translation-preservation-value Γ⊩v⦂τ)
  translation-preservation-exp (typeApp Γ⊢e₁⦂τ′→τ Γ⊢e₂⦂τ′) =
    typeEagerlet
      (translation-preservation-exp Γ⊢e₁⦂τ′→τ)
      (typeEagerlet
        (comp-typepres-renaming
          (translation-preservation-exp Γ⊢e₂⦂τ′)
          λ _ → refl)
        (typeApp (typeForce typeVar) typeVar))
  translation-preservation-exp (typeSeq Γ⊢e₁⦂𝟙 Γ⊢e₂⦂τ) =
    typeEagerlet
      (translation-preservation-exp Γ⊢e₁⦂𝟙)
      (typeSequence
        typeVar
        (comp-typepres-renaming
          (translation-preservation-exp Γ⊢e₂⦂τ)
          λ _ → refl))
