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
open import CBPV.Base.Terms hiding (n)
open import CBPV.Base.Types
open CBPV hiding (Ctx; _∷_; Γ)

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

  ⟦Ctx⟧ : Translation (Ctx n) (CBPV.Ctx n)
  Translation.⟦ ⟦Ctx⟧ ⟧ Γ m = ⟦ Γ m ⟧

  mutual
    ⟦Value⟧ : Translation (Value n) (Val n)
    Translation.⟦ ⟦Value⟧ ⟧ unit = unit
    Translation.⟦ ⟦Value⟧ ⟧ (ƛ e) = ⟪ ƛ ⟦ e ⟧ ⟫
    Translation.⟦ ⟦Value⟧ ⟧ (# x) = # x

    ⟦Exp⟧ : Translation (Exp n) (Comp n)
    Translation.⟦ ⟦Exp⟧ ⟧ (val v) = return ⟦ v ⟧
    Translation.⟦ ⟦Exp⟧ ⟧ (e₁ · e₂) =
      $⇐ ⟦ e₁ ⟧ ⋯
      $⇐ ⟦ e₂ ⟧ [ suc ]c ⋯
      (# (suc zero) !) · # zero
    Translation.⟦ ⟦Exp⟧ ⟧ (e₁ » e₂) =
      $⇐ ⟦ e₁ ⟧ ⋯
      # zero » ⟦ e₂ ⟧ [ suc ]c

⟦Γ∷τ⟧-expand : ⟦ Γ ∷ τ ⟧ ≡ ⟦ Γ ⟧ CBPV.∷ ⟦ τ ⟧
⟦Γ∷τ⟧-expand = extensionality λ where
                                  zero    → refl
                                  (suc m) → refl

mutual
  translation-preservation-value : Γ ⊩ v ⦂ τ
                                   ----------------------
                                 → ⟦ Γ ⟧ ⊢v ⟦ v ⟧ ⦂ ⟦ τ ⟧
  translation-preservation-value typeVar = typeVar
  translation-preservation-value typeUnit = typeUnit
  translation-preservation-value {Γ = Γ} (typeAbs {τ = τ} ⊢e)
    with translation-preservation-exp ⊢e
  ...  | ⊢⟦e⟧
    rewrite ⟦Γ∷τ⟧-expand {Γ = Γ} {τ} = typeThunk (typeAbs ⊢⟦e⟧)

  translation-preservation-exp : Γ ⊢ e ⦂ τ
                                 ----------------------
                               → ⟦ Γ ⟧ ⊢c ⟦ e ⟧ ⦂ 𝑭 ⟦ τ ⟧
  translation-preservation-exp (typeVal ⊩v) =
    typeRet (translation-preservation-value ⊩v)
  translation-preservation-exp (typeApp ⊢e₁ ⊢e₂) =
    typeEagerlet
      (translation-preservation-exp ⊢e₁)
      (typeEagerlet
        (comp-typepres-renaming
          (translation-preservation-exp ⊢e₂)
          λ _ → refl)
        (typeApp (typeForce typeVar) typeVar))
  translation-preservation-exp (typeSeq ⊢e₁ ⊢e₂) =
    typeEagerlet
      (translation-preservation-exp ⊢e₁)
      (typeSequence
        typeVar
        (comp-typepres-renaming
          (translation-preservation-exp ⊢e₂)
          λ _ → refl))
