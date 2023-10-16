import Relation.Binary.PropositionalEquality as Eq
open import Axiom.Extensionality.Propositional using (Extensionality)
import Relation.Binary.PropositionalEquality as Eq
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ)
open import Level using (0ℓ)
open Eq using (_≡_; refl)

import CBPV.Base.SyntacticTyping as CBPV
open import CBN.Base.SyntacticTyping
open import CBN.Base.Terms
open import CBN.Base.Translation
open import CBN.Base.Types
open import CBPV.Base.Renaming
open import CBPV.Base.Terms
open import CBPV.Base.Types
open CBPV hiding (_∷_; Γ)

module CBN.Base.TypePreservation where

postulate
  extensionality : Extensionality 0ℓ 0ℓ

⟦Γ∷τ⟧-expand : ⟦ Γ ∷ τ ⟧ ≡ ⟦ Γ ⟧ CBPV.∷ 𝑼 ⟦ τ ⟧
⟦Γ∷τ⟧-expand = extensionality λ where
                                  zero    → refl
                                  (suc m) → refl

↦-preserves : e ↦ M
            → Γ ⊢ e ⦂ τ
              ------------------
            → ⟦ Γ ⟧ ⊢c M ⦂ ⟦ τ ⟧
↦-preserves transVar typeVar = typeForce typeVar
↦-preserves transUnit typeUnit = typeRet typeUnit
↦-preserves {Γ = Γ} (transAbs e↦M) (typeAbs {τ = τ} ⊢e)
  with ↦-preserves e↦M ⊢e
...  | ih
  rewrite (⟦Γ∷τ⟧-expand {Γ = Γ} {τ}) = typeAbs ih
↦-preserves (transApp e₁↦M e₂↦N) (typeApp ⊢e₁ ⊢e₂) =
  typeApp
    (↦-preserves e₁↦M ⊢e₁)
    (typeThunk (↦-preserves e₂↦N ⊢e₂))
↦-preserves (transSeq e₁↦M e₂↦N) (typeSeq ⊢e₁ ⊢e₂) =
  typeLetin
    (↦-preserves e₁↦M ⊢e₁)
    (typeSequence
      typeVar
      (comp-typepres-renaming (↦-preserves e₂↦N ⊢e₂) λ{_ → refl}))
↦-preserves (transInl e↦M) (typeInl ⊢e) =
  typeRet (typeInl (typeThunk (↦-preserves e↦M ⊢e)))
↦-preserves (transInr e↦M) (typeInr ⊢e) =
  typeRet (typeInr (typeThunk (↦-preserves e↦M ⊢e)))
↦-preserves (transPair e₁↦M₁ e₂↦M₂) (typePair ⊢M₁ ⊢M₂) =
  typeCpair
    (↦-preserves e₁↦M₁ ⊢M₁)
    (↦-preserves e₂↦M₂ ⊢M₂)
↦-preserves (transFst e↦M) (typeFst ⊢M) =
  typeProjl (↦-preserves e↦M ⊢M)
↦-preserves (transSnd e↦M) (typeSnd ⊢M) =
  typeProjr (↦-preserves e↦M ⊢M)
↦-preserves (transCase e↦M e₁↦M₁ e₂↦M₂) (typeCase ⊢e ⊢e₁ ⊢e₂) =
  typeLetin
    (↦-preserves e↦M ⊢e)
    (typeCase
      typeVar
      (comp-typepres-renaming (↦-preserves e₁↦M₁ ⊢e₁)
      λ where zero → refl ; (suc _) → refl)
      (comp-typepres-renaming (↦-preserves e₂↦M₂ ⊢e₂)
      λ where zero → refl ; (suc _) → refl))

translation-preservation : Γ ⊢ e ⦂ τ
                           ----------------------
                         → ⟦ Γ ⟧ ⊢c ⟦ e ⟧ ⦂ ⟦ τ ⟧
translation-preservation = ↦-preserves e↦⟦e⟧
