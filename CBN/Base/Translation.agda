import Relation.Binary.PropositionalEquality as Eq
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)
open import Level using (0ℓ)
open Eq using (_≡_; refl)

import CBPV.Base.SyntacticTyping as CBPV
open import CBN.Base.SyntacticTyping
open import CBN.Base.Terms
open import CBN.Base.Types
open import CBPV.Base.Eagerlet
open import CBPV.Base.Renaming
open import CBPV.Base.Terms hiding (n; m)
open import CBPV.Base.Types
open CBPV hiding (Ctx; _∷_; Γ)

module CBN.Base.Translation where

postulate
  extensionality : Extensionality 0ℓ 0ℓ

data _↦_ : Term n → Comp n → Set where
  transVar : # m ↦ # m !

  transUnit : unit {n} ↦ return unit

  transInl : e ↦ M
             ------------------------
           → inl e ↦ return inl ⟪ M ⟫

  transInr : e ↦ M
             ------------------------
           → inr e ↦ return inr ⟪ M ⟫

  transAbs : e ↦ M
             ---------
           → ƛ e ↦ ƛ M

  transApp : e₁ ↦ M
           → e₂ ↦ N
             --------------------
           → e₁ · e₂ ↦ M · ⟪ N ⟫

  transSeq : e₁ ↦ M
           → e₂ ↦ N
             ----------------------------------------
           → e₁ » e₂ ↦  $⇐ M ⋯ (# zero) » N [ suc ]c

  transCase : e ↦ M
            → e₁ ↦ M₁
            → e₂ ↦ M₂
              ----------------------------------------------------------------------------
            → case e inl⇒ e₁ inr⇒ e₂ ↦ $⇐ M ⋯ case # zero inl⇒ M₁ [ ↑↑ ]c inr⇒ M₂ [ ↑↑ ]c

infix 3 _↦_

record Translation (A B : Set) : Set where
  field
    ⟦_⟧ : A → B

open Translation ⦃...⦄ public

instance
  ⟦Type⟧ : Translation Type CompType
  Translation.⟦ ⟦Type⟧ ⟧ 𝟙 = 𝑭 𝟙
  Translation.⟦ ⟦Type⟧ ⟧ (τ₁ ⇒ τ₂) = 𝑼 ⟦ τ₁ ⟧ ⇒ ⟦ τ₂ ⟧
  Translation.⟦ ⟦Type⟧ ⟧ (τ₁ ∪ τ₂) = 𝑭 (𝑼 ⟦ τ₁ ⟧ ∪ 𝑼 ⟦ τ₂ ⟧)

  ⟦Ctx⟧ : Translation (Ctx n) (CBPV.Ctx n)
  Translation.⟦ ⟦Ctx⟧ ⟧ Γ m = 𝑼 ⟦ Γ m ⟧

  ⟦Term⟧ : Translation (Term n) (Comp n)
  Translation.⟦ ⟦Term⟧ ⟧ (# m) = # m !
  Translation.⟦ ⟦Term⟧ ⟧ unit = return unit
  Translation.⟦ ⟦Term⟧ ⟧ (ƛ e) = ƛ ⟦ e ⟧
  Translation.⟦ ⟦Term⟧ ⟧ (e₁ · e₂) = ⟦ e₁ ⟧ · ⟪ ⟦ e₂ ⟧ ⟫
  Translation.⟦ ⟦Term⟧ ⟧ (e₁ » e₂) =
    $⇐ ⟦ e₁ ⟧ ⋯
    (# zero) » ⟦ e₂ ⟧ [ suc ]c
  Translation.⟦ ⟦Term⟧ ⟧ (inl e) = return inl ⟪ ⟦ e ⟧ ⟫
  Translation.⟦ ⟦Term⟧ ⟧ (inr e) = return inr ⟪ ⟦ e ⟧ ⟫
  Translation.⟦ ⟦Term⟧ ⟧ (case e inl⇒ e₁ inr⇒ e₂) =
    $⇐ ⟦ e ⟧ ⋯
    case # zero inl⇒ ⟦ e₁ ⟧ [ ↑↑ ]c inr⇒ ⟦ e₂ ⟧ [ ↑↑ ]c

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
  typeEagerlet
    (↦-preserves e₁↦M ⊢e₁)
    (typeSequence
      typeVar
      (comp-typepres-renaming (↦-preserves e₂↦N ⊢e₂) λ{_ → refl}))
↦-preserves (transInl e↦M) (typeInl ⊢e) =
  typeRet (typeInl (typeThunk (↦-preserves e↦M ⊢e)))
↦-preserves (transInr e↦M) (typeInr ⊢e) =
  typeRet (typeInr (typeThunk (↦-preserves e↦M ⊢e)))
↦-preserves (transCase e↦M e₁↦M₁ e₂↦M₂) (typeCase ⊢e ⊢e₁ ⊢e₂) =
  typeEagerlet
    (↦-preserves e↦M ⊢e)
    (typeCase
      typeVar
      (comp-typepres-renaming (↦-preserves e₁↦M₁ ⊢e₁)
      λ where zero → refl ; (suc _) → refl)
      (comp-typepres-renaming (↦-preserves e₂↦M₂ ⊢e₂)
      λ where zero → refl ; (suc _) → refl))

e↦⟦e⟧ : e ↦ ⟦ e ⟧
e↦⟦e⟧ {e = # x} = transVar
e↦⟦e⟧ {e = unit} = transUnit
e↦⟦e⟧ {e = ƛ e} = transAbs e↦⟦e⟧
e↦⟦e⟧ {e = e₁ · e₂} = transApp e↦⟦e⟧ e↦⟦e⟧
e↦⟦e⟧ {e = e₁ » e₂} = transSeq e↦⟦e⟧ e↦⟦e⟧
e↦⟦e⟧ {e = inl e} = transInl e↦⟦e⟧
e↦⟦e⟧ {e = inr e} = transInr e↦⟦e⟧
e↦⟦e⟧ {e = case e inl⇒ e₁ inr⇒ e₂} = transCase e↦⟦e⟧ e↦⟦e⟧ e↦⟦e⟧

translation-preservation : Γ ⊢ e ⦂ τ
                           ----------------------
                         → ⟦ Γ ⟧ ⊢c ⟦ e ⟧ ⦂ ⟦ τ ⟧
translation-preservation = ↦-preserves e↦⟦e⟧
