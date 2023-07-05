import Relation.Binary.PropositionalEquality as Eq
open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)
open Eq using (_≡_; refl)

import CBPV.Base.SyntacticTyping as CBPV
open import CBN.Base.SyntacticTyping
open import CBN.Base.Terms
open import CBN.Base.Types
open import CBPV.Base.Renaming
open import CBPV.Base.Terms
open import CBPV.Base.Types
open CBPV hiding (Ctx; _∷_)

module CBN.Base.Translation where

postulate
  extensionality : Extensionality 0ℓ 0ℓ

data _↦_ {n : ℕ} : Term n → Comp n → Set where
  transVar : ∀ {m : Fin n}
             ------------
           → # m ↦ # m !

  transUnit : unit ↦ return unit

  transAbs : ∀ {e : Term (suc n)} {M : Comp (suc n)}
           → e ↦ M
             ---------
           → ƛ e ↦ ƛ M

  transApp : ∀ {e1 e2 : Term n} {M N : Comp n}
           → e1 ↦ M
           → e2 ↦ N
             --------------------
           → e1 · e2 ↦ M · ⟪ N ⟫

  transSeq : ∀ {e1 e2 : Term n} {M N : Comp n}
           → e1 ↦ M
           → e2 ↦ N
             -----------------------------------------------
           → e1 » e2 ↦ $⇐ M ⋯ (# zero) » N [ suc ]c

infix 3 _↦_

record Translation (A B : Set) : Set where
  field
    ⟦_⟧ : A → B

open Translation ⦃...⦄ public

instance
  ⟦Type⟧ : Translation Type CompType
  Translation.⟦ ⟦Type⟧ ⟧ 𝟙 = 𝑭 𝟙
  Translation.⟦ ⟦Type⟧ ⟧ (τ₁ ⇒ τ₂) = 𝑼 ⟦ τ₁ ⟧ ⇒ ⟦ τ₂ ⟧

  ⟦Ctx⟧ : ∀ {n : ℕ} → Translation (Ctx n) (CBPV.Ctx n)
  Translation.⟦ ⟦Ctx⟧ ⟧ Γ m = 𝑼 ⟦ Γ m ⟧

  ⟦Term⟧ : ∀ {n : ℕ} → Translation (Term n) (Comp n)
  Translation.⟦ ⟦Term⟧ ⟧ (# m) = # m !
  Translation.⟦ ⟦Term⟧ ⟧ unit = return unit
  Translation.⟦ ⟦Term⟧ ⟧ (ƛ e) = ƛ ⟦ e ⟧
  Translation.⟦ ⟦Term⟧ ⟧ (e₁ · e₂) = ⟦ e₁ ⟧ · ⟪ ⟦ e₂ ⟧ ⟫
  Translation.⟦ ⟦Term⟧ ⟧ (e₁ » e₂) =
    $⇐ ⟦ e₁ ⟧ ⋯
    (# zero) » ⟦ e₂ ⟧ [ suc ]c

⟦Γ∷τ⟧-expand : ∀ {n : ℕ} {Γ : Ctx n} {τ : Type}
               → ⟦ Γ ∷ τ ⟧ ≡ ⟦ Γ ⟧ CBPV.∷ 𝑼 ⟦ τ ⟧
⟦Γ∷τ⟧-expand = extensionality λ where
                                  zero    → refl
                                  (suc m) → refl

trans-preserves : ∀ {n : ℕ} {e : Term n} {M : Comp n}
                    {Γ : Ctx n} {τ : Type}
                → e ↦ M
                → Γ ⊢ e ⦂ τ
                  ------------------
                → ⟦ Γ ⟧ ⊢c M ⦂ ⟦ τ ⟧
trans-preserves transVar typeVar = typeForce typeVar
trans-preserves transUnit typeUnit = typeRet typeUnit
trans-preserves {Γ = Γ} (transAbs e↦M) (typeAbs {τ = τ} Γ∷τ⊢e⦂τ′)
  with trans-preserves e↦M Γ∷τ⊢e⦂τ′
...  | ih
  rewrite (⟦Γ∷τ⟧-expand {Γ = Γ} {τ}) = typeAbs ih
trans-preserves (transApp e₁↦M e₂↦N) (typeApp Γ⊢e₁⦂τ′⇒τ Γ⊢e₂⦂τ′) =
  typeApp
    (trans-preserves e₁↦M Γ⊢e₁⦂τ′⇒τ)
    (typeThunk (trans-preserves e₂↦N Γ⊢e₂⦂τ′))
trans-preserves (transSeq e₁↦M e₂↦N) (typeSeq Γ⊢e₁⦂𝟙 Γ⊢e₂⦂τ) =
  typeLetin
    (trans-preserves e₁↦M Γ⊢e₁⦂𝟙)
    (typeSequence
      typeVar
      (comp-typepres-renaming (trans-preserves e₂↦N Γ⊢e₂⦂τ) λ{_ → refl}))

e↦⟦e⟧ : ∀ {n : ℕ} {e : Term n} → e ↦ ⟦ e ⟧
e↦⟦e⟧ {e = # x} = transVar
e↦⟦e⟧ {e = unit} = transUnit
e↦⟦e⟧ {e = ƛ e} = transAbs e↦⟦e⟧
e↦⟦e⟧ {e = e₁ · e₂} = transApp e↦⟦e⟧ e↦⟦e⟧
e↦⟦e⟧ {e = e₁ » e₂} = transSeq e↦⟦e⟧ e↦⟦e⟧

translation-preservation : ∀ {n : ℕ} {Γ : Ctx n} {e : Term n} {τ : Type}
                         → Γ ⊢ e ⦂ τ
                           --------------------------
                         → ⟦ Γ ⟧ ⊢c ⟦ e ⟧ ⦂ ⟦ τ ⟧
translation-preservation = trans-preserves e↦⟦e⟧
