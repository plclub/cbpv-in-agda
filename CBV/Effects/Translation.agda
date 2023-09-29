import Relation.Binary.PropositionalEquality as Eq
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)
open import Level using (0ℓ)
open Eq using (_≡_; refl; sym)

open import CBV.Effects.Terms
open import CBPV.Effects.Terms hiding (n)
open import Effects

module CBV.Effects.Translation (E : Effect) where

import CBPV.Effects.SyntacticTyping E as CBPV
open import CBPV.Effects.Eagerlet E
open import CBPV.Effects.Renaming E
open import CBPV.Effects.Types E
open import CBV.Effects.SyntacticTyping E
open import CBV.Effects.Types E
open CBPV hiding (Ctx; _∷_; Γ)
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
  Translation.⟦ ⟦Type⟧ ⟧ (τ₁ ─ φ ⟶ τ₂) = 𝑼 φ (⟦ τ₁ ⟧ ⇒ 𝑭 ⟦ τ₂ ⟧)

  ⟦Ctx⟧ : Translation (Ctx n) (CBPV.Ctx n)
  Translation.⟦ ⟦Ctx⟧ ⟧ Γ m = ⟦ Γ m ⟧

  mutual
    ⟦Value⟧ : Translation (Value n) (Val n)
    Translation.⟦ ⟦Value⟧ ⟧ unit = unit
    Translation.⟦ ⟦Value⟧ ⟧ (ƛ e) = ⟪ ƛ ⟦ e ⟧ ⟫
    Translation.⟦ ⟦Value⟧ ⟧ (♯ x) = ♯ x

    ⟦Exp⟧ : Translation (Exp n) (Comp n)
    Translation.⟦ ⟦Exp⟧ ⟧ (val v) = return ⟦ v ⟧
    Translation.⟦ ⟦Exp⟧ ⟧ (e₁ · e₂) =
      $⇐ ⟦ e₁ ⟧ ⋯
      $⇐ ⟦ e₂ ⟧ [ suc ]c ⋯
      (♯ suc zero !) · ♯ zero
    Translation.⟦ ⟦Exp⟧ ⟧ (e₁ » e₂) =
      $⇐ ⟦ e₁ ⟧ ⋯
      ♯ zero » ⟦ e₂ ⟧ [ suc ]c
    Translation.⟦ ⟦Exp⟧ ⟧ tick = tick

⟦Γ∷τ⟧-expand : ⟦ Γ ∷ τ ⟧ ≡ ⟦ Γ ⟧ CBPV.∷ ⟦ τ ⟧
⟦Γ∷τ⟧-expand = extensionality λ where
                                  zero    → refl
                                  (suc m) → refl

mutual
  translation-preservation-value : Γ ⊩ v ⦂ τ # φ
                                   ----------------------
                                 → ⟦ Γ ⟧ ⊢v ⟦ v ⟧ ⦂ ⟦ τ ⟧
  translation-preservation-value typeUnit = typeUnit
  translation-preservation-value typeVar = typeVar
  translation-preservation-value {Γ = Γ} (typeAbs {τ = τ} ⊢e′)
    with translation-preservation-exp ⊢e′
  ...  | ⊢⟦e⟧
    rewrite ⟦Γ∷τ⟧-expand {Γ = Γ} {τ} = typeThunk (typeAbs ⊢⟦e⟧)

  translation-preservation-exp : ∀ {n : ℕ} {Γ : Ctx n} {e : Exp n}
                                     {τ : Type} {φ : Eff}
                               → Γ ⊢ e ⦂ τ # φ
                                 ----------------------------
                               → ⟦ Γ ⟧ ⊢c ⟦ e ⟧ ⦂ 𝑭 ⟦ τ ⟧ # φ
  translation-preservation-exp (typeVal ⊩v) =
    typeRet (translation-preservation-value ⊩v)
  translation-preservation-exp (typeApp ⊢e₁ ⊢e₂ φ₁+φ₂+φ₃≤φ) =
    typeEagerlet
      (translation-preservation-exp ⊢e₁)
      (typeEagerlet
        (comp-typepres-renaming
          (translation-preservation-exp ⊢e₂)
          λ _ → refl)
        (typeApp (typeForce typeVar ≤-refl) typeVar)
        ≤-refl)
      (≤-trans (≡→≤ (sym +-assoc)) φ₁+φ₂+φ₃≤φ)
  translation-preservation-exp (typeSeq ⊢e₁ ⊢e₂ φ₁+φ₂≤φ) =
    typeEagerlet
      (translation-preservation-exp ⊢e₁)
      (typeSequence
        typeVar
        (comp-typepres-renaming
          (translation-preservation-exp ⊢e₂)
          λ m → refl))
      φ₁+φ₂≤φ
  translation-preservation-exp (typeTick tock≤φ) =
    typeTick tock≤φ
