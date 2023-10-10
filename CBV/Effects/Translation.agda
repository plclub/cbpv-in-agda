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
  Translation.⟦ ⟦Type⟧ ⟧ (τ₁ * τ₂) = ⟦ τ₁ ⟧ * ⟦ τ₂ ⟧
  Translation.⟦ ⟦Type⟧ ⟧ (τ₁ ∪ τ₂) = ⟦ τ₁ ⟧ ∪ ⟦ τ₂ ⟧

  ⟦Ctx⟧ : Translation (Ctx n) (CBPV.Ctx n)
  Translation.⟦ ⟦Ctx⟧ ⟧ Γ m = ⟦ Γ m ⟧

  mutual
    ⟦Value⟧ : Translation (Value n) (Val n)
    Translation.⟦ ⟦Value⟧ ⟧ unit = unit
    Translation.⟦ ⟦Value⟧ ⟧ (ƛ e) = ⟪ ƛ ⟦ e ⟧ ⟫
    Translation.⟦ ⟦Value⟧ ⟧ (♯ x) = ♯ x
    Translation.⟦ ⟦Value⟧ ⟧ (inl v) = inl ⟦ v ⟧
    Translation.⟦ ⟦Value⟧ ⟧ (inr v) = inr ⟦ v ⟧
    Translation.⟦ ⟦Value⟧ ⟧ ⟨ v₁ , v₂ ⟩ = ⟨ ⟦ v₁ ⟧ , ⟦ v₂ ⟧ ⟩

    ⟦Exp⟧ : Translation (Exp n) (Comp n)
    Translation.⟦ ⟦Exp⟧ ⟧ (val v) = return ⟦ v ⟧
    Translation.⟦ ⟦Exp⟧ ⟧ (e₁ · e₂) =
      $⟵ ⟦ e₁ ⟧ ⋯
      $⟵ ⟦ e₂ ⟧ [ suc ]c ⋯
      (♯ suc zero !) · ♯ zero
    Translation.⟦ ⟦Exp⟧ ⟧ (e₁ » e₂) =
      $⟵ ⟦ e₁ ⟧ ⋯
      ♯ zero » ⟦ e₂ ⟧ [ suc ]c
    Translation.⟦ ⟦Exp⟧ ⟧ (inl e) =
     $⟵ ⟦ e ⟧ ⋯ return (inl (♯ zero))
    Translation.⟦ ⟦Exp⟧ ⟧ (inr e) =
     $⟵ ⟦ e ⟧ ⋯ return (inr (♯ zero))
    Translation.⟦ ⟦Exp⟧ ⟧ ⟨ e₁ , e₂ ⟩ =
      $⟵ ⟦ e₁ ⟧ ⋯
      $⟵ ⟦ e₂ ⟧ [ suc ]c ⋯
      return ⟨ ♯ suc zero , ♯ zero ⟩
    Translation.⟦ ⟦Exp⟧ ⟧ (case e inl⇒ e₁ inr⇒ e₂) =
      $⟵ ⟦ e ⟧ ⋯
      case ♯ zero
        inl⇒ ⟦ e₁ ⟧ [ ↑↑ ]c
        inr⇒ ⟦ e₂ ⟧ [ ↑↑ ]c
    Translation.⟦ ⟦Exp⟧ ⟧ ($≔ e₁ ⋯ e₂) =
      $⟵ ⟦ e₁ ⟧ ⋯
      $≔ ♯ zero ⋯
      ⟦ e₂ ⟧ [ ↑↑↑ ]c
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
  translation-preservation-value (typePair ⊩v₁ ⊩v₂) =
    typePair
      (translation-preservation-value ⊩v₁)
      (translation-preservation-value ⊩v₂)
  translation-preservation-value (typeInl ⊩v) =
    typeInl (translation-preservation-value ⊩v)
  translation-preservation-value (typeInr ⊩v) =
    typeInr (translation-preservation-value ⊩v)

  translation-preservation-exp : Γ ⊢ e ⦂ τ # φ
                                 ----------------------------
                               → ⟦ Γ ⟧ ⊢c ⟦ e ⟧ ⦂ 𝑭 ⟦ τ ⟧ # φ
  translation-preservation-exp (typeVal ⊩v) =
    typeRet (translation-preservation-value ⊩v)
  translation-preservation-exp (typeApp ⊢e₁ ⊢e₂ φ₁+φ₂+φ₃≤φ) =
    typeLetin
      (translation-preservation-exp ⊢e₁)
      (typeLetin
        (comp-typepres-renaming
          (translation-preservation-exp ⊢e₂)
          λ _ → refl)
        (typeApp (typeForce typeVar ≤-refl) typeVar)
        ≤-refl)
      (≤-trans (≡→≤ (sym +-assoc)) φ₁+φ₂+φ₃≤φ)
  translation-preservation-exp (typeSeq ⊢e₁ ⊢e₂ φ₁+φ₂≤φ) =
    typeLetin
      (translation-preservation-exp ⊢e₁)
      (typeSequence
        typeVar
        (comp-typepres-renaming
          (translation-preservation-exp ⊢e₂)
          λ m → refl))
      φ₁+φ₂≤φ
  translation-preservation-exp (typePair ⊢e₁ ⊢e₂ φ₁+φ₂≤φ) =
    typeLetin
      (translation-preservation-exp ⊢e₁)
      (typeLetin
        (comp-typepres-renaming
          (translation-preservation-exp ⊢e₂)
          (λ _ → refl))
        (typeRet (typePair typeVar typeVar))
        (≡→≤ +-pure-idʳ))
      φ₁+φ₂≤φ
  translation-preservation-exp (typeInl ⊢e) =
    typeLetin
      (translation-preservation-exp ⊢e)
      (typeRet (typeInl typeVar))
      (≡→≤ +-pure-idʳ)
  translation-preservation-exp (typeInr ⊢e) =
    typeLetin
      (translation-preservation-exp ⊢e)
      (typeRet (typeInr typeVar))
      (≡→≤ +-pure-idʳ)
  translation-preservation-exp (typeCase ⊢e ⊢e₁ ⊢e₂ φ₁+φ₂≤φ) =
    typeLetin
      (translation-preservation-exp ⊢e)
      (typeCase
        typeVar
        (comp-typepres-renaming
          (translation-preservation-exp ⊢e₁)
          λ where zero → refl ; (suc _) → refl)
        (comp-typepres-renaming
          (translation-preservation-exp ⊢e₂)
          λ where zero → refl ; (suc _) → refl))
       φ₁+φ₂≤φ
  translation-preservation-exp (typeSplit ⊢e₁ ⊢e₂ φ₁+φ₂≤φ) =
    typeLetin
      (translation-preservation-exp ⊢e₁)
      (typeSplit
        typeVar
        (comp-typepres-renaming
          (translation-preservation-exp ⊢e₂)
          λ where zero → refl ; (suc zero) → refl ; (suc (suc _)) → refl))
      φ₁+φ₂≤φ
  translation-preservation-exp (typeTick tock≤φ) =
    typeTick tock≤φ
