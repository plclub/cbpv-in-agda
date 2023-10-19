import Relation.Binary.PropositionalEquality as Eq
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)
open import Level using (0ℓ)
open Eq using (_≡_; refl; sym)

open import CBV.Monadic.Terms
open import CBPV.Effects.Terms hiding (n)
open import Effects

module CBV.Monadic.Translation (E : Effect) where

import CBPV.Effects.SyntacticTyping E as CBPV
open import CBPV.Effects.Renaming E
open import CBPV.Effects.Types E
open import CBV.Monadic.SyntacticTyping E
open import CBV.Monadic.Types E
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
  Translation.⟦ ⟦Type⟧ ⟧ (τ₁ ⇒ τ₂) = 𝑼 pure (⟦ τ₁ ⟧ ⇒ 𝑭 ⟦ τ₂ ⟧)
  Translation.⟦ ⟦Type⟧ ⟧ (𝑻 φ τ) = 𝑼 φ (𝑭 ⟦ τ ⟧)

  ⟦Ctx⟧ : Translation (Ctx n) (CBPV.Ctx n)
  Translation.⟦ ⟦Ctx⟧ ⟧ Γ m = ⟦ Γ m ⟧

  mutual
    ⟦Value⟧ : Translation (Value n) (Val n)
    Translation.⟦ ⟦Value⟧ ⟧ unit = unit
    Translation.⟦ ⟦Value⟧ ⟧ (ƛ e) = ⟪ ƛ ⟦ e ⟧ ⟫
    Translation.⟦ ⟦Value⟧ ⟧ (# x) = ♯ x

    ⟦Exp⟧ : Translation (Exp n) (Comp n)
    Translation.⟦ ⟦Exp⟧ ⟧ (val v) = return ⟦ v ⟧
    Translation.⟦ ⟦Exp⟧ ⟧ (e₁ · e₂) =
      $⟵ ⟦ e₁ ⟧ ⋯
      $⟵ ⟦ e₂ ⟧ [ suc ]c ⋯
      (♯ suc zero !) · ♯ zero
    Translation.⟦ ⟦Exp⟧ ⟧ (e₁ » e₂) =
      $⟵ ⟦ e₁ ⟧ ⋯
      ♯ zero » ⟦ e₂ ⟧ [ suc ]c
    Translation.⟦ ⟦Exp⟧ ⟧ (return e) = return ⟪ ⟦ e ⟧ ⟫
    Translation.⟦ ⟦Exp⟧ ⟧ ($⟵ e₁ ⋯ e₂) =
      return ⟪ $⟵ $⟵ ⟦ e₁ ⟧ ⋯ ♯ zero ! ⋯ $⟵ ⟦ e₂ ⟧ ⋯ ♯ zero ! ⟫
    Translation.⟦ ⟦Exp⟧ ⟧ (tick) = return ⟪ $⟵ tick ⋯ return ♯ zero ⟫

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
                                 -------------------------------
                               → ⟦ Γ ⟧ ⊢c ⟦ e ⟧ ⦂ 𝑭 ⟦ τ ⟧ # pure
  translation-preservation-exp (typeVal Γ⊩v⦂τ) =
    typeRet (translation-preservation-value Γ⊩v⦂τ) ≤-refl
  translation-preservation-exp (typeApp ⊢e₁ ⊢e₂) =
    typeLetin
      (translation-preservation-exp ⊢e₁)
      (typeLetin
        (comp-typepres-renaming
          (translation-preservation-exp ⊢e₂)
          λ _ → refl)
        (typeApp (typeForce typeVar ≤-refl) typeVar)
        (≡→≤ +-pure-idˡ))
      (≡→≤ +-pure-idˡ)
  translation-preservation-exp (typeSeq ⊢e₁ ⊢e₂) =
    typeLetin
      (translation-preservation-exp ⊢e₁)
      (typeSequence
        typeVar
        (comp-typepres-renaming
          (translation-preservation-exp ⊢e₂)
          λ _ → refl))
      (≡→≤ +-pure-idˡ)
  translation-preservation-exp (typeReturn ⊢e pure≤φ) =
    typeRet (typeThunk (type-subeff (translation-preservation-exp ⊢e) pure≤φ)) ≤-refl
  translation-preservation-exp {Γ = Γ} (typeBind {τ′ = τ′} ⊢e₁ ⊢e₂ φ₁+φ₂≤φ)
    with translation-preservation-exp ⊢e₁
  ...  | ⊢⟦e₁⟧
    with translation-preservation-exp ⊢e₂
  ...  | ⊢⟦e₂⟧
    rewrite ⟦Γ∷τ⟧-expand {Γ = Γ} {τ′} =
    typeRet
      (typeThunk
        (typeLetin
          (typeLetin
            ⊢⟦e₁⟧
            (typeForce typeVar ≤-refl)
            (≡→≤ +-pure-idˡ))
          (typeLetin
            ⊢⟦e₂⟧
            (typeForce typeVar ≤-refl)
            (≡→≤ +-pure-idˡ))
          φ₁+φ₂≤φ))
    ≤-refl
  translation-preservation-exp (typeTick tock≤φ) =
    typeRet
      (typeThunk
        (typeLetin (typeTick tock≤φ) (typeRet typeVar ≤-refl) (≡→≤ +-pure-idʳ)))
    ≤-refl
