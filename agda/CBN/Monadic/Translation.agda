open import Data.Fin using (suc; zero)
open import Data.Nat using (ℕ)

open import CBN.Monadic.Terms
open import CBPV.Effects.Renaming
open import CBPV.Effects.Terms
open import Effects

module CBN.Monadic.Translation (E : Effect) where

import CBN.Monadic.SyntacticTyping E as CBN
open import CBN.Monadic.Types E
open import CBPV.Effects.Types E
open import CBPV.Effects.SyntacticTyping E
open CBN hiding (Ctx)
open Effect E

record Translation (A B : Set) : Set where
  field
    ⟦_⟧ : A → B

open Translation ⦃...⦄ public

instance
  ⟦Type⟧ : Translation Type CompType
  Translation.⟦ ⟦Type⟧ ⟧ 𝟙 = 𝑭 𝟙
  Translation.⟦ ⟦Type⟧ ⟧ (τ₁ ⇒ τ₂) = 𝑼 pure ⟦ τ₁ ⟧ ⇒ ⟦ τ₂ ⟧
  Translation.⟦ ⟦Type⟧ ⟧ (𝑻 φ τ) = 𝑭 (𝑼 φ (𝑭 (𝑼 pure ⟦ τ ⟧)))

  ⟦Ctx⟧ : ∀ {n : ℕ} → Translation (CBN.Ctx n) (Ctx n)
  Translation.⟦ ⟦Ctx⟧ ⟧ Γ m = 𝑼 pure ⟦ Γ m ⟧

  ⟦Term⟧ : ∀ {n : ℕ} → Translation (Term n) (Comp n)
  Translation.⟦ ⟦Term⟧ ⟧ (# m) = ♯ m !
  Translation.⟦ ⟦Term⟧ ⟧ unit = return unit
  Translation.⟦ ⟦Term⟧ ⟧ (ƛ e) = ƛ ⟦ e ⟧
  Translation.⟦ ⟦Term⟧ ⟧ (e₁ · e₂) = ⟦ e₁ ⟧ · ⟪ ⟦ e₂ ⟧ ⟫
  Translation.⟦ ⟦Term⟧ ⟧ (e₁ » e₂) =
    $⇐ ⟦ e₁ ⟧ ⋯
    (♯ zero) » ⟦ e₂ ⟧ [ suc ]c
  Translation.⟦ ⟦Term⟧ ⟧ (return e) = return ⟪ return ⟪ ⟦ e ⟧ ⟫ ⟫
  Translation.⟦ ⟦Term⟧ ⟧ ($⇐ e₁ ⋯ e₂) =
    return ⟪
      $⇐ ⟦ e₁ ⟧ ⋯
      $⇐ ♯ zero ! ⋯
      $⇐ ⟦ e₂ ⟧ [ suc ]c [ suc ]c ⋯
      ♯ zero !
    ⟫

  -- 𝑭 𝑼φ 𝑭 𝑼⊥ 𝑭 𝟙
  Translation.⟦ ⟦Term⟧ ⟧ tick = return ⟪ $⇐ tick ⋯ return ⟪ return ♯ zero ⟫ ⟫

translation-preservation : ∀ {n : ℕ} {Γ : CBN.Ctx n} {e : Term n} {τ : Type}
                         → Γ ⊢ e ⦂ τ
                           --------------------------
                         → ⟦ Γ ⟧ ⊢c ⟦ e ⟧ ⦂ ⟦ τ ⟧ # pure
translation-preservation = {!!}
