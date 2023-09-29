import Relation.Binary.PropositionalEquality as Eq
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)
open import Level using (0ℓ)
open Eq using (_≡_; refl; trans; sym)

open import CBN.Monadic.Terms
open import CBPV.Effects.Terms hiding (n; m)
open import Effects

module CBN.Monadic.Translation (E : Effect) where

import CBPV.Effects.SyntacticTyping E as CBPV
open import CBN.Monadic.SyntacticTyping E as CBN
open import CBN.Monadic.Types E
open import CBPV.Effects.Renaming E
open import CBPV.Effects.Types E
open CBPV hiding (Ctx; _∷_; Γ)
open Effect E
open Effects.Properties E

postulate
  extensionality : Extensionality 0ℓ 0ℓ

data _↦_ : Term n → Comp n → Set where
  transVar : # m ↦ ♯ m !

  transUnit : unit {n} ↦ return unit

  transAbs : e ↦ M
             ---------
           → ƛ e ↦ ƛ M

  transApp : e₁ ↦ M
           → e₂ ↦ N
             --------------------
           → e₁ · e₂ ↦ M · ⟪ N ⟫

  transSeq : e₁ ↦ M
           → e₂ ↦ N
             ---------------------------------------
           → e₁ » e₂ ↦ $⟵ M ⋯ (♯ zero) » N [ suc ]c

  transReturn : e ↦ M
                ----------------------------------
              → return e ↦ return ⟪ return ⟪ M ⟫ ⟫

  transBind : e₁ ↦ M
            → e₂ ↦ N
              ---------------------------------------------------------------
            → $⟵ e₁ ⋯ e₂ ↦ return ⟪ $⟵ $⟵ M ⋯ ♯ zero ! ⋯ $⟵ N ⋯ ♯ zero ! ⟫

  transTick : tick {n} ↦ return ⟪ $⟵ tick ⋯ return ⟪ return ♯ zero ⟫ ⟫

infix 3 _↦_

record Translation (A B : Set) : Set where
  field
    ⟦_⟧ : A → B

open Translation ⦃...⦄ public

instance
  ⟦Type⟧ : Translation Type CompType
  Translation.⟦ ⟦Type⟧ ⟧ 𝟙 = 𝑭 𝟙
  Translation.⟦ ⟦Type⟧ ⟧ (τ₁ ⇒ τ₂) = 𝑼 pure ⟦ τ₁ ⟧ ⇒ ⟦ τ₂ ⟧
  Translation.⟦ ⟦Type⟧ ⟧ (𝑻 φ τ) = 𝑭 (𝑼 φ (𝑭 (𝑼 pure ⟦ τ ⟧)))

  ⟦Ctx⟧ : ∀ {n : ℕ} → Translation (Ctx n) (CBPV.Ctx n)
  Translation.⟦ ⟦Ctx⟧ ⟧ Γ m = 𝑼 pure ⟦ Γ m ⟧

  ⟦Term⟧ : ∀ {n : ℕ} → Translation (Term n) (Comp n)
  Translation.⟦ ⟦Term⟧ ⟧ (# m) = ♯ m !
  Translation.⟦ ⟦Term⟧ ⟧ unit = return unit
  Translation.⟦ ⟦Term⟧ ⟧ (ƛ e) = ƛ ⟦ e ⟧
  Translation.⟦ ⟦Term⟧ ⟧ (e₁ · e₂) = ⟦ e₁ ⟧ · ⟪ ⟦ e₂ ⟧ ⟫
  Translation.⟦ ⟦Term⟧ ⟧ (e₁ » e₂) =
    $⟵ ⟦ e₁ ⟧ ⋯
    (♯ zero) » ⟦ e₂ ⟧ [ suc ]c
  Translation.⟦ ⟦Term⟧ ⟧ (return e) = return ⟪ return ⟪ ⟦ e ⟧ ⟫ ⟫
  Translation.⟦ ⟦Term⟧ ⟧ ($⟵ e₁ ⋯ e₂) =
    return ⟪
      $⟵
        $⟵ ⟦ e₁ ⟧ ⋯
        ♯ zero !
      ⋯ $⟵ ⟦ e₂ ⟧ ⋯ ♯ zero !
    ⟫
  Translation.⟦ ⟦Term⟧ ⟧ tick = return ⟪ $⟵ tick ⋯ return ⟪ return ♯ zero ⟫ ⟫

⟦Γ∷τ⟧-expand : ⟦ Γ ∷ τ ⟧ ≡ ⟦ Γ ⟧ CBPV.∷ 𝑼 pure ⟦ τ ⟧
⟦Γ∷τ⟧-expand = extensionality λ where
                                  zero    → refl
                                  (suc m) → refl

↦-preserves : e ↦ M
            → Γ ⊢ e ⦂ τ
              -------------------------
            → ⟦ Γ ⟧ ⊢c M ⦂ ⟦ τ ⟧ # pure
↦-preserves transVar typeVar = typeForce typeVar pure-≤
↦-preserves transUnit typeUnit = typeRet typeUnit
↦-preserves {Γ = Γ} (transAbs e↦M) (typeAbs {τ = τ} ⊢e)
  with ↦-preserves e↦M ⊢e
...  | ⊢M
  rewrite ⟦Γ∷τ⟧-expand {Γ = Γ} {τ} = typeAbs ⊢M
↦-preserves (transApp e₁↦M e₂↦N) (typeApp ⊢e₁ ⊢e₂)
  with ↦-preserves e₁↦M ⊢e₁ | ↦-preserves e₂↦N ⊢e₂
...  | ⊢M                   | ⊢N                   =
  typeApp ⊢M (typeThunk ⊢N)
↦-preserves (transSeq e₁↦M e₂↦N) (typeSeq ⊢e₁ ⊢e₂)
  with ↦-preserves e₁↦M ⊢e₁ | ↦-preserves e₂↦N ⊢e₂
...  | ⊢M                   | ⊢N                   =
  typeLetin
    ⊢M
    (typeSequence typeVar (comp-typepres-renaming ⊢N λ{_ → refl}))
    (≡→≤ +-pure-idʳ)
↦-preserves (transReturn e↦M) (typeReturn ⊢e)
  with ↦-preserves e↦M ⊢e
...  | ⊢M                 =
  typeRet (typeThunk (typeRet (typeThunk ⊢M)))
↦-preserves {Γ = Γ} (transBind e₁↦M e₂↦N) (typeBind {τ′ = τ′} ⊢e₁ ⊢e₂ φ₁+φ₂≤φ)
  with ↦-preserves e₁↦M ⊢e₁ | ↦-preserves e₂↦N ⊢e₂
...  | ⊢M                   | ⊢N
  rewrite ⟦Γ∷τ⟧-expand {Γ = Γ} {τ′} =
  typeRet
    (typeThunk
      (typeLetin
        (typeLetin
          ⊢M
          (typeForce typeVar ≤-refl)
          (≡→≤ +-pure-idˡ))
        (typeLetin
          ⊢N
          (typeForce typeVar ≤-refl)
          (≡→≤ +-pure-idˡ))
        φ₁+φ₂≤φ))
↦-preserves transTick (typeTick tock≤φ) =
  typeRet
    (typeThunk
      (typeLetin
        (typeTick tock≤φ)
        (typeRet (typeThunk (typeRet typeVar)))
        (≡→≤ +-pure-idʳ)))

e↦⟦e⟧ : e ↦ ⟦ e ⟧
e↦⟦e⟧ {e = # x} = transVar
e↦⟦e⟧ {e = unit} = transUnit
e↦⟦e⟧ {e = ƛ e} = transAbs e↦⟦e⟧
e↦⟦e⟧ {e = e₁ · e₂} = transApp e↦⟦e⟧ e↦⟦e⟧
e↦⟦e⟧ {e = e₁ » e₂} = transSeq e↦⟦e⟧ e↦⟦e⟧
e↦⟦e⟧ {e = return e} = transReturn e↦⟦e⟧
e↦⟦e⟧ {e = $⟵ e₁ ⋯ e₂} = transBind e↦⟦e⟧ e↦⟦e⟧
e↦⟦e⟧ {e = tick} = transTick

translation-preservation : Γ ⊢ e ⦂ τ
                           -----------------------------
                         → ⟦ Γ ⟧ ⊢c ⟦ e ⟧ ⦂ ⟦ τ ⟧ # pure
translation-preservation = ↦-preserves e↦⟦e⟧
