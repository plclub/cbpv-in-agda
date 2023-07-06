import Relation.Binary.PropositionalEquality as Eq
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)
open import Level using (0ℓ)
open Eq using (_≡_; refl; trans; sym)

open import CBN.Monadic.Terms
open import CBPV.Effects.Renaming
open import CBPV.Effects.Terms
open import Effects

module CBN.Monadic.Translation (E : Effect) where

import CBPV.Effects.SyntacticTyping E as CBPV
open import CBN.Monadic.SyntacticTyping E as CBN
open import CBN.Monadic.Types E
open import CBPV.Effects.Types E
open CBPV hiding (Ctx; _∷_)
open Effect E
open Effects.Properties E

postulate
  extensionality : Extensionality 0ℓ 0ℓ

data _↦_ {n : ℕ} : Term n → Comp n → Set where
  transVar : ∀ {m : Fin n}
             ------------
           → # m ↦ ♯ m !

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
             ---------------------------------------
           → e1 » e2 ↦ $⇐ M ⋯ (♯ zero) » N [ suc ]c

  transReturn : ∀ {e : Term n} {M : Comp n}
              → e ↦ M
                ----------------------------------
              → return e ↦ return ⟪ return ⟪ M ⟫ ⟫

  transBind : ∀ {e₁ : Term n} {M : Comp n} {e₂ : Term (suc n)}
                {N : Comp (suc n)}
            → e₁ ↦ M
            → e₂ ↦ N
              ---------------------------------------------------------------
            → $⇐ e₁ ⋯ e₂ ↦ return ⟪ $⇐ $⇐ M ⋯ ♯ zero ! ⋯ $⇐ N ⋯ ♯ zero ! ⟫

  transTick : tick ↦ return ⟪ $⇐ tick ⋯ return ⟪ return ♯ zero ⟫ ⟫

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
    $⇐ ⟦ e₁ ⟧ ⋯
    (♯ zero) » ⟦ e₂ ⟧ [ suc ]c
  Translation.⟦ ⟦Term⟧ ⟧ (return e) = return ⟪ return ⟪ ⟦ e ⟧ ⟫ ⟫
  Translation.⟦ ⟦Term⟧ ⟧ ($⇐ e₁ ⋯ e₂) =
    return ⟪
      $⇐
        $⇐ ⟦ e₁ ⟧ ⋯
        ♯ zero !
      ⋯ $⇐ ⟦ e₂ ⟧ ⋯ ♯ zero !
    ⟫
  Translation.⟦ ⟦Term⟧ ⟧ tick = return ⟪ $⇐ tick ⋯ return ⟪ return ♯ zero ⟫ ⟫

⟦Γ∷τ⟧-expand : ∀ {n : ℕ} {Γ : Ctx n} {τ : Type}
               → ⟦ Γ ∷ τ ⟧ ≡ ⟦ Γ ⟧ CBPV.∷ 𝑼 pure ⟦ τ ⟧
⟦Γ∷τ⟧-expand = extensionality λ where
                                  zero    → refl
                                  (suc m) → refl

↦-preserves : ∀ {n : ℕ} {e : Term n} {M : Comp n}
                    {Γ : Ctx n} {τ : Type}
            → e ↦ M
            → Γ ⊢ e ⦂ τ
              -------------------------
            → ⟦ Γ ⟧ ⊢c M ⦂ ⟦ τ ⟧ # pure
↦-preserves transVar typeVar = typeForce typeVar pure-≤
↦-preserves transUnit typeUnit = typeRet typeUnit
↦-preserves {Γ = Γ} (transAbs e↦M) (typeAbs {τ = τ} Γ∷τ⊢e⦂τ′)
  with ↦-preserves e↦M Γ∷τ⊢e⦂τ′
...  | ⟦Γ∷τ⟧⊢M⦂⟦τ′⟧
  rewrite ⟦Γ∷τ⟧-expand {Γ = Γ} {τ} = typeAbs ⟦Γ∷τ⟧⊢M⦂⟦τ′⟧
↦-preserves (transApp e₁↦M e₂↦N) (typeApp Γ⊢e₁⦂τ′⇒τ Γ⊢e₂⦂τ′)
  with ↦-preserves e₁↦M Γ⊢e₁⦂τ′⇒τ | ↦-preserves e₂↦N Γ⊢e₂⦂τ′
...  | ⟦Γ⟧⊢M⦂⟦τ′⇒τ⟧               | ⟦Γ⟧⊢N⦂τ′                 =
  typeApp ⟦Γ⟧⊢M⦂⟦τ′⇒τ⟧ (typeThunk ⟦Γ⟧⊢N⦂τ′)
↦-preserves (transSeq e₁↦M e₂↦N) (typeSeq Γ⊢e₁⦂𝟙 Γ⊢e₂⦂τ)
  with ↦-preserves e₁↦M Γ⊢e₁⦂𝟙 | ↦-preserves e₂↦N Γ⊢e₂⦂τ
...  | ⟦Γ⟧⊢M⦂⟦𝟙⟧               | ⟦Γ⟧⊢e₂⦂⟦τ⟧               =
  typeLetin
    ⟦Γ⟧⊢M⦂⟦𝟙⟧
    (typeSequence typeVar (comp-typepres-renaming ⟦Γ⟧⊢e₂⦂⟦τ⟧ λ{_ → refl}))
    (≡→≤ +-pure-idʳ)
↦-preserves (transReturn e↦M) (typeReturn Γ⊢e⦂τ)
  with ↦-preserves e↦M Γ⊢e⦂τ
...  | ⟦Γ⟧⊢M⦂⟦τ⟧             =
  typeRet (typeThunk (typeRet (typeThunk ⟦Γ⟧⊢M⦂⟦τ⟧)))
↦-preserves {Γ = Γ} (transBind e₁↦M e₂↦N) (typeBind {τ′ = τ′} Γ⊢e₁⦂𝑻φ₁τ′
    Γ∷τ′⊢e₂⦂𝑻φ₂τ φ₁+φ₂≤φ)
  with ↦-preserves e₁↦M Γ⊢e₁⦂𝑻φ₁τ′ | ↦-preserves e₂↦N Γ∷τ′⊢e₂⦂𝑻φ₂τ
...  | ⟦Γ⟧⊢e₁⦂⟦𝑻φ₁τ′⟧              | ⟦Γ∷τ′⟧⊢e₂⦂⟦𝑻φ₂τ⟧
  rewrite ⟦Γ∷τ⟧-expand {Γ = Γ} {τ′} =
  typeRet
    (typeThunk
      (typeLetin
        (typeLetin
          ⟦Γ⟧⊢e₁⦂⟦𝑻φ₁τ′⟧
          (typeForce typeVar ≤-refl)
          (≡→≤ +-pure-idˡ))
        (typeLetin
          ⟦Γ∷τ′⟧⊢e₂⦂⟦𝑻φ₂τ⟧
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

e↦⟦e⟧ : ∀ {n : ℕ} {e : Term n} → e ↦ ⟦ e ⟧
e↦⟦e⟧ {e = # x} = transVar
e↦⟦e⟧ {e = unit} = transUnit
e↦⟦e⟧ {e = ƛ e} = transAbs e↦⟦e⟧
e↦⟦e⟧ {e = e₁ · e₂} = transApp e↦⟦e⟧ e↦⟦e⟧
e↦⟦e⟧ {e = e₁ » e₂} = transSeq e↦⟦e⟧ e↦⟦e⟧
e↦⟦e⟧ {e = return e} = transReturn e↦⟦e⟧
e↦⟦e⟧ {e = $⇐ e₁ ⋯ e₂} = transBind e↦⟦e⟧ e↦⟦e⟧
e↦⟦e⟧ {e = tick} = transTick

translation-preservation : ∀ {n : ℕ} {Γ : CBN.Ctx n} {e : Term n} {τ : Type}
                         → Γ ⊢ e ⦂ τ
                           -----------------------------
                         → ⟦ Γ ⟧ ⊢c ⟦ e ⟧ ⦂ ⟦ τ ⟧ # pure
translation-preservation = ↦-preserves e↦⟦e⟧
