import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; suc)
open Eq using (sym)

open import CBPV.Effects.Terms
open import Effects

module CBPV.Effects.SmallStep (E : Effect) where

open import CBPV.Effects.Substitution E
open Effect E
open Effects.Properties E

data _⟶_#_ {n : ℕ} : Comp n → Comp n → Eff → Set where
  -- Computation rules
  βforceThunk : ⟪ M ⟫ ! ⟶ M # pure

  β : (ƛ M) · V ⟶ M 〔 V 〕 # pure

  βletin : $⟵ return V ⋯ M ⟶ M 〔 V 〕 # pure

  βsplit : $≔ ⟨ V₁ , V₂ ⟩ ⋯ M ⟶ M ⦅ V₂ • V₁ • id ⦆c # pure

  βcaseInl : case inl V inl⇒ M₁ inr⇒ M₂ ⟶ M₁ 〔 V 〕 # pure

  βcaseInr : case inr V inl⇒ M₁ inr⇒ M₂ ⟶ M₂ 〔 V 〕 # pure

  βSeq : unit » M ⟶ M # pure

  βtick : tick ⟶ return unit # tock

  -- Compatibility rules
  stepApp : M ⟶ M′ # φ
            -------------------
          → M · V ⟶ M′ · V # φ

  stepLetin : M ⟶ M′ # φ
              -------------------------
            → $⟵ M ⋯ N ⟶ $⟵ M′ ⋯ N # φ

infix 4 _⟶_#_

data _⟶*_#_ {n : ℕ} : Comp n → Comp n → Eff → Set where
  _∎ : ∀ (M : Comp n)
         -------------
       → M ⟶* M # pure

  _⟶⟨_⟩_ : M ⟶ M′ # φ₁
         → M′ ⟶* M″ # φ₂
         → φ₁ + φ₂ ≤ φ
           -------------
         → M ⟶* M″ # φ

infix 5 _∎
infixr 4 _⟶⟨_⟩_
infix 4 _⟶*_#_

⟶*-trans : M ⟶* M′ # φ₁
         → M′ ⟶* M″ # φ₂
           -----------------
         → M ⟶* M″ # φ₁ + φ₂
⟶*-trans {M = M} (_ ∎) (_ ∎) rewrite +-pure-idʳ {φ = pure} = M ∎
⟶*-trans (_ ∎) (x ⟶⟨ y ⟩ φ₁+φ₂≤φ)  = x ⟶⟨ y ⟩ ≤-trans φ₁+φ₂≤φ (≡→≤ (sym (+-pure-idˡ)))
⟶*-trans (x ⟶⟨ y ⟩ φ₁+φ₂≤φ) z =
  x ⟶⟨ ⟶*-trans y z ⟩ ≤-trans (≡→≤ (sym (+-assoc))) (≤-+-compatibleʳ φ₁+φ₂≤φ)

⟶*-app-compatible : M ⟶* M′ # φ
                    -------------------
                  → M · V ⟶* M′ · V # φ
⟶*-app-compatible {M = M} {V = V} (_ ∎) = M · V ∎
⟶*-app-compatible (x ⟶⟨ y ⟩ pf) = stepApp x ⟶⟨ ⟶*-app-compatible y ⟩ pf

⟶*-letin-compatible : M ⟶* M′ # φ
                    → $⟵ M ⋯ N ⟶* $⟵ M′ ⋯ N # φ
⟶*-letin-compatible {M = M} {N = N} (_ ∎) = ($⟵ M ⋯ N) ∎
⟶*-letin-compatible (x ⟶⟨ y ⟩ pf) = stepLetin x ⟶⟨ ⟶*-letin-compatible y ⟩ pf
