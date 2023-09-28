open import Data.Nat using (ℕ; suc)

open import CBPV.Effects.Substitution
open import CBPV.Effects.Terms
open import Effects

module CBPV.Effects.SmallStep (E : Effect) where

open Effect E
open Effects.Properties E

data _⟶_#_ {n : ℕ} : Comp n → Comp n → Eff → Set where
  stepForceThunk : ∀ {M : Comp n}
                   ------------------
                 → ⟪ M ⟫ ! ⟶ M # pure

  β : ∀ {M : Comp (suc n)} {V : Val n}
      ---------------------------
    → (ƛ M) · V ⟶ M 〔 V 〕 # pure

  βLetIn : ∀ {V : Val n} {M : Comp (suc n)}
          → $⟵ return V ⋯ M ⟶ M 〔 V 〕 # pure

  stepApp : ∀ {M M′ : Comp n} {V : Val n} {φ : Eff}
          → M ⟶ M′ # φ
            -------------------
          → M · V ⟶ M′ · V # φ

  stepLetin : ∀ {M M′ : Comp n} {N : Comp (suc n)} {φ : Eff}
            → M ⟶ M′ # φ
              -------------------------
            → $⟵ M ⋯ N ⟶ $⟵ M′ ⋯ N # φ

  βSeq : ∀ {M : Comp n}
            -------------------
          → unit » M ⟶ M # pure

  βtick : tick ⟶ return unit # tock


infix 4 _⟶_#_

data _⟶*_#_ {n : ℕ} : Comp n → Comp n → Eff → Set where
  _∎ : ∀ (M : Comp n)
         ------------
       → M ⟶* M # pure

  _⟶⟨_⟩ : ∀ {M M′ M″ : Comp n} {φ₁ φ₂ : Eff}
        → M ⟶ M′ # φ₁
        → M′ ⟶* M″ # φ₂
          --------
        → M ⟶* M″ # φ₁ + φ₂

infix 5 _∎
infixr 4 _⟶⟨_⟩
infix 4 _⟶*_#_

⟶*-trans : ∀ {n : ℕ} {M M′ M″ : Comp n} {φ₁ φ₂ : Eff}
         → M ⟶* M′ # φ₁
         → M′ ⟶* M″ # φ₂
           -----------------
         → M ⟶* M″ # φ₁ + φ₂
⟶*-trans {M = M} (_ ∎) (_ ∎) rewrite +-pure-idʳ {φ = pure} = M ∎
⟶*-trans {φ₂ = φ₂} (_ ∎) (x ⟶⟨ y ⟩) rewrite +-pure-idˡ {φ = φ₂} = x ⟶⟨ y ⟩
⟶*-trans {φ₂ = φ₃} (_⟶⟨_⟩ {φ₁ = φ₁} {φ₂} x y) z rewrite +-assoc {φ₁} {φ₂} {φ₃} =
  x ⟶⟨ ⟶*-trans y z ⟩

⟶*-app-compatible : ∀ {n : ℕ} {M M′ : Comp n} {V : Val n} {φ : Eff}
                  → M ⟶* M′ # φ
                    -------------------
                  → M · V ⟶* M′ · V # φ
⟶*-app-compatible {M = M} {V = V} (_ ∎) = M · V ∎
⟶*-app-compatible (x ⟶⟨ y ⟩) = stepApp x ⟶⟨ ⟶*-app-compatible y ⟩

⟶*-letin-compatible : ∀ {n : ℕ} {M M′ : Comp n} {N : Comp (suc n)} {φ : Eff}
                    → M ⟶* M′ # φ
                    → $⟵ M ⋯ N ⟶* $⟵ M′ ⋯ N # φ
⟶*-letin-compatible {M = M} {N = N} (_ ∎) = ($⟵ M ⋯ N) ∎
⟶*-letin-compatible (x ⟶⟨ y ⟩) = stepLetin x ⟶⟨ ⟶*-letin-compatible y ⟩