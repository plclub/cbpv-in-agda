open import Data.Nat using (ℕ; suc)

open import CBPV.Base.Substitution
open import CBPV.Base.Terms

module CBPV.Base.SmallStep where

data _⟶_ : Comp n → Comp n → Set where
  -- Computation rules
  βforceThunk : ⟪ M ⟫ ! ⟶ M

  β : (ƛ M) · V ⟶ M 〔 V 〕

  βletin : $⟵ return V ⋯ M ⟶ M 〔 V 〕

  βseq : unit » M ⟶ M

  βsplit : $≔ ⟨ V₁ , V₂ ⟩ ⋯ M ⟶ M ⦅ V₂ • V₁ • id ⦆c

  βcaseInl : case inl V inl⇒ M₁ inr⇒ M₂ ⟶ M₁ 〔 V 〕

  βcaseInr : case inr V inl⇒ M₁ inr⇒ M₂ ⟶ M₂ 〔 V 〕

  βprojl : projl ⟨ M₁ , M₂ ⟩ ⟶ M₁

  βprojr : projr ⟨ M₁ , M₂ ⟩ ⟶ M₂

  -- Compatibility rules
  stepProjl : M ⟶ M′
              ------------------
            → projl M ⟶ projl M′

  stepProjr : M ⟶ M′
              ------------------
            → projr M ⟶ projr M′

  stepApp : M ⟶ M′
            --------------
          → M · V ⟶ M′ · V

  stepLetin : M ⟶ M′
              ----------------------
            → $⟵ M ⋯ N ⟶ $⟵ M′ ⋯ N

infix 4 _⟶_

data _⟶*_ {n : ℕ} : Comp n → Comp n → Set where
  _∎ : ∀ (M : Comp n)
         ------------
       → M ⟶* M

  _⟶⟨_⟩ : ∀ {M M′ M″ : Comp n}
        → M ⟶ M′
        → M′ ⟶* M″
          --------
        → M ⟶* M″

infix 5 _∎
infixr 4 _⟶⟨_⟩
infix 4 _⟶*_

⟶*-trans : M ⟶* M′
         → M′ ⟶* M″
           --------
         → M ⟶* M″
⟶*-trans {M = M} (_ ∎) (_ ∎) = M ∎
⟶*-trans (_ ∎) (x ⟶⟨ y ⟩) = x ⟶⟨ y ⟩
⟶*-trans (x ⟶⟨ y ⟩) z = x ⟶⟨ ⟶*-trans y z ⟩

⟶*-app-compatible : M ⟶* M′
                    ---------------
                  → M · V ⟶* M′ · V
⟶*-app-compatible {M = M} {V = V} (_ ∎) = M · V ∎
⟶*-app-compatible (x ⟶⟨ y ⟩) = stepApp x ⟶⟨ ⟶*-app-compatible y ⟩

⟶*-letin-compatible : M ⟶* M′
                    → $⟵ M ⋯ N ⟶* $⟵ M′ ⋯ N
⟶*-letin-compatible {M = M} {N = N} (_ ∎) = ($⟵ M ⋯ N) ∎
⟶*-letin-compatible (x ⟶⟨ y ⟩) = stepLetin x ⟶⟨ ⟶*-letin-compatible y ⟩

⟶*-projl-compatible : M ⟶* M′
                      -------------------
                    → projl M ⟶* projl M′
⟶*-projl-compatible (M ∎) = projl M ∎
⟶*-projl-compatible (x ⟶⟨ y ⟩) = stepProjl x ⟶⟨ ⟶*-projl-compatible y ⟩

⟶*-projr-compatible : M ⟶* M′
                      -------------------
                    → projr M ⟶* projr M′
⟶*-projr-compatible (M ∎) = projr M ∎
⟶*-projr-compatible (x ⟶⟨ y ⟩) = stepProjr x ⟶⟨ ⟶*-projr-compatible y ⟩
