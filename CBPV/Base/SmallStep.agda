open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_)

open import CBPV.Base.Substitution
open import CBPV.Base.Terms

module CBPV.Base.SmallStep where

data Normal : Comp n → Set where
  normalAbs : Normal (ƛ M)

  normalCpair : Normal ⟨ M₁ , M₂ ⟩

  normalReturn : Normal (return V)

data _⟶_ : Comp n → Comp n → Set where
  -- Computation rules
  βforceThunk : ⟪ M ⟫ ! ⟶ M

  β : (ƛ M) · V ⟶ M 〔 V 〕

  βletin : $⟵ return V ⋯ M ⟶ M 〔 V 〕

  βseq : unit » M ⟶ M

  βsplit : $≔ ⟨ V₁ , V₂ ⟩ ⋯ M ⟶ M ⦅ V₂ • V₁ • id ⦆c

  βprojl : projl ⟨ M₁ , M₂ ⟩ ⟶ M₁

  βprojr : projr ⟨ M₁ , M₂ ⟩ ⟶ M₂

  βcaseInl : case inl V inl⇒ M₁ inr⇒ M₂ ⟶ M₁ 〔 V 〕

  βcaseInr : case inr V inl⇒ M₁ inr⇒ M₂ ⟶ M₂ 〔 V 〕

  -- Compatibility rules
  stepApp : M ⟶ M′
            --------------
          → M · V ⟶ M′ · V

  stepLetin : M ⟶ M′
              ----------------------
            → $⟵ M ⋯ N ⟶ $⟵ M′ ⋯ N

  stepProjl : M ⟶ M′
              ------------------
            → projl M ⟶ projl M′

  stepProjr : M ⟶ M′
              ------------------
            → projr M ⟶ projr M′

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

_has-normal-form_ : Comp n → Comp n → Set
M has-normal-form N = M ⟶* N × Normal N

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
                    → projl M ⟶* projl M′
⟶*-projl-compatible {M = M} (_ ∎) = projl M ∎
⟶*-projl-compatible (x ⟶⟨ y ⟩) = stepProjl x ⟶⟨ ⟶*-projl-compatible y ⟩


⟶*-projr-compatible : M ⟶* M′
                    → projr M ⟶* projr M′
⟶*-projr-compatible {M = M} (_ ∎) = projr M ∎
⟶*-projr-compatible (x ⟶⟨ y ⟩) = stepProjr x ⟶⟨ ⟶*-projr-compatible y ⟩
