open import Data.Nat using (ℕ; suc)

open import CBPV.Base.Substitution
open import CBPV.Base.Terms

module CBPV.Base.SmallStep where

data _⟶_ {n : ℕ} : Comp n → Comp n → Set where
  stepForceThunk : ∀ {M : Comp n}
                   --------------
                 → ⟪ M ⟫ ! ⟶ M

  β : ∀ {M : Comp (suc n)} {V : Val n}
      -------------------
    → (ƛ M) · V ⟶ M 〔 V 〕

  βLetIn : ∀ {V : Val n} {M : Comp (suc n)}
          → $⟵ return V ⋯ M ⟶ M 〔 V 〕

  stepApp : ∀ {M M′ : Comp n} {V : Val n}
          → M ⟶ M′
            --------------
          → M · V ⟶ M′ · V

  stepLetin : ∀ {M M′ : Comp n} {N : Comp (suc n)}
            → M ⟶ M′
              ----------------------
            → $⟵ M ⋯ N ⟶ $⟵ M′ ⋯ N

  βSeq : ∀ {M : Comp n}
            ------------
          → unit » M ⟶ M

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

⟶*-trans : ∀ {n : ℕ} {M M′ M″ : Comp n}
         → M ⟶* M′
         → M′ ⟶* M″
           --------
         → M ⟶* M″
⟶*-trans {M = M} (_ ∎) (_ ∎) = M ∎
⟶*-trans (_ ∎) (x ⟶⟨ y ⟩) = x ⟶⟨ y ⟩
⟶*-trans (x ⟶⟨ y ⟩) z = x ⟶⟨ ⟶*-trans y z ⟩

⟶*-app-compatible : ∀ {n : ℕ} {M M′ : Comp n} {V : Val n}
                  → M ⟶* M′
                    ---------------
                  → M · V ⟶* M′ · V
⟶*-app-compatible {M = M} {V = V} (_ ∎) = M · V ∎
⟶*-app-compatible (x ⟶⟨ y ⟩) = stepApp x ⟶⟨ ⟶*-app-compatible y ⟩

⟶*-letin-compatible : ∀ {n : ℕ} {M M′ : Comp n} {N : Comp (suc n)}
                    → M ⟶* M′
                    → $⟵ M ⋯ N ⟶* $⟵ M′ ⋯ N
⟶*-letin-compatible {M = M} {N = N} (_ ∎) = ($⟵ M ⋯ N) ∎
⟶*-letin-compatible (x ⟶⟨ y ⟩) = stepLetin x ⟶⟨ ⟶*-letin-compatible y ⟩
