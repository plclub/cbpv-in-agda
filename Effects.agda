import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

module Effects where
  record Effect : Set₁ where
    infix 4 _≤_
    infixl 6 _+_

    field
      Eff : Set

      pure : Eff
      tock : Eff

      _+_ : Eff → Eff → Eff

      +-assoc : ∀ {φ₁ φ₂ φ₃ : Eff}
              → (φ₁ + φ₂) + φ₃ ≡ φ₁ + (φ₂ + φ₃)

      +-pure-idʳ : ∀ {φ : Eff} → φ + pure ≡ φ

      +-pure-idˡ : ∀ {φ : Eff} → pure + φ ≡ φ

      _≤_ : Eff → Eff → Set

      ≤-refl : ∀ {φ : Eff} → φ ≤ φ

      ≤-trans : ∀ {φ₁ φ₂ φ₃ : Eff}
              → φ₁ ≤ φ₂
              → φ₂ ≤ φ₃
              → φ₁ ≤ φ₃

      ≤-+-compatibleʳ : ∀ {φ₁ φ₂ ψ : Eff}
                      → φ₁ ≤ φ₂
                      → φ₁ + ψ ≤ φ₂ + ψ

      ≤-+-compatibleˡ : ∀ {φ₁ φ₂ ψ : Eff}
                      → φ₁ ≤ φ₂
                      → ψ + φ₁ ≤ ψ + φ₂

    variable φ φ′ φ₁ φ₂ φ₃ ψ ψ₁ ψ₂ : Eff

  module Properties (E : Effect) where
    open Effect E

    ≤-+ʳ : pure ≤ φ₂ → φ₁ ≤ φ₁ + φ₂
    ≤-+ʳ {φ₂} {φ₁} pure≤φ₂
      with ≤-+-compatibleˡ {pure} {φ₂} {φ₁} pure≤φ₂
    ...  | pf
      rewrite +-pure-idʳ {φ₁} = pf

    ≤-+-invertʳ : φ₁ + φ ≤ φ₂
                → pure ≤ φ
                → φ₁ ≤ φ₂
    ≤-+-invertʳ pf pure≤φ = ≤-trans (≤-+ʳ pure≤φ) pf

    ≡→≤ : φ₁ ≡ φ₂
        → φ₁ ≤ φ₂
    ≡→≤ refl = ≤-refl
