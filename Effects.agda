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

      pure-≤ : ∀ {φ : Eff} → pure ≤ φ

    variable φ φ′ φ₁ φ₂ φ₃ ψ ψ₁ ψ₂ : Eff

  module Properties (E : Effect) where
    open Effect E

    ≤-+ʳ : φ₁ ≤ φ₁ + φ₂
    ≤-+ʳ {φ₁} {φ₂}
      with ≤-+-compatibleˡ {pure} {φ₂} {φ₁} pure-≤
    ...  | pf
      rewrite +-pure-idʳ {φ₁} = pf

    ≤-+ˡ : φ₁ ≤ φ₂ + φ₁
    ≤-+ˡ {φ₁} {φ₂}
      with ≤-+-compatibleʳ {pure} {φ₂} {φ₁} pure-≤
    ...  | pf
      rewrite +-pure-idˡ {φ₁} = pf

    ≤-+-invertʳ : φ₁ + φ ≤ φ₂
                → φ₁ ≤ φ₂
    ≤-+-invertʳ pf = ≤-trans ≤-+ʳ pf

    ≤-+-invertˡ : φ + φ₁ ≤ φ₂
                → φ₁ ≤ φ₂
    ≤-+-invertˡ pf = ≤-trans ≤-+ˡ pf

    ≡→≤ : φ₁ ≡ φ₂
        → φ₁ ≤ φ₂
    ≡→≤ refl = ≤-refl
