open import Effects

module CBV.Effects.Types (E : Effect) where

open Effect E

data Type : Set where
  𝟙 : Type
  _─_⟶_ : Type → Eff → Type → Type
  _*_ : Type → Type → Type
  _∪_ : Type → Type → Type

variable τ τ′ τ₁ τ₂ : Type

infixr 7 _─_⟶_
infixl 8 _*_
infixl 8 _∪_
