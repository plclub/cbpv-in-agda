open import Effects

module CBN.Monadic.Types (E : Effect) where

open Effect E

data Type : Set where
  𝟙 : Type
  _⇒_ : Type → Type → Type
  𝑻 : Eff → Type → Type

variable τ τ′ τ₁ τ₂ : Type
