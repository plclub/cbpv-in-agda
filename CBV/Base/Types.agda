module CBV.Base.Types where

data Type : Set where
  𝟙 : Type
  _⇒_ : Type → Type → Type
  _*_ : Type → Type → Type
  _∪_ : Type → Type → Type

variable τ τ′ τ₁ τ₂ : Type

infixr 7 _⇒_
infixl 8 _*_
infixl 8 _∪_
