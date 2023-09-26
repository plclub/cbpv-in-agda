module CBN.Base.Types where

data Type : Set where
  𝟙 : Type
  _⇒_ : Type → Type → Type
