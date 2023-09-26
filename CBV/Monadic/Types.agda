open import Effects

module CBV.Monadic.Types (E : Effect) where

open Effect E

data Type : Set where
  𝟙 : Type
  _⇒_ : Type → Type → Type
  𝑻 : Eff → Type → Type
