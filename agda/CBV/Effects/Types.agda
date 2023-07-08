open import Effects

module CBV.Effects.Types (E : Effect) where

open Effect E

data Type : Set where
  𝟙 : Type
  _─_⟶_ : Type → Eff → Type → Type
