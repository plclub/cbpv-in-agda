open import Effects

module CBPV.Effects.Types (E : Effect) where

open Effect E

mutual
  data ValType : Set where
    𝟙 : ValType
    𝑼 : Eff → CompType → ValType

  data CompType : Set where
    _⇒_ : ValType → CompType → CompType
    𝑭 : ValType → CompType

infixr 7 _⇒_
