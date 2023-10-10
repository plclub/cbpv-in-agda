open import Effects

module CBPV.Effects.Types (E : Effect) where

open Effect E

mutual
  data ValType : Set where
    𝟙 : ValType
    𝑼 : Eff → CompType → ValType
    _*_ : ValType → ValType → ValType
    _∪_ : ValType → ValType → ValType

  data CompType : Set where
    _⇒_ : ValType → CompType → CompType
    𝑭 : ValType → CompType
    _&_ : CompType → CompType → CompType

variable A A₁ A₂ : ValType
variable B B₁ B₂ : CompType

infixr 7 _⇒_
infixl 8 _*_
infixl 8 _∪_
infixl 8 _&_
