module CBPV.Base.Types where

mutual
  data ValType : Set where
    𝟙 : ValType
    𝑼 : CompType → ValType

  data CompType : Set where
    _⇒_ : ValType → CompType → CompType
    𝑭 : ValType → CompType

infixr 7 _⇒_
