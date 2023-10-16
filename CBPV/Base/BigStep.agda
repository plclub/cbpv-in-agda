open import Data.Nat using (ℕ; suc)

open import CBPV.Base.Substitution
open import CBPV.Base.Terms

module CBPV.Base.BigStep where

data _⇓_ : Comp n → Comp n where
