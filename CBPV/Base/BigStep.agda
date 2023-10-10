import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; zero; suc)
open Eq using (_≡_)

open import CBPV.Base.Substitution
open import CBPV.Base.Terms

module CBPV.Base.BigStep where

data Terminal : ℕ → Set where
  return_ : Val n → Terminal n
  ƛ_ : Comp (suc n) → Terminal n

variable T : Terminal n

from-terminal : Terminal n → Comp n
from-terminal (return V) = return V
from-terminal (ƛ M) = (ƛ M)

data _⟱_ : Comp n → Terminal zero → Set where
  ⟱terminal : from-terminal T ≡ M
              -------------------
            → M ⟱ T

  ⟱forceThunk : M ⟱ T
                -----------
              → ⟪ M ⟫ ! ⟱ T

  ⟱seq : M ⟱ T
         ---------
       → V » M ⟱ T

  ⟱letin : M ⟱ return V
         → N 〔 V 〕 ⟱ T
           -------------
         → $⟵ M ⋯ N ⟱ T

  ⟱app : M ⟱ ƛ M′
       → M′ 〔 V 〕 ⟱ T
         --------------
       → M · V ⟱ T

  ⟱split : M ⦅ V₂ • V₁ • id ⦆c ⟱ T
           ------------------------
         → $≔ ⟨ V₁ , V₂ ⟩ ⋯ M ⟱ T

  ⟱caseInl : M₁ 〔 V 〕 ⟱ T
             -------------------------------
           → case inl V inl⇒ M₁ inr⇒ M₂ ⟱ T

  ⟱caseInr : M₂ 〔 V 〕 ⟱ T
             -------------------------------
           → case inr V inl⇒ M₁ inr⇒ M₂ ⟱ T

infix 4 _⟱_
