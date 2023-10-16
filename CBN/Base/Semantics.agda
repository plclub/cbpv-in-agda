import Relation.Binary.PropositionalEquality as Eq
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; suc)
open Eq using (_≡_)

open import CBN.Base.Terms

module CBN.Base.Semantics where

mutual
  data Clos : Set where
    clos⦅_,_⦆ : Env n → Term n → Clos

  Env : ℕ → Set
  Env n = Fin n → Clos
  
variable a b d : Clos
variable γ δ : Env n

_++_ : Env n → Clos → Env (suc n)
(γ ++ a) zero = a
(γ ++ a) (suc m) = γ m

infixl 5 _++_

data _⊢_⇓_ : Env n → Term n → Clos → Set where
  evalVar : γ m ≡ clos⦅ δ , e ⦆
          → δ ⊢ e ⇓ a
            -------------------
          → γ ⊢ # m ⇓ a

  evalUnit : γ ⊢ unit ⇓ clos⦅ γ , unit ⦆

  evalInl : γ ⊢ inl e ⇓ clos⦅ γ , inl e ⦆

  evalInr : γ ⊢ inr e ⇓ clos⦅ γ , inr e ⦆

  evalPair : γ ⊢ ⟨ e₁ , e₂ ⟩ ⇓ clos⦅ γ , ⟨ e₁ , e₂ ⟩ ⦆

  evalAbs : γ ⊢ ƛ e ⇓ clos⦅ γ , ƛ e ⦆

  evalApp : γ ⊢ e₁ ⇓ clos⦅ δ , ƛ e ⦆
          → δ ++ clos⦅ γ , e₂ ⦆ ⊢ e ⇓ a
            ---------------------------
          → γ ⊢ e₁ · e₂ ⇓ a

  evalSeq : γ ⊢ e₁ ⇓ clos⦅ δ , unit ⦆
          → γ ⊢ e₂ ⇓ a
            ---------------
          → γ ⊢ e₁ » e₂ ⇓ a

  evalFst : γ ⊢ e ⇓ clos⦅ δ , ⟨ e₁ , e₂ ⟩ ⦆
          → δ ⊢ e₁ ⇓ a
            -------------------------------
          → γ ⊢ fst e ⇓ a

  evalSnd : γ ⊢ e ⇓ clos⦅ δ , ⟨ e₁ , e₂ ⟩ ⦆
          → δ ⊢ e₂ ⇓ a
            ------------------------------
          → γ ⊢ snd e ⇓ a 

  evalCaseInl : γ ⊢ e ⇓ clos⦅ δ , inl e′ ⦆
              → γ ++ clos⦅ δ , e′ ⦆ ⊢ e₁ ⇓ a
                ------------------------------
              → γ ⊢ case e inl⇒ e₁ inr⇒ e₂ ⇓ a

  evalCaseInr : γ ⊢ e ⇓ clos⦅ δ , inr e′ ⦆
              → γ ++ clos⦅ δ , e′ ⦆ ⊢ e₂ ⇓ a
                ------------------------------
              → γ ⊢ case e inl⇒ e₁ inr⇒ e₂ ⇓ a

infix 4 _⊢_⇓_
