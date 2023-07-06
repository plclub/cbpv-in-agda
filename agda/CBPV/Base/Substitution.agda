open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)

open import CBPV.Base.Renaming
open import CBPV.Base.Terms

module CBPV.Base.Substitution where

Sub : ℕ → ℕ → Set
Sub n n′ = (m : Fin n′) → Val n

exts : ∀ {n n′ : ℕ} → Sub n n′ → Sub (suc n) (suc n′)
exts σ zero = # zero
exts σ (suc m) = (σ m) [ suc ]v

mutual
  _⦅_⦆v : ∀ {n n′ : ℕ}
          → Val n′
          → Sub n n′
           --------
          → Val n
  unit ⦅ _ ⦆v    = unit
  # m ⦅ σ ⦆v     = σ m
  ⟪ M ⟫ ⦅ σ ⦆v   = ⟪ M ⦅ σ ⦆c ⟫

  _⦅_⦆c : ∀ {n n′ : ℕ}
         → Comp n′
         → Sub n n′
           --------
         → Comp n
  (ƛ M) ⦅ σ ⦆c   = ƛ M ⦅ exts σ ⦆c
  (M · V) ⦅ σ ⦆c = M ⦅ σ ⦆c · V ⦅ σ ⦆v
  (V » M) ⦅ σ ⦆c = V ⦅ σ ⦆v » M ⦅ σ ⦆c
  (return V) ⦅ σ ⦆c = return V ⦅ σ ⦆v
  ($⟵ M ⋯ N) ⦅ σ ⦆c = $⟵ M ⦅ σ ⦆c ⋯ N ⦅ exts σ ⦆c
  (V !) ⦅ σ ⦆c = V ⦅ σ ⦆v !

infix 8 _⦅_⦆v
infix 8 _⦅_⦆c

_〔_〕 : ∀ {n : ℕ} → Comp (suc n) → Val n → Comp n
M 〔 V 〕 = M ⦅ σ ⦆c where
  σ = λ where
          zero    → V
          (suc m) → # m
