import Axiom.Extensionality.Propositional as Ext
import Relation.Binary.PropositionalEquality as Eq
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)
open import Level using (0ℓ)
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; step-≡; _∎)
open Ext using (Extensionality)

open import CBPV.Base.Renaming
open import CBPV.Base.Terms

module CBPV.Base.Substitution where

postulate
  extensionality : Extensionality 0ℓ 0ℓ

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

_•_ : ∀ {n m : ℕ} → Sub n m → Val n → Sub n (suc m)
(σ • v) zero = v
(σ • v) (suc m) = σ m

infixl 5 _•_

id : ∀ {n : ℕ} → Sub n n
id m = # m

subst-zero : ∀ {n} → Val n → Sub n (suc n)
subst-zero V zero = V
subst-zero V (suc m) = # m

_〔_〕 : ∀ {n : ℕ} → Comp (suc n) → Val n → Comp n
M 〔 V 〕 = M ⦅ subst-zero V ⦆c

_∘_ : ∀ {n m p : ℕ} → Sub m n → Sub p m → Sub p n
(σ ∘ τ) m = σ m ⦅ τ ⦆v

cong-sub : ∀ 

exts-ids : ∀ {n : ℕ} → exts (id {n}) ≡ id
exts-ids = extensionality lemma where
  lemma = λ where zero    → refl
                  (suc m) → refl



mutual
  sub-id-val : ∀ {n : ℕ} (V : Val n)
             → V ⦅ id ⦆v ≡ V
  sub-id-val (# x) = refl
  sub-id-val (unit) = refl
  sub-id-val (⟪ M ⟫) rewrite sub-id M = refl

  sub-id : ∀ {n : ℕ} (M : Comp n)
         → M ⦅ id ⦆c ≡ M
  sub-id (ƛ M) = {!!}
  sub-id (M · V) rewrite sub-id-val V | sub-id M = refl
  sub-id (V » M) rewrite sub-id-val V | sub-id M = refl
  sub-id (V !) rewrite sub-id-val V = refl
  sub-id (return V) rewrite sub-id-val V = refl
  sub-id ($⟵ M ⋯ N) = {!!}

postulate
  sub-sub : ∀ {n m p : ℕ} {σ : Sub m n} {τ : Sub p m} {M : Comp n}
          → M ⦅ σ ⦆c ⦅ τ ⦆c ≡ M ⦅ σ ∘ τ ⦆c

  subst-zero-exts-cons : ∀ {n m : ℕ} {σ : Sub n m} {V : Val n}
                       → exts σ ∘ subst-zero V ≡ σ • V
