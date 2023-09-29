import Relation.Binary.PropositionalEquality as Eq
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)
open Eq using (_≡_; refl)

open import CBPV.Base.Terms
open import CBPV.Base.Types
open import CBPV.Base.SyntacticTyping

module CBPV.Base.Renaming where

Ren : ℕ → ℕ → Set
Ren n n′ = (m : Fin n′) → Fin n

ext : ∀ {n n′ : ℕ} → Ren n n′ → Ren (suc n) (suc n′)
ext ρ zero = zero
ext ρ (suc m) = suc (ρ m)

mutual
  _[_]v : ∀ {n n′ : ℕ}
         → Val n′
         → Ren n n′
           --------
         → Val n
  unit [ _ ]v    = unit
  # m [ ρ ]v     = # ρ m
  ⟪ M ⟫ [ ρ ]v   = ⟪ M [ ρ ]c ⟫

  _[_]c : ∀ {n n′ : ℕ}
         → Comp n′
         → Ren n n′
           --------
         → Comp n
  (ƛ M) [ ρ ]c   = ƛ M [ ext ρ ]c
  (M · V) [ ρ ]c = M [ ρ ]c · V [ ρ ]v
  (V » M) [ ρ ]c = V [ ρ ]v » M [ ρ ]c
  (return V) [ ρ ]c = return V [ ρ ]v
  ($⟵ M ⋯ N) [ ρ ]c = $⟵ M [ ρ ]c ⋯ N [ ext ρ ]c
  (V !) [ ρ ]c = V [ ρ ]v !

infix 8 _[_]v
infix 8 _[_]c

mutual
  val-typepres-renaming : ∀ {ρ : Ren n n′}
                         → Δ ⊢v V ⦂ A
                         → (∀ (m : Fin n′) → Δ m ≡ Γ (ρ m))
                           --------------------------------
                         → Γ ⊢v V [ ρ ]v ⦂ A
  val-typepres-renaming (typeVar {m = m}) pf rewrite pf m = typeVar
  val-typepres-renaming typeUnit _ = typeUnit
  val-typepres-renaming (typeThunk ⊢M) pf = typeThunk (comp-typepres-renaming ⊢M pf)

  comp-typepres-renaming : ∀ {ρ : Ren n n′} 
                         → Δ ⊢c M ⦂ B
                         → (∀ (m : Fin n′) → Δ m ≡ Γ (ρ m))
                           --------------------------------
                         → Γ ⊢c M [ ρ ]c ⦂ B
  comp-typepres-renaming (typeAbs ⊢M) pf =
    typeAbs (comp-typepres-renaming ⊢M ext-pf)
    where
      ext-pf = λ where
                   zero    → refl
                   (suc m) → pf m
  comp-typepres-renaming (typeApp ⊢M ⊢V) pf =
    typeApp (comp-typepres-renaming ⊢M pf) (val-typepres-renaming ⊢V pf)
  comp-typepres-renaming (typeSequence ⊢V ⊢M) pf =
    typeSequence
      (val-typepres-renaming ⊢V pf)
      (comp-typepres-renaming ⊢M pf)
  comp-typepres-renaming (typeForce ⊢V) pf =
    typeForce (val-typepres-renaming ⊢V pf)
  comp-typepres-renaming (typeRet ⊢V) pf =
    typeRet (val-typepres-renaming ⊢V pf)
  comp-typepres-renaming (typeLetin ⊢M ⊢N) pf =
    typeLetin
      (comp-typepres-renaming ⊢M pf)
      (comp-typepres-renaming ⊢N ext-pf)
    where
      ext-pf = λ where
                   zero    → refl
                   (suc m) → pf m
