open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)

open import CBPV.Base.Terms

module CBPV.Base.Renaming  where

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
  ($⇐ M ⋯ N) [ ρ ]c = $⇐ M [ ρ ]c ⋯ N [ ext ρ ]c
  (V !) [ ρ ]c = V [ ρ ]v !

infix 8 _[_]v
infix 8 _[_]c
