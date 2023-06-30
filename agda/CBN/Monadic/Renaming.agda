open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)

open import CBN.Monadic.Terms

module CBN.Monadic.Renaming  where

Ren : ℕ → ℕ → Set
Ren n n′ = (m : Fin n′) → Fin n

ext : ∀ {n n′ : ℕ} → Ren n n′ → Ren (suc n) (suc n′)
ext ρ zero = zero
ext ρ (suc m) = suc (ρ m)

_[_] : ∀ {n n′ : ℕ}
      → Term n′
      → Ren n n′
        -------
      → Term n
unit [ _ ]    = unit
# m [ ρ ]     = # ρ m
(ƛ t) [ ρ ]   = ƛ t [ ext ρ ]
(e₁ · e₂) [ ρ ] = e₁ [ ρ ] · e₂ [ ρ ]
(e₁ » e₂) [ ρ ] = e₁ [ ρ ] » e₂ [ ρ ]
(return e) [ ρ ] = return e [ ρ ]
($⇐ e₁ ⋯ e₂) [ ρ ] = $⇐ e₁ [ ρ ] ⋯ e₂ [ ρ ]
tick [ _ ] = tick

infix 8 _[_]
