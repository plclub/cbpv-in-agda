import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ)
open Eq using (_≡_; refl)

open import CBPV.Base.Semantics
open import CBPV.Base.Terms

module CBPV.Base.Determinism where

mutual
  determinism-val : ρ ⊢v V ⇓ W
                  → ρ ⊢v V ⇓ W′
                  → W ≡ W′
  determinism-val evalVar evalVar = refl
  determinism-val evalUnit evalUnit = refl
  determinism-val evalThunk evalThunk = refl
  determinism-val (evalPair V₁⇓ V₂⇓) (evalPair V₁⇓′ V₂⇓′)
    rewrite determinism-val V₁⇓ V₁⇓′ | determinism-val V₂⇓ V₂⇓′ = refl
  determinism-val (evalInl V⇓) (evalInl V⇓′)
    rewrite determinism-val V⇓ V⇓′ = refl
  determinism-val (evalInr V⇓) (evalInr V⇓′)
    rewrite determinism-val V⇓ V⇓′ = refl

  determinism-comp : ρ ⊢c M ⇓ T
                   → ρ ⊢c M ⇓ T′
                   → T ≡ T′
  determinism-comp evalAbs evalAbs = refl
  determinism-comp (evalRet V⇓) (evalRet V⇓′)
    rewrite determinism-val V⇓ V⇓′ = refl
  determinism-comp (evalSeq V⇓ M⇓) (evalSeq V⇓′ M⇓′)
    rewrite determinism-val V⇓ V⇓′ | determinism-comp M⇓ M⇓′ = refl
  determinism-comp (evalApp M⇓ V⇓ M′⇓) (evalApp M⇓′ V⇓′ M′⇓′)
    with determinism-comp M⇓ M⇓′
  ...  | refl
    rewrite determinism-val V⇓ V⇓′ | determinism-comp M′⇓ M′⇓′ = refl
  determinism-comp (evalForce V⇓ M⇓) (evalForce V⇓′ M⇓′)
    with determinism-val V⇓ V⇓′
  ...  | refl
    rewrite determinism-comp M⇓ M⇓′ = refl
  determinism-comp (evalLetin M⇓ N⇓) (evalLetin M⇓′ N⇓′)
    with determinism-comp M⇓ M⇓′
  ...  | refl
    rewrite determinism-comp N⇓ N⇓′ = refl
  determinism-comp (evalSplit V⇓ M⇓) (evalSplit V⇓′ M⇓′)
    with determinism-val V⇓ V⇓′
  ...  | refl
    rewrite determinism-comp M⇓ M⇓′ = refl
  determinism-comp (evalCaseInl V⇓ M⇓) (evalCaseInl V⇓′ M⇓′)
    with determinism-val V⇓ V⇓′
  ...  | refl
    rewrite determinism-comp M⇓ M⇓′ = refl
  determinism-comp (evalCaseInl V⇓ _) (evalCaseInr V⇓′ _)
    with determinism-val V⇓ V⇓′
  ... | ()
  determinism-comp (evalCaseInr V⇓ _) (evalCaseInl V⇓′ _)
    with determinism-val V⇓ V⇓′
  ... | ()
  determinism-comp (evalCaseInr V⇓ M⇓) (evalCaseInr V⇓′ M⇓′)
    with determinism-val V⇓ V⇓′
  ...  | refl
    rewrite determinism-comp M⇓ M⇓′ = refl
