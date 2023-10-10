import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open Eq using (_≡_; refl)

open import CBPV.Effects.Terms
open import Effects

module CBPV.Effects.Determinism (E : Effect) where

open import CBPV.Effects.Semantics E

open Effect E

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

  determinism-comp : ρ ⊢c M ⇓ T # φ
                   → ρ ⊢c M ⇓ T′ # φ′
                   → T ≡ T′ × φ ≡ φ′
  determinism-comp evalAbs evalAbs = refl , refl
  determinism-comp (evalRet V⇓) (evalRet V⇓′)
    rewrite determinism-val V⇓ V⇓′ = refl , refl
  determinism-comp (evalSeq V⇓ M⇓) (evalSeq V⇓′ M⇓′)
    rewrite determinism-val V⇓ V⇓′
    with determinism-comp M⇓ M⇓′
  ...  | refl , refl = refl , refl
  determinism-comp (evalApp M⇓ V⇓ M′⇓) (evalApp M⇓′ V⇓′ M′⇓′)
    with determinism-comp M⇓ M⇓′
  ...  | refl , refl
    rewrite determinism-val V⇓ V⇓′
    with determinism-comp M′⇓ M′⇓′
  ...  | refl , refl = refl , refl
  determinism-comp (evalForce V⇓ M⇓) (evalForce V⇓′ M⇓′)
    with determinism-val V⇓ V⇓′
  ...  | refl
    with determinism-comp M⇓ M⇓′
  ...  | refl , refl = refl , refl
  determinism-comp (evalLetin M⇓ N⇓) (evalLetin M⇓′ N⇓′)
    with determinism-comp M⇓ M⇓′
  ...  | refl , refl
    with determinism-comp N⇓ N⇓′
  ...  | refl , refl = refl , refl
  determinism-comp (evalSplit V⇓ M⇓) (evalSplit V⇓′ M⇓′)
    with determinism-val V⇓ V⇓′
  ...  | refl
    with determinism-comp M⇓ M⇓′
  ...  | refl , refl = refl , refl
  determinism-comp (evalCaseInl V⇓ M⇓) (evalCaseInl V⇓′ M⇓′)
    with determinism-val V⇓ V⇓′
  ...  | refl
    with determinism-comp M⇓ M⇓′
  ...  | refl , refl = refl , refl
  determinism-comp (evalCaseInl V⇓ _) (evalCaseInr V⇓′ _)
    with determinism-val V⇓ V⇓′
  ...  | ()
  determinism-comp (evalCaseInr V⇓ _) (evalCaseInl V⇓′ _)
    with determinism-val V⇓ V⇓′
  ...  | ()
  determinism-comp (evalCaseInr V⇓ M⇓) (evalCaseInr V⇓′ M⇓′)
    with determinism-val V⇓ V⇓′
  ...  | refl
    with determinism-comp M⇓ M⇓′
  ...  | refl , refl = refl , refl
  determinism-comp evalCpair evalCpair = refl , refl
  determinism-comp (evalProjl M⇓ M₁⇓) (evalProjl M⇓′ M₁⇓′)
    with determinism-comp M⇓ M⇓′
  ...  | refl , refl
   with determinism-comp M₁⇓ M₁⇓′
  ... | refl , refl = refl , refl
  determinism-comp (evalProjr M⇓ M₂⇓) (evalProjr M⇓′ M₂⇓′)
    with determinism-comp M⇓ M⇓′
  ...  | refl , refl
    with determinism-comp M₂⇓ M₂⇓′
  ...  | refl , refl = refl , refl
  determinism-comp evalTick evalTick = refl , refl
