import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open Eq using (_≡_; refl; sym)

open import CBPV.Base.Semantics
open import CBPV.Base.SmallStep
open import CBPV.Base.Substitution
open import CBPV.Base.Terms

module CBPV.Base.Adequacy where

mutual
  _~_ : Env n → Sub zero n → Set
  ρ ~ σ = ∀ m → ρ m ≈v σ m

  _≈v_ : ClosVal → Val zero → Set
  unit ≈v unit = ⊤
  clos⦅ ρ ,⟪ M ⟫⦆ ≈v V = ∃[ σ ] ρ ~ σ × V ≡ ⟪ M ⦅ σ ⦆c ⟫
  _ ≈v _ = ⊥

  _≈c_ : ClosTerminal → Comp zero → Set
  (return V₁) ≈c (return V₂) = V₁ ≈v V₂
  clos⦅ ρ ,ƛ M ⦆ ≈c N = ∃[ σ ] ρ ~ σ × N ≡ (ƛ M) ⦅ σ ⦆c
  _ ≈c _ = ⊥

infix 4 _~_
infix 4 _≈v_
infix 4 _≈c_

~-ext : ρ ~ σ → W ≈v V → ρ ∷ᵨ W ~ V • σ
~-ext _ W≈V zero = W≈V
~-ext ρ~σ _ (suc m) = ρ~σ m

mutual
  ⇓-adequate-val : ρ ~ σ
                 → ρ ⊢v V ⇓ W
                 → W ≈v V ⦅ σ ⦆v
  ⇓-adequate-val ρ~σ (evalVar {m = m}) = ρ~σ m
  ⇓-adequate-val ρ~σ evalUnit = tt
  ⇓-adequate-val {σ = σ} ρ~σ evalThunk = σ , ρ~σ , refl

  ⇓-adequate : ρ ~ σ
             → ρ ⊢c M ⇓ T
               -----------------------------
             → ∃[ N ] M ⦅ σ ⦆c ⟶* N × T ≈c N
  ⇓-adequate {σ = σ} {M = M} ρ~σ evalAbs =
    M ⦅ σ ⦆c , M ⦅ σ ⦆c ∎ , σ , ρ~σ , refl
  ⇓-adequate {σ = σ} ρ~σ (evalRet {V = V} V⇓) =
    return V ⦅ σ ⦆v , (return V ⦅ σ ⦆v) ∎ , ⇓-adequate-val ρ~σ V⇓
  ⇓-adequate {σ = σ} ρ~σ (evalSeq {V = V} V⇓ M⇓)
    with ⇓-adequate-val ρ~σ V⇓ | ⇓-adequate ρ~σ M⇓
  ...  | unit≈V                | N , M⟶ , T≈N
    with V ⦅ σ ⦆v in eq
  ... | unit =
    N , (βSeq ⟶⟨ M⟶ ⟩) , T≈N
  ⇓-adequate {σ = σ} ρ~σ (evalApp {M′ = M′} {V} M⇓ V⇓ T′⇓)
    with ⇓-adequate ρ~σ M⇓
  ... | N′ , M⟶ , (σ′ , ρ′~σ′ , refl)
    with ⇓-adequate-val ρ~σ V⇓
  ... | W≈V
    with ⇓-adequate (~-ext ρ′~σ′ W≈V) T′⇓ | β {M = M′ ⦅ exts σ′ ⦆c} {V = V ⦅ σ ⦆v}
  ... | N , T′⟶* , T≈N                    | step
    rewrite sub-sub (exts σ′) (V ⦅ σ ⦆v • id) M′
          | sym (subst-zero-exts-cons σ′ (V ⦅ σ ⦆v))
          | sym (sub-sub (exts σ′) (subst-zero (V ⦅ σ ⦆v)) M′) =
    N ,
    ⟶*-trans (⟶*-app-compatible M⟶) (step ⟶⟨ T′⟶* ⟩ ) ,
    T≈N
  ⇓-adequate ρ~σ (evalForce V⇓ M⇓)
    with ⇓-adequate-val ρ~σ V⇓
  ... | σ′ , ρ′~σ′ , eq
    with ⇓-adequate ρ′~σ′ M⇓
  ... | N , M⟶* , T≈N
    rewrite eq =
    N , (stepForceThunk ⟶⟨ M⟶* ⟩) , T≈N
  ⇓-adequate {σ = σ} ρ~σ (evalLetin {N = N} M⇓ N⇓)
    with ⇓-adequate ρ~σ M⇓
  ... | retV , M⟶ , W≈V
    with retV in eq
  ... | return V
    with ⇓-adequate (~-ext ρ~σ W≈V) N⇓
  ... | N′ , N⟶ , T≈N′
    rewrite sym (subst-zero-exts-cons σ V)
          | sym (sub-sub (exts σ) (subst-zero V) N) =
    N′ , ⟶*-trans (⟶*-letin-compatible M⟶) (βLetIn ⟶⟨ N⟶ ⟩)  , T≈N′

adequacy : ∅ᵨ ⊢c M ⇓ T
           ----------------------
         → ∃[ N ] M ⟶* N × T ≈c N
adequacy {M = M} M⇓
  with ⇓-adequate {σ = id} (λ ()) M⇓
... | lemma
  rewrite sub-id M                   = lemma
