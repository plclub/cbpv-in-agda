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
  _~_ : ∀ {n : ℕ} → Env n → Sub zero n → Set
  _~_ {n} ρ σ = ∀ (m : Fin n) → ρ m ≈v σ m

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

~-ext : ∀ {n : ℕ} {ρ : Env n} {σ : Sub zero n} {W : ClosVal} {V : Val zero}
      → ρ ~ σ
      → W ≈v V
      → ρ ∷ᵨ W ~ V • σ
~-ext _ W≈V zero = W≈V
~-ext ρ~σ _ (suc m) = ρ~σ m

mutual
  ⇓v-adequate : ∀ {n : ℕ} {V : Val n} {W : ClosVal} {ρ : Env n} {σ : Sub zero n}
           → ρ ~ σ
           → ρ ∣ V ⇓v W
           → W ≈v V ⦅ σ ⦆v
  ⇓v-adequate ρ~σ (evalVar {m = m}) = ρ~σ m
  ⇓v-adequate ρ~σ evalUnit = tt
  ⇓v-adequate {σ = σ} ρ~σ evalThunk = σ , ρ~σ , refl

  ⇓c-adequate : ∀ {n : ℕ} {M : Comp n} {T : ClosTerminal} {ρ : Env n} {σ : Sub zero n}
        → ρ ~ σ
        → ρ ∣ M ⇓c T
        → ∃[ N ] M ⦅ σ ⦆c ⟶* N × T ≈c N
  ⇓c-adequate {M = M} {σ = σ} ρ~σ evalAbs =
    M ⦅ σ ⦆c , M ⦅ σ ⦆c ∎ , σ , ρ~σ , refl
  ⇓c-adequate {σ = σ} ρ~σ (evalRet {V = V} V⇓W) =
    M , M ∎ , ⇓v-adequate ρ~σ V⇓W where M = return V ⦅ σ ⦆v
  ⇓c-adequate {σ = σ} ρ~σ (evalSeq {V = V} V⇓ M⇓T)
    with ⇓v-adequate ρ~σ V⇓ | ⇓c-adequate ρ~σ M⇓T
  ...  | unit≈V          | N , M⟶N , T≈N
    with V ⦅ σ ⦆v in eq
  ... | unit =
    N , (βSeq ⟶⟨ M⟶N ⟩) , T≈N
  ⇓c-adequate {σ = σ} ρ~σ (evalApp {M′ = M′} {V} M⇓ V⇓ T′⇓)
    with ⇓c-adequate ρ~σ M⇓
  ... | N′ , M⟶N′ , (σ′ , ρ′~σ′ , refl)
    with ⇓v-adequate ρ~σ V⇓
  ... | W≈V
    with ⇓c-adequate (~-ext ρ′~σ′ W≈V) T′⇓ | β {M = M′ ⦅ exts σ′ ⦆c} {V = V ⦅ σ ⦆v}
  ... | N , T′⟶*N , T≈N                 | β-M′·V
    rewrite sub-sub (exts σ′) (V ⦅ σ ⦆v • id) M′
          | sym (subst-zero-exts-cons σ′ (V ⦅ σ ⦆v))
          | sym (sub-sub (exts σ′) (subst-zero (V ⦅ σ ⦆v)) M′) =
    N ,
    ⟶*-trans (⟶*-app-compatible M⟶N′) (β-M′·V ⟶⟨ T′⟶*N ⟩) ,
    T≈N
  ⇓c-adequate ρ~σ (evalForce V⇓⟪M⟫ M⇓T)
    with ⇓v-adequate ρ~σ V⇓⟪M⟫
  ... | σ′ , ρ′~σ′ , V≡⟪M⟫
    with ⇓c-adequate ρ′~σ′ M⇓T
  ... | N , M⟶*N , T≈N
    rewrite V≡⟪M⟫ =
    N , (stepForceThunk ⟶⟨ M⟶*N ⟩) , T≈N
  ⇓c-adequate {σ = σ} ρ~σ (evalLetin {N = N} M⇓W N⇓T)
    with ⇓c-adequate ρ~σ M⇓W
  ... | retV , M⟶V , W≈V
    with retV in eq
  ... | return V
    with ⇓c-adequate (~-ext ρ~σ W≈V) N⇓T
  ... | N′ , N⟶N′ , T≈N′
    rewrite sym (subst-zero-exts-cons σ V)
          | sym (sub-sub (exts σ) (subst-zero V) N) =
    N′ , ⟶*-trans (⟶*-letin-compatible M⟶V) (βLetIn ⟶⟨ N⟶N′ ⟩)  , T≈N′

adequacy : ∀ {n : ℕ} {M : Comp zero} {T : ClosTerminal}
         → ∅ᵨ ∣ M ⇓c T
           ----------------------
         → ∃[ N ] M ⟶* N × T ≈c N
adequacy {M = M} M⇓T
  with ⇓c-adequate {σ = id} (λ ()) M⇓T
... | N , M⟶N , T≈N
  rewrite sub-id M =
  N , M⟶N , T≈N