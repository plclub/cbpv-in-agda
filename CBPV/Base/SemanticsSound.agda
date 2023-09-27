import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open Eq using (_≡_; refl; sym)

open import CBPV.Base.Semantics
open import CBPV.Base.SmallStep
open import CBPV.Base.Substitution
open import CBPV.Base.Terms

module CBPV.Base.SemanticsSound where

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
      → ρ ∷ᵨ W ~ σ • V
~-ext _ W≈V zero = W≈V
~-ext ρ~σ _ (suc m) = ρ~σ m

mutual
  ⇓v-sound : ∀ {n : ℕ} {V : Val n} {W : ClosVal} {ρ : Env n} {σ : Sub zero n}
           → ρ ~ σ
           → ρ ∣ V ⇓v W
           → W ≈v V ⦅ σ ⦆v
  ⇓v-sound ρ~σ (evalVar {m = m}) = ρ~σ m
  ⇓v-sound ρ~σ evalUnit = tt
  ⇓v-sound {σ = σ} ρ~σ evalThunk = σ , ρ~σ , refl

  ⇓c-sound : ∀ {n : ℕ} {M : Comp n} {T : ClosTerminal} {ρ : Env n} {σ : Sub zero n}
        → ρ ~ σ
        → ρ ∣ M ⇓c T
        → ∃[ N ] M ⦅ σ ⦆c ⟶* N × T ≈c N
  ⇓c-sound {M = M} {σ = σ} ρ~σ evalAbs =
    M ⦅ σ ⦆c , M ⦅ σ ⦆c ∎ , σ , ρ~σ , refl
  ⇓c-sound {σ = σ} ρ~σ (evalRet {V = V} V⇓W) =
    M , M ∎ , ⇓v-sound ρ~σ V⇓W where M = return V ⦅ σ ⦆v
  ⇓c-sound {σ = σ} ρ~σ (evalSeq {V = V} V⇓ M⇓T)
    with ⇓v-sound ρ~σ V⇓ | ⇓c-sound ρ~σ M⇓T
  ...  | unit≈V          | N , M⟶N , T≈N
    with V ⦅ σ ⦆v in eq
  ... | unit =
    N , (stepSeq ⟶⟨ M⟶N ⟩) , T≈N
  ⇓c-sound {σ = σ} ρ~σ (evalApp {M′ = M′} {V} M⇓ V⇓ T′⇓)
    with ⇓c-sound ρ~σ M⇓
  ... | N′ , M⟶N′ , (σ′ , ρ′~σ′ , refl)
    with ⇓v-sound ρ~σ V⇓
  ... | W≈V
    with ⇓c-sound (~-ext ρ′~σ′ W≈V) T′⇓ | β {M = M′ ⦅ exts σ′ ⦆c} {V = V ⦅ σ ⦆v}
  ... | N , T′⟶*N , T≈N                 | β-M′·V
    rewrite sub-sub {σ  = exts σ′} {id • V ⦅ σ ⦆v} {M′}
          | sym (subst-zero-exts-cons {σ = σ′} {V = V ⦅ σ ⦆v})
          | sym (sub-sub {σ = exts σ′} {subst-zero (V ⦅ σ ⦆v)} {M′}) =
    N ,
    ⟶*-trans (⟶*-app-compatible M⟶N′) (β-M′·V ⟶⟨ T′⟶*N ⟩) ,
    T≈N
  ⇓c-sound ρ~σ (evalForce V⇓⟪M⟫ M⇓T)
    with ⇓v-sound ρ~σ V⇓⟪M⟫
  ... | σ′ , ρ′~σ′ , V≡⟪M⟫
    with ⇓c-sound ρ′~σ′ M⇓T
  ... | N , M⟶*N , T≈N
    rewrite V≡⟪M⟫ =
    N , (stepForceThunk ⟶⟨ M⟶*N ⟩) , T≈N
  ⇓c-sound {σ = σ} ρ~σ (evalLetin {N = N} M⇓W N⇓T)
    with ⇓c-sound ρ~σ M⇓W
  ... | retV , M⟶V , W≈V
    with retV in eq
  ... | return V
    with ⇓c-sound (~-ext ρ~σ W≈V) N⇓T
  ... | N′ , N⟶N′ , T≈N′
    rewrite sym (subst-zero-exts-cons {σ = σ} {V})
          | sym (sub-sub {σ = exts σ} {subst-zero V} {N}) =
    N′ , ⟶*-trans (⟶*-letin-compatible M⟶V) (βLetIn ⟶⟨ N⟶N′ ⟩)  , T≈N′

sound : ∀ {n : ℕ} {M : Comp zero} {T : ClosTerminal}
      → ∅ᵨ ∣ M ⇓c T
        ----------------------
      → ∃[ N ] M ⟶* N × T ≈c N
sound {M = M} M⇓T
  with ⇓c-sound {σ = id} (λ ()) M⇓T
... | N , M⟶N , T≈N
  rewrite sub-id {M = M} =
  N , M⟶N , T≈N
