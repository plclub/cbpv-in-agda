import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open Eq using (_≡_; refl; sym; subst; trans)

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
  ⟨ W₁ , W₂ ⟩ ≈v ⟨ V₁ , V₂ ⟩ = W₁ ≈v V₁ × W₂ ≈v V₂
  inl W ≈v inl V = W ≈v V
  inr W ≈v inr V = W ≈v V
  _ ≈v _ = ⊥

  _≈c_ : ClosTerminal → Comp zero → Set
  (return V₁) ≈c (return V₂) = V₁ ≈v V₂
  clos⦅ ρ ,ƛ M ⦆ ≈c N = ∃[ σ ] ρ ~ σ × N ≡ (ƛ M) ⦅ σ ⦆c
  clos⦅ ρ ,⟨ M₁ , M₂ ⟩⦆ ≈c N =
    ∃[ σ ] ρ ~ σ × N ≡ ⟨ M₁ , M₂ ⟩ ⦅ σ ⦆c
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
  ⇓-adequate-val ρ~σ (evalPair V₁⇓ V₂⇓) =
    ⇓-adequate-val ρ~σ V₁⇓ , ⇓-adequate-val ρ~σ V₂⇓
  ⇓-adequate-val ρ~σ (evalInl V⇓) = ⇓-adequate-val ρ~σ V⇓
  ⇓-adequate-val ρ~σ (evalInr V⇓) = ⇓-adequate-val ρ~σ V⇓

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
    N , (βseq ⟶⟨ M⟶ ⟩) , T≈N
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
    N , (βforceThunk ⟶⟨ M⟶* ⟩) , T≈N
  ⇓-adequate {σ = σ} ρ~σ (evalLetin {N = N} M⇓ N⇓)
    with ⇓-adequate ρ~σ M⇓
  ... | retV , M⟶ , W≈V
    with retV in eq
  ... | return V
    with ⇓-adequate (~-ext ρ~σ W≈V) N⇓
  ... | N′ , N⟶ , T≈N′
    rewrite sym (subst-zero-exts-cons σ V)
          | sym (sub-sub (exts σ) (subst-zero V) N) =
    N′ , ⟶*-trans (⟶*-letin-compatible M⟶) (βletin ⟶⟨ N⟶ ⟩)  , T≈N′
  ⇓-adequate {σ = σ} ρ~σ (evalSplit {V = V} {M = M} V⇓ M⇓)
    with V ⦅ σ ⦆v in eq | ⇓-adequate-val ρ~σ V⇓ 
  ...  | ⟨ V₁ , V₂ ⟩   | W₁≈V₁ , W₂≈V₂
    with ⇓-adequate (~-ext (~-ext ρ~σ W₁≈V₁) W₂≈V₂) M⇓
  ...  | N , M⟶ , T≈N =
    N ,
    (βsplit ⟶⟨ subst (_⟶* N) subst-lemma M⟶ ⟩) ,
    T≈N
    where
      subst-lemma : M ⦅ V₂ • V₁ • σ ⦆c ≡ (M ⦅ exts (exts σ) ⦆c) ⦅ V₂ • V₁ • id ⦆c
      subst-lemma
        rewrite sub-sub (exts (exts σ)) (V₂ • V₁ • id) M
              | exts-seq-cons (exts σ) V₂ (V₁ • id)
              | exts-seq-cons σ V₁ id
              | sub-idR {σ = σ}                          = refl
  ⇓-adequate {σ = σ} ρ~σ (evalCaseInl {V = V} {M₁ = M₁} V⇓ M₁⇓)
    with V ⦅ σ ⦆v in eq | ⇓-adequate-val ρ~σ V⇓
  ...  | inl V         | W≈V
    with ⇓-adequate (~-ext ρ~σ W≈V) M₁⇓
  ...  | N , M₁⟶ , T≈N
    rewrite sym (subst-zero-exts-cons σ V)
          | sym (sub-sub (exts σ) (subst-zero V) M₁) =
    N , (βcaseInl ⟶⟨ M₁⟶ ⟩) , T≈N
  ⇓-adequate {σ = σ} ρ~σ (evalCaseInr {V = V} {M₂ = M₂} V⇓ M₂⇓)
    with V ⦅ σ ⦆v in eq | ⇓-adequate-val ρ~σ V⇓
  ...  | inr V         | W≈V
    with ⇓-adequate (~-ext ρ~σ W≈V) M₂⇓
  ...  | N , M₂⟶ , T≈N
    rewrite sym (subst-zero-exts-cons σ V)
          | sym (sub-sub (exts σ) (subst-zero V) M₂) =
    N , (βcaseInr ⟶⟨ M₂⟶ ⟩) , T≈N
  ⇓-adequate {σ = σ} ρ~σ (evalCpair {M₁ = M₁} {M₂ = M₂}) =
    ⟨ M₁ ⦅ σ ⦆c , M₂ ⦅ σ ⦆c ⟩ ,
    ⟨ M₁ ⦅ σ ⦆c , M₂ ⦅ σ ⦆c ⟩ ∎ ,
    σ ,
    ρ~σ ,
    refl
  ⇓-adequate ρ~σ (evalProjl M⇓ M₁⇓)
    with ⇓-adequate ρ~σ M⇓
  ...  | _ , M⟶ , (σ′ , ρ′~σ′ , eq)
    with ⇓-adequate ρ′~σ′ M₁⇓
  ...  | N , M₁⟶ , T≈N
    rewrite eq =
    N , ⟶*-trans (⟶*-projl-compatible M⟶) (βprojl ⟶⟨ M₁⟶ ⟩) , T≈N
  ⇓-adequate ρ~σ (evalProjr M⇓ M₂⇓)
    with ⇓-adequate ρ~σ M⇓
  ...  | _ , M⟶ , (σ′ , ρ′~σ′ , eq)
    with ⇓-adequate ρ′~σ′ M₂⇓
  ...  | N , M₂⟶ , T≈N
    rewrite eq =
    N , ⟶*-trans (⟶*-projr-compatible M⟶) (βprojr ⟶⟨ M₂⟶ ⟩) , T≈N

adequacy : ∅ᵨ ⊢c M ⇓ T
           ----------------------
         → ∃[ N ] M ⟶* N × T ≈c N
adequacy {M = M} M⇓
  with ⇓-adequate {σ = id} (λ ()) M⇓
... | lemma
  rewrite sub-id M                   = lemma
