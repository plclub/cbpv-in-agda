import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open Eq using (_≡_; refl; sym; subst)

open import CBPV.Effects.Terms
open import Effects

module CBPV.Effects.Adequacy (E : Effect) where

open import CBPV.Effects.Semantics E
open import CBPV.Effects.SmallStep E
open import CBPV.Effects.Substitution E

open Effect E
open Effects.Properties E

mutual
  _~_ : ∀ {n : ℕ} → Env n → Sub zero n → Set
  _~_ {n} ρ σ = ∀ (m : Fin n) → ρ m ≈v σ m

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
  clos⦅ ρ ,⟨ M₁ , M₂ ⟩⦆ ≈c N = ∃[ σ ] ρ ~ σ × N ≡ ⟨ M₁ , M₂ ⟩ ⦅ σ ⦆c
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
             → ρ ⊢c M ⇓ T # φ
             → ∃[ N ] ∃[ φ′ ] M ⦅ σ ⦆c ⟶* N # φ′ × T ≈c N × φ′ ≤ φ
  ⇓-adequate {σ = σ} {M = M} ρ~σ evalAbs =
    M ⦅ σ ⦆c , pure , M ⦅ σ ⦆c ∎ , (σ , ρ~σ , refl) , ≤-refl
  ⇓-adequate {σ = σ} ρ~σ (evalRet {V = V} V⇓) =
    return V ⦅ σ ⦆v , pure , (return V ⦅ σ ⦆v) ∎ , ⇓-adequate-val ρ~σ V⇓ , ≤-refl
  ⇓-adequate {σ = σ} ρ~σ (evalSeq {V = V} V⇓ M⇓)
    with ⇓-adequate-val ρ~σ V⇓  | ⇓-adequate ρ~σ M⇓
  ...  | unit≈V                 | N , φ′ , M⟶ , T≈N , φ′≤φ
    with V ⦅ σ ⦆v in eq
  ... | unit =
    N , φ′ , (βSeq ⟶⟨ M⟶ ⟩ ≡→≤ +-pure-idˡ) , T≈N , φ′≤φ
  ⇓-adequate {σ = σ} ρ~σ (evalApp {M′ = M′} {V = V} M⇓ V⇓ T′⇓)
    with ⇓-adequate ρ~σ M⇓
  ... | N′ , φ₁′ , M⟶ , (σ′ , ρ′~σ′ , refl) , φ₁′≤φ₁
    with ⇓-adequate-val ρ~σ V⇓
  ... | W≈V
    with ⇓-adequate (~-ext ρ′~σ′ W≈V) T′⇓ | β {M = M′ ⦅ exts σ′ ⦆c} {V = V ⦅ σ ⦆v}
  ... | N , φ₂′ , T′⟶* , T≈N , φ₂′≤φ₂     | step
    rewrite sub-sub (exts σ′) (V ⦅ σ ⦆v • id) M′
          | sym (subst-zero-exts-cons σ′ (V ⦅ σ ⦆v))
          | sym (sub-sub (exts σ′) (subst-zero (V ⦅ σ ⦆v)) M′) =
    N ,
    φ₁′ + φ₂′ ,
    ⟶*-trans (⟶*-app-compatible M⟶) (step ⟶⟨ T′⟶* ⟩ ≡→≤ +-pure-idˡ) ,
    T≈N ,
    ≤-trans (≤-+-compatibleʳ φ₁′≤φ₁) (≤-+-compatibleˡ φ₂′≤φ₂)
  ⇓-adequate ρ~σ (evalForce V⇓ M⇓)
    with ⇓-adequate-val ρ~σ V⇓
  ... | σ′ , ρ′~σ′ , eq
    with ⇓-adequate ρ′~σ′ M⇓
  ... | N , φ′ , M⟶* , T≈N , φ′≤φ
    rewrite eq =
    N , φ′ , (βforceThunk ⟶⟨ M⟶* ⟩ ≡→≤ +-pure-idˡ) , T≈N , φ′≤φ
  ⇓-adequate {σ = σ} ρ~σ (evalLetin {N = N} M⇓ N⇓)
    with ⇓-adequate ρ~σ M⇓
  ... | retV , φ₁′ , M⟶ , W≈V , φ₁′≤φ₁
    with retV in eq
  ... | return V
    with ⇓-adequate (~-ext ρ~σ W≈V) N⇓
  ... | N′ , φ₂′ , N⟶ , T≈N′ , φ₂′≤φ₂
    rewrite sym (subst-zero-exts-cons σ V)
          | sym (sub-sub (exts σ) (subst-zero V) N) =
    N′ ,
    φ₁′ + φ₂′ ,
    ⟶*-trans (⟶*-letin-compatible M⟶) (βletin ⟶⟨ N⟶ ⟩ ≡→≤ +-pure-idˡ) ,
    T≈N′ ,
    ≤-trans (≤-+-compatibleʳ φ₁′≤φ₁) (≤-+-compatibleˡ φ₂′≤φ₂)
  ⇓-adequate {σ = σ} ρ~σ evalTick =
    (return unit) ⦅ σ ⦆c ,
    tock ,
    (βtick ⟶⟨ (return unit)  ∎ ⟩ ≡→≤ +-pure-idʳ) ,
    tt ,
    ≤-refl
  ⇓-adequate {σ = σ} ρ~σ (evalSplit {V = V} {M = M} V⇓ M⇓)
    with V ⦅ σ ⦆v in eq | ⇓-adequate-val ρ~σ V⇓
  ...  | ⟨ V₁ , V₂ ⟩   | W₁≈V₁ , W₂≈V₂
    with ⇓-adequate (~-ext (~-ext ρ~σ W₁≈V₁) W₂≈V₂) M⇓
  ...  | N , φ′ , M⟶ , T≈N , φ′≤φ =
    N ,
    φ′ ,
    (βsplit ⟶⟨ subst (_⟶* N # φ′) subst-lemma M⟶ ⟩ ≡→≤ +-pure-idˡ) ,
    T≈N ,
    φ′≤φ
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
  ...  | N , φ′ , M₁⟶ , T≈N , φ′≤φ
    rewrite sym (subst-zero-exts-cons σ V)
          | sym (sub-sub (exts σ) (subst-zero V) M₁) =
    N , φ′ , (βcaseInl ⟶⟨ M₁⟶ ⟩ ≡→≤ +-pure-idˡ) , T≈N , φ′≤φ
  ⇓-adequate {σ = σ} ρ~σ (evalCaseInr {V = V} {M₂ = M₂} V⇓ M₂⇓)
    with V ⦅ σ ⦆v in eq | ⇓-adequate-val ρ~σ V⇓
  ...  | inr V         | W≈V
    with ⇓-adequate (~-ext ρ~σ W≈V) M₂⇓
  ...  | N , φ′ , M₂⟶ , T≈N , φ′≤φ
    rewrite sym (subst-zero-exts-cons σ V)
          | sym (sub-sub (exts σ) (subst-zero V) M₂) =
    N , φ′ , (βcaseInr ⟶⟨ M₂⟶ ⟩ ≡→≤ +-pure-idˡ) , T≈N , φ′≤φ
  ⇓-adequate {σ = σ} {M = M} ρ~σ evalCpair =
    M ⦅ σ ⦆c , pure , M ⦅ σ ⦆c ∎ , (σ , ρ~σ , refl) , ≤-refl
  ⇓-adequate ρ~σ (evalProjl M⇓ M₁⇓)
    with ⇓-adequate ρ~σ M⇓
  ...  | N′ , φ₁′ , M⟶ , (σ′ , ρ′~σ′ , eq) , φ₁′≤φ₁
    with ⇓-adequate ρ′~σ′ M₁⇓
  ...  | N , φ₂′ , M₁⟶ , T≈N , φ₂′≤φ₂
    rewrite eq =
    N ,
    φ₁′ + φ₂′ ,
    ⟶*-trans (⟶*-projl-compatible M⟶) (βprojl ⟶⟨ M₁⟶ ⟩ ≡→≤ +-pure-idˡ) ,
    T≈N ,
    ≤-trans (≤-+-compatibleˡ φ₂′≤φ₂) (≤-+-compatibleʳ φ₁′≤φ₁)
  ⇓-adequate ρ~σ (evalProjr M⇓ M₂⇓)
    with ⇓-adequate ρ~σ M⇓
  ...  | N′ , φ₁′ , M⟶ , (σ′ , ρ′~σ′ , eq) , φ₁′≤φ₁
    with ⇓-adequate ρ′~σ′ M₂⇓
  ...  | N , φ₂′ , M₂⟶ , T≈N , φ₂′≤φ₂
    rewrite eq =
    N ,
    φ₁′ + φ₂′ ,
    ⟶*-trans (⟶*-projr-compatible M⟶) (βprojr ⟶⟨ M₂⟶ ⟩ ≡→≤ +-pure-idˡ) ,
    T≈N ,
    ≤-trans (≤-+-compatibleˡ φ₂′≤φ₂) (≤-+-compatibleʳ φ₁′≤φ₁)

adequacy : ∅ᵨ ⊢c M ⇓ T # φ
           --------------------------------------------
         → ∃[ N ] ∃[ φ′ ] M ⟶* N # φ′ × T ≈c N × φ′ ≤ φ
adequacy {M = M} M⇓T with ⇓-adequate {σ = id} (λ ()) M⇓T
...                     | lemma
                     rewrite sub-id M                     = lemma
