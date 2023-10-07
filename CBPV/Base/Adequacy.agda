import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (∃-syntax; _×_; _,_; Σ-syntax)
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

≈→normal : T ≈c N → Normal N
≈→normal {return _} {return _} T≈N = normalReturn
≈→normal {clos⦅ _ ,ƛ _ ⦆} (_ , _ , eq) rewrite eq = normalAbs
≈→normal {clos⦅ _ ,⟨ _ , _ ⟩⦆} (_ , _ , eq) rewrite eq = normalCpair

~-ext : ρ ~ σ → W ≈v V → ρ ∷ᵨ W ~ V • σ
~-ext _ W≈V zero = W≈V
~-ext ρ~σ _ (suc m) = ρ~σ m

mutual
  ⇓-val-≈ : ρ ~ σ
                 → ρ ⊢v V ⇓ W
                 → W ≈v V ⦅ σ ⦆v
  ⇓-val-≈ ρ~σ (evalVar {m = m}) = ρ~σ m
  ⇓-val-≈ ρ~σ evalUnit = tt
  ⇓-val-≈ {σ = σ} ρ~σ evalThunk = σ , ρ~σ , refl
  ⇓-val-≈ ρ~σ (evalPair V₁⇓ V₂⇓) =
    ⇓-val-≈ ρ~σ V₁⇓ , ⇓-val-≈ ρ~σ V₂⇓
  ⇓-val-≈ ρ~σ (evalInl V⇓) = ⇓-val-≈ ρ~σ V⇓
  ⇓-val-≈ ρ~σ (evalInr V⇓) = ⇓-val-≈ ρ~σ V⇓

  ⇓→⟶* : ρ ~ σ
             → ρ ⊢c M ⇓ T
               -----------------------------
             → ∃[ N ] M ⦅ σ ⦆c ⟶* N × T ≈c N
  ⇓→⟶* {σ = σ} {M = M} ρ~σ evalAbs =
    M ⦅ σ ⦆c , M ⦅ σ ⦆c ∎ , σ , ρ~σ , refl
  ⇓→⟶* {σ = σ} ρ~σ (evalRet {V = V} V⇓) =
    return V ⦅ σ ⦆v , (return V ⦅ σ ⦆v) ∎ , ⇓-val-≈ ρ~σ V⇓
  ⇓→⟶* {σ = σ} ρ~σ (evalSeq {V = V} V⇓ M⇓)
    with ⇓-val-≈ ρ~σ V⇓ | ⇓→⟶* ρ~σ M⇓
  ...  | unit≈V                | N , M⟶ , T≈N
    with V ⦅ σ ⦆v in eq
  ... | unit =
    N , (βseq ⟶⟨ M⟶ ⟩) , T≈N
  ⇓→⟶* {σ = σ} ρ~σ (evalApp {M′ = M′} {V} M⇓ V⇓ T′⇓)
    with ⇓→⟶* ρ~σ M⇓
  ... | N′ , M⟶ , (σ′ , ρ′~σ′ , refl)
    with ⇓-val-≈ ρ~σ V⇓
  ... | W≈V
    with ⇓→⟶* (~-ext ρ′~σ′ W≈V) T′⇓ | β {M = M′ ⦅ exts σ′ ⦆c} {V = V ⦅ σ ⦆v}
  ... | N , T′⟶* , T≈N                    | step
    rewrite sub-sub (exts σ′) (V ⦅ σ ⦆v • id) M′
          | sym (subst-zero-exts-cons σ′ (V ⦅ σ ⦆v))
          | sym (sub-sub (exts σ′) (subst-zero (V ⦅ σ ⦆v)) M′) =
    N ,
    ⟶*-trans (⟶*-app-compatible M⟶) (step ⟶⟨ T′⟶* ⟩ ) ,
    T≈N
  ⇓→⟶* ρ~σ (evalForce V⇓ M⇓)
    with ⇓-val-≈ ρ~σ V⇓
  ... | σ′ , ρ′~σ′ , eq
    with ⇓→⟶* ρ′~σ′ M⇓
  ... | N , M⟶* , T≈N
    rewrite eq =
    N , (βforceThunk ⟶⟨ M⟶* ⟩) , T≈N
  ⇓→⟶* {σ = σ} ρ~σ (evalLetin {N = N} M⇓ N⇓)
    with ⇓→⟶* ρ~σ M⇓
  ... | retV , M⟶ , W≈V
    with retV in eq
  ... | return V
    with ⇓→⟶* (~-ext ρ~σ W≈V) N⇓
  ... | N′ , N⟶ , T≈N′
    rewrite sym (subst-zero-exts-cons σ V)
          | sym (sub-sub (exts σ) (subst-zero V) N) =
    N′ , ⟶*-trans (⟶*-letin-compatible M⟶) (βletin ⟶⟨ N⟶ ⟩)  , T≈N′
  ⇓→⟶* {σ = σ} ρ~σ (evalSplit {V = V} {M = M} V⇓ M⇓)
    with V ⦅ σ ⦆v in eq | ⇓-val-≈ ρ~σ V⇓
  ...  | ⟨ V₁ , V₂ ⟩   | W₁≈V₁ , W₂≈V₂
    with ⇓→⟶* (~-ext (~-ext ρ~σ W₁≈V₁) W₂≈V₂) M⇓
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
  ⇓→⟶* {σ = σ} ρ~σ (evalCaseInl {V = V} {M₁ = M₁} V⇓ M₁⇓)
    with V ⦅ σ ⦆v in eq | ⇓-val-≈ ρ~σ V⇓
  ...  | inl V         | W≈V
    with ⇓→⟶* (~-ext ρ~σ W≈V) M₁⇓
  ...  | N , M₁⟶ , T≈N
    rewrite sym (subst-zero-exts-cons σ V)
          | sym (sub-sub (exts σ) (subst-zero V) M₁) =
    N , (βcaseInl ⟶⟨ M₁⟶ ⟩) , T≈N
  ⇓→⟶* {σ = σ} ρ~σ (evalCaseInr {V = V} {M₂ = M₂} V⇓ M₂⇓)
    with V ⦅ σ ⦆v in eq | ⇓-val-≈ ρ~σ V⇓
  ...  | inr V         | W≈V
    with ⇓→⟶* (~-ext ρ~σ W≈V) M₂⇓
  ...  | N , M₂⟶ , T≈N
    rewrite sym (subst-zero-exts-cons σ V)
          | sym (sub-sub (exts σ) (subst-zero V) M₂) =
    N , (βcaseInr ⟶⟨ M₂⟶ ⟩) , T≈N
  ⇓→⟶* {σ = σ} ρ~σ (evalCpair {M₁ = M₁} {M₂ = M₂}) =
    ⟨ M₁ ⦅ σ ⦆c , M₂ ⦅ σ ⦆c ⟩ ,
    ⟨ M₁ ⦅ σ ⦆c , M₂ ⦅ σ ⦆c ⟩ ∎ ,
    σ ,
    ρ~σ ,
    refl
  ⇓→⟶* ρ~σ (evalProjl M⇓ M₁⇓)
    with ⇓→⟶* ρ~σ M⇓
  ...  | _ , M⟶ , (σ′ , ρ′~σ′ , eq)
    with ⇓→⟶* ρ′~σ′ M₁⇓
  ...  | N , M₁⟶ , T≈N
    rewrite eq =
    N , ⟶*-trans (⟶*-projl-compatible M⟶) (βprojl ⟶⟨ M₁⟶ ⟩) , T≈N
  ⇓→⟶* ρ~σ (evalProjr M⇓ M₂⇓)
    with ⇓→⟶* ρ~σ M⇓
  ...  | _ , M⟶ , (σ′ , ρ′~σ′ , eq)
    with ⇓→⟶* ρ′~σ′ M₂⇓
  ...  | N , M₂⟶ , T≈N
    rewrite eq =
    N , ⟶*-trans (⟶*-projr-compatible M⟶) (βprojr ⟶⟨ M₂⟶ ⟩) , T≈N

my-lem : ρ ⊢v V ⦅ σ ⦆v ⇓ W
       → ∃[ ρ′ ] (∀ m → ρ ⊢v σ m ⇓ ρ′ m) × ρ′ ⊢v V ⇓ W
my-lem = {!!}

my-lemma : ∀ {σ : Sub n n′}
         → ρ ⊢c M ⦅ σ ⦆c ⇓ T
         → ∃[ ρ′ ] (∀ m → ρ ⊢v σ m ⇓ ρ′ m) × ρ′ ⊢c M ⇓ T
my-lemma {M = ƛ M} evalAbs = {!!}
my-lemma {M = M · x} M⇓ = {!!}
my-lemma {M = x » M} M⇓ = {!!}
my-lemma {M = x !} M⇓ = {!!}
my-lemma {M = return x} M⇓ = {!!}
my-lemma {M = $⟵ M ⋯ M₁} M⇓ = {!!}
my-lemma {M = $≔ x ⋯ M} M⇓ = {!!}
my-lemma {ρ = ρ} {M = ⟨ M₁ , M₂ ⟩} {σ = σ} evalCpair =
  (λ m → {!ρ (σ m)!} ), {!!} , {!!}
my-lemma {ρ = ρ} {M = projl M} (evalProjl M⇓ M₁⇓)
  with my-lemma M⇓
... | fst , fst₁ , snd = fst , fst₁ , evalProjl snd M₁⇓
my-lemma {M = projr M} M⇓ = {!!}
my-lemma {M = case x inl⇒ M inr⇒ M₁} M⇓ = {!!}

_⇓⟨_⟩ : M ⟶ N → ρ ⊢c N ⇓ T → ρ ⊢c M ⇓ T
βforceThunk ⇓⟨ N⇓ ⟩ =
  evalForce evalThunk N⇓
β ⇓⟨ N⇓ ⟩ =
  evalApp evalAbs {!!} {!!}
βletin ⇓⟨ N⇓ ⟩ =
  evalLetin {!!} {!!}
βseq ⇓⟨ N⇓ ⟩ =
  evalSeq evalUnit N⇓
βsplit ⇓⟨ N⇓ ⟩ =
  evalSplit {!!} {!!}
βprojl ⇓⟨ N⇓ ⟩ =
  evalProjl evalCpair N⇓
βprojr ⇓⟨ N⇓ ⟩ =
  evalProjr evalCpair N⇓
βcaseInl ⇓⟨ N⇓ ⟩ =
  evalCaseInl {!!} {!!}
βcaseInr ⇓⟨ N⇓ ⟩ =
  evalCaseInr {!!} {!!}
stepApp M⟶ ⇓⟨ evalApp N⇓ V⇓ M′⇓ ⟩ =
  evalApp (M⟶ ⇓⟨ N⇓ ⟩) V⇓ M′⇓
stepLetin M⟶ ⇓⟨ evalLetin M⇓ N⇓ ⟩ =
  evalLetin (M⟶ ⇓⟨ M⇓ ⟩) N⇓
stepProjl M⟶ ⇓⟨ evalProjl M⇓ M₁⇓ ⟩ =
  evalProjl (M⟶ ⇓⟨ M⇓ ⟩) M₁⇓
stepProjr M⟶ ⇓⟨ evalProjr M⇓ M₂⇓ ⟩ =
  evalProjr (M⟶ ⇓⟨ M⇓ ⟩) M₂⇓

adequacy₁ : ∅ᵨ ⊢c M ⇓ T → ∃[ N ] M has-normal-form N × T ≈c N
adequacy₁ {M = M} {T = T} M⇓
  with ⇓→⟶* {σ = id} (λ ()) M⇓
... | N , M⟶*N , T≈N
  rewrite sub-id M =
  N , (M⟶*N , ≈→normal {T = T} T≈N) , T≈N

adequacy₂ : M has-normal-form N → ∅ᵨ ⊢c M ⇓ T × T ≈c N
adequacy₂ = {!!}
