import Axiom.Extensionality.Propositional as Ext
import Relation.Binary.PropositionalEquality as Eq
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)
open import Function using (_∘_)
open import Level using (0ℓ)
open Eq using (_≡_; refl; cong; cong₂; trans; sym)
open Eq.≡-Reasoning using (begin_; step-≡; _∎)
open Ext using (Extensionality)

open import CBPV.Base.Renaming
open import CBPV.Base.Terms
open import CBPV.Base.Types
open import CBPV.Base.SyntacticTyping

module CBPV.Base.Substitution where

postulate
  extensionality : Extensionality 0ℓ 0ℓ

Sub : ℕ → ℕ → Set
Sub n n′ = (m : Fin n′) → Val n

variable σ τ : Sub n n′

exts : ∀ {n n′ : ℕ} → Sub n n′ → Sub (suc n) (suc n′)
exts σ zero = # zero
exts σ (suc m) = (σ m) [ suc ]v

mutual
  _⦅_⦆v : ∀ {n n′ : ℕ}
          → Val n′
          → Sub n n′
           --------
          → Val n
  unit ⦅ _ ⦆v    = unit
  # m ⦅ σ ⦆v     = σ m
  ⟪ M ⟫ ⦅ σ ⦆v   = ⟪ M ⦅ σ ⦆c ⟫
  ⟨ V₁ , V₂ ⟩ ⦅ σ ⦆v = ⟨ V₁ ⦅ σ ⦆v , V₂ ⦅ σ ⦆v ⟩
  inl V ⦅ σ ⦆v = inl (V ⦅ σ ⦆v)
  inr V ⦅ σ ⦆v = inr (V ⦅ σ ⦆v)

  _⦅_⦆c : ∀ {n n′ : ℕ}
         → Comp n′
         → Sub n n′
           --------
         → Comp n
  (ƛ M) ⦅ σ ⦆c   = ƛ M ⦅ exts σ ⦆c
  (M · V) ⦅ σ ⦆c = M ⦅ σ ⦆c · V ⦅ σ ⦆v
  (V » M) ⦅ σ ⦆c = V ⦅ σ ⦆v » M ⦅ σ ⦆c
  (return V) ⦅ σ ⦆c = return V ⦅ σ ⦆v
  ($⟵ M ⋯ N) ⦅ σ ⦆c = $⟵ M ⦅ σ ⦆c ⋯ N ⦅ exts σ ⦆c
  (V !) ⦅ σ ⦆c = V ⦅ σ ⦆v !
  ($≔ V ⋯ M) ⦅ σ ⦆c = $≔ V ⦅ σ ⦆v ⋯ M ⦅ exts (exts σ) ⦆c
  ⟨ M₁ , M₂ ⟩ ⦅ σ ⦆c = ⟨ M₁ ⦅ σ ⦆c , M₂ ⦅ σ ⦆c ⟩
  projl M ⦅ σ ⦆c = projl (M ⦅ σ ⦆c)
  projr M ⦅ σ ⦆c = projr (M ⦅ σ ⦆c)
  (case V inl⇒ M₁ inr⇒ M₂) ⦅ σ ⦆c = case V ⦅ σ ⦆v inl⇒ M₁ ⦅ exts σ ⦆c inr⇒ M₂ ⦅ exts σ ⦆c

infix 8 _⦅_⦆v
infix 8 _⦅_⦆c

_•_ : ∀ {n m : ℕ} → Val n → Sub n m → Sub n (suc m)
(V • σ) zero = V
(V • σ) (suc m) = σ m

infixr 6 _•_

id : ∀ {n : ℕ} → Sub n n
id m = # m

subst-zero : ∀ {n} → Val n → Sub n (suc n)
subst-zero V zero = V
subst-zero V (suc m) = # m

_〔_〕 : ∀ {n : ℕ} → Comp (suc n) → Val n → Comp n
M 〔 V 〕 = M ⦅ subst-zero V ⦆c

_⨟_ : ∀ {n m p : ℕ} → Sub m n → Sub p m → Sub p n
(σ ⨟ τ) m = σ m ⦅ τ ⦆v

infixr 5 _⨟_

cong-exts : ∀ {n m : ℕ} {σ σ′ : Sub n m}
          → σ ≡ σ′
          → exts σ ≡ exts σ′
cong-exts {σ = σ} {σ′} ss = extensionality lemma where
  lemma : ∀ m → exts σ m ≡ exts σ′ m
  lemma zero = refl
  lemma (suc _) rewrite ss = refl

mutual
  cong-sub-val : ∀ {n m : ℕ} {σ σ′ : Sub n m} {V V′ : Val m}
               → σ ≡ σ′
               → V ≡ V′
               → V ⦅ σ ⦆v ≡ V′ ⦅ σ′ ⦆v
  cong-sub-val {V = # x} ss refl rewrite ss = refl
  cong-sub-val {V = unit} _ refl = refl
  cong-sub-val {V = ⟪ M ⟫} ss refl
    rewrite cong-sub {M = M} ss refl = refl
  cong-sub-val {V = ⟨ V₁ , V₂ ⟩} ss refl
    rewrite cong-sub-val {V = V₁} ss refl | cong-sub-val {V = V₂} ss refl = refl
  cong-sub-val {V = inl V} ss refl
    rewrite cong-sub-val {V = V} ss refl = refl
  cong-sub-val {V = inr V} ss refl
    rewrite cong-sub-val {V = V} ss refl = refl

  cong-sub : ∀ {n m : ℕ} {σ σ′ : Sub n m} {M M′ : Comp m}
           → σ ≡ σ′
           → M ≡ M′
           → M ⦅ σ ⦆c ≡ M′ ⦅ σ′ ⦆c
  cong-sub {σ = σ} {σ′} {ƛ M} ss refl
    rewrite cong-sub {M = M} (cong-exts ss) refl = refl
  cong-sub {M = M · V} ss refl
    rewrite cong-sub {M = M} ss refl | cong-sub-val {V = V} ss refl = refl
  cong-sub {M = V » M} ss refl
    rewrite cong-sub-val {V = V} ss refl | cong-sub {M = M} ss refl = refl
  cong-sub {M = V !} ss refl
    rewrite cong-sub-val {V = V} ss refl = refl
  cong-sub {M = return V} ss refl
    rewrite cong-sub-val {V = V} ss refl = refl
  cong-sub {M = $⟵ M ⋯ N} ss refl
    rewrite cong-sub {M = M} ss refl
          | cong-sub {M = N} (cong-exts ss) refl = refl
  cong-sub {M = $≔ V ⋯ M} ss refl
    rewrite cong-sub-val {V = V} ss refl
          | cong-sub {M = M} (cong-exts (cong-exts ss)) refl = refl
  cong-sub {M = ⟨ M₁ , M₂ ⟩} ss refl
    rewrite cong-sub {M = M₁} ss refl | cong-sub {M = M₂} ss refl = refl
  cong-sub {M = projl M} ss refl
    rewrite cong-sub {M = M} ss refl = refl
  cong-sub {M = projr M} ss refl
    rewrite cong-sub {M = M} ss refl = refl
  cong-sub {M = case V inl⇒ M₁ inr⇒ M₂} ss refl
    rewrite cong-sub-val {V = V} ss refl
          | cong-sub {M = M₁} (cong-exts ss) refl
          | cong-sub {M = M₂} (cong-exts ss) refl = refl

exts-ids : ∀ {n : ℕ} → exts (id {n}) ≡ id
exts-ids = extensionality lemma where
  lemma = λ where zero    → refl
                  (suc m) → refl

mutual
  sub-id-val : ∀ {n : ℕ} (V : Val n)
             → V ⦅ id ⦆v ≡ V
  sub-id-val (# x) = refl
  sub-id-val (unit) = refl
  sub-id-val (⟪ M ⟫) rewrite sub-id M = refl
  sub-id-val ⟨ V₁ , V₂ ⟩
    rewrite sub-id-val V₁ | sub-id-val V₂ = refl
  sub-id-val (inl V) rewrite sub-id-val V = refl
  sub-id-val (inr V) rewrite sub-id-val V = refl

  sub-id : ∀ {n : ℕ} (M : Comp n)
         → M ⦅ id ⦆c ≡ M
  sub-id (ƛ M)
    rewrite cong-sub {M = M} exts-ids refl | sub-id M = refl
  sub-id (M · V) rewrite sub-id-val V | sub-id M = refl
  sub-id (V » M) rewrite sub-id-val V | sub-id M = refl
  sub-id (V !) rewrite sub-id-val V = refl
  sub-id (return V) rewrite sub-id-val V = refl
  sub-id ($⟵ M ⋯ N)
    rewrite sub-id M | cong-sub {M = N} exts-ids refl | sub-id N = refl
  sub-id ($≔ V ⋯ M)
    rewrite sub-id-val V
          | cong-sub {M = M} (trans (cong exts exts-ids) (exts-ids)) refl
          | sub-id M                                                      = refl
  sub-id ⟨ M₁ , M₂ ⟩
    rewrite sub-id M₁ | sub-id M₂ = refl
  sub-id (projl M) rewrite sub-id M = refl
  sub-id (projr M) rewrite sub-id M = refl
  sub-id (case V inl⇒ M₁ inr⇒ M₂)
    rewrite sub-id-val V
          | cong-sub {M = M₁} exts-ids refl
          | sub-id M₁
          | cong-sub {M = M₂} exts-ids refl
          | sub-id M₂                       = refl

sub-idR : ∀ {n m : ℕ} {σ : Sub n m}
        → σ ⨟ id ≡ σ
sub-idR {σ = σ} = extensionality lemma where
  lemma : ∀ x → σ x ⦅ id ⦆v ≡ σ x
  lemma x rewrite sub-id-val (σ x) = refl

compose-ext : {n m p : ℕ} {ρ : Ren m n} {ω : Ren p m}
            → (ext ω) ∘ (ext ρ) ≡ ext (ω ∘ ρ)
compose-ext = extensionality lemma where
  lemma = λ where zero    → refl
                  (suc m) → refl

mutual
  compose-rename-val : ∀ {n m p : ℕ} (ρ : Ren m n) (ω : Ren p m) (V : Val n)
                     → V [ ρ ]v [ ω ]v ≡ V [ ω ∘ ρ ]v
  compose-rename-val _ _ (# x) = refl
  compose-rename-val _ _ unit = refl
  compose-rename-val ρ ω ⟪ M ⟫ rewrite compose-rename ρ ω M = refl
  compose-rename-val ρ ω ⟨ V₁ , V₂ ⟩
    rewrite compose-rename-val ρ ω V₁
          | compose-rename-val ρ ω V₂ = refl
  compose-rename-val ρ ω (inl V) rewrite compose-rename-val ρ ω V = refl
  compose-rename-val ρ ω (inr V) rewrite compose-rename-val ρ ω V = refl

  compose-rename : ∀ {n m p : ℕ} (ρ : Ren m n) (ω : Ren p m) (M : Comp n)
                 → M [ ρ ]c [ ω ]c ≡ M [ ω ∘ ρ ]c
  compose-rename ρ ω (ƛ M)
    rewrite compose-rename (ext ρ) (ext ω) M | compose-ext {ρ = ρ} {ω} = refl
  compose-rename ρ ω (M · V)
    rewrite compose-rename-val ρ ω V | compose-rename ρ ω M = refl
  compose-rename ρ ω (V » M)
    rewrite compose-rename-val ρ ω V | compose-rename ρ ω M = refl
  compose-rename ρ ω (V !) 
    rewrite compose-rename-val ρ ω V = refl
  compose-rename ρ ω (return V)
    rewrite compose-rename-val ρ ω V = refl
  compose-rename ρ ω ($⟵ M ⋯ N)
    rewrite compose-rename ρ ω M
          | compose-rename (ext ρ) (ext ω) N
          | compose-ext {ρ = ρ} {ω}          = refl
  compose-rename ρ ω ($≔ V ⋯ M)
    rewrite compose-rename-val ρ ω V
          | compose-rename (ext (ext ρ)) (ext (ext ω)) M
          | compose-ext {ρ = ext ρ} {ext ω}
          | compose-ext {ρ = ρ} {ω}                      = refl
  compose-rename ρ ω ⟨ M₁ , M₂ ⟩
    rewrite compose-rename ρ ω M₁ | compose-rename ρ ω M₂ = refl
  compose-rename ρ ω (projl M) rewrite compose-rename ρ ω M = refl
  compose-rename ρ ω (projr M) rewrite compose-rename ρ ω M = refl
  compose-rename ρ ω (case V inl⇒ M₁ inr⇒ M₂)
    rewrite compose-rename-val ρ ω V
          | compose-rename (ext ρ) (ext ω) M₁
          | compose-rename (ext ρ) (ext ω) M₂
          | compose-ext {ρ = ρ} {ω}           = refl

mutual
  commute-subst-rename-val : ∀ {n m p q : ℕ} (σ : Sub m n) (ρ : Ren p m)
                               (ρ′ : Ren q n) (σ′ : Sub p q) (V : Val n)
                           → (∀ (x : Fin n) → σ′ (ρ′ x) ≡ σ x [ ρ ]v)
                           → V [ ρ′ ]v ⦅ σ′ ⦆v ≡ V ⦅ σ ⦆v [ ρ ]v
  commute-subst-rename-val σ ρ ρ′ σ′ (# x) pf = pf x
  commute-subst-rename-val σ ρ ρ′ σ′ unit pf = refl
  commute-subst-rename-val σ ρ ρ′ σ′ ⟪ M ⟫ pf
    rewrite commute-subst-rename σ ρ ρ′ σ′ M pf = refl
  commute-subst-rename-val σ ρ ρ′ σ′ ⟨ V₁ , V₂ ⟩ pf
    rewrite commute-subst-rename-val σ ρ ρ′ σ′ V₁ pf
          | commute-subst-rename-val σ ρ ρ′ σ′ V₂ pf = refl
  commute-subst-rename-val σ ρ ρ′ σ′ (inl V) pf
    rewrite commute-subst-rename-val σ ρ ρ′ σ′ V pf = refl
  commute-subst-rename-val σ ρ ρ′ σ′ (inr V) pf
    rewrite commute-subst-rename-val σ ρ ρ′ σ′ V pf = refl
  
  commute-subst-rename : ∀ {n m p q : ℕ} (σ : Sub m n) (ρ : Ren p m)
                           (ρ′ : Ren q n) (σ′ : Sub p q) (M : Comp n)
                       → (∀ (x : Fin n) → σ′ (ρ′ x) ≡ σ x [ ρ ]v)
                       → M [ ρ′ ]c ⦅ σ′ ⦆c ≡ M ⦅ σ ⦆c [ ρ ]c
  commute-subst-rename σ ρ ρ′ σ′ (ƛ M) pf =
    cong ƛ_ (commute-subst-rename (exts σ) (ext ρ) (ext ρ′) (exts σ′) M H)
    where
      H : ∀ x → exts σ′ (ext ρ′ x) ≡ exts σ x [ ext ρ ]v
      H zero = refl
      H (suc m)
        rewrite pf m
              | compose-rename-val ρ suc (σ m)
              | compose-rename-val suc (ext ρ) (σ m) = refl
  commute-subst-rename σ ρ ρ′ σ′ (M · V) pf
    rewrite commute-subst-rename σ ρ ρ′ σ′ M pf
          | commute-subst-rename-val σ ρ ρ′ σ′ V pf = refl
  commute-subst-rename σ ρ ρ′ σ′ (V » M) pf
    rewrite commute-subst-rename-val σ ρ ρ′ σ′ V pf
          | commute-subst-rename σ ρ ρ′ σ′ M pf = refl
  commute-subst-rename σ ρ ρ′ σ′ (V !) pf
    rewrite commute-subst-rename-val σ ρ ρ′ σ′ V pf = refl
  commute-subst-rename σ ρ ρ′ σ′ (return V) pf
    rewrite commute-subst-rename-val σ ρ ρ′ σ′ V pf = refl
  commute-subst-rename σ ρ ρ′ σ′ ($⟵ M ⋯ N) pf
    rewrite commute-subst-rename σ ρ ρ′ σ′ M pf =
    cong
      ($⟵_⋯_ (M ⦅ σ ⦆c [ ρ ]c))
      (commute-subst-rename (exts σ) (ext ρ) (ext ρ′) (exts σ′) N H)
    where
      H : ∀ x → exts σ′ (ext ρ′ x) ≡ exts σ x [ ext ρ ]v
      H zero = refl
      H (suc m)
        rewrite pf m
              | compose-rename-val ρ suc (σ m)
              | compose-rename-val suc (ext ρ) (σ m) = refl
  commute-subst-rename σ ρ ρ′ σ′ ($≔ V ⋯ M) pf
    rewrite commute-subst-rename-val σ ρ ρ′ σ′ V pf =
    cong
      ($≔_⋯_ (V ⦅ σ ⦆v [ ρ ]v))
      (commute-subst-rename (exts (exts σ)) (ext (ext ρ)) (ext (ext ρ′)) (exts (exts σ′)) M H)
    where
      H : ∀ x
        → exts (exts σ′) (ext (ext ρ′) x) ≡ exts (exts σ) x [ ext (ext ρ) ]v
      H zero = refl
      H (suc zero) = refl
      H (suc (suc m))
        rewrite pf m
              | compose-rename-val ρ suc (σ m)
              | compose-rename-val (λ x → suc (ρ x)) suc (σ m)
              | compose-rename-val suc suc (σ m)
              | compose-rename-val (λ x → suc (suc x)) (ext (ext ρ)) (σ m) = refl
  commute-subst-rename σ ρ ρ′ σ′ ⟨ M₁ , M₂ ⟩ pf
    rewrite commute-subst-rename σ ρ ρ′ σ′ M₁ pf
          | commute-subst-rename σ ρ ρ′ σ′ M₂ pf = refl
  commute-subst-rename σ ρ ρ′ σ′ (projl M) pf
    rewrite commute-subst-rename σ ρ ρ′ σ′ M pf = refl
  commute-subst-rename σ ρ ρ′ σ′ (projr M) pf
    rewrite commute-subst-rename σ ρ ρ′ σ′ M pf = refl
  commute-subst-rename σ ρ ρ′ σ′ (case V inl⇒ M₁ inr⇒ M₂) pf
    rewrite commute-subst-rename-val σ ρ ρ′ σ′ V pf =
    cong₂
      (case_inl⇒_inr⇒_ (V ⦅ σ ⦆v [ ρ ]v))
      (commute-subst-rename (exts σ) (ext ρ) (ext ρ′) (exts σ′) M₁ H)
      (commute-subst-rename (exts σ) (ext ρ) (ext ρ′) (exts σ′) M₂ H)
    where
      H : ∀ x → exts σ′ (ext ρ′ x) ≡ exts σ x [ ext ρ ]v
      H zero = refl
      H (suc m)
        rewrite pf m
              | compose-rename-val ρ suc (σ m)
              | compose-rename-val suc (ext ρ) (σ m) = refl

exts-seq : ∀ {m n p : ℕ} (σ : Sub m n) (τ : Sub p m)
         → exts σ ⨟ exts τ ≡ exts (σ ⨟ τ)
exts-seq σ τ = extensionality lemma where
  lemma : ∀ x → exts σ x ⦅ exts τ ⦆v ≡ exts (σ ⨟ τ) x
  lemma zero = refl
  lemma (suc m) =
    commute-subst-rename-val τ suc suc (exts τ) (σ m) (λ _ → refl)

mutual
  sub-sub-val : ∀ {n m p : ℕ} (σ : Sub m n) (τ : Sub p m) (V : Val n)
              → V ⦅ σ ⦆v ⦅ τ ⦆v ≡ V ⦅ σ ⨟ τ ⦆v
  sub-sub-val σ τ (# x) = refl
  sub-sub-val σ τ unit = refl
  sub-sub-val σ τ ⟪ M ⟫
    rewrite sub-sub σ τ M = refl
  sub-sub-val σ τ ⟨ V₁ , V₂ ⟩
    rewrite sub-sub-val σ τ V₁ | sub-sub-val σ τ V₂ = refl
  sub-sub-val σ τ (inl V) rewrite sub-sub-val σ τ V = refl
  sub-sub-val σ τ (inr V) rewrite sub-sub-val σ τ V = refl

  sub-sub : ∀ {n m p : ℕ} (σ : Sub m n) (τ : Sub p m) (M : Comp n)
          → M ⦅ σ ⦆c ⦅ τ ⦆c ≡ M ⦅ σ ⨟ τ ⦆c
  sub-sub σ τ (ƛ M)
    rewrite sub-sub (exts σ) (exts τ) M
          | cong-sub {M = M} (exts-seq σ τ) refl = refl
  sub-sub σ τ (M · V)
    rewrite sub-sub σ τ M | sub-sub-val σ τ V = refl
  sub-sub σ τ (V » M)
    rewrite sub-sub-val σ τ V | sub-sub σ τ M = refl
  sub-sub σ τ (V !) rewrite sub-sub-val σ τ V = refl
  sub-sub σ τ (return V) rewrite sub-sub-val σ τ V = refl
  sub-sub σ τ ($⟵ M ⋯ N)
    rewrite sub-sub σ τ M
          | sub-sub (exts σ) (exts τ) N
          | cong-sub {M = N} (exts-seq σ τ) refl = refl
  sub-sub σ τ ($≔ V ⋯ M)
    rewrite sub-sub-val σ τ V
          | sub-sub (exts (exts σ)) (exts (exts τ)) M
          | cong-sub {M = M} (exts-seq (exts σ) (exts τ)) refl
          | cong-sub {M = M} (cong exts (exts-seq σ τ)) refl   = refl
  sub-sub σ τ ⟨ M₁ , M₂ ⟩
    rewrite sub-sub σ τ M₁ | sub-sub σ τ M₂ = refl
  sub-sub σ τ (projl M) rewrite sub-sub σ τ M = refl
  sub-sub σ τ (projr M) rewrite sub-sub σ τ M = refl
  sub-sub σ τ (case V inl⇒ M₁ inr⇒ M₂)
    rewrite sub-sub-val σ τ V
          | sub-sub (exts σ) (exts τ) M₁
          | cong-sub {M = M₁} (exts-seq σ τ) refl
          | sub-sub (exts σ) (exts τ) M₂
          | cong-sub {M = M₂} (exts-seq σ τ) refl = refl

sub-assoc : ∀ {n m p q : ℕ} (σ : Sub m n) (τ : Sub p m) (θ : Sub q p)
          → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
sub-assoc σ τ θ = extensionality lemma where
  lemma = λ x → sub-sub-val τ θ (σ x)

↑ : ∀ {n : ℕ} → Sub (suc n) n
↑ m = # (suc m)

ren : ∀ {n m : ℕ} → Ren n m → Sub n m
ren ρ m = # (ρ m)

ren-ext : ∀ {n m : ℕ} (ρ : Ren n m)
        → ren (ext ρ) ≡ exts (ren ρ)
ren-ext ρ = extensionality lemma where
  lemma = λ where zero    → refl
                  (suc m) → refl

mutual
  rename-subst-ren-val : ∀ {n m : ℕ} (ρ : Ren n m) (V : Val m)
                       → V [ ρ ]v ≡ V ⦅ ren ρ ⦆v
  rename-subst-ren-val ρ (# x) = refl
  rename-subst-ren-val ρ unit = refl
  rename-subst-ren-val ρ ⟪ M ⟫
    rewrite rename-subst-ren ρ M = refl
  rename-subst-ren-val ρ ⟨ V₁ , V₂ ⟩
    rewrite rename-subst-ren-val ρ V₁ | rename-subst-ren-val ρ V₂ = refl
  rename-subst-ren-val ρ (inl V)
    rewrite rename-subst-ren-val ρ V = refl
  rename-subst-ren-val ρ (inr V)
    rewrite rename-subst-ren-val ρ V = refl
  
  rename-subst-ren : ∀ {n m : ℕ} (ρ : Ren n m) (M : Comp m)
                   → M [ ρ ]c ≡ M ⦅ ren ρ ⦆c
  rename-subst-ren ρ (ƛ M)
    rewrite rename-subst-ren (ext ρ) M
          | cong-sub {M = M} (ren-ext ρ) refl = refl
  rename-subst-ren ρ (M · V)
    rewrite rename-subst-ren ρ M | rename-subst-ren-val ρ V = refl
  rename-subst-ren ρ (V » M)
    rewrite rename-subst-ren-val ρ V | rename-subst-ren ρ M = refl
  rename-subst-ren ρ (V !)
    rewrite rename-subst-ren-val ρ V = refl
  rename-subst-ren ρ (return V)
    rewrite rename-subst-ren-val ρ V = refl
  rename-subst-ren ρ ($⟵ M ⋯ N)
    rewrite rename-subst-ren ρ M
          | rename-subst-ren (ext ρ) N
          | cong-sub {M = N} (ren-ext ρ) refl = refl
  rename-subst-ren ρ ($≔ V ⋯ M)
    rewrite rename-subst-ren-val ρ V
          | rename-subst-ren (ext (ext ρ)) M
          | cong-sub {M = M} (trans (ren-ext (ext ρ)) (cong exts (ren-ext ρ))) refl = refl
  rename-subst-ren ρ ⟨ M₁ , M₂ ⟩
    rewrite rename-subst-ren ρ M₁ | rename-subst-ren ρ M₂ = refl
  rename-subst-ren ρ (projl M)
    rewrite rename-subst-ren ρ M = refl
  rename-subst-ren ρ (projr M)
    rewrite rename-subst-ren ρ M = refl
  rename-subst-ren ρ (case V inl⇒ M₁ inr⇒ M₂)
    rewrite rename-subst-ren-val ρ V
          | rename-subst-ren (ext ρ) M₁
          | cong-sub {M = M₁} (ren-ext ρ) refl
          | rename-subst-ren (ext ρ) M₂
          | cong-sub {M = M₂} (ren-ext ρ) refl = refl

subst-zero-cons-ids : ∀ {n : ℕ} (V : Val n)
                    → subst-zero V ≡ (V • id)
subst-zero-cons-ids _ = extensionality lemma where
  lemma = λ where zero    → refl
                  (suc m) → refl

exts-cons-shift : ∀ {n m : ℕ} (σ : Sub n m)
                → exts σ ≡ # zero • (σ ⨟ ↑)
exts-cons-shift σ = extensionality lemma where
  lemma = λ where zero    → refl
                  (suc m) → rename-subst-ren-val suc (σ m)

sub-dist : ∀ {n m p : ℕ} (σ : Sub m n) (τ : Sub p m) (V : Val m)
         → (V • σ) ⨟ τ ≡ V ⦅ τ ⦆v • (σ ⨟ τ)
sub-dist _ _ _ = extensionality lemma where
  lemma = λ where zero    → refl
                  (suc m) → refl

cong-cons : ∀ {n m : ℕ} {V V′ : Val n} {σ τ : Sub n m}
          → V ≡ V′
          → σ ≡ τ
          → V • σ ≡ V′ • τ
cong-cons {V = V} {σ = σ} {τ} refl st = extensionality lemma where
  lemma : ∀ x → (V • σ) x ≡ (V • τ) x
  lemma zero = refl
  lemma (suc m) rewrite st = refl

cong-seq : ∀ {n m p : ℕ} {σ : Sub m n} {τ : Sub p m} {σ′ : Sub m n} {τ′ : Sub p m}
         → σ ≡ σ′
         → τ ≡ τ′
         → σ ⨟ τ ≡ σ′ ⨟ τ′
cong-seq {σ = σ} {τ} {σ′} {τ′} ss tt = extensionality lemma where
  lemma : ∀ x → σ x ⦅ τ ⦆v ≡ σ′ x ⦅ τ′ ⦆v
  lemma x
    rewrite ss | tt = refl

sub-tail : ∀ {n m : ℕ} (σ : Sub n m) (V : Val n)
         → ↑ ⨟ (V • σ) ≡ σ
sub-tail σ V = refl         

subst-zero-exts-cons : ∀ {n m : ℕ} (σ : Sub n m) (V : Val n)
                     → exts σ ⨟ subst-zero V ≡ V • σ
subst-zero-exts-cons σ V =
  begin
    exts σ ⨟ subst-zero V
  ≡⟨ cong-seq (exts-cons-shift σ) (subst-zero-cons-ids V) ⟩
    (# zero • (σ ⨟ ↑)) ⨟ (V • id)
  ≡⟨ sub-dist (σ ⨟ ↑) (V • id) (# zero) ⟩
    V • ((σ ⨟ ↑) ⨟ (V • id))
  ≡⟨ cong-cons refl (sub-assoc σ ↑ (V • id)) ⟩
    V • (σ ⨟ ↑ ⨟ (V • id))
  ≡⟨ cong-cons refl (cong-seq {σ = σ} refl (sub-tail id V)) ⟩
    V • (σ ⨟ id)
    ≡⟨ cong-cons refl (extensionality (λ x → sub-id-val (σ x))) ⟩
    V • σ
  ∎

exts-seq-cons : ∀ {m : ℕ} (σ : Sub m n′) (V : Val n) (τ : Sub n m)
              → exts σ ⨟ (V • τ) ≡ V • (σ ⨟ τ)
exts-seq-cons σ V τ =
  begin
    exts σ ⨟ (V • τ)
  ≡⟨ cong-seq (exts-cons-shift σ) refl ⟩
    (# zero • (σ ⨟ ↑)) ⨟ (V • τ)
  ≡⟨ sub-dist (σ ⨟ ↑) (V • τ) (# zero) ⟩
    V • ((σ ⨟ ↑) ⨟ V • τ)
  ≡⟨ cong-cons refl (sub-assoc σ ↑ (V • τ)) ⟩
    V • (σ ⨟ ↑ ⨟ V • τ)
  ≡⟨ cong-cons refl (cong-seq {σ = σ} refl (sub-tail τ V)) ⟩
    V • (σ ⨟ τ)
  ∎

mutual
  val-typepres-substitution : ∀ {σ : Sub n n′} 
                            → Δ ⊢v V ⦂ A
                            → (∀ (m : Fin n′) → Γ ⊢v σ m ⦂ Δ m)
                              ---------------------------------
                            → Γ ⊢v V ⦅ σ ⦆v ⦂ A
  val-typepres-substitution (typeVar {m = m}) pf = pf m
  val-typepres-substitution typeUnit _ = typeUnit
  val-typepres-substitution (typeThunk ⊢M) pf =
    typeThunk (comp-typepres-substitution ⊢M pf)
  val-typepres-substitution (typePair ⊢V₁ ⊢V₂) pf =
    typePair
      (val-typepres-substitution ⊢V₁ pf)
      (val-typepres-substitution ⊢V₂ pf)
  val-typepres-substitution (typeInl ⊢V) pf =
    typeInl (val-typepres-substitution ⊢V pf)
  val-typepres-substitution (typeInr ⊢V) pf =
    typeInr (val-typepres-substitution ⊢V pf)

  comp-typepres-substitution : ∀ {σ : Sub n n′}
                             → Δ ⊢c M ⦂ B
                             → (∀ (m : Fin n′) → Γ ⊢v σ m ⦂ Δ m)
                               ---------------------------------
                             → Γ ⊢c M ⦅ σ ⦆c ⦂ B
  comp-typepres-substitution (typeAbs ⊢M) pf =
    typeAbs (comp-typepres-substitution ⊢M exts-pf)
    where
      exts-pf = λ where
                    zero    → typeVar
                    (suc m) → val-typepres-renaming (pf m) λ _ → refl
  comp-typepres-substitution (typeApp ⊢M ⊢V) pf =
    typeApp
      (comp-typepres-substitution ⊢M pf)
      (val-typepres-substitution ⊢V pf)
  comp-typepres-substitution (typeSequence ⊢V ⊢M) pf =
    typeSequence
      (val-typepres-substitution ⊢V pf)
      (comp-typepres-substitution ⊢M pf)
  comp-typepres-substitution (typeForce ⊢V) pf =
    typeForce (val-typepres-substitution ⊢V pf)
  comp-typepres-substitution (typeRet ⊢V) pf =
    typeRet (val-typepres-substitution ⊢V pf)
  comp-typepres-substitution (typeLetin ⊢M ⊢N) pf =
    typeLetin
      (comp-typepres-substitution ⊢M pf)
      (comp-typepres-substitution ⊢N exts-pf)
    where
      exts-pf = λ where
                    zero    → typeVar
                    (suc m) → val-typepres-renaming (pf m) λ _ → refl
  comp-typepres-substitution (typeSplit ⊢V ⊢M) pf =
    typeSplit
      (val-typepres-substitution ⊢V pf)
      (comp-typepres-substitution ⊢M exts-pf)
    where
      exts-pf = λ where
                    zero          → typeVar
                    (suc zero)    → typeVar
                    (suc (suc m)) → val-typepres-renaming
                                      (val-typepres-renaming (pf m) (λ _ → refl))
                                      λ _ → refl
  comp-typepres-substitution (typeCpair ⊢M₁ ⊢M₂) pf =
    typeCpair
      (comp-typepres-substitution ⊢M₁ pf)
      (comp-typepres-substitution ⊢M₂ pf)
  comp-typepres-substitution (typeProjl ⊢M) pf =
    typeProjl (comp-typepres-substitution ⊢M pf)
  comp-typepres-substitution (typeProjr ⊢M) pf =
    typeProjr (comp-typepres-substitution ⊢M pf)
  comp-typepres-substitution (typeCase ⊢V ⊢M₁ ⊢M₂) pf =
    typeCase
      (val-typepres-substitution ⊢V pf)
      (comp-typepres-substitution ⊢M₁ exts-pf₁)
      (comp-typepres-substitution ⊢M₂ exts-pf₂)
    where
      exts-pf₁ = λ where
                     zero    → typeVar
                     (suc m) → val-typepres-renaming (pf m) λ _ → refl
      exts-pf₂ = λ where
                     zero    → typeVar
                     (suc m) → val-typepres-renaming (pf m) λ _ → refl
