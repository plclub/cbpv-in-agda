import Relation.Binary.PropositionalEquality as Eq
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)
open Eq using (_≡_; refl)

open import CBPV.Effects.Terms
open import Effects

module CBPV.Effects.Renaming (E : Effect)  where

open import CBPV.Effects.Types E
open import CBPV.Effects.SyntacticTyping E
open Effect E

Ren : ℕ → ℕ → Set
Ren n n′ = (m : Fin n′) → Fin n

ext : ∀ {n n′ : ℕ} → Ren n n′ → Ren (suc n) (suc n′)
ext ρ zero = zero
ext ρ (suc m) = suc (ρ m)

mutual
  _[_]v : ∀ {n n′ : ℕ}
         → Val n′
         → Ren n n′
           --------
         → Val n
  unit [ _ ]v    = unit
  ♯ m [ ρ ]v     = ♯ ρ m
  ⟪ M ⟫ [ ρ ]v   = ⟪ M [ ρ ]c ⟫
  ⟨ V₁ , V₂ ⟩ [ ρ ]v = ⟨ V₁ [ ρ ]v , V₂ [ ρ ]v ⟩
  inl V [ ρ ]v = inl (V [ ρ ]v)
  inr V [ ρ ]v = inr (V [ ρ ]v)

  _[_]c : ∀ {n n′ : ℕ}
         → Comp n′
         → Ren n n′
           --------
         → Comp n
  (ƛ M) [ ρ ]c   = ƛ M [ ext ρ ]c
  (M · V) [ ρ ]c = M [ ρ ]c · V [ ρ ]v
  (V » M) [ ρ ]c = V [ ρ ]v » M [ ρ ]c
  (return V) [ ρ ]c = return V [ ρ ]v
  ($⟵ M ⋯ N) [ ρ ]c = $⟵ M [ ρ ]c ⋯ N [ ext ρ ]c
  (V !) [ ρ ]c = V [ ρ ]v !
  ($≔ V ⋯ M) [ ρ ]c = $≔ V [ ρ ]v ⋯ M [ ext (ext ρ) ]c
  (case V inl⇒ M₁ inr⇒ M₂) [ ρ ]c = case V [ ρ ]v inl⇒ M₁ [ ext ρ ]c inr⇒ M₂ [ ext ρ ]c
  ⟨ M₁ , M₂ ⟩ [ ρ ]c = ⟨ M₁ [ ρ ]c , M₂ [ ρ ]c ⟩
  projl M [ ρ ]c = projl (M [ ρ ]c)
  projr M [ ρ ]c = projr (M [ ρ ]c)
  tick [ ρ ]c = tick

infix 8 _[_]v
infix 8 _[_]c

↑↑ : Ren (suc n) n
↑↑ zero = zero
↑↑ = suc

↑↑↑ : Ren (suc n) n
↑↑↑ zero = zero
↑↑↑ (suc zero) = suc zero
↑↑↑ = suc

mutual
  val-typepres-renaming : ∀ {ρ : Ren n n′}
                         → Δ ⊢v V ⦂ A
                         → (∀ (m : Fin n′) → Δ m ≡ Γ (ρ m))
                           --------------------------------
                         → Γ ⊢v V [ ρ ]v ⦂ A
  val-typepres-renaming (typeVar {m = m}) pf rewrite pf m = typeVar
  val-typepres-renaming typeUnit _ = typeUnit
  val-typepres-renaming (typeThunk ⊢M) pf =
    typeThunk (comp-typepres-renaming ⊢M pf)
  val-typepres-renaming (typePair ⊢V₁ ⊢V₂) pf =
    typePair
      (val-typepres-renaming ⊢V₁ pf)
      (val-typepres-renaming ⊢V₂ pf)
  val-typepres-renaming (typeInl ⊢V) pf =
    typeInl (val-typepres-renaming ⊢V pf)
  val-typepres-renaming (typeInr ⊢V) pf =
    typeInr (val-typepres-renaming ⊢V pf)

  comp-typepres-renaming : ∀ {ρ : Ren n n′}
                         → Δ ⊢c M ⦂ B # φ
                         → (∀ (m : Fin n′) → Δ m ≡ Γ (ρ m))
                           --------------------------------
                         → Γ ⊢c M [ ρ ]c ⦂ B # φ
  comp-typepres-renaming (typeAbs ⊢M) pf =
    typeAbs (comp-typepres-renaming ⊢M ext-pf)
    where
      ext-pf = λ where
                   zero    → refl
                   (suc m) → pf m
  comp-typepres-renaming (typeApp ⊢M ⊢V) pf =
    typeApp (comp-typepres-renaming ⊢M pf) (val-typepres-renaming ⊢V pf)
  comp-typepres-renaming (typeSequence ⊢V ⊢M) pf =
    typeSequence
      (val-typepres-renaming ⊢V pf)
      (comp-typepres-renaming ⊢M pf)
  comp-typepres-renaming (typeForce ⊢V φ′≤φ) pf =
    typeForce (val-typepres-renaming ⊢V pf) φ′≤φ
  comp-typepres-renaming (typeRet ⊢V pure≤φ) pf =
    typeRet (val-typepres-renaming ⊢V pf) pure≤φ
  comp-typepres-renaming (typeLetin ⊢M ⊢N φ₁+φ₂≤φ) pf =
    typeLetin
      (comp-typepres-renaming ⊢M pf)
      (comp-typepres-renaming ⊢N ext-pf)
      φ₁+φ₂≤φ
    where
      ext-pf = λ where
                   zero    → refl
                   (suc m) → pf m
  comp-typepres-renaming (typeSplit ⊢V ⊢M) pf =
    typeSplit
      (val-typepres-renaming ⊢V pf)
      (comp-typepres-renaming ⊢M ext-pf)
    where
      ext-pf = λ where
                   zero          → refl
                   (suc zero)    → refl
                   (suc (suc m)) → pf m
  comp-typepres-renaming (typeCase ⊢V ⊢M₁ ⊢M₂) pf =
    typeCase
      (val-typepres-renaming ⊢V pf)
      (comp-typepres-renaming ⊢M₁ ext-pf₁)
      (comp-typepres-renaming ⊢M₂ ext-pf₂)
    where
      ext-pf₁ = λ where
                    zero    → refl
                    (suc m) → pf m
      ext-pf₂ = λ where
                    zero    → refl
                    (suc m) → pf m
  comp-typepres-renaming (typeCpair ⊢M₁ ⊢M₂) pf =
    typeCpair
      (comp-typepres-renaming ⊢M₁ pf)
      (comp-typepres-renaming ⊢M₂ pf)
  comp-typepres-renaming (typeProjl ⊢M) pf =
    typeProjl (comp-typepres-renaming ⊢M pf)
  comp-typepres-renaming (typeProjr ⊢M) pf =
    typeProjr (comp-typepres-renaming ⊢M pf)
  comp-typepres-renaming (typeTick tock≤φ) _ = typeTick tock≤φ
