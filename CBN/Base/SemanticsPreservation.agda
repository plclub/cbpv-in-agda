import Relation.Binary.PropositionalEquality as Eq
open import Axiom.Extensionality.Propositional using (Extensionality)
import Relation.Binary.PropositionalEquality as Eq
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Level using (0ℓ)
open Eq using (_≡_; refl; subst; cong; sym)

import CBPV.Base.Semantics as CBPV
open import CBN.Base.Terms
open import CBN.Base.Translation
open import CBN.Base.Types
open import CBN.Base.Semantics
open import CBPV.Base.Renaming
open import CBPV.Base.Terms hiding (n; m)
open import CBPV.Base.Types
open CBPV hiding (Env)

module CBN.Base.SemanticsPreservation where

postulate
  extensionality : Extensionality 0ℓ 0ℓ

instance
  ⟦Env⟧ : Translation (Env n) (CBPV.Env n)
  Translation.⟦ ⟦Env⟧ ⟧ γ m with γ m
  ... | clos⦅ δ , e ⦆ = clos⦅ ⟦ δ ⟧ ,⟪ ⟦ e ⟧ ⟫⦆

data _↣_ : Clos → ClosTerminal → Set where
  transVar : γ m ↣ T
           → clos⦅ γ , # m ⦆ ↣ T

  transUnit : clos⦅ γ , unit ⦆ ↣ return unit

  transInl : clos⦅ γ , inl e ⦆ ↣ return inl clos⦅ ⟦ γ ⟧ ,⟪ ⟦ e ⟧ ⟫⦆

  transInr : clos⦅ γ , inr e ⦆ ↣ return inr clos⦅ ⟦ γ ⟧ ,⟪ ⟦ e ⟧ ⟫⦆

  transAbs : clos⦅ γ , ƛ e ⦆ ↣ clos⦅ ⟦ γ ⟧ ,ƛ ⟦ e ⟧ ⦆

  transPair : clos⦅ γ , ⟨ e₁ , e₂ ⟩ ⦆ ↣ clos⦅ ⟦ γ ⟧ ,⟨ ⟦ e₁ ⟧ , ⟦ e₂ ⟧ ⟩⦆

infix 4 _↣_

⟦++⟧-expand : ∀ (δ : Env n) (γ : Env n′) (e : Term n′)
            → ⟦ δ ++ clos⦅ γ , e ⦆ ⟧ ≡ ⟦ δ ⟧ ∷ᵨ clos⦅ ⟦ γ ⟧ ,⟪ ⟦ e ⟧ ⟫⦆
⟦++⟧-expand _ _ _ = extensionality λ where
                                       zero    → refl
                                       (suc m) → refl

cong-⟦env⟧ : γ m ≡ clos⦅ δ , e ⦆ → ⟦ γ ⟧ m ≡ clos⦅ ⟦ δ ⟧ ,⟪ ⟦ e ⟧ ⟫⦆
cong-⟦env⟧ {γ = γ} {m = m} eq
  with γ m
... | clos⦅ δ′ , e′ ⦆
  with eq
... | refl = refl

mutual
  translation-preservation : γ ⊢ e ⇓ a → ∃[ T ] a ↣ T × ⟦ γ ⟧ ⊢c ⟦ e ⟧ ⇓ T
  translation-preservation {γ = γ} (evalVar {m = m} eq e⇓)
    with translation-preservation e⇓
  ...  | T , a↣T , ⟦e⟧⇓ =
    T , a↣T , evalForce var⇓  ⟦e⟧⇓
    where
    var⇓ = subst (⟦ γ ⟧ ⊢v # m ⇓_) (cong-⟦env⟧ {γ = γ} eq) evalVar
  translation-preservation {γ = γ} {e = e₁ · e₂} (evalApp {δ = δ} e₁⇓ e⇓)
    with translation-preservation e₁⇓
  ...  | _ , transAbs , ⟦e₁⟧⇓
    with translation-preservation e⇓
  ...  | T , a↣T , ⟦e⟧⇓
    rewrite ⟦++⟧-expand δ γ e₂ =
    T , a↣T , evalApp ⟦e₁⟧⇓ evalThunk ⟦e⟧⇓
  translation-preservation evalUnit =
    return unit , transUnit , evalRet evalUnit
  translation-preservation {γ = γ} {e = inl e} evalInl =
    return inl clos⦅ ⟦ γ ⟧ ,⟪ ⟦ e ⟧ ⟫⦆ , transInl , evalRet (evalInl evalThunk)
  translation-preservation {γ = γ} {e = inr e} evalInr =
    return inr clos⦅ ⟦ γ ⟧ ,⟪ ⟦ e ⟧ ⟫⦆ , transInr , evalRet (evalInr evalThunk)
  translation-preservation {γ = γ} {e = ⟨ e₁ , e₂ ⟩} evalPair =
    clos⦅ ⟦ γ ⟧ ,⟨ ⟦ e₁ ⟧ , ⟦ e₂ ⟧ ⟩⦆ , transPair , evalCpair
  translation-preservation {γ = γ} {e = ƛ e} evalAbs =
    clos⦅ ⟦ γ ⟧ ,ƛ ⟦ e ⟧ ⦆ , transAbs , evalAbs
  translation-preservation (evalSeq e₁⇓ e₂⇓)
    with translation-preservation e₁⇓
  ...  | _ , transUnit , ⟦e₁⟧⇓
    with translation-preservation e₂⇓
  ...  | T , a↣T , ⟦e₂⟧⇓ =
    T , a↣T , evalLetin ⟦e₁⟧⇓ (evalSeq evalVar {!!})
  translation-preservation (evalFst e⇓ e₁⇓)
    with translation-preservation e⇓
  ...  | _ , transPair , ⟦e⟧⇓
    with translation-preservation e₁⇓
  ...  | T , a↣T , ⟦e₁⟧⇓ =
    T , a↣T , evalProjl ⟦e⟧⇓ ⟦e₁⟧⇓
  translation-preservation (evalSnd e⇓ e₂⇓)
    with translation-preservation e⇓
  ...  | _ , transPair , ⟦e⟧⇓
    with translation-preservation e₂⇓
  ...  | T , a↣T , ⟦e₂⟧⇓ =
    T , a↣T , evalProjr ⟦e⟧⇓ ⟦e₂⟧⇓
  translation-preservation (evalCaseInl e⇓ e₁⇓)
    with translation-preservation e⇓
  ...  | _ , transInl , ⟦e⟧⇓
    with translation-preservation e₁⇓
  ...  | T , a↣T , ⟦e₁⟧⇓ =
    T , a↣T , evalLetin ⟦e⟧⇓ (evalCaseInl evalVar {!!})
  translation-preservation (evalCaseInr e⇓ e₂⇓)
    with translation-preservation e⇓
  ...  | _ , transInr , ⟦e⟧⇓
    with translation-preservation e₂⇓
  ...  | T , a↣T , ⟦e₂⟧⇓ =
    T , a↣T , evalLetin ⟦e⟧⇓ (evalCaseInr evalVar {!!})
