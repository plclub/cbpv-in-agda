open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; ∃; ∃-syntax; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Unary using (_∈_)

open import CBPV.Base.Terms
open import CBPV.Base.Types
open import CBPV.Base.SyntacticTyping
open import CBPV.Base.Semantics

module CBPV.Base.SemanticTyping where

mutual
  𝒲⟦_⟧ : ValType → ClosVal → Set
  𝒲⟦ 𝟙 ⟧ unit = ⊤
  𝒲⟦ 𝑼 B ⟧ clos⦅ ρ ,⟪ M ⟫⦆ = (ρ , M) ∈ ℳ⟦ B ⟧
  𝒲⟦ A₁ * A₂ ⟧ ⟨ W₁ , W₂ ⟩ = W₁ ∈ 𝒲⟦ A₁ ⟧ × W₂ ∈ 𝒲⟦ A₂ ⟧
  𝒲⟦ A₁ ∪ A₂ ⟧ (inl W) = W ∈ 𝒲⟦ A₁ ⟧
  𝒲⟦ A₁ ∪ A₂ ⟧ (inr W) = W ∈ 𝒲⟦ A₂ ⟧
  𝒲⟦ _ ⟧ _ = ⊥

  𝒯⟦_⟧ : CompType → ClosTerminal → Set
  𝒯⟦ 𝑭 A ⟧ (return V) = V ∈ 𝒲⟦ A ⟧
  𝒯⟦ A ⇒ B ⟧ clos⦅ ρ ,ƛ M ⦆ =
    ∀ {W : ClosVal} → W ∈ 𝒲⟦ A ⟧ → (ρ ∷ᵨ W , M) ∈ ℳ⟦ B ⟧
  𝒯⟦ _ ⟧ _ = ⊥

  ℳ⟦_⟧ : CompType → Env n × Comp n → Set
  ℳ⟦ B ⟧ (ρ , M) = ∃[ T ] ρ ⊢c M ⇓ T × T ∈ 𝒯⟦ B ⟧

𝒱⟦_⟧ : ValType → Env n × Val n → Set
𝒱⟦ A ⟧ (ρ , V) = ∃[ W ] ρ ⊢v V ⇓ W × W ∈ 𝒲⟦ A ⟧


_⊨_ : Ctx n → Env n → Set
Γ ⊨ ρ = ∀ m → ρ m ∈ 𝒲⟦ Γ m ⟧

infix 4 _⊨_

⊨-ext : Γ ⊨ ρ → W ∈ 𝒲⟦ A ⟧ → Γ ∷ A ⊨ ρ ∷ᵨ W
⊨-ext _ pf zero = pf
⊨-ext Γ⊨ρ _ (suc m) = Γ⊨ρ m

_⊨v_⦂_ : Ctx n → Val n → ValType → Set
Γ ⊨v V ⦂ A = ∀ {ρ} → Γ ⊨ ρ → (ρ , V) ∈ 𝒱⟦ A ⟧

infix 4 _⊨v_⦂_

_⊨c_⦂_ : Ctx n → Comp n → CompType → Set
Γ ⊨c M ⦂ B = ∀ {ρ} → Γ ⊨ ρ → (ρ , M) ∈ ℳ⟦ B ⟧

infix 4 _⊨c_⦂_

semanticVar : Γ ⊨v # m ⦂ Γ m
semanticVar {m = m} {ρ = ρ} ⊨ρ = ρ m , evalVar {m = m} , ⊨ρ m

semanticUnit : Γ ⊨v unit ⦂ 𝟙
semanticUnit _ = unit , evalUnit , tt

semanticThunk : Γ ⊨c M ⦂ B
                ----------------
              → Γ ⊨v ⟪ M ⟫ ⦂ 𝑼 B
semanticThunk {M = M} ⊨M {ρ} ⊨ρ = clos⦅ ρ ,⟪ M ⟫⦆ , evalThunk , ⊨M ⊨ρ

semanticPair : Γ ⊨v V₁ ⦂ A₁
             → Γ ⊨v V₂ ⦂ A₂
               --------------------------
             → Γ ⊨v ⟨ V₁ , V₂ ⟩ ⦂ A₁ * A₂
semanticPair ⊨V₁ ⊨V₂ ⊨ρ
  with ⊨V₁ ⊨ρ          | ⊨V₂ ⊨ρ
... | W₁ , V₁⇓ , W₁∈𝒲 | W₂ , V₂⇓ , W₂∈𝒲 =
  ⟨ W₁ , W₂ ⟩ , evalPair V₁⇓ V₂⇓ , W₁∈𝒲 , W₂∈𝒲

semanticInl : Γ ⊨v V ⦂ A₁
              --------------------
            → Γ ⊨v inl V ⦂ A₁ ∪ A₂
semanticInl ⊨V ⊨ρ
  with ⊨V ⊨ρ
...  | W , V⇓ , W∈𝒲 =
  inl W , evalInl V⇓ , W∈𝒲

semanticInr : Γ ⊨v V ⦂ A₂
              --------------------
            → Γ ⊨v inr V ⦂ A₁ ∪ A₂
semanticInr ⊨V ⊨ρ
  with ⊨V ⊨ρ
...  | W , V⇓ , W∈𝒲 =
  inr W , evalInr V⇓ , W∈𝒲

semanticAbs : Γ ∷ A ⊨c M ⦂ B
              ----------------
            → Γ ⊨c ƛ M ⦂ A ⇒ B
semanticAbs {M = M} ⊨M {ρ} ⊨ρ =
  clos⦅ ρ ,ƛ M ⦆ , evalAbs , λ W∈𝒲 → ⊨M (⊨-ext ⊨ρ W∈𝒲)

semanticApp : Γ ⊨c M ⦂ A ⇒ B
            → Γ ⊨v V ⦂ A
              --------------
            → Γ ⊨c M · V ⦂ B
semanticApp ⊨M ⊨V ⊨ρ
  with ⊨M ⊨ρ
... | T′@(clos⦅ ρ′ ,ƛ M′ ⦆) , M⇓ , pf
  with ⊨V ⊨ρ
...  | W , V⇓ , W∈𝒲
  with pf W∈𝒲
...  | T , M′⇓ , T∈𝒯 =
  T , evalApp M⇓ V⇓ M′⇓ , T∈𝒯

semanticSeq : Γ ⊨v V ⦂ 𝟙
            → Γ ⊨c M ⦂ B
              --------------
            → Γ ⊨c V » M ⦂ B
semanticSeq ⊨V ⊨M ⊨ρ
  with ⊨V ⊨ρ
...  | unit , V⇓ , _
  with ⊨M ⊨ρ
...  | T , M⇓ , 𝒯 =
  T , evalSeq V⇓ M⇓ , 𝒯

semanticForce : Γ ⊨v V ⦂ 𝑼 B
                ------------
              → Γ ⊨c V ! ⦂ B
semanticForce ⊨V ⊨ρ
  with ⊨V ⊨ρ
...  | W@(clos⦅ ρ′ ,⟪ M ⟫⦆) , V⇓ , T , M⇓ , T∈𝒯 =
  T , evalForce V⇓ M⇓ , T∈𝒯

semanticRet : Γ ⊨v V ⦂ A
              -------------------
            → Γ ⊨c return V ⦂ 𝑭 A
semanticRet ⊨V ⊨ρ
  with ⊨V ⊨ρ
... | W , V⇓ , W∈𝒲 =
  return W , evalRet V⇓ , W∈𝒲

semanticLetin : Γ ⊨c M ⦂ 𝑭 A
              → Γ ∷ A ⊨c N ⦂ B
                ------------------
              → Γ ⊨c $⟵ M ⋯ N ⦂ B
semanticLetin ⊨M ⊨N ⊨ρ
  with ⊨M ⊨ρ
...  | T′@(return W) , M⇓ , W∈𝒲
  with ⊨N (⊨-ext ⊨ρ W∈𝒲)
...  | T , N⇓ , T∈𝒯 =
  T , evalLetin M⇓ N⇓ , T∈𝒯

semanticSplit : Γ ⊨v V ⦂ A₁ * A₂
              → Γ ∷ A₁ ∷ A₂ ⊨c M ⦂ B
                --------------------
              → Γ ⊨c $≔ V ⋯ M ⦂ B
semanticSplit ⊨V ⊨M ⊨ρ
  with ⊨V ⊨ρ
...  | ⟨ W₁ , W₂ ⟩ , V⇓ , (W₁∈𝒲 , W₂∈𝒲)
  with ⊨M (⊨-ext (⊨-ext ⊨ρ W₁∈𝒲) W₂∈𝒲)
...  | T , M⇓ , T∈𝒯 =
  T , evalSplit V⇓ M⇓ , T∈𝒯

semanticCase : Γ ⊨v V ⦂ A₁ ∪ A₂
             → Γ ∷ A₁ ⊨c M₁ ⦂ B
             → Γ ∷ A₂ ⊨c M₂ ⦂ B
               -------------------------------
             → Γ ⊨c case V inl⇒ M₁ inr⇒ M₂ ⦂ B
semanticCase ⊨V ⊨M₁ ⊨M₂ ⊨ρ
  with ⊨V ⊨ρ
... | inl W , V⇓ , W∈𝒲 =
  let (T , M₁⇓ , T∈𝒯) = ⊨M₁ (⊨-ext ⊨ρ W∈𝒲) in
  T , evalCaseInl V⇓ M₁⇓ , T∈𝒯
... | inr W , V⇓ , W∈𝒲 =
  let (T , M₂⇓ , T∈𝒯) = ⊨M₂ (⊨-ext ⊨ρ W∈𝒲) in
  T , evalCaseInr V⇓ M₂⇓ , T∈𝒯
