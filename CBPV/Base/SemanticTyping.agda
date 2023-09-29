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
  𝐺⟦_⟧v : ValType → ClosVal → Set
  𝐺⟦ 𝟙 ⟧v unit = ⊤
  𝐺⟦ 𝑼 B ⟧v clos⦅ ρ ,⟪ M ⟫⦆ = (ρ , M) ∈ 𝐺⟦ B ⟧e
  𝐺⟦ _ ⟧v _ = ⊥

  𝐺⟦_⟧c : CompType → ClosTerminal → Set
  𝐺⟦ 𝑭 A ⟧c (return V) = V ∈ 𝐺⟦ A ⟧v
  𝐺⟦ A ⇒ B ⟧c clos⦅ ρ ,ƛ M ⦆ =
    ∀ {W : ClosVal} → W ∈ 𝐺⟦ A ⟧v → (ρ ∷ᵨ W , M) ∈ 𝐺⟦ B ⟧e
  𝐺⟦ _ ⟧c _ = ⊥

  𝐺⟦_⟧e : CompType → Env n × Comp n → Set
  𝐺⟦ B ⟧e (ρ , M) = ∃[ T ] ρ ⊢c M ⇓ T × T ∈ 𝐺⟦ B ⟧c

𝐺⟦_⟧z : ValType → Env n × Val n → Set
𝐺⟦ A ⟧z (ρ , V) = ∃[ W ] ρ ⊢v V ⇓ W × W ∈ 𝐺⟦ A ⟧v


_⊨_ : Ctx n → Env n → Set
Γ ⊨ ρ = ∀ m → ρ m ∈ 𝐺⟦ Γ m ⟧v

infix 4 _⊨_

⊨-ext : Γ ⊨ ρ → W ∈ 𝐺⟦ A ⟧v → Γ ∷ A ⊨ ρ ∷ᵨ W
⊨-ext _ pf zero = pf
⊨-ext Γ⊨ρ _ (suc m) = Γ⊨ρ m

_⊨v_⦂_ : Ctx n → Val n → ValType → Set
Γ ⊨v V ⦂ A = ∀ {ρ} → Γ ⊨ ρ → (ρ , V) ∈ 𝐺⟦ A ⟧z

infix 4 _⊨v_⦂_

_⊨c_⦂_ : Ctx n → Comp n → CompType → Set
Γ ⊨c M ⦂ B = ∀ {ρ} → Γ ⊨ ρ → (ρ , M) ∈ 𝐺⟦ B ⟧e

infix 4 _⊨c_⦂_

semanticVar : Γ ⊨v # m ⦂ Γ m
semanticVar {m = m} {ρ = ρ} ⊨ρ = ρ m , evalVar {m = m} , ⊨ρ m

semanticUnit : Γ ⊨v unit ⦂ 𝟙
semanticUnit _ = unit , evalUnit , tt

semanticThunk : Γ ⊨c M ⦂ B
                ----------------
              → Γ ⊨v ⟪ M ⟫ ⦂ 𝑼 B
semanticThunk {M = M} ⊨M {ρ} ⊨ρ = clos⦅ ρ ,⟪ M ⟫⦆ , evalThunk , ⊨M ⊨ρ

semanticAbs : Γ ∷ A ⊨c M ⦂ B
              ----------------
            → Γ ⊨c ƛ M ⦂ A ⇒ B
semanticAbs {M = M} ⊨M {ρ} ⊨ρ =
  clos⦅ ρ ,ƛ M ⦆ , evalAbs , λ W∈𝐺⟦A⟧ → ⊨M (⊨-ext ⊨ρ W∈𝐺⟦A⟧)

semanticApp : Γ ⊨c M ⦂ A ⇒ B
            → Γ ⊨v V ⦂ A
              --------------
            → Γ ⊨c M · V ⦂ B
semanticApp ⊨M ⊨V ⊨ρ
  with ⊨M ⊨ρ
... | T′@(clos⦅ ρ′ ,ƛ M′ ⦆) , M⇓ , pf
  with ⊨V ⊨ρ
...  | W , V⇓ , W∈𝐺⟦A⟧
  with pf W∈𝐺⟦A⟧
...  | T , M′⇓ , T∈𝐺⟦B⟧ =
  T , evalApp M⇓ V⇓ M′⇓ , T∈𝐺⟦B⟧

semanticSeq : Γ ⊨v V ⦂ 𝟙
            → Γ ⊨c M ⦂ B
              --------------
            → Γ ⊨c V » M ⦂ B
semanticSeq ⊨V ⊨M ⊨ρ
  with ⊨V ⊨ρ
...  | unit , V⇓ , _
  with ⊨M ⊨ρ
...  | T , M⇓ , T∈𝐺⟦B⟧ =
  T , evalSeq V⇓ M⇓ , T∈𝐺⟦B⟧

semanticForce : Γ ⊨v V ⦂ 𝑼 B
                ------------
              → Γ ⊨c V ! ⦂ B
semanticForce ⊨V ⊨ρ
  with ⊨V ⊨ρ
...  | W@(clos⦅ ρ′ ,⟪ M ⟫⦆) , V⇓ , T , M⇓ , T∈𝐺⟦B⟧ =
  T , evalForce V⇓ M⇓ , T∈𝐺⟦B⟧

semanticRet : Γ ⊨v V ⦂ A
            → Γ ⊨c return V ⦂ 𝑭 A
semanticRet ⊨V ⊨ρ
  with ⊨V ⊨ρ
... | W , V⇓ , W∈𝐺⟦A⟧ =
  return W , evalRet V⇓ , W∈𝐺⟦A⟧

semanticLetin : Γ ⊨c M ⦂ 𝑭 A
              → Γ ∷ A ⊨c N ⦂ B
              → Γ ⊨c $⟵ M ⋯ N ⦂ B
semanticLetin ⊨M ⊨N ⊨ρ
  with ⊨M ⊨ρ
...  | T′@(return W) , M⇓ , W∈𝐺⟦A⟧
  with ⊨N (⊨-ext ⊨ρ W∈𝐺⟦A⟧)
...  | T , N⇓ , T∈𝐺⟦B⟧ =
  T , evalLetin M⇓ N⇓ , T∈𝐺⟦B⟧
