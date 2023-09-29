open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; ∃; ∃-syntax; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Unary using (_∈_)

open import CBPV.Effects.Terms
open import Effects

module CBPV.Effects.SemanticTyping (E : Effect) where

open import CBPV.Effects.Semantics E
open import CBPV.Effects.SyntacticTyping E
open import CBPV.Effects.Types E
open Effect E
open Properties E

mutual
  𝐺⟦_⟧v : ValType → ClosVal → Set
  𝐺⟦ 𝟙 ⟧v unit = ⊤
  𝐺⟦ 𝑼 φ B ⟧v clos⦅ ρ ,⟪ M ⟫⦆ = (ρ , M , φ) ∈ 𝐺⟦ B ⟧e
  𝐺⟦ _ ⟧v _ = ⊥

  𝐺⟦_⟧c : CompType → ClosTerminal × Eff → Set
  𝐺⟦ 𝑭 A ⟧c (return V , φ) = V ∈ 𝐺⟦ A ⟧v
  𝐺⟦ A ⇒ B ⟧c (clos⦅ ρ ,ƛ M ⦆ , φ) =
    ∀ {W : ClosVal} → W ∈ 𝐺⟦ A ⟧v → (ρ ∷ᵨ W , M , φ) ∈ 𝐺⟦ B ⟧e
  𝐺⟦ _ ⟧c _ = ⊥

  𝐺⟦_⟧e : CompType → Env n × Comp n × Eff → Set
  𝐺⟦ B ⟧e (ρ , M , φ) =
    ∃[ T ] ∃[ φ₁ ] ∃[ φ₂ ] ρ ⊢c M ⇓ T # φ₁ × (T , φ₂) ∈ 𝐺⟦ B ⟧c × φ₁ + φ₂ ≤ φ

𝐺⟦_⟧z : ValType → Env n × Val n → Set
𝐺⟦ A ⟧z (ρ , V) = ∃[ W ] ρ ⊢v V ⇓ W × W ∈ 𝐺⟦ A ⟧v

_⊨_ : ∀ {n : ℕ} → Ctx n → Env n → Set
_⊨_ {n} Γ ρ = ∀ (m : Fin n) → ρ m ∈ 𝐺⟦ Γ m ⟧v

infix 4 _⊨_

⊨-ext : Γ ⊨ ρ → W ∈ 𝐺⟦ A ⟧v → Γ ∷ A ⊨ ρ ∷ᵨ W
⊨-ext _ pf zero = pf
⊨-ext Γ⊨ρ _ (suc m) = Γ⊨ρ m

_⊨v_⦂_ : ∀ {n : ℕ} → Ctx n → Val n → ValType → Set
Γ ⊨v V ⦂ A = ∀ {ρ} → Γ ⊨ ρ → (ρ , V) ∈ 𝐺⟦ A ⟧z

infix 4 _⊨v_⦂_

_⊨c_⦂_#_ : ∀ {n : ℕ} → Ctx n → Comp n → CompType → Eff → Set
Γ ⊨c M ⦂ B # φ = ∀ {ρ} → Γ ⊨ ρ → (ρ , M , φ) ∈ 𝐺⟦ B ⟧e

infix 4 _⊨c_⦂_#_

semanticVar : Γ ⊨v ♯ m ⦂ Γ m
semanticVar {m = m} {ρ} ⊨ρ = ρ m , evalVar {m = m} , ⊨ρ m

semanticUnit : Γ ⊨v unit ⦂ 𝟙
semanticUnit _ = unit , evalUnit , tt

semanticThunk : Γ ⊨c M ⦂ B # φ
                ------------------
              → Γ ⊨v ⟪ M ⟫ ⦂ 𝑼 φ B
semanticThunk {M = M} ⊨M {ρ} ⊨ρ = clos⦅ ρ ,⟪ M ⟫⦆ , evalThunk , ⊨M ⊨ρ

semanticAbs : Γ ∷ A ⊨c M ⦂ B # φ
              --------------------
            → Γ ⊨c ƛ M ⦂ A ⇒ B # φ
semanticAbs {M = M} {φ = φ} ⊨M {ρ} ⊨ρ =
  clos⦅ ρ ,ƛ M ⦆ ,
  pure ,
  φ ,
  evalAbs ,
  (λ W∈𝐺⟦A⟧ → ⊨M (⊨-ext ⊨ρ W∈𝐺⟦A⟧) ) ,
  ≡→≤ +-pure-idˡ

semanticApp : Γ ⊨c M ⦂ A ⇒ B # φ
            → Γ ⊨v V ⦂ A
              ------------------
            → Γ ⊨c M · V ⦂ B # φ
semanticApp ⊨M ⊨V ⊨ρ
  with ⊨M ⊨ρ
...  | T′@(clos⦅ ρ′ ,ƛ M′ ⦆) , φ′ , ψ , M⇓ , pf , φ′+ψ≤φ
  with ⊨V ⊨ρ
...  | W , V⇓ , W∈𝐺⟦A⟧
  with pf W∈𝐺⟦A⟧
...  | T , ψ₁ , ψ₂ , M′⇓ , T,ψ∈𝐺⟦B⟧ , ψ₁+ψ₂≤ψ =
  T , φ′ + ψ₁ , ψ₂ , evalApp M⇓ V⇓ M′⇓ , T,ψ∈𝐺⟦B⟧ ,
    subeff-lemma
  where
    subeff-lemma =
      ≤-trans (≤-trans (≡→≤ +-assoc) (≤-+-compatibleˡ ψ₁+ψ₂≤ψ)) φ′+ψ≤φ

semanticSequence : Γ ⊨v V ⦂ 𝟙
                 → Γ ⊨c M ⦂ B # φ
                   ------------------
                 → Γ ⊨c V » M ⦂ B # φ
semanticSequence ⊨V ⊨M ⊨ρ
  with ⊨V ⊨ρ
...  | unit , V⇓ , _
  with ⊨M ⊨ρ
...  | T , φ₁ , φ₂ , M⇓ , T,φ₂∈𝐺⟦B⟧ , φ₁+φ₂≤φ =
    T , φ₁ , φ₂ , evalSeq V⇓ M⇓ , T,φ₂∈𝐺⟦B⟧ , φ₁+φ₂≤φ

semanticForce : Γ ⊨v V ⦂ 𝑼 φ′ B
              → φ′ ≤ φ
                ----------------
              → Γ ⊨c V ! ⦂ B # φ
semanticForce ⊨V φ′≤φ ⊨ρ
  with ⊨V ⊨ρ
...  | W@(clos⦅ ρ ,⟪ M ⟫⦆) , V⇓ , T , φ₁ , φ₂ , M⇓ , T∈𝐺 , φ₁+φ₂≤φ′ =
  T , φ₁ , φ₂ , evalForce V⇓ M⇓ , T∈𝐺 , ≤-trans φ₁+φ₂≤φ′ φ′≤φ

semanticRet : Γ ⊨v V ⦂ A
              -----------------------
            → Γ ⊨c return V ⦂ 𝑭 A # φ
semanticRet {φ = φ} ⊨V ⊨ρ
  with ⊨V ⊨ρ
...  |  W , V⇓ , W∈𝐺⟦A⟧ =
  return W , pure , φ , evalRet V⇓ , W∈𝐺⟦A⟧ , ≡→≤ +-pure-idˡ

semanticLetin : Γ ⊨c M ⦂ 𝑭 A # φ₁
              → Γ ∷ A ⊨c N ⦂ B # φ₂
              → φ₁ + φ₂ ≤ φ
                ---------------------
              → Γ ⊨c $⟵ M ⋯ N ⦂ B # φ
semanticLetin ⊨M ⊨N φ₁+φ₂≤φ ⊨ρ
  with ⊨M ⊨ρ
...  | T′@(return W) , φ₁₁ , φ₁₂ , M⇓ , W∈𝐺⟦A⟧ , φ₁₁+φ₁₂≤φ₁
  with ⊨N (⊨-ext ⊨ρ W∈𝐺⟦A⟧)
...  | T , φ₂₁ , φ₂₂ , N⇓ , T,φ₂₂∈𝐺⟦B⟧ , φ₂₁+φ₂₂≤φ₂ =
  T , φ₁₁ + φ₂₁ , φ₂₂ , evalLetin M⇓ N⇓ , T,φ₂₂∈𝐺⟦B⟧ ,
    subeff-lemma
  where
    subeff-lemma =
      ≤-trans
        (≤-trans (≡→≤ +-assoc) (≤-+-compatibleʳ (≤-+-invertʳ φ₁₁+φ₁₂≤φ₁)))
        (≤-trans (≤-+-compatibleˡ φ₂₁+φ₂₂≤φ₂) φ₁+φ₂≤φ)

semanticTick : ∀ {n : ℕ} {Γ : Ctx n} {φ : Eff}
             → tock ≤ φ
               -----------------
             → Γ ⊨c tick ⦂ 𝑭 𝟙 # φ
semanticTick tock≤φ _ = return unit , tock , pure , evalTick , tt , subeff-lemma
  where
    subeff-lemma = ≤-trans (≡→≤ +-pure-idʳ) tock≤φ
