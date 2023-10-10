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
  𝒲⟦_⟧ : ValType → ClosVal → Set
  𝒲⟦ 𝟙 ⟧ unit = ⊤
  𝒲⟦ 𝑼 φ B ⟧ clos⦅ ρ ,⟪ M ⟫⦆ = (ρ , M , φ) ∈ ℳ⟦ B ⟧
  𝒲⟦ A₁ * A₂ ⟧ ⟨ W₁ , W₂ ⟩ = W₁ ∈ 𝒲⟦ A₁ ⟧ × W₂ ∈ 𝒲⟦ A₂ ⟧
  𝒲⟦ A₁ ∪ A₂ ⟧ (inl W) = W ∈ 𝒲⟦ A₁ ⟧
  𝒲⟦ A₁ ∪ A₂ ⟧ (inr W) = W ∈ 𝒲⟦ A₂ ⟧
  𝒲⟦ _ ⟧ _ = ⊥

  𝒯⟦_⟧ : CompType → ClosTerminal × Eff → Set
  𝒯⟦ 𝑭 A ⟧ (return V , φ) = V ∈ 𝒲⟦ A ⟧
  𝒯⟦ A ⇒ B ⟧ (clos⦅ ρ ,ƛ M ⦆ , φ) =
    ∀ {W : ClosVal} → W ∈ 𝒲⟦ A ⟧ → (ρ ∷ᵨ W , M , φ) ∈ ℳ⟦ B ⟧
  𝒯⟦ B₁ & B₂ ⟧ (clos⦅ ρ ,⟨ M₁ , M₂ ⟩⦆ , φ) =
    (ρ , M₁ , φ) ∈ ℳ⟦ B₁ ⟧ × (ρ , M₂ , φ) ∈ ℳ⟦ B₂ ⟧
  𝒯⟦ _ ⟧ _ = ⊥

  ℳ⟦_⟧ : CompType → Env n × Comp n × Eff → Set
  ℳ⟦ B ⟧ (ρ , M , φ) =
    ∃[ T ] ∃[ φ₁ ] ∃[ φ₂ ] ρ ⊢c M ⇓ T # φ₁ × (T , φ₂) ∈ 𝒯⟦ B ⟧ × φ₁ + φ₂ ≤ φ

𝒱⟦_⟧ : ValType → Env n × Val n → Set
𝒱⟦ A ⟧ (ρ , V) = ∃[ W ] ρ ⊢v V ⇓ W × W ∈ 𝒲⟦ A ⟧

_⊨_ : ∀ {n : ℕ} → Ctx n → Env n → Set
_⊨_ {n} Γ ρ = ∀ (m : Fin n) → ρ m ∈ 𝒲⟦ Γ m ⟧

infix 4 _⊨_

⊨-ext : Γ ⊨ ρ → W ∈ 𝒲⟦ A ⟧ → Γ ∷ A ⊨ ρ ∷ᵨ W
⊨-ext _ pf zero = pf
⊨-ext Γ⊨ρ _ (suc m) = Γ⊨ρ m

_⊨v_⦂_ : ∀ {n : ℕ} → Ctx n → Val n → ValType → Set
Γ ⊨v V ⦂ A = ∀ {ρ} → Γ ⊨ ρ → (ρ , V) ∈ 𝒱⟦ A ⟧

infix 4 _⊨v_⦂_

_⊨c_⦂_#_ : ∀ {n : ℕ} → Ctx n → Comp n → CompType → Eff → Set
Γ ⊨c M ⦂ B # φ = ∀ {ρ} → Γ ⊨ ρ → (ρ , M , φ) ∈ ℳ⟦ B ⟧

infix 4 _⊨c_⦂_#_

semanticVar : Γ ⊨v ♯ m ⦂ Γ m
semanticVar {m = m} {ρ} ⊨ρ = ρ m , evalVar {m = m} , ⊨ρ m

semanticUnit : Γ ⊨v unit ⦂ 𝟙
semanticUnit _ = unit , evalUnit , tt

semanticThunk : Γ ⊨c M ⦂ B # φ
                ------------------
              → Γ ⊨v ⟪ M ⟫ ⦂ 𝑼 φ B
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

semanticAbs : Γ ∷ A ⊨c M ⦂ B # φ
              --------------------
            → Γ ⊨c ƛ M ⦂ A ⇒ B # φ
semanticAbs {M = M} {φ = φ} ⊨M {ρ} ⊨ρ =
  clos⦅ ρ ,ƛ M ⦆ ,
  pure ,
  φ ,
  evalAbs ,
  (λ W∈𝒲 → ⊨M (⊨-ext ⊨ρ W∈𝒲) ) ,
  ≡→≤ +-pure-idˡ

semanticApp : Γ ⊨c M ⦂ A ⇒ B # φ
            → Γ ⊨v V ⦂ A
              ------------------
            → Γ ⊨c M · V ⦂ B # φ
semanticApp ⊨M ⊨V ⊨ρ
  with ⊨M ⊨ρ
...  | T′@(clos⦅ ρ′ ,ƛ M′ ⦆) , φ′ , ψ , M⇓ , pf , φ′+ψ≤φ
  with ⊨V ⊨ρ
...  | W , V⇓ , W∈𝒲
  with pf W∈𝒲
...  | T , ψ₁ , ψ₂ , M′⇓ , T∈𝒯 , ψ₁+ψ₂≤ψ =
  T , φ′ + ψ₁ , ψ₂ , evalApp M⇓ V⇓ M′⇓ , T∈𝒯 ,
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
...  | T , φ₁ , φ₂ , M⇓ , T∈𝒯 , φ₁+φ₂≤φ =
    T , φ₁ , φ₂ , evalSeq V⇓ M⇓ , T∈𝒯 , φ₁+φ₂≤φ

semanticCpair : Γ ⊨c M₁ ⦂ B₁ # φ
              → Γ ⊨c M₂ ⦂ B₂ # φ
                ------------------------------
              → Γ ⊨c ⟨ M₁ , M₂ ⟩ ⦂ B₁ & B₂ # φ
semanticCpair {M₁ = M₁} {φ = φ} {M₂ = M₂} ⊨M₁ ⊨M₂ {ρ} ⊨ρ =
  clos⦅ ρ ,⟨ M₁ , M₂ ⟩⦆ , pure , φ , evalCpair , (⊨M₁ ⊨ρ , ⊨M₂ ⊨ρ) , ≡→≤ +-pure-idˡ

semanticProjl : Γ ⊨c M ⦂ B₁ & B₂ # φ
                ---------------------
              → Γ ⊨c projl M ⦂ B₁ # φ
semanticProjl ⊨M ⊨ρ
  with ⊨M ⊨ρ
...  | clos⦅ _ ,⟨ M₁ , _ ⟩⦆ , φ₁ , φ₂ , M⇓ , ((T₁ , ψ₁ , ψ₂ , M₁⇓ , T₁∈𝒯 , ψ₁+ψ₂≤φ₂) , _) , φ₁+φ₂≤φ =
  T₁ , φ₁ + ψ₁ , ψ₂ , evalProjl M⇓ M₁⇓ , T₁∈𝒯 , subeff-lemma
  where
    subeff-lemma =
      ≤-trans (≡→≤ +-assoc) (≤-trans (≤-+-compatibleˡ ψ₁+ψ₂≤φ₂) φ₁+φ₂≤φ)

semanticProjr : Γ ⊨c M ⦂ B₁ & B₂ # φ
                ---------------------
              → Γ ⊨c projr M ⦂ B₂ # φ
semanticProjr ⊨M ⊨ρ
  with ⊨M ⊨ρ
...  | clos⦅ _ ,⟨ M₁ , _ ⟩⦆ , φ₁ , φ₂ , M⇓ , (_ , (T₂ , ψ₁ , ψ₂ , M₂⇓ , T₂∈𝒯 , ψ₁+ψ₂≤φ₂)) , φ₁+φ₂≤φ =
  T₂ , φ₁ + ψ₁ , ψ₂ , evalProjr M⇓ M₂⇓ , T₂∈𝒯 , subeff-lemma
  where
    subeff-lemma =
      ≤-trans (≡→≤ +-assoc) (≤-trans (≤-+-compatibleˡ ψ₁+ψ₂≤φ₂) φ₁+φ₂≤φ)

semanticForce : Γ ⊨v V ⦂ 𝑼 φ′ B
              → φ′ ≤ φ
                ----------------
              → Γ ⊨c V ! ⦂ B # φ
semanticForce ⊨V φ′≤φ ⊨ρ
  with ⊨V ⊨ρ
...  | W@(clos⦅ ρ ,⟪ M ⟫⦆) , V⇓ , T , φ₁ , φ₂ , M⇓ , T∈𝒯 , φ₁+φ₂≤φ′ =
  T , φ₁ , φ₂ , evalForce V⇓ M⇓ , T∈𝒯 , ≤-trans φ₁+φ₂≤φ′ φ′≤φ

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
...  | T′@(return W) , φ₁₁ , φ₁₂ , M⇓ , W∈𝒲 , φ₁₁+φ₁₂≤φ₁
  with ⊨N (⊨-ext ⊨ρ W∈𝒲)
...  | T , φ₂₁ , φ₂₂ , N⇓ , T∈𝒯 , φ₂₁+φ₂₂≤φ₂ =
  T , φ₁₁ + φ₂₁ , φ₂₂ , evalLetin M⇓ N⇓ , T∈𝒯 ,
    subeff-lemma
  where
    subeff-lemma =
      ≤-trans
        (≤-trans (≡→≤ +-assoc) (≤-+-compatibleʳ (≤-+-invertʳ φ₁₁+φ₁₂≤φ₁)))
        (≤-trans (≤-+-compatibleˡ φ₂₁+φ₂₂≤φ₂) φ₁+φ₂≤φ)

semanticSplit : Γ ⊨v V ⦂ A₁ * A₂
              → Γ ∷ A₁ ∷ A₂ ⊨c M ⦂ B # φ
                ------------------------
              → Γ ⊨c $≔ V ⋯ M ⦂ B # φ
semanticSplit ⊨V ⊨M ⊨ρ
  with ⊨V ⊨ρ
...  | ⟨ W₁ , W₂ ⟩ , V⇓ , (W₁∈𝒲 , W₂∈𝒲)
  with ⊨M (⊨-ext (⊨-ext ⊨ρ W₁∈𝒲) W₂∈𝒲)
...  | T , φ₁ , φ₂ , M⇓ , T∈𝒯 , φ₁+φ₂≤φ =
  T , φ₁ , φ₂ , evalSplit V⇓ M⇓ , T∈𝒯 , φ₁+φ₂≤φ

semanticCase : Γ ⊨v V ⦂ A₁ ∪ A₂
             → Γ ∷ A₁ ⊨c M₁ ⦂ B # φ
             → Γ ∷ A₂ ⊨c M₂ ⦂ B # φ
               -----------------------------------
             → Γ ⊨c case V inl⇒ M₁ inr⇒ M₂ ⦂ B # φ
semanticCase ⊨V ⊨M₁ ⊨M₂ ⊨ρ
  with ⊨V ⊨ρ
... | inl W , V⇓ , W∈𝒲 =
  let (T , φ₁ , φ₂ , M₁⇓ , T∈𝒯 , φ₁+φ₂≤φ) = ⊨M₁ (⊨-ext ⊨ρ W∈𝒲) in
  T , φ₁ , φ₂ , evalCaseInl V⇓ M₁⇓ , T∈𝒯 , φ₁+φ₂≤φ
... | inr W , V⇓ , W∈𝒲 =
  let (T , φ₁ , φ₂ , M₂⇓ , T∈𝒯 , φ₁+φ₂≤φ) = ⊨M₂ (⊨-ext ⊨ρ W∈𝒲) in
  T , φ₁ , φ₂ , evalCaseInr V⇓ M₂⇓ , T∈𝒯 , φ₁+φ₂≤φ

semanticTick : ∀ {n : ℕ} {Γ : Ctx n} {φ : Eff}
             → tock ≤ φ
               -----------------
             → Γ ⊨c tick ⦂ 𝑭 𝟙 # φ
semanticTick tock≤φ _ = return unit , tock , pure , evalTick , tt , subeff-lemma
  where
    subeff-lemma = ≤-trans (≡→≤ +-pure-idʳ) tock≤φ
