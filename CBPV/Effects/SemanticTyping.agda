open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; ∃; ∃-syntax; _,_)
open import Data.Unit using (⊤; tt)

open import CBPV.Effects.Terms
open import Effects

module CBPV.Effects.SemanticTyping (E : Effect) where

open import CBPV.Effects.Semantics E
open import CBPV.Effects.SyntacticTyping E
open import CBPV.Effects.Types E
open Effect E
open Properties E

mutual
  _∈-𝐺⟦_⟧v : ClosVal → ValType → Set
  unit ∈-𝐺⟦ 𝟙 ⟧v = ⊤
  clos⦅ ρ ,⟪ M ⟫⦆ ∈-𝐺⟦ 𝑼 φ B ⟧v = ρ , M , φ ∈-𝐺⟦ B ⟧e

  unit ∈-𝐺⟦ 𝑼 _ _ ⟧v = ⊥
  clos⦅ _ ,⟪ _ ⟫⦆ ∈-𝐺⟦ 𝟙 ⟧v = ⊥

  _∈-𝐺⟦_⟧c : ClosTerminal × Eff → CompType → Set
  (return V) , φ ∈-𝐺⟦ 𝑭 A ⟧c = V ∈-𝐺⟦ A ⟧v
  clos⦅ ρ ,ƛ M ⦆ , φ ∈-𝐺⟦ A ⇒ B ⟧c =
    ∀ {W : ClosVal} → W ∈-𝐺⟦ A ⟧v → ρ ∷ᵨ W , M , φ ∈-𝐺⟦ B ⟧e

  (return _) , _ ∈-𝐺⟦ _ ⇒ _ ⟧c = ⊥
  clos⦅ _ ,ƛ _ ⦆ , _ ∈-𝐺⟦ 𝑭 _ ⟧c = ⊥

  _∈-𝐺⟦_⟧e : ∀ {n : ℕ} → Env n × Comp n × Eff → CompType → Set
  ρ , M , φ ∈-𝐺⟦ B ⟧e =
    ∃[ T ] ∃[ φ₁ ] ∃[ φ₂ ] ρ ∣ M ⇓c T # φ₁ × T , φ₂ ∈-𝐺⟦ B ⟧c × φ₁ + φ₂ ≤ φ

_∈-𝐺⟦_⟧z : ∀ {n : ℕ} → Env n × Val n → ValType → Set
ρ , V ∈-𝐺⟦ A ⟧z = ∃[ W ] ρ ∣ V ⇓v W × W ∈-𝐺⟦ A ⟧v

infix 4 _∈-𝐺⟦_⟧v
infix 3 _∈-𝐺⟦_⟧c
infix 3 _∈-𝐺⟦_⟧e
infix 3 _∈-𝐺⟦_⟧z

_⊨_ : ∀ {n : ℕ} → Ctx n → Env n → Set
_⊨_ {n} Γ ρ = ∀ (m : Fin n) → ρ m ∈-𝐺⟦ Γ m ⟧v

infix 4 _⊨_

⊨-ext : ∀ {n : ℕ} {Γ : Ctx n} {ρ : Env n} {W : ClosVal} {A : ValType}
      → Γ ⊨ ρ
      → W ∈-𝐺⟦ A ⟧v
      → Γ ∷ A ⊨ ρ ∷ᵨ W
⊨-ext _ pf zero = pf
⊨-ext Γ⊨ρ _ (suc m) = Γ⊨ρ m

_⊨v_⦂_ : ∀ {n : ℕ} → Ctx n → Val n → ValType → Set
_⊨v_⦂_ {n} Γ V A = ∀ {ρ : Env n} → Γ ⊨ ρ → ρ , V ∈-𝐺⟦ A ⟧z

infix 4 _⊨v_⦂_

_⊨c_⦂_#_ : ∀ {n : ℕ} → Ctx n → Comp n → CompType → Eff → Set
_⊨c_⦂_#_ {n} Γ M B φ = ∀ {ρ : Env n} → Γ ⊨ ρ → ρ , M , φ ∈-𝐺⟦ B ⟧e

infix 4 _⊨c_⦂_#_

semanticVar : ∀ {n : ℕ} {Γ : Ctx n} {m : Fin n}
              --------------
            → Γ ⊨v ♯ m ⦂ Γ m
semanticVar {m = m} {ρ} Γ⊨ρ = W , evalVar {W = W} , W∈𝐺⟦A⟧v where
  W = ρ m
  W∈𝐺⟦A⟧v = Γ⊨ρ m

semanticUnit : ∀ {n : ℕ} {Γ : Ctx n}
               -------------
             → Γ ⊨v unit ⦂ 𝟙
semanticUnit _ = unit , evalUnit , tt

semanticThunk : ∀ {n : ℕ} {Γ : Ctx n} {M : Comp n} {B : CompType} {φ : Eff}
              → Γ ⊨c M ⦂ B # φ
                ------------------
              → Γ ⊨v ⟪ M ⟫ ⦂ 𝑼 φ B
semanticThunk {M = M} Γ⊨M⦂B#φ {ρ} Γ⊨ρ = clos⦅ ρ ,⟪ M ⟫⦆ , evalThunk , Γ⊨M⦂B#φ Γ⊨ρ

semanticAbs : ∀ {n : ℕ} {Γ : Ctx n} {A : ValType} {M : Comp (suc n)}
                {B : CompType} {φ : Eff}
            → Γ ∷ A ⊨c M ⦂ B # φ
              --------------------
            → Γ ⊨c ƛ M ⦂ A ⇒ B # φ
semanticAbs {M = M} {φ = φ} Γ∷A⊨M⦂B#φ {ρ} Γ⊨ρ =
  clos⦅ ρ ,ƛ M ⦆ , pure , φ , evalAbs ,
    (λ W∈𝐺⟦A⟧v → Γ∷A⊨M⦂B#φ (⊨-ext Γ⊨ρ W∈𝐺⟦A⟧v) ) , subeff-lemma
  where
    subeff-lemma = ≡→≤ +-pure-idˡ

semanticApp : ∀ {n : ℕ} {Γ : Ctx n} {M : Comp n} {A : ValType} {B : CompType}
                {φ : Eff} {V : Val n}
            → Γ ⊨c M ⦂ A ⇒ B # φ
            → Γ ⊨v V ⦂ A
              ------------------
            → Γ ⊨c M · V ⦂ B # φ
semanticApp Γ⊨M⦂A⇒B#φ Γ⊨V⦂A Γ⊨ρ
  with Γ⊨M⦂A⇒B#φ Γ⊨ρ
...  | T′@(clos⦅ ρ′ ,ƛ M′ ⦆) , φ′ , ψ , ρ∣M⇓T′#φ′ , pf , φ′+ψ≤φ
  with Γ⊨V⦂A Γ⊨ρ
...  | W , ρ∣V⇓W , W∈𝐺⟦A⟧v
  with pf W∈𝐺⟦A⟧v
...  | T , ψ₁ , ψ₂ , ρ′∷W∣M′⇓T#ψ₂ , T,ψ∈𝐺⟦B⟧v , ψ₁+ψ₂≤ψ =
  T , φ′ + ψ₁ , ψ₂ , evalApp ρ∣M⇓T′#φ′ ρ∣V⇓W ρ′∷W∣M′⇓T#ψ₂ , T,ψ∈𝐺⟦B⟧v ,
    subeff-lemma
  where
    subeff-lemma =
      ≤-trans (≤-trans (≡→≤ +-assoc) (≤-+-compatibleˡ ψ₁+ψ₂≤ψ)) φ′+ψ≤φ

semanticSequence : ∀ {n : ℕ} {Γ : Ctx n} {V : Val n} {M : Comp n} {B : CompType}
                     {φ : Eff}
                 → Γ ⊨v V ⦂ 𝟙
                 → Γ ⊨c M ⦂ B # φ
                   ------------------
                 → Γ ⊨c V » M ⦂ B # φ
semanticSequence Γ⊨V⦂𝟙 Γ⊨M⦂B Γ⊨ρ
  with Γ⊨V⦂𝟙 Γ⊨ρ
...  | unit , ρ∣V⇓unit , _
  with Γ⊨M⦂B Γ⊨ρ
...  | T , φ₁ , φ₂ , ρ∣M⇓T#φ₁ , T,φ₂∈𝐺⟦B⟧c , φ₁+φ₂≤φ =
    T , φ₁ , φ₂ , evalSeq ρ∣V⇓unit ρ∣M⇓T#φ₁ , T,φ₂∈𝐺⟦B⟧c , φ₁+φ₂≤φ

semanticForce : ∀ {n : ℕ} {Γ : Ctx n} {V : Val n} {φ φ′ : Eff} {B : CompType}
              → Γ ⊨v V ⦂ 𝑼 φ′ B
              → φ′ ≤ φ
                ----------------
              → Γ ⊨c V ! ⦂ B # φ
semanticForce Γ⊨V⦂𝑼φ′B φ′≤φ Γ⊨ρ
  with Γ⊨V⦂𝑼φ′B Γ⊨ρ
...  | W@(clos⦅ ρ ,⟪ M ⟫⦆) , V⇓W , T , φ₁ , φ₂ , M⇓T , T∈𝐺 , φ₁+φ₂≤φ′ =
  T , φ₁ , φ₂ , evalForce V⇓W M⇓T , T∈𝐺 , ≤-trans φ₁+φ₂≤φ′ φ′≤φ

semanticRet : ∀ {n : ℕ} {Γ : Ctx n} {V : Val n} {A : ValType} {φ : Eff}
            → Γ ⊨v V ⦂ A
              -----------------------
            → Γ ⊨c return V ⦂ 𝑭 A # φ
semanticRet {φ = φ} Γ⊨V⦂A Γ⊨ρ
  with Γ⊨V⦂A Γ⊨ρ
...  |  W , ρ∣V⇓W , W∈𝐺⟦A⟧v =
  return W , pure , φ , evalRet ρ∣V⇓W , W∈𝐺⟦A⟧v , subeff-lemma
  where
    subeff-lemma = ≡→≤ +-pure-idˡ

semanticLetin : ∀ {n : ℕ} {Γ : Ctx n} {M : Comp n} {A : ValType} {φ₁ φ₂ φ : Eff}
                  {N : Comp (suc n)} {B : CompType}
              → Γ ⊨c M ⦂ 𝑭 A # φ₁
              → Γ ∷ A ⊨c N ⦂ B # φ₂
              → φ₁ + φ₂ ≤ φ
                ---------------------
              → Γ ⊨c $⟵ M ⋯ N ⦂ B # φ
semanticLetin Γ⊨M⦂𝑭A#φ₁ Γ∷A⊨N⦂B#φ₂ φ₁+φ₂≤φ Γ⊨ρ
  with Γ⊨M⦂𝑭A#φ₁ Γ⊨ρ
...  | T′@(return W) , φ₁₁ , φ₁₂ , ρ∣M⇓T′#φ₁₁ , W∈𝐺⟦A⟧v , φ₁₁+φ₁₂≤φ₁
  with Γ∷A⊨N⦂B#φ₂ (⊨-ext Γ⊨ρ W∈𝐺⟦A⟧v)
...  | T , φ₂₁ , φ₂₂ , ρ∷W∣N⇓T#φ₂₁ , T,φ₂₂∈𝐺⟦B⟧c , φ₂₁+φ₂₂≤φ₂ =
  T , φ₁₁ + φ₂₁ , φ₂₂ , evalLetin ρ∣M⇓T′#φ₁₁ ρ∷W∣N⇓T#φ₂₁ , T,φ₂₂∈𝐺⟦B⟧c ,
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
