open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; ∃; ∃-syntax; _,_)
open import Data.Unit using (⊤; tt)

open import CBPV.Base.Terms
open import CBPV.Base.Types
open import CBPV.Base.SyntacticTyping
open import CBPV.Base.Semantics

module CBPV.Base.SemanticTyping where

mutual
  _∈-𝐺⟦_⟧v : ClosVal → ValType → Set
  unit ∈-𝐺⟦ 𝟙 ⟧v = ⊤
  clos⦅ ρ ,⟪ M ⟫⦆ ∈-𝐺⟦ 𝑼 B ⟧v = (ρ , M) ∈-𝐺⟦ B ⟧e

  unit ∈-𝐺⟦ 𝑼 _ ⟧v = ⊥
  clos⦅ _ ,⟪ _ ⟫⦆ ∈-𝐺⟦ 𝟙 ⟧v = ⊥

  _∈-𝐺⟦_⟧c : ClosTerminal → CompType → Set
  (return V) ∈-𝐺⟦ 𝑭 A ⟧c = V ∈-𝐺⟦ A ⟧v
  clos⦅ ρ ,ƛ M ⦆ ∈-𝐺⟦ A ⇒ B ⟧c =
    ∀ {W : ClosVal} → W ∈-𝐺⟦ A ⟧v → ρ ∷ᵨ W , M ∈-𝐺⟦ B ⟧e

  (return _) ∈-𝐺⟦ _ ⇒ _ ⟧c = ⊥
  clos⦅ _ ,ƛ _ ⦆ ∈-𝐺⟦ 𝑭 _ ⟧c = ⊥

  _∈-𝐺⟦_⟧e : ∀ {n : ℕ} → Env n × Comp n → CompType → Set
  ρ , M ∈-𝐺⟦ B ⟧e = ∃[ T ] ρ ∣ M ⇓c T × T ∈-𝐺⟦ B ⟧c

_∈-𝐺⟦_⟧z : ∀ {n : ℕ} → Env n × Val n → ValType → Set
ρ , V ∈-𝐺⟦ A ⟧z = ∃[ W ] ρ ∣ V ⇓v W × W ∈-𝐺⟦ A ⟧v

infix 4 _∈-𝐺⟦_⟧v
infix 4 _∈-𝐺⟦_⟧c
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

_⊨c_⦂_ : ∀ {n : ℕ} → Ctx n → Comp n → CompType → Set
_⊨c_⦂_ {n} Γ M B = ∀ {ρ : Env n} → Γ ⊨ ρ → ρ , M ∈-𝐺⟦ B ⟧e

infix 4 _⊨c_⦂_

semanticVar : ∀ {n : ℕ} {Γ : Ctx n} {m : Fin n}
              --------------
            → Γ ⊨v # m ⦂ Γ m
semanticVar {m = m} {ρ = ρ} Γ⊨ρ = ρ m , evalVar {W = ρ m} , Γ⊨ρ m

semanticUnit : ∀ {n : ℕ} {Γ : Ctx n}
               -------------
             → Γ ⊨v unit ⦂ 𝟙
semanticUnit _ = unit , evalUnit , tt

semanticThunk : ∀ {n : ℕ} {Γ : Ctx n} {M : Comp n} {B : CompType}
              → Γ ⊨c M ⦂ B
                ----------------
              → Γ ⊨v ⟪ M ⟫ ⦂ 𝑼 B
semanticThunk {M = M} Γ⊨M⦂B {ρ} Γ⊨ρ = clos⦅ ρ ,⟪ M ⟫⦆ , evalThunk , Γ⊨M⦂B Γ⊨ρ

semanticAbs : ∀ {n : ℕ} {Γ : Ctx n} {A : ValType} {M : Comp (suc n)}
                {B : CompType}
            → Γ ∷ A ⊨c M ⦂ B
              ----------------
            → Γ ⊨c ƛ M ⦂ A ⇒ B
semanticAbs {M = M} Γ∷A⊨M⦂B {ρ} Γ⊨ρ =
  clos⦅ ρ ,ƛ M ⦆ , evalAbs , λ{ W∈𝐺⟦A⟧e → Γ∷A⊨M⦂B (⊨-ext Γ⊨ρ W∈𝐺⟦A⟧e) }

semanticApp : ∀ {n : ℕ} {Γ : Ctx n} {M : Comp n} {A : ValType} {B : CompType}
                {V : Val n}
            → Γ ⊨c M ⦂ A ⇒ B
            → Γ ⊨v V ⦂ A
              --------------
            → Γ ⊨c M · V ⦂ B
semanticApp Γ⊨M⦂A⇒B Γ⊨V⦂A Γ⊨ρ
  with Γ⊨M⦂A⇒B Γ⊨ρ
... | T′@(clos⦅ ρ′ ,ƛ M′ ⦆) , ρ∣M⇓T′ , pf
  with Γ⊨V⦂A Γ⊨ρ
...  | W , ρ∣V⇓vW , W∈𝐺⟦A⟧v
  with pf W∈𝐺⟦A⟧v
...  | T , ρ′∷ᵨW∣M′⇓T , T∈𝐺⟦B⟧c =
  T , evalApp ρ∣M⇓T′ ρ∣V⇓vW ρ′∷ᵨW∣M′⇓T , T∈𝐺⟦B⟧c

semanticSeq : ∀ {n : ℕ} {Γ : Ctx n} {V : Val n} {M : Comp n} {B : CompType}
            → Γ ⊨v V ⦂ 𝟙
            → Γ ⊨c M ⦂ B
              --------------
            → Γ ⊨c V » M ⦂ B
semanticSeq Γ⊨V⦂𝟙 Γ⊨M⦂B Γ⊨ρ
  with Γ⊨V⦂𝟙 Γ⊨ρ
...  | unit , ρ∣V⇓unit , _
  with Γ⊨M⦂B Γ⊨ρ
...  | T , ρ∣M⇓T , T∈𝐺⟦B⟧c =
  T , evalSeq ρ∣V⇓unit ρ∣M⇓T , T∈𝐺⟦B⟧c

semanticForce : ∀ {n : ℕ} {Γ : Ctx n} {V : Val n} {B : CompType}
              → Γ ⊨v V ⦂ 𝑼 B
                ------------
              → Γ ⊨c V ! ⦂ B
semanticForce Γ⊨V⦂𝑼B Γ⊨ρ
  with Γ⊨V⦂𝑼B Γ⊨ρ
...  | W@(clos⦅ ρ ,⟪ M ⟫⦆) , ρ∣V⇓W , T , ρ|M⇓T , T∈𝐺⟦B⟧c =
  T , evalForce ρ∣V⇓W ρ|M⇓T , T∈𝐺⟦B⟧c

semanticRet : ∀ {n : ℕ} {Γ : Ctx n} {V : Val n} {A : ValType}
            → Γ ⊨v V ⦂ A
            → Γ ⊨c return V ⦂ 𝑭 A
semanticRet Γ⊨V⦂A Γ⊨ρ
  with Γ⊨V⦂A Γ⊨ρ
... | W , ρ∣V⇓W , W∈𝐺⟦A⟧v =
  return W , evalRet ρ∣V⇓W , W∈𝐺⟦A⟧v

semanticLetin : ∀ {n : ℕ} {Γ : Ctx n} {M : Comp n} {A : ValType}
                  {N : Comp (suc n)} {B : CompType}
              → Γ ⊨c M ⦂ 𝑭 A
              → Γ ∷ A ⊨c N ⦂ B
              → Γ ⊨c $⇐ M ⋯ N ⦂ B
semanticLetin Γ⊨M⦂𝑭A Γ∷A⊨N⦂B Γ⊨ρ
  with Γ⊨M⦂𝑭A Γ⊨ρ
...  | T′@(return W) , ρ∣M⇓T′ , W∈𝐺⟦A⟧v
  with Γ∷A⊨N⦂B (⊨-ext Γ⊨ρ W∈𝐺⟦A⟧v)
...  | T , ρ∷W∣N⇓T , T∈𝐺⟦B⟧c =
  T , evalLetin ρ∣M⇓T′ ρ∷W∣N⇓T , T∈𝐺⟦B⟧c
