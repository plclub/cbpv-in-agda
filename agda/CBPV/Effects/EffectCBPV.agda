open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_×_; ∃; ∃-syntax; _,_)
open import Data.Unit using (⊤; tt)

open import Effects

module CBPV.Effectful.EffectCBPV (E : Effect) where

open Effect E
open Properties E

-- Types

mutual
  data ValType : Set where
    𝟙 : ValType
    𝑼 : Eff → CompType → ValType

  data CompType : Set where
    _⇒_ : ValType → CompType → CompType
    𝑭 : ValType → CompType

infixr 7 _⇒_

-- Terms

mutual
  data Val (n : ℕ) : Set where
    ♯_ : Fin n → Val n
    unit : Val n
    ⟪_⟫ : Comp n → Val n

  data Comp (n : ℕ) : Set where
    ƛ_ : Comp (suc n) → Comp n
    _·_ : Comp n → Val n → Comp n
    _»_ : Val n → Comp n → Comp n
    _! : Val n → Comp n
    return_ : Val n → Comp n
    $⇐_⋯_ : Comp n → Comp (suc n) → Comp n
    tick : Comp n

infix 5 ƛ_
infixl 7 _»_
infix 6 _!
infix 6 return_
infixl 7 _·_
infix 9 ♯_
infixr 4 $⇐_⋯_
infix 5 ⟪_⟫

-- Typing contexts

Ctx : ℕ → Set
Ctx n = Fin n → ValType

∅ : Ctx zero
∅ ()

_∷_ : ∀ {n : ℕ} → Ctx n → ValType → Ctx (suc n)
Γ ∷ A = λ where
          zero → A
          (suc n) → Γ n

infixl 5 _∷_

-- Syntactic typing rules

mutual
  data _⊢v_⦂_ {n : ℕ} (Γ : Ctx n) : Val n → ValType → Set where
    typeVar : ∀ {m : Fin n}
              --------------
            → Γ ⊢v ♯ m ⦂ Γ m

    typeUnit : Γ ⊢v unit ⦂ 𝟙

    typeThunk : ∀ {M : Comp n} {B : CompType} {φ : Eff}
              → Γ ⊢c M ⦂ B # φ
                ----------------
              → Γ ⊢v ⟪ M ⟫ ⦂ 𝑼 φ B

  data _⊢c_⦂_#_ {n : ℕ} (Γ : Ctx n) : Comp n → CompType → Eff → Set where
    typeAbs : ∀ {A : ValType} {M : Comp (suc n)} {B : CompType}
                {φ : Eff}
            → Γ ∷ A ⊢c M ⦂ B # φ
              ----------------
            → Γ ⊢c ƛ M ⦂ A ⇒ B # φ

    typeApp : ∀ {M : Comp n} {A : ValType} {B : CompType} {V : Val n} {φ : Eff}
            → Γ ⊢c M ⦂ A ⇒ B # φ
            → Γ ⊢v V ⦂ A
              --------------
            → Γ ⊢c M · V ⦂ B # φ

    typeSequence : ∀ {V : Val n} {M : Comp n} {B : CompType} {φ : Eff}
                 → Γ ⊢v V ⦂ 𝟙
                 → Γ ⊢c M ⦂ B # φ
                   --------------
                 → Γ ⊢c V » M ⦂ B # φ

    typeForce : ∀ {V : Val n} {B : CompType} {φ₁ φ₂ : Eff}
              → Γ ⊢v V ⦂ 𝑼 φ₁ B
              → φ₁ ≤ φ₂
                ------------
              → Γ ⊢c V ! ⦂ B # φ₂

    typeRet : ∀ {V : Val n} {A : ValType} {φ : Eff}
            → Γ ⊢v V ⦂ A
              -------------------
            → Γ ⊢c return V ⦂ 𝑭 A # φ
    typeLetin : ∀ {M : Comp n} {A : ValType} {N : Comp (suc n)} {B : CompType}
                  {φ₁ φ₂ φ : Eff}
              → Γ ⊢c M ⦂ 𝑭 A # φ₁
              → Γ ∷ A ⊢c N ⦂ B # φ₂
              → φ₁ + φ₂ ≤ φ
                ------------------
              → Γ ⊢c $⇐ M ⋯ N ⦂ B # φ

    typeTick : ∀ {φ : Eff}
             → tock ≤ φ
               -----------------------
             → Γ ⊢c tick ⦂ 𝑭 𝟙 # φ

infix 4 _⊢v_⦂_
infix 4 _⊢c_⦂_#_

-- Subeffecting well-typed terms

type-subeff : ∀ {n : ℕ} {Γ : Ctx n} {M : Comp n} {B : CompType} {φ ψ : Eff}
            → Γ ⊢c M ⦂ B # φ
            → φ ≤ ψ
            → Γ ⊢c M ⦂ B # ψ
type-subeff (typeAbs pf) φ≤ψ = typeAbs (type-subeff pf φ≤ψ)
type-subeff (typeApp pf₁ pf₂) φ≤ψ = typeApp (type-subeff pf₁ φ≤ψ) pf₂
type-subeff (typeSequence pf₁ pf₂) φ≤ψ = typeSequence pf₁ (type-subeff pf₂ φ≤ψ)
type-subeff (typeForce pf φ₁≤φ₂) φ₂≤φ₃ = typeForce pf (≤-trans φ₁≤φ₂ φ₂≤φ₃)
type-subeff (typeRet pf) φ≤ψ = typeRet pf
type-subeff (typeLetin pf₁ pf₂ φ₁+φ₂≤φ) φ≤ψ =
  typeLetin pf₁ pf₂ (≤-trans φ₁+φ₂≤φ φ≤ψ)
type-subeff (typeTick tock) φ≤ψ = typeTick (≤-trans tock φ≤ψ)

mutual
  -- Closed values

  data ClosVal : Set where
    unit : ClosVal

    clos⦅_,⟪_⟫⦆ : ∀ {n : ℕ} → Env n → Comp n → ClosVal

  -- Closed terminals

  data ClosTerminal : Set where
    return_ : ClosVal → ClosTerminal

    clos⦅_,ƛ_⦆ : ∀ {n : ℕ} → Env n → Comp (suc n) → ClosTerminal

  -- Environments

  Env : ℕ → Set
  Env n = Fin n → ClosVal

∅ᵨ : Env zero
∅ᵨ ()

_∷ᵨ_ : ∀ {n : ℕ} → Env n → ClosVal → Env (suc n)
ρ ∷ᵨ W = λ where
          zero → W
          (suc n) → ρ n

infixl 5 _∷ᵨ_

-- Operational semantics

data _∣_⇓v_ {n : ℕ} (ρ : Env n) : Val n → ClosVal → Set where
  evalVar : ∀ {m : Fin n} {W : ClosVal}
            -------------
          → ρ ∣ ♯ m ⇓v ρ m

  evalUnit : ρ ∣ unit ⇓v unit

  evalThunk : ∀ {M : Comp n}
              --------------------------
            → ρ ∣ ⟪ M ⟫ ⇓v clos⦅ ρ ,⟪ M ⟫⦆

data _∣_⇓c_#_ {n : ℕ} (ρ : Env n) : Comp n → ClosTerminal → Eff → Set where
  evalAbs : ∀ {M : Comp (suc n)}
            ------------------------------
          → ρ ∣ ƛ M ⇓c clos⦅ ρ ,ƛ M ⦆ # pure

  evalRet : ∀ {V : Val n} {W : ClosVal}
          → ρ ∣ V ⇓v W
            ------------------------------
          → ρ ∣ return V ⇓c return W # pure

  evalSeq : ∀ {V : Val n} {M : Comp n} {T : ClosTerminal} {φ : Eff}
          → ρ ∣ V ⇓v unit
          → ρ ∣ M ⇓c T # φ
            ------------------
          → ρ ∣ V » M ⇓c T # φ

  evalApp : ∀ {m : ℕ} {M : Comp n} {ρ′ : Env m} {M′ : Comp (suc m)} {V : Val n}
              {W : ClosVal} {T : ClosTerminal} {φ₁ φ₂ : Eff}
          → ρ ∣ M ⇓c clos⦅ ρ′ ,ƛ M′ ⦆ # φ₁
          → ρ ∣ V ⇓v W
          → ρ′ ∷ᵨ W ∣ M′ ⇓c T # φ₂
            -----------------------------
          → ρ ∣ M · V ⇓c T # φ₁ + φ₂

  evalForce : ∀ {m : ℕ} {V : Val n} {ρ′ : Env m} {M : Comp m}
                {T : ClosTerminal} {φ : Eff}
            → ρ ∣ V ⇓v clos⦅ ρ′ ,⟪ M ⟫⦆
            → ρ′ ∣ M ⇓c T # φ
              -----------------
            → ρ ∣ V ! ⇓c T # φ

  evalLetin : ∀ {M : Comp n} {W : ClosVal} {T : ClosTerminal}
                {N : Comp (suc n)} {φ₁ φ₂ : Eff}
            → ρ ∣ M ⇓c return W # φ₁
            → ρ ∷ᵨ W ∣ N ⇓c T # φ₂
              ---------------------------
            → ρ ∣ $⇐ M ⋯ N ⇓c T # φ₁ + φ₂

  evalTick : ρ ∣ tick ⇓c return unit # tock

infix 4 _∣_⇓v_
infix 4 _∣_⇓c_#_

-- Logical relation for proving effect soundness

mutual
  _∈-𝐺⟦_⟧v : ClosVal → ValType → Set
  unit ∈-𝐺⟦ 𝟙 ⟧v = ⊤
  clos⦅ ρ ,⟪ M ⟫⦆ ∈-𝐺⟦ 𝑼 φ B ⟧v = ρ , M , φ ∈-𝐺⟦ B ⟧e

  unit ∈-𝐺⟦ 𝑼 _ _ ⟧v = ⊥
  clos⦅ _ ,⟪ _ ⟫⦆ ∈-𝐺⟦ 𝟙 ⟧v = ⊥

  _,_∈-𝐺⟦_⟧c : ClosTerminal → Eff → CompType → Set
  (return V) , ⊥ ∈-𝐺⟦ 𝑭 A ⟧c = V ∈-𝐺⟦ A ⟧v
  clos⦅ ρ ,ƛ M ⦆ , φ ∈-𝐺⟦ A ⇒ B ⟧c =
    ∀ {W : ClosVal} → W ∈-𝐺⟦ A ⟧v → ρ ∷ᵨ W , M , φ ∈-𝐺⟦ B ⟧e

  (return _) , _ ∈-𝐺⟦ _ ⇒ _ ⟧c = ⊥
  clos⦅ _ ,ƛ _ ⦆ , _ ∈-𝐺⟦ 𝑭 _ ⟧c = ⊥

  _,_,_∈-𝐺⟦_⟧e : ∀ {n : ℕ} → Env n → Comp n → Eff → CompType → Set
  ρ , M , φ ∈-𝐺⟦ B ⟧e =
    ∃[ T ] ∃[ φ₁ ] ∃[ φ₂ ] ρ ∣ M ⇓c T # φ₁ × T , φ₂ ∈-𝐺⟦ B ⟧c × φ₁ + φ₂ ≤ φ

_,_∈-𝐺⟦_⟧z : ∀ {n : ℕ} → Env n → Val n → ValType → Set
ρ , V ∈-𝐺⟦ A ⟧z = ∃[ W ] ρ ∣ V ⇓v W × W ∈-𝐺⟦ A ⟧v

infix 4 _∈-𝐺⟦_⟧v
infix 4 _,_∈-𝐺⟦_⟧c
infix 4 _,_,_∈-𝐺⟦_⟧e
infix 4 _,_∈-𝐺⟦_⟧z

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

-- Semantic typing rules

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
              → Γ ⊨c $⇐ M ⋯ N ⦂ B # φ
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

-- Fundamental lemma of logical relations

mutual
  fundamental-lemma-val : ∀ {n : ℕ} {Γ : Ctx n} {V : Val n}
                            {A : ValType}
                        → Γ ⊢v V ⦂ A
                        → Γ ⊨v V ⦂ A
  fundamental-lemma-val typeVar = semanticVar
  fundamental-lemma-val typeUnit = semanticUnit
  fundamental-lemma-val (typeThunk Γ⊢⟪M⟫⦂A) {ρ} =
    semanticThunk (fundamental-lemma-comp Γ⊢⟪M⟫⦂A)

  fundamental-lemma-comp : ∀ {n : ℕ} {Γ : Ctx n} {M : Comp n} {B : CompType}
                             {φ : Eff}
                         → Γ ⊢c M ⦂ B # φ
                         → Γ ⊨c M ⦂ B # φ
  fundamental-lemma-comp (typeAbs Γ⊢M⦂B#φ) =
    semanticAbs (fundamental-lemma-comp Γ⊢M⦂B#φ)
  fundamental-lemma-comp (typeApp Γ⊢M⦂B#φ Γ⊢V⦂A) =
    semanticApp (fundamental-lemma-comp Γ⊢M⦂B#φ) (fundamental-lemma-val Γ⊢V⦂A)
  fundamental-lemma-comp (typeSequence Γ⊢V⦂𝟙 Γ⊢M⦂B#φ) =
    semanticSequence
      (fundamental-lemma-val Γ⊢V⦂𝟙)
      (fundamental-lemma-comp Γ⊢M⦂B#φ)
  fundamental-lemma-comp (typeForce Γ⊢V⦂𝑼φ′B φ′≤φ) =
    semanticForce (fundamental-lemma-val Γ⊢V⦂𝑼φ′B) φ′≤φ
  fundamental-lemma-comp (typeRet Γ⊢V⦂A) =
    semanticRet (fundamental-lemma-val Γ⊢V⦂A)
  fundamental-lemma-comp (typeLetin Γ⊢M⦂𝑭A#φ₁ Γ∷A⊢N⦂B#φ₂ φ₁+φ₂≤φ) =
    semanticLetin
      (fundamental-lemma-comp Γ⊢M⦂𝑭A#φ₁)
      (fundamental-lemma-comp Γ∷A⊢N⦂B#φ₂)
      φ₁+φ₂≤φ
  fundamental-lemma-comp (typeTick tock≤φ) = semanticTick tock≤φ

-- Effect soundness

effect-soundness : ∀ {M : Comp zero} {B : CompType} {φ : Eff}
                 → ∅ ⊢c M ⦂ B # φ
                 → ∃[ T ] ∃[ φ′ ] φ′ ≤ φ × ∅ᵨ ∣ M ⇓c T # φ′
effect-soundness ∅⊢cM⦂B#φ
  with fundamental-lemma-comp ∅⊢cM⦂B#φ (λ ())
...  | T , φ′ , _ , ∅ᵨ∣M⇓cT#φ′ , _ , φ′+φ″≤φ =
  T , φ′ , subeff-lemma ,  ∅ᵨ∣M⇓cT#φ′
  where
    subeff-lemma = ≤-+-invertʳ φ′+φ″≤φ
