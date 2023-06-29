open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)

open import Effects

module EffectCBPV (E : Effect) where

open Effect E
open Properties E

mutual
  data ValType : Set where
    𝟙 : ValType
    𝑼 : Eff → CompType → ValType

  data CompType : Set where
    _⇒_ : ValType → CompType → CompType
    𝑭 : ValType → CompType

infixr 7 _⇒_

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

Ctx : ℕ → Set
Ctx n = Fin n → ValType

∅ : Ctx zero
∅ ()

_∷_ : ∀ {n : ℕ} → Ctx n → ValType → Ctx (suc n)
Γ ∷ A = λ where
          zero → A
          (suc n) → Γ n

infixl 5 _∷_

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
  data ClosVal : Set where
    unit : ClosVal

    clos⦅_,⟪_⟫⦆ : ∀ {n : ℕ} → Env n → Comp n → ClosVal

  data ClosTerminal : Set where
    return_ : ClosVal → ClosTerminal

    clos⦅_,ƛ_⦆ : ∀ {n : ℕ} → Env n → Comp (suc n) → ClosTerminal

  Env : ℕ → Set
  Env n = Fin n → ClosVal

∅ᵨ : Env zero
∅ᵨ ()

_∷ᵨ_ : ∀ {n : ℕ} → Env n → ClosVal → Env (suc n)
ρ ∷ᵨ W = λ where
          zero → W
          (suc n) → ρ n

infixl 5 _∷ᵨ_

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

mutual
  fundamental-lemma-val : ∀ {n : ℕ} {Γ : Ctx n} {V : Val n}
                            {A : ValType}
                        → Γ ⊢v V ⦂ A
                        → Γ ⊨v V ⦂ A
  fundamental-lemma-val = {!!}
{-
  fundamental-lemma-val (typeVar {m}) {ρ} Γ⊨ρ =
    ⟨ ρ m , ⟨ evalVar {W = ρ m} , Γ⊨ρ m ⟩ ⟩
  fundamental-lemma-val typeUnit Γ⊨ρ =
    ⟨ unit , ⟨ evalUnit , tt ⟩ ⟩
  fundamental-lemma-val (typeThunk {M} Γ⊢cM⦂B) {ρ} Γ⊨ρ =
    ⟨ clos⦅ ρ ,⟪ M ⟫⦆ , ⟨ evalThunk , fundamental-lemma-comp Γ⊢cM⦂B Γ⊨ρ ⟩ ⟩
-}

  fundamental-lemma-comp : ∀ {n : ℕ} {Γ : Ctx n} {M : Comp n} {B : CompType}
                             {φ : Eff}
                         → Γ ⊢c M ⦂ B # φ
                         → Γ ⊨c M ⦂ B # φ
  fundamental-lemma-comp = {!!}
{-
  fundamental-lemma-comp {n} (typeAbs {A} {M} {B} Γ∷A⊢cM⦂B) {ρ} Γ⊨ρ =
    ⟨ clos⦅ ρ ,ƛ M ⦆ , ⟨ evalAbs , ih ⟩ ⟩
    where
      ih : ∀ {W : ClosVal} → W ∈-𝐺⟦ A ⟧v → ρ ∷ᵨ W , M ∈-𝐺⟦ B ⟧e
      ih pf = fundamental-lemma-comp Γ∷A⊢cM⦂B (⊨-ext Γ⊨ρ pf)
  fundamental-lemma-comp {n} (typeApp Γ⊢cM⦂B Γ⊢vV⦂A) Γ⊨ρ
    with fundamental-lemma-val Γ⊢vV⦂A Γ⊨ρ
  ...  | ⟨ W , ⟨ ρ∣V⇓vW , W∈𝐺⟦A⟧v ⟩ ⟩
    with fundamental-lemma-comp Γ⊢cM⦂B Γ⊨ρ
  ... | ⟨ T′@(clos⦅ ρ′ ,ƛ M′ ⦆) , ⟨ ρ∣M⇓cT′ , pf ⟩ ⟩ =
    let ⟨ T , ⟨ ρ′∷ᵨW∣M′⇓cT , T∈𝐺⟦B⟧c ⟩ ⟩ = pf W∈𝐺⟦A⟧v in
    ⟨ T , ⟨ evalApp ρ∣M⇓cT′ ρ∣V⇓vW ρ′∷ᵨW∣M′⇓cT , T∈𝐺⟦B⟧c ⟩ ⟩
  fundamental-lemma-comp (typeSequence Γ⊢vV⦂𝟙 Γ⊢cM⦂B) Γ⊨ρ
    with fundamental-lemma-val Γ⊢vV⦂𝟙 Γ⊨ρ
  ...  | ⟨ unit , ⟨ ρ∣V⇓vunit , _ ⟩ ⟩
    with fundamental-lemma-comp Γ⊢cM⦂B Γ⊨ρ
  ...  | ⟨ T , ⟨ ρ∣M⇓cT , T∈𝐺⟦B⟧c ⟩ ⟩ =
    ⟨ T , ⟨ evalSeq ρ∣V⇓vunit ρ∣M⇓cT , T∈𝐺⟦B⟧c ⟩ ⟩
  fundamental-lemma-comp (typeForce Γ⊢vV⦂𝑼B) Γ⊨ρ
    with fundamental-lemma-val Γ⊢vV⦂𝑼B Γ⊨ρ
  ...  | ⟨ W@(clos⦅ ρ ,⟪ M ⟫⦆) , ⟨ ρ∣V⇓vW , ⟨ T , ⟨ ρ|M⇓cT , T∈𝐺⟦B⟧c ⟩ ⟩ ⟩ ⟩ =
    ⟨ T , ⟨ evalForce ρ∣V⇓vW ρ|M⇓cT , T∈𝐺⟦B⟧c ⟩ ⟩
  fundamental-lemma-comp (typeRet Γ⊢vV⦂A) Γ⊨ρ
    with fundamental-lemma-val Γ⊢vV⦂A Γ⊨ρ
  ... | ⟨ W , ⟨ ρ∣V⇓vW , W∈𝐺⟦A⟧v ⟩ ⟩ =
    ⟨ return W , ⟨ evalRet ρ∣V⇓vW , W∈𝐺⟦A⟧v ⟩ ⟩
  fundamental-lemma-comp (typeLetin Γ⊢cM⦂𝑭A Γ∷A⊢cN⦂B) Γ⊨ρ
    with fundamental-lemma-comp Γ⊢cM⦂𝑭A Γ⊨ρ
  ...  | ⟨ T′@(return W) , ⟨ ρ∣M⇓cT′ , W∈𝐺⟦A⟧v ⟩ ⟩
    with fundamental-lemma-comp Γ∷A⊢cN⦂B (⊨-ext Γ⊨ρ W∈𝐺⟦A⟧v)
  ...  | ⟨ T , ⟨ ρ∷W∣N⇓cT , T∈𝐺⟦B⟧c ⟩ ⟩ =
    ⟨ T , ⟨ (evalLetin ρ∣M⇓cT′ ρ∷W∣N⇓cT) , T∈𝐺⟦B⟧c ⟩ ⟩

-}

effect-soundness : ∀ {M : Comp zero} {B : CompType} {φ : Eff}
                 → ∅ ⊢c M ⦂ B # φ
                 → ∃[ T ] ∃[ φ′ ] φ′ ≤ φ × ∅ᵨ ∣ M ⇓c T # φ′
effect-soundness ∅⊢cM⦂B#φ
  with fundamental-lemma-comp ∅⊢cM⦂B#φ (λ ())
...  | ⟨ T , ⟨ φ′ , ⟨ _ , ⟨ ∅ᵨ∣M⇓cT#φ′ , ⟨ _ , φ′+φ″≤φ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ T , ⟨ φ′ , ⟨ ≤-+-invertʳ φ′+φ″≤φ ,  ∅ᵨ∣M⇓cT#φ′ ⟩ ⟩ ⟩
