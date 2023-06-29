open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)

module CBPV where

mutual
  data ValType : Set where
    𝟙 : ValType
    𝑼 : CompType → ValType

  data CompType : Set where
    _⇒_ : ValType → CompType → CompType
    𝑭 : ValType → CompType

infixr 7 _⇒_

mutual
  data Val (n : ℕ) : Set where
    #_ : Fin n → Val n
    unit : Val n
    ⟪_⟫ : Comp n → Val n

  data Comp (n : ℕ) : Set where
    ƛ_ : Comp (suc n) → Comp n
    _·_ : Comp n → Val n → Comp n
    _»_ : Val n → Comp n → Comp n
    _! : Val n → Comp n
    return_ : Val n → Comp n
    $⇐_⋯_ : Comp n → Comp (suc n) → Comp n

infix 5 ƛ_
infixl 7 _»_
infix 6 _!
infix 6 return_
infixl 7 _·_
infix 9 #_
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
            → Γ ⊢v # m ⦂ Γ m

    typeUnit : Γ ⊢v unit ⦂ 𝟙

    typeThunk : ∀ {M : Comp n} {B : CompType}
              → Γ ⊢c M ⦂ B
                ----------------
              → Γ ⊢v ⟪ M ⟫ ⦂ 𝑼 B

  data _⊢c_⦂_ {n : ℕ} (Γ : Ctx n) : Comp n → CompType → Set where
    typeAbs : ∀ {A : ValType} {M : Comp (suc n)} {B : CompType}
            → Γ ∷ A ⊢c M ⦂ B
              ----------------
            → Γ ⊢c ƛ M ⦂ A ⇒ B

    typeApp : ∀ {M : Comp n} {A : ValType} {B : CompType} {V : Val n}
            → Γ ⊢c M ⦂ A ⇒ B
            → Γ ⊢v V ⦂ A
              --------------
            → Γ ⊢c M · V ⦂ B

    typeSequence : ∀ {V : Val n} {M : Comp n} {B : CompType}
                 → Γ ⊢v V ⦂ 𝟙
                 → Γ ⊢c M ⦂ B
                   --------------
                 → Γ ⊢c V » M ⦂ B

    typeForce : ∀ {V : Val n} {B : CompType}
              → Γ ⊢v V ⦂ 𝑼 B
                ------------
              → Γ ⊢c V ! ⦂ B

    typeRet : ∀ {V : Val n} {A : ValType}
            → Γ ⊢v V ⦂ A
              -------------------
            → Γ ⊢c return V ⦂ 𝑭 A

    typeLetin : ∀ {M : Comp n} {A : ValType} {N : Comp (suc n)} {B : CompType}
              → Γ ⊢c M ⦂ 𝑭 A
              → Γ ∷ A ⊢c N ⦂ B
                ------------------
              → Γ ⊢c $⇐ M ⋯ N ⦂ B

infix 4 _⊢v_⦂_
infix 4 _⊢c_⦂_

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
          → ρ ∣ # m ⇓v ρ m

  evalUnit : ρ ∣ unit ⇓v unit

  evalThunk : ∀ {M : Comp n}
              --------------------------
            → ρ ∣ ⟪ M ⟫ ⇓v clos⦅ ρ ,⟪ M ⟫⦆

infix 4 _∣_⇓v_
infix 4 _∣_⇓c_

data _∣_⇓c_ {n : ℕ} (ρ : Env n) : Comp n → ClosTerminal → Set where
  evalAbs : ∀ {M : Comp (suc n)}
            -----------------------
          → ρ ∣ ƛ M ⇓c clos⦅ ρ ,ƛ M ⦆

  evalRet : ∀ {V : Val n} {W : ClosVal}
          → ρ ∣ V ⇓v W
            ------------------------
          → ρ ∣ return V ⇓c return W

  evalSeq : ∀ {V : Val n} {M : Comp n} {T : ClosTerminal}
          → ρ ∣ V ⇓v unit
          → ρ ∣ M ⇓c T
            --------------
          → ρ ∣ V » M ⇓c T

  evalApp : ∀ {m : ℕ} {M : Comp n} {ρ′ : Env m} {M′ : Comp (suc m)} {V : Val n}
              {W : ClosVal} {T : ClosTerminal}
          → ρ ∣ M ⇓c clos⦅ ρ′ ,ƛ M′ ⦆
          → ρ ∣ V ⇓v W
          → ρ′ ∷ᵨ W ∣ M′ ⇓c T
            ----------------
          → ρ ∣ M · V ⇓c T

  evalForce : ∀ {m : ℕ} {V : Val n} {ρ′ : Env m} {M : Comp m}
                {T : ClosTerminal}
            → ρ ∣ V ⇓v clos⦅ ρ′ ,⟪ M ⟫⦆
            → ρ′ ∣ M ⇓c T
              -----------
            → ρ ∣ V ! ⇓c T

  evalLetin : ∀ {M : Comp n} {W : ClosVal} {T : ClosTerminal}
                {N : Comp (suc n)}
            → ρ ∣ M ⇓c return W
            → ρ ∷ᵨ W ∣ N ⇓c T
              -----------------
            → ρ ∣ $⇐ M ⋯ N ⇓c T

mutual
  _∈-𝐺⟦_⟧v : ClosVal → ValType → Set
  unit ∈-𝐺⟦ 𝟙 ⟧v = ⊤
  clos⦅ ρ ,⟪ M ⟫⦆ ∈-𝐺⟦ 𝑼 B ⟧v = ρ , M ∈-𝐺⟦ B ⟧e

  unit ∈-𝐺⟦ 𝑼 _ ⟧v = ⊥
  clos⦅ _ ,⟪ _ ⟫⦆ ∈-𝐺⟦ 𝟙 ⟧v = ⊥

  _∈-𝐺⟦_⟧c : ClosTerminal → CompType → Set
  (return V) ∈-𝐺⟦ 𝑭 A ⟧c = V ∈-𝐺⟦ A ⟧v
  clos⦅ ρ ,ƛ M ⦆ ∈-𝐺⟦ A ⇒ B ⟧c =
    ∀ {W : ClosVal} → W ∈-𝐺⟦ A ⟧v → ρ ∷ᵨ W , M ∈-𝐺⟦ B ⟧e

  (return _) ∈-𝐺⟦ _ ⇒ _ ⟧c = ⊥
  clos⦅ _ ,ƛ _ ⦆ ∈-𝐺⟦ 𝑭 _ ⟧c = ⊥

  _,_∈-𝐺⟦_⟧e : ∀ {n : ℕ} → Env n → Comp n → CompType → Set
  ρ , M ∈-𝐺⟦ B ⟧e = ∃[ T ] ρ ∣ M ⇓c T × T ∈-𝐺⟦ B ⟧c

_,_∈-𝐺⟦_⟧z : ∀ {n : ℕ} → Env n → Val n → ValType → Set
ρ , V ∈-𝐺⟦ A ⟧z = ∃[ W ] ρ ∣ V ⇓v W × W ∈-𝐺⟦ A ⟧v

infix 4 _∈-𝐺⟦_⟧v
infix 4 _∈-𝐺⟦_⟧c
infix 4 _,_∈-𝐺⟦_⟧e
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

_⊨c_⦂_ : ∀ {n : ℕ} → Ctx n → Comp n → CompType → Set
_⊨c_⦂_ {n} Γ M B = ∀ {ρ : Env n} → Γ ⊨ ρ → ρ , M ∈-𝐺⟦ B ⟧e

infix 4 _⊨c_⦂_

mutual
  fundamental-lemma-val : ∀ {n : ℕ} {Γ : Ctx n} {V : Val n}
                            {A : ValType}
                        → Γ ⊢v V ⦂ A
                        → Γ ⊨v V ⦂ A
  fundamental-lemma-val (typeVar {m}) {ρ} Γ⊨ρ =
    ⟨ ρ m , ⟨ evalVar {W = ρ m} , Γ⊨ρ m ⟩ ⟩
  fundamental-lemma-val typeUnit Γ⊨ρ =
    ⟨ unit , ⟨ evalUnit , tt ⟩ ⟩
  fundamental-lemma-val (typeThunk {M} Γ⊢cM⦂B) {ρ} Γ⊨ρ =
    ⟨ clos⦅ ρ ,⟪ M ⟫⦆ , ⟨ evalThunk , fundamental-lemma-comp Γ⊢cM⦂B Γ⊨ρ ⟩ ⟩

  fundamental-lemma-comp : ∀ {n : ℕ} {Γ : Ctx n} {M : Comp n}
                             {B : CompType}
                         → Γ ⊢c M ⦂ B
                         → Γ ⊨c M ⦂ B
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

type-soundness-termination : ∀ {M : Comp zero} {B : CompType}
                           → ∅ ⊢c M ⦂ B
                           → ∃[ T ] ∅ᵨ ∣ M ⇓c T
type-soundness-termination ∅⊢cM⦂B =
  let ⟨ T , ⟨ ∅ᵨ∣M⇓cT , _ ⟩ ⟩ = fundamental-lemma-comp ∅⊢cM⦂B λ ()
  in ⟨ T , ∅ᵨ∣M⇓cT ⟩
