import Relation.Binary.PropositionalEquality as Eq
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open Eq using (_≡_; refl)

open import CBPV.Base.Renaming
open import CBPV.Base.Substitution
open import CBPV.Base.Terms
open import CBPV.Base.Types

module CBPV.Base.SyntacticTyping where

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
              → Γ ⊢c $⟵ M ⋯ N ⦂ B

infix 4 _⊢v_⦂_
infix 4 _⊢c_⦂_

mutual
  val-typepres-renaming : ∀ {n n′ : ℕ} {Γ : Ctx n} {V : Val n′} {A : ValType}
                            {ρ : Ren n n′} {Δ : Ctx n′}
                         → Δ ⊢v V ⦂ A
                         → (∀ (m : Fin n′) → Δ m ≡ Γ (ρ m))
                           --------------------------------
                         → Γ ⊢v V [ ρ ]v ⦂ A
  val-typepres-renaming (typeVar {m}) pf rewrite pf m = typeVar
  val-typepres-renaming typeUnit _ = typeUnit
  val-typepres-renaming (typeThunk Δ⊢M⦂B) pf =
    typeThunk (comp-typepres-renaming Δ⊢M⦂B pf)

  comp-typepres-renaming : ∀ {n n′ : ℕ} {Γ : Ctx n} {M : Comp n′} {B : CompType}
                             {ρ : Ren n n′} {Δ : Ctx n′}
                         → Δ ⊢c M ⦂ B
                         → (∀ (m : Fin n′) → Δ m ≡ Γ (ρ m))
                           --------------------------------
                         → Γ ⊢c M [ ρ ]c ⦂ B
  comp-typepres-renaming (typeAbs Δ⊢M⦂A⇒B) pf =
    typeAbs (comp-typepres-renaming Δ⊢M⦂A⇒B ext-pf)
    where
      ext-pf = λ where
                   zero    → refl
                   (suc m) → pf m
  comp-typepres-renaming (typeApp Δ⊢M⦂B Δ⊢V⦂A) pf =
    typeApp (comp-typepres-renaming Δ⊢M⦂B pf) (val-typepres-renaming Δ⊢V⦂A pf)
  comp-typepres-renaming (typeSequence Δ⊢V⦂𝟙 Δ⊢M⦂B) pf =
    typeSequence
      (val-typepres-renaming Δ⊢V⦂𝟙 pf)
      (comp-typepres-renaming Δ⊢M⦂B pf)
  comp-typepres-renaming (typeForce Δ⊢V⦂𝑼′B) pf =
    typeForce (val-typepres-renaming Δ⊢V⦂𝑼′B pf)
  comp-typepres-renaming (typeRet Δ⊢V⦂A) pf =
    typeRet (val-typepres-renaming Δ⊢V⦂A pf)
  comp-typepres-renaming (typeLetin Δ⊢M⦂𝑭A Δ∷A⊢N⦂B) pf =
    typeLetin
      (comp-typepres-renaming Δ⊢M⦂𝑭A pf)
      (comp-typepres-renaming Δ∷A⊢N⦂B ext-pf)
    where
      ext-pf = λ where
                   zero    → refl
                   (suc m) → pf m

mutual
  val-typepres-substitution : ∀ {n n′ : ℕ} {Γ : Ctx n} {V : Val n′}
                                {A : ValType} {σ : Sub n n′} {Δ : Ctx n′}
                            → Δ ⊢v V ⦂ A
                            → (∀ (m : Fin n′) → Γ ⊢v σ m ⦂ Δ m)
                              ---------------------------------
                            → Γ ⊢v V ⦅ σ ⦆v ⦂ A
  val-typepres-substitution (typeVar {m}) pf = pf m
  val-typepres-substitution typeUnit _ = typeUnit
  val-typepres-substitution (typeThunk Δ⊢M⦂B) pf =
    typeThunk (comp-typepres-substitution Δ⊢M⦂B pf)


  comp-typepres-substitution : ∀ {n n′ : ℕ} {Γ : Ctx n} {M : Comp n′}
                                 {B : CompType} {σ : Sub n n′} {Δ : Ctx n′}
                             → Δ ⊢c M ⦂ B
                             → (∀ (m : Fin n′) → Γ ⊢v σ m ⦂ Δ m)
                               ---------------------------------
                             → Γ ⊢c M ⦅ σ ⦆c ⦂ B
  comp-typepres-substitution (typeAbs Δ∷A⊢M⦂B) pf =
    typeAbs (comp-typepres-substitution Δ∷A⊢M⦂B exts-pf)
    where
      exts-pf = λ where
                    zero    → typeVar
                    (suc m) → val-typepres-renaming (pf m) λ _ → refl
  comp-typepres-substitution (typeApp Δ⊢M⦂A⇒B Δ⊢V⦂A) pf =
    typeApp
      (comp-typepres-substitution Δ⊢M⦂A⇒B pf)
      (val-typepres-substitution Δ⊢V⦂A pf)
  comp-typepres-substitution (typeSequence Δ⊢V⦂𝟙 Δ⊢M⦂B) pf =
    typeSequence
      (val-typepres-substitution Δ⊢V⦂𝟙 pf)
      (comp-typepres-substitution Δ⊢M⦂B pf)
  comp-typepres-substitution (typeForce Δ⊢V⦂𝑼B) pf =
    typeForce (val-typepres-substitution Δ⊢V⦂𝑼B pf)
  comp-typepres-substitution (typeRet Δ⊢V⦂A) pf =
    typeRet (val-typepres-substitution Δ⊢V⦂A pf)
  comp-typepres-substitution (typeLetin Δ⊢M⦂𝑭A Δ∷A⊢N⦂B) pf =
    typeLetin
      (comp-typepres-substitution Δ⊢M⦂𝑭A pf)
      (comp-typepres-substitution Δ∷A⊢N⦂B exts-pf)
    where
      exts-pf = λ where
                    zero    → typeVar
                    (suc m) → val-typepres-renaming (pf m) λ _ → refl
