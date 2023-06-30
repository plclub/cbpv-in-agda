open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)

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
              → Γ ⊢c $⇐ M ⋯ N ⦂ B

infix 4 _⊢v_⦂_
infix 4 _⊢c_⦂_
