open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_×_; ∃; ∃-syntax; _,_)
open import Data.Unit using (⊤; tt)

open import CBPV.Base.Semantics
open import CBPV.Base.SemanticTyping
open import CBPV.Base.SyntacticTyping
open import CBPV.Base.Terms
open import CBPV.Base.Types

module CBPV.Base.TypeSoundness where

mutual
  fundamental-lemma-val : ∀ {n : ℕ} {Γ : Ctx n} {V : Val n}
                            {A : ValType}
                        → Γ ⊢v V ⦂ A
                        → Γ ⊨v V ⦂ A
  fundamental-lemma-val typeVar = semanticVar
  fundamental-lemma-val typeUnit = semanticUnit
  fundamental-lemma-val (typeThunk Γ⊢cM⦂B) =
    semanticThunk (fundamental-lemma-comp Γ⊢cM⦂B)

  fundamental-lemma-comp : ∀ {n : ℕ} {Γ : Ctx n} {M : Comp n}
                             {B : CompType}
                         → Γ ⊢c M ⦂ B
                         → Γ ⊨c M ⦂ B
  fundamental-lemma-comp (typeAbs Γ∷A⊢M⦂B) =
    semanticAbs (fundamental-lemma-comp Γ∷A⊢M⦂B)
  fundamental-lemma-comp (typeApp Γ⊢M⦂A⇒B Γ⊢V⦂A) =
    semanticApp (fundamental-lemma-comp Γ⊢M⦂A⇒B) (fundamental-lemma-val Γ⊢V⦂A)
  fundamental-lemma-comp (typeSequence Γ⊢V⦂𝟙 Γ⊢M⦂B) =
    semanticSeq (fundamental-lemma-val Γ⊢V⦂𝟙) (fundamental-lemma-comp Γ⊢M⦂B)
  fundamental-lemma-comp (typeForce Γ⊢V⦂𝑼B) =
    semanticForce (fundamental-lemma-val Γ⊢V⦂𝑼B)
  fundamental-lemma-comp (typeRet Γ⊢V⦂A) =
    semanticRet (fundamental-lemma-val Γ⊢V⦂A)
  fundamental-lemma-comp (typeLetin Γ⊢M⦂𝑭A Γ∷A⊢N⦂B) =
    semanticLetin
      (fundamental-lemma-comp Γ⊢M⦂𝑭A)
      (fundamental-lemma-comp Γ∷A⊢N⦂B)

type-soundness : ∀ {M : Comp zero} {B : CompType}
               → ∅ ⊢c M ⦂ B
               → ∃[ T ] ∅ᵨ ∣ M ⇓c T
type-soundness ∅⊢cM⦂B
  with fundamental-lemma-comp ∅⊢cM⦂B (λ ())
...  | T , ∅ᵨ∣M⇓cT , _ = T , ∅ᵨ∣M⇓cT
