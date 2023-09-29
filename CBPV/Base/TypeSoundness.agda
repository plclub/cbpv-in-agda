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
  fundamental-lemma-val : Γ ⊢v V ⦂ A
                        → Γ ⊨v V ⦂ A
  fundamental-lemma-val typeVar = semanticVar
  fundamental-lemma-val typeUnit = semanticUnit
  fundamental-lemma-val (typeThunk ⊢M) =
    semanticThunk (fundamental-lemma-comp ⊢M)

  fundamental-lemma-comp : Γ ⊢c M ⦂ B
                         → Γ ⊨c M ⦂ B
  fundamental-lemma-comp (typeAbs ⊢M) =
    semanticAbs (fundamental-lemma-comp ⊢M)
  fundamental-lemma-comp (typeApp ⊢M ⊢V) =
    semanticApp
      (fundamental-lemma-comp ⊢M)
      (fundamental-lemma-val ⊢V)
  fundamental-lemma-comp (typeSequence {B = B} ⊢V ⊢M) =
    semanticSeq {B = B}
      (fundamental-lemma-val ⊢V)
      (fundamental-lemma-comp ⊢M)
  fundamental-lemma-comp (typeForce ⊢V) =
    semanticForce (fundamental-lemma-val ⊢V)
  fundamental-lemma-comp (typeRet ⊢V) =
    semanticRet (fundamental-lemma-val ⊢V)
  fundamental-lemma-comp (typeLetin {B = B} ⊢M ⊢N) =
    semanticLetin {B = B}
      (fundamental-lemma-comp ⊢M)
      (fundamental-lemma-comp ⊢N)

type-soundness : ∅ ⊢c M ⦂ B
               → ∃[ T ] ∅ᵨ ⊢c M ⇓ T
type-soundness ⊢M
  with fundamental-lemma-comp ⊢M (λ ())
...  | T , M⇓ , _                       = T , M⇓
