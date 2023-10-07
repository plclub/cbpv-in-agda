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
  fundamental-lemma-val {Γ = Γ} typeVar =
    semanticVar {Γ = Γ}
  fundamental-lemma-val {Γ = Γ} typeUnit =
    semanticUnit {Γ = Γ}
  fundamental-lemma-val {Γ = Γ} (typeThunk ⊢M) =
    semanticThunk {Γ = Γ} (fundamental-lemma-comp ⊢M)
  fundamental-lemma-val {Γ = Γ} (typePair ⊢V₁ ⊢V₂) =
    semanticPair {Γ = Γ}
      (fundamental-lemma-val ⊢V₁)
      (fundamental-lemma-val ⊢V₂)
  fundamental-lemma-val {Γ = Γ} (typeInl ⊢V) =
    semanticInl {Γ = Γ} (fundamental-lemma-val ⊢V)
  fundamental-lemma-val {Γ = Γ} (typeInr ⊢V) =
    semanticInr {Γ = Γ} (fundamental-lemma-val ⊢V)

  fundamental-lemma-comp : Γ ⊢c M ⦂ B
                         → Γ ⊨c M ⦂ B
  fundamental-lemma-comp (typeAbs ⊢M) =
    semanticAbs (fundamental-lemma-comp ⊢M)
  fundamental-lemma-comp {Γ = Γ} (typeApp ⊢M ⊢V) =
    semanticApp {Γ = Γ}
      (fundamental-lemma-comp ⊢M)
      (fundamental-lemma-val ⊢V)
  fundamental-lemma-comp {Γ = Γ} (typeSequence {B = B} ⊢V ⊢M) =
    semanticSeq {Γ = Γ} {B = B}
      (fundamental-lemma-val ⊢V)
      (fundamental-lemma-comp ⊢M)
  fundamental-lemma-comp {Γ = Γ} (typeForce ⊢V) =
    semanticForce {Γ = Γ} (fundamental-lemma-val ⊢V)
  fundamental-lemma-comp {Γ = Γ} (typeRet ⊢V) =
    semanticRet {Γ = Γ} (fundamental-lemma-val ⊢V)
  fundamental-lemma-comp (typeLetin {B = B} ⊢M ⊢N) =
    semanticLetin {B = B}
      (fundamental-lemma-comp ⊢M)
      (fundamental-lemma-comp ⊢N)
  fundamental-lemma-comp (typeSplit {B = B} ⊢V ⊢M) =
    semanticSplit {B = B}
      (fundamental-lemma-val ⊢V)
      (fundamental-lemma-comp ⊢M)
  fundamental-lemma-comp (typeCase {B = B} ⊢V ⊢M₁ ⊢M₂) =
    semanticCase {B = B}
      (fundamental-lemma-val ⊢V)
      (fundamental-lemma-comp ⊢M₁)
      (fundamental-lemma-comp ⊢M₂)

type-soundness : ∅ ⊢c M ⦂ B
               → ∃[ T ] ∅ᵨ ⊢c M ⇓ T
type-soundness ⊢M
  with fundamental-lemma-comp ⊢M (λ ())
...  | T , M⇓ , _                       = T , M⇓
