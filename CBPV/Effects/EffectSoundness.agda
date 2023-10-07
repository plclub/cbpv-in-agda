open import Data.Nat using (ℕ; zero)
open import Data.Product using (_×_; ∃; ∃-syntax; _,_)

open import CBPV.Effects.Terms
open import Effects

module CBPV.Effects.EffectSoundness (E : Effect) where

open import CBPV.Effects.Semantics E
open import CBPV.Effects.SemanticTyping E
open import CBPV.Effects.SyntacticTyping E
open import CBPV.Effects.Types E
open Effect E
open Properties E

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

  fundamental-lemma-comp : Γ ⊢c M ⦂ B # φ
                         → Γ ⊨c M ⦂ B # φ
  fundamental-lemma-comp (typeAbs ⊢M) =
    semanticAbs (fundamental-lemma-comp ⊢M)
  fundamental-lemma-comp {Γ = Γ} (typeApp ⊢M ⊢V) =
    semanticApp {Γ = Γ}
      (fundamental-lemma-comp ⊢M)
      (fundamental-lemma-val ⊢V)
  fundamental-lemma-comp {Γ = Γ} (typeSequence {B = B} ⊢V ⊢M) =
    semanticSequence {Γ = Γ} {B = B}
      (fundamental-lemma-val ⊢V)
      (fundamental-lemma-comp ⊢M)
  fundamental-lemma-comp {Γ = Γ} (typeForce ⊢V φ′≤φ) =
    semanticForce {Γ = Γ} (fundamental-lemma-val ⊢V) φ′≤φ
  fundamental-lemma-comp {Γ = Γ} (typeRet ⊢V) =
    semanticRet {Γ = Γ} (fundamental-lemma-val ⊢V)
  fundamental-lemma-comp (typeLetin {B = B} ⊢M ⊢N φ₁+φ₂≤φ) =
    semanticLetin {B = B}
      (fundamental-lemma-comp ⊢M)
      (fundamental-lemma-comp ⊢N)
      φ₁+φ₂≤φ
  fundamental-lemma-comp {B = B} (typeSplit ⊢V ⊢M) =
    semanticSplit {B = B}
      (fundamental-lemma-val ⊢V)
      (fundamental-lemma-comp ⊢M)
  fundamental-lemma-comp {B = B} (typeCase ⊢V ⊢M₁ ⊢M₂) =
    semanticCase {B = B}
      (fundamental-lemma-val ⊢V)
      (fundamental-lemma-comp ⊢M₁)
      (fundamental-lemma-comp ⊢M₂)
  fundamental-lemma-comp {Γ = Γ} (typeTick tock≤φ) =
    semanticTick {Γ = Γ} tock≤φ

effect-soundness : ∅ ⊢c M ⦂ B # φ
                 → ∃[ T ] ∃[ φ′ ] φ′ ≤ φ × ∅ᵨ ⊢c M ⇓ T # φ′
effect-soundness ⊢M
  with fundamental-lemma-comp ⊢M (λ ())
...  | T , φ′ , _ , M⇓ , _ , φ′+φ″≤φ =
  T , φ′ , ≤-+-invertʳ φ′+φ″≤φ , M⇓
