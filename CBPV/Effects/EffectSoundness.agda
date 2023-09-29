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
  fundamental-lemma-val typeVar = semanticVar
  fundamental-lemma-val typeUnit = semanticUnit
  fundamental-lemma-val (typeThunk ⊢M) =
    semanticThunk (fundamental-lemma-comp ⊢M)

  fundamental-lemma-comp : Γ ⊢c M ⦂ B # φ
                         → Γ ⊨c M ⦂ B # φ
  fundamental-lemma-comp (typeAbs ⊢M) =
    semanticAbs (fundamental-lemma-comp ⊢M)
  fundamental-lemma-comp (typeApp ⊢M ⊢V) =
    semanticApp
      (fundamental-lemma-comp ⊢M)
      (fundamental-lemma-val ⊢V)
  fundamental-lemma-comp (typeSequence {B = B} ⊢V ⊢M) =
    semanticSequence {B = B}
      (fundamental-lemma-val ⊢V)
      (fundamental-lemma-comp ⊢M)
  fundamental-lemma-comp (typeForce ⊢V φ′≤φ) =
    semanticForce (fundamental-lemma-val ⊢V) φ′≤φ
  fundamental-lemma-comp (typeRet ⊢V) =
    semanticRet (fundamental-lemma-val ⊢V)
  fundamental-lemma-comp (typeLetin {B = B} ⊢M ⊢N φ₁+φ₂≤φ) =
    semanticLetin {B = B}
      (fundamental-lemma-comp ⊢M)
      (fundamental-lemma-comp ⊢N)
      φ₁+φ₂≤φ
  fundamental-lemma-comp (typeTick tock≤φ) =
    semanticTick tock≤φ

effect-soundness : ∅ ⊢c M ⦂ B # φ
                 → ∃[ T ] ∃[ φ′ ] φ′ ≤ φ × ∅ᵨ ⊢c M ⇓ T # φ′
effect-soundness ⊢M
  with fundamental-lemma-comp ⊢M (λ ())
...  | T , φ′ , _ , M⇓ , _ , φ′+φ″≤φ =
  T , φ′ , ≤-+-invertʳ φ′+φ″≤φ , M⇓
