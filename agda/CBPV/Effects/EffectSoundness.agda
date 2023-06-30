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

effect-soundness : ∀ {M : Comp zero} {B : CompType} {φ : Eff}
                 → ∅ ⊢c M ⦂ B # φ
                 → ∃[ T ] ∃[ φ′ ] φ′ ≤ φ × ∅ᵨ ∣ M ⇓c T # φ′
effect-soundness ∅⊢cM⦂B#φ
  with fundamental-lemma-comp ∅⊢cM⦂B#φ (λ ())
...  | T , φ′ , _ , ∅ᵨ∣M⇓cT#φ′ , _ , φ′+φ″≤φ =
  T , φ′ , subeff-lemma ,  ∅ᵨ∣M⇓cT#φ′
  where
    subeff-lemma = ≤-+-invertʳ φ′+φ″≤φ
