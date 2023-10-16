open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ)

import CBPV.Base.SyntacticTyping as CBPV
open import CBN.Base.SyntacticTyping
open import CBN.Base.Terms
open import CBN.Base.Types
open import CBPV.Base.Renaming
open import CBPV.Base.Terms hiding (n; m)
open import CBPV.Base.Types
open CBPV hiding (Ctx)

module CBN.Base.Translation where

data _↦_ : Term n → Comp n → Set where
  transVar : # m ↦ # m !

  transUnit : unit {n} ↦ return unit

  transInl : e ↦ M
             ------------------------
           → inl e ↦ return inl ⟪ M ⟫

  transInr : e ↦ M
             ------------------------
           → inr e ↦ return inr ⟪ M ⟫

  transPair : e₁ ↦ M₁
            → e₂ ↦ M₂
              -------------------------
            → ⟨ e₁ , e₂ ⟩ ↦ ⟨ M₁ , M₂ ⟩

  transAbs : e ↦ M
             ---------
           → ƛ e ↦ ƛ M

  transApp : e₁ ↦ M
           → e₂ ↦ N
             --------------------
           → e₁ · e₂ ↦ M · ⟪ N ⟫

  transSeq : e₁ ↦ M
           → e₂ ↦ N
             ----------------------------------------
           → e₁ » e₂ ↦  $⟵ M ⋯ (# zero) » N [ suc ]c

  transFst : e ↦ M
             ---------------
           → fst e ↦ projl M

  transSnd : e ↦ M
             ---------------
           → snd e ↦ projr M

  transCase : e ↦ M
            → e₁ ↦ M₁
            → e₂ ↦ M₂
              ----------------------------------------------------------------------------
            → case e inl⇒ e₁ inr⇒ e₂ ↦ $⟵ M ⋯ case # zero inl⇒ M₁ [ ↑↑ ]c inr⇒ M₂ [ ↑↑ ]c

infix 3 _↦_

record Translation (A B : Set) : Set where
  field
    ⟦_⟧ : A → B

open Translation ⦃...⦄ public

instance
  ⟦Type⟧ : Translation Type CompType
  Translation.⟦ ⟦Type⟧ ⟧ 𝟙 = 𝑭 𝟙
  Translation.⟦ ⟦Type⟧ ⟧ (τ₁ ⇒ τ₂) = 𝑼 ⟦ τ₁ ⟧ ⇒ ⟦ τ₂ ⟧
  Translation.⟦ ⟦Type⟧ ⟧ (τ₁ ∪ τ₂) = 𝑭 (𝑼 ⟦ τ₁ ⟧ ∪ 𝑼 ⟦ τ₂ ⟧)
  Translation.⟦ ⟦Type⟧ ⟧ (τ₁ * τ₂) = ⟦ τ₁ ⟧ & ⟦ τ₂ ⟧

  ⟦Ctx⟧ : Translation (Ctx n) (CBPV.Ctx n)
  Translation.⟦ ⟦Ctx⟧ ⟧ Γ m = 𝑼 ⟦ Γ m ⟧

  ⟦Term⟧ : Translation (Term n) (Comp n)
  Translation.⟦ ⟦Term⟧ ⟧ (# m) = # m !
  Translation.⟦ ⟦Term⟧ ⟧ unit = return unit
  Translation.⟦ ⟦Term⟧ ⟧ (ƛ e) = ƛ ⟦ e ⟧
  Translation.⟦ ⟦Term⟧ ⟧ (e₁ · e₂) = ⟦ e₁ ⟧ · ⟪ ⟦ e₂ ⟧ ⟫
  Translation.⟦ ⟦Term⟧ ⟧ (e₁ » e₂) =
    $⟵ ⟦ e₁ ⟧ ⋯
    (# zero) » ⟦ e₂ ⟧ [ suc ]c
  Translation.⟦ ⟦Term⟧ ⟧ (inl e) = return inl ⟪ ⟦ e ⟧ ⟫
  Translation.⟦ ⟦Term⟧ ⟧ (inr e) = return inr ⟪ ⟦ e ⟧ ⟫
  Translation.⟦ ⟦Term⟧ ⟧ ⟨ e₁ , e₂ ⟩ = ⟨ ⟦ e₁ ⟧ , ⟦ e₂ ⟧ ⟩
  Translation.⟦ ⟦Term⟧ ⟧ (fst e) = projl ⟦ e ⟧
  Translation.⟦ ⟦Term⟧ ⟧ (snd e) = projr ⟦ e ⟧
  Translation.⟦ ⟦Term⟧ ⟧ (case e inl⇒ e₁ inr⇒ e₂) =
    $⟵ ⟦ e ⟧ ⋯
    case # zero inl⇒ ⟦ e₁ ⟧ [ ↑↑ ]c inr⇒ ⟦ e₂ ⟧ [ ↑↑ ]c

e↦⟦e⟧ : e ↦ ⟦ e ⟧
e↦⟦e⟧ {e = # x} = transVar
e↦⟦e⟧ {e = unit} = transUnit
e↦⟦e⟧ {e = ƛ e} = transAbs e↦⟦e⟧
e↦⟦e⟧ {e = e₁ · e₂} = transApp e↦⟦e⟧ e↦⟦e⟧
e↦⟦e⟧ {e = e₁ » e₂} = transSeq e↦⟦e⟧ e↦⟦e⟧
e↦⟦e⟧ {e = inl e} = transInl e↦⟦e⟧
e↦⟦e⟧ {e = inr e} = transInr e↦⟦e⟧
e↦⟦e⟧ {e = ⟨ e₁ , e₂ ⟩ } = transPair e↦⟦e⟧ e↦⟦e⟧
e↦⟦e⟧ {e = fst e} = transFst e↦⟦e⟧
e↦⟦e⟧ {e = snd e} = transSnd e↦⟦e⟧
e↦⟦e⟧ {e = case e inl⇒ e₁ inr⇒ e₂} = transCase e↦⟦e⟧ e↦⟦e⟧ e↦⟦e⟧
