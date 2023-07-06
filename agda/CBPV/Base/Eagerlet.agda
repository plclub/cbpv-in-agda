open import Data.Fin using (suc; zero)
open import Data.Nat using (ℕ; suc)

open import CBPV.Base.Substitution
open import CBPV.Base.SyntacticTyping
open import CBPV.Base.Terms
open import CBPV.Base.Types

module CBPV.Base.Eagerlet where

$⇐_⋯_ : ∀ {n : ℕ} → Comp n → Comp (suc n) → Comp n
$⇐ return V ⋯ N = N 〔 V 〕
$⇐ M@(ƛ _) ⋯ N = $⟵ M ⋯ N
$⇐ M@(_ · _) ⋯ N = $⟵ M ⋯ N
$⇐ M@(_ » _) ⋯ N = $⟵ M ⋯ N
$⇐ M@(_ !) ⋯ N = $⟵ M ⋯ N
$⇐ M@($⟵ _ ⋯ _) ⋯ N = $⟵ M ⋯ N

infixr 4 $⇐_⋯_

typeEagerlet : ∀ {n : ℕ} {Γ : Ctx n} {M : Comp n} {A : ValType}
                   {N : Comp (suc n)} {B : CompType}
               → Γ ⊢c M ⦂ 𝑭 A
               → Γ ∷ A ⊢c N ⦂ B
                 -----------------
               → Γ ⊢c $⇐ M ⋯ N ⦂ B
typeEagerlet {M = return V} (typeRet Γ⊢V⦂A) Γ∷A⊢N⦂B =
  comp-typepres-substitution Γ∷A⊢N⦂B λ where
                                         zero    → Γ⊢V⦂A
                                         (suc m) → typeVar
typeEagerlet {M = _ · _} Γ⊢M⦂𝑭A Γ∷A⊢N⦂B = typeLetin Γ⊢M⦂𝑭A Γ∷A⊢N⦂B
typeEagerlet {M = _ » _} Γ⊢M⦂𝑭A Γ∷A⊢N⦂B = typeLetin Γ⊢M⦂𝑭A Γ∷A⊢N⦂B
typeEagerlet {M = _ !} Γ⊢M⦂𝑭A Γ∷A⊢N⦂B = typeLetin Γ⊢M⦂𝑭A Γ∷A⊢N⦂B
typeEagerlet {M = $⟵ _ ⋯ _} Γ⊢M⦂𝑭A Γ∷A⊢N⦂B = typeLetin Γ⊢M⦂𝑭A Γ∷A⊢N⦂B
