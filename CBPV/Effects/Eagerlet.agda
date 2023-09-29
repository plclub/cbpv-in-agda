open import Data.Fin using (suc; zero)
open import Data.Nat using (ℕ; suc)

open import CBPV.Effects.Terms
open import Effects

module CBPV.Effects.Eagerlet (E : Effect) where

open import CBPV.Effects.Substitution E
open import CBPV.Effects.SyntacticTyping E
open import CBPV.Effects.Types E
open Effect E
open Effects.Properties E

$⇐_⋯_ : ∀ {n : ℕ} → Comp n → Comp (suc n) → Comp n
$⇐ return V ⋯ N = N 〔 V 〕
$⇐ M@(ƛ _) ⋯ N = $⟵ M ⋯ N
$⇐ M@(_ · _) ⋯ N = $⟵ M ⋯ N
$⇐ M@(_ » _) ⋯ N = $⟵ M ⋯ N
$⇐ M@(_ !) ⋯ N = $⟵ M ⋯ N
$⇐ M@($⟵ _ ⋯ _) ⋯ N = $⟵ M ⋯ N
$⇐ M@(tick) ⋯ N = $⟵ M ⋯ N

infixr 4 $⇐_⋯_

typeEagerlet : ∀ {n : ℕ} {Γ : Ctx n} {M : Comp n} {A : ValType} {φ₁ φ₂ φ : Eff}
                   {N : Comp (suc n)} {B : CompType}
               → Γ ⊢c M ⦂ 𝑭 A # φ₁
               → Γ ∷ A ⊢c N ⦂ B # φ₂
               → φ₁ + φ₂ ≤ φ
                 ----------------------
               → Γ ⊢c $⇐ M ⋯ N ⦂ B # φ
typeEagerlet {M = return V} (typeRet Γ⊢V⦂A) Γ∷A⊢N⦂B#φ₂ φ₁+φ₂≤φ =
  comp-typepres-substitution
    (type-subeff Γ∷A⊢N⦂B#φ₂ (≤-+-invertˡ φ₁+φ₂≤φ))
     λ where
         zero    → Γ⊢V⦂A
         (suc m) → typeVar
typeEagerlet {M = _ · _} = typeLetin
typeEagerlet {M = _ » _} = typeLetin
typeEagerlet {M = _ !} = typeLetin
typeEagerlet {M = $⟵ _ ⋯ _} = typeLetin
typeEagerlet {M = tick} = typeLetin
