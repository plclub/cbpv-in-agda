open import Data.Fin using (suc; zero)
open import Data.Nat using (ℕ; suc)

open import CBPV.Base.Substitution
open import CBPV.Base.SyntacticTyping
open import CBPV.Base.Terms
open import CBPV.Base.Types

module CBPV.Base.Eagerlet where

$⇐_⋯_ : Comp n → Comp (suc n) → Comp n
$⇐ return V ⋯ N = N 〔 V 〕
$⇐ M ⋯ N = $⟵ M ⋯ N

infixr 4 $⇐_⋯_

typeEagerlet : Γ ⊢c M ⦂ 𝑭 A
             → Γ ∷ A ⊢c N ⦂ B
               -----------------
             → Γ ⊢c $⇐ M ⋯ N ⦂ B
typeEagerlet {M = return V} (typeRet ⊢V) ⊢N =
  comp-typepres-substitution ⊢N λ where
                                    zero    → ⊢V
                                    (suc m) → typeVar
typeEagerlet {M = _ · _} = typeLetin
typeEagerlet {M = _ » _} = typeLetin
typeEagerlet {M = _ !} = typeLetin
typeEagerlet {M = $⟵ _ ⋯ _} = typeLetin
typeEagerlet {M = $≔ _ ⋯ _} = typeLetin
typeEagerlet {M = case _ inl⇒ _ inr⇒ _} = typeLetin