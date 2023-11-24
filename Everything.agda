{- Effects and Coeffects in Call-By-Push-Value -}

-- This is an Agda formalization of Section 2 of "Effects and Coeffects in
-- Call-By-Push-Value", available at https://github.com/plclub/cbpv-in-agda

-- This code has been tested with Agda version 2.6.2.2 and standard library
-- version 1.7.1.

module Everything where

{- Section 2.1 -}

import Effects -- Preordered monoid along with properties of preordered monoids
               -- (named 'effects' as that is how they are used)

import CBPV.Effects.SyntacticTyping  -- Type-and-effect system for CBPV

{- Section 2.2 -}

import CBPV.Effects.Semantics -- Environment-based big-step operational
                              -- semantics for CBPV instrumented with effects

import CBPV.Effects.Determinism -- Operational semantics are deterministic

{- Section 2.3 -}

import CBPV.Effects.SemanticTyping -- Logical relation + semantic typing rules

import CBPV.Effects.EffectSoundness -- Type-and-effect system accurately bounds
                                    -- effects at runtime

{- Section 2.4 -}

import CBV.Effects.Translation  -- Standard CBV translation (extended with
                                -- effects) is type-and-effect preserving

import CBN.Monadic.Translation -- Standard CBN translation (extended with graded
                               -- monads) is type-and-effect preserving

import CBV.Monadic.Translation -- Standard CBV translation (now extended with
                               -- graded monads) is type-and-effect preserving

{- Section 2: Extra -}

import CBPV.Effects.Adequacy -- Evaluation in environment-based big-step
                             -- operational semantics implies multi-step
                             -- reduction in substitution-based small-step
                             -- semantics (with agreeing effects)

{- Extra -}

-- These are the same results as presented in section 2, though without effects.
-- They are adapted from "Call-by-push-value in Coq: operational, equational,
-- and denotational theory" (CPP 2019)

import CBPV.Base.SyntacticTyping
import CBPV.Base.Semantics
import CBPV.Base.Determinism
import CBPV.Base.SemanticTyping
import CBPV.Base.TypeSoundness
import CBN.Base.Translation
import CBV.Base.Translation
import CBPV.Base.Adequacy
