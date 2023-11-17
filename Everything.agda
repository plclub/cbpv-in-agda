{- Effects and Coeffects in Call-By-Push-Value -}

-- This is an Agda formalization of Section 2 of "Effects and Coeffects in
-- Call-By-Push-Value", available at https://github.com/plclub/cbpv-in-agda

-- This code has been tested with Agda version 2.6.2.2 and standard library
-- version 1.7.1.

module Everything where

{- Section 2.1 -}
import Effects
import CBPV.Effects.SyntacticTyping

{- Section 2.2 -}
import CBPV.Effects.Semantics
import CBPV.Effects.Determinism

{- Section 2.3 -}
import CBPV.Effects.SemanticTyping
import CBPV.Effects.EffectSoundness

{- Section 2.4 -}
import CBV.Effects.Translation
import CBN.Monadic.Translation
import CBV.Monadic.Translation

{- Section 3: Extra -}
import CBPV.Effects.Adequacy

{- Extra -}
import CBPV.Base.SyntacticTyping
import CBPV.Base.Semantics
import CBPV.Base.Determinism
import CBPV.Base.SemanticTyping
import CBPV.Base.TypeSoundness
import CBPV.Base.Adequacy
import CBN.Base.Translation
import CBV.Base.Translation
