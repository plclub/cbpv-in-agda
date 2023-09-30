bool : Type
Value : Type
Exp : Type

One : Value
Lam : (Value -> Exp) -> Value 
Pair : Value -> Value -> Value 
Inj: bool -> Value -> Value

Tock : Exp
Val : Value -> Exp 
App : Exp -> Exp -> Exp 
CaseS : Exp -> (Value -> Exp) -> (Value -> Exp) -> Exp
CaseP: Exp -> (Value -> Value -> Exp) -> Exp.
