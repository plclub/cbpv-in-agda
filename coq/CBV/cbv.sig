type : Type
bool : Type
Value : Type
Exp : Type

Unit : type 
Arr : type -> type -> type 
Cross : type -> type -> type 
Plus : type -> type -> type 

One : Value
Lam : (Value -> Exp) -> Value 
Pair : Value -> Value -> Value 
Inj: bool -> Value -> Value

Val : Value -> Exp 
App : Exp -> Exp -> Exp 
CaseS : Exp -> (Value -> Exp) -> (Value -> Exp) -> Exp
CaseP: Exp -> (Value -> Value -> Exp) -> Exp.
