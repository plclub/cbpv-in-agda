type : Type
bool : Type
effect : Type
Value : Type
Exp : Type

Tick : effect
Add : effect -> effect -> effect
Pure : effect

Unit : type 
Arr : type -> effect -> type -> type 
Cross : type -> type -> type 
Plus : type -> type -> type 

One : Value
Lam : (Value -> Exp) -> Value 
Pair : Value -> Value -> Value 
Inj: bool -> Value -> Value

Tock : Exp
Val : Value -> Exp 
App : Exp -> Exp -> Exp 
CaseS : Exp -> (Value -> Exp) -> (Value -> Exp) -> Exp
CaseP: Exp -> (Value -> Value -> Exp) -> Exp.
