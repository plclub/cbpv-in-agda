type : Type
exp : Type
bool: Type

Unit : type
Arr : type -> type -> type 
Cross : type -> type -> type 
Plus : type -> type -> type 

One : exp
Lam : (exp -> exp) -> exp 
App : exp -> exp -> exp 
Pair : exp -> exp -> exp 
Proj : bool -> exp -> exp
Inj : bool -> exp -> exp 
CaseS: exp -> (exp -> exp) -> (exp -> exp) -> exp

