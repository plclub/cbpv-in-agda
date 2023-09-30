Require Export Effects.

Section valtypecomptype.

Inductive valtype  : Type :=
  | zero : valtype 
  | one : valtype 
  | U : effect   -> comptype   -> valtype 
  | Sigma : valtype   -> valtype   -> valtype 
  | cross : valtype   -> valtype   -> valtype 
 with comptype  : Type :=
  | cone : comptype 
  | F : valtype   -> comptype 
  | Pi : comptype   -> comptype   -> comptype 
  | arrow : valtype   -> comptype   -> comptype .

End valtypecomptype.
