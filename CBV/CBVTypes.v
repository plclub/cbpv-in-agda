Require Export Effects.

Section type.
Inductive type  : Type :=
  | Unit : type 
  | Arr : type   -> effect   -> type   -> type 
  | Cross : type   -> type   -> type 
  | Plus : type   -> type   -> type .

Lemma congr_Unit  : Unit  = Unit  .
Proof. congruence. Qed.

Lemma congr_Arr  { s0 : type   } { s1 : effect   } { s2 : type   } { t0 : type   } { t1 : effect   } { t2 : type   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : Arr s0 s1 s2 = Arr t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_Cross  { s0 : type   } { s1 : type   } { t0 : type   } { t1 : type   } (H1 : s0 = t0) (H2 : s1 = t1) : Cross s0 s1 = Cross t0 t1 .
Proof. congruence. Qed.

Lemma congr_Plus  { s0 : type   } { s1 : type   } { t0 : type   } { t1 : type   } (H1 : s0 = t0) (H2 : s1 = t1) : Plus s0 s1 = Plus t0 t1 .
Proof. congruence. Qed.

End type.
