Set Implicit Arguments.
Require Import Psatz  Logic List Classes.Morphisms Coq.Program.Tactics.
Import List Notations.
Require Export CBPV.TAlgebra CBPV.Normalisation CBPV.ProgramContexts.



Reserved Notation "A [ B ]" (at level 50).


Class SubstitutionNotation (A B C: Type) :=
  {
    subst: A -> B -> C
  }.

Notation "A [ B ]" := (subst A B).

Instance substitution_comp {n m: nat}:
  SubstitutionNotation (comp m) (fin m -> value n) (comp n)
  := {| subst := fun c sigma => subst_comp sigma c |}.


Instance substitution_value {n m: nat}:
  SubstitutionNotation (value m) (fin m -> value n)  (value n)
  := {| subst := fun v sigma => subst_value sigma v |}.


Instance substitution_context_filling_comp {n m: nat} {t: bool}:
  SubstitutionNotation (cctx t m n) (if t then value n else comp n) (comp m)
  := {| subst := fillc |}.


Instance substitution_context_filling_value {n m: nat} {t: bool}:
  SubstitutionNotation (vctx t m n) (if t then value n else comp n) (value m)
  := {| subst := fillv |}.

Hint Transparent subst.


Fixpoint plug_fill_vctx_value m n (C: vctx true m n) k t' (C': vctx t' n k) e {struct C}:
  C[C'[e]] = (plugvctx C C')[e]

with plug_fill_vctx_comp m n (C: vctx false m n)  k t' (C': cctx t' n k) e {struct C}:
  C[C'[e]] = (plugvctx C C')[e]

with plug_fill_cctx_value  m n (C: cctx true m n) k t' (C': vctx t' n k) e {struct C}:
  C[C'[e]] = (plugcctx C C')[e]

with plug_fill_cctx_comp m n (C: cctx false m n)  k t' (C': cctx t' n k) e {struct C}:
  C[C'[e]] = (plugcctx C C')[e].
Proof.
  all: destruct C; cbn; intros; intuition; unfold subst in *; cbn in *; congruence.
Qed.
