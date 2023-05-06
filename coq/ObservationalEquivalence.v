(**
  We also show that the observational equivalence relations are congruent.
*)


Set Implicit Arguments.
Require Import Psatz  Logic List Classes.Morphisms.
Import List Notations.
Require Export CBPV.ProgramContexts.


(** * Contextual Equivalence *)

(** Dependent pairs of term and typing judgement *)
Record CBPVv {n: nat} (Gamma: ctx n) (A: valtype) :=
  mkCBPVv { CBPVv_v :> value n; CBPVv_H :> Gamma ⊩ CBPVv_v : A }.

Record CBPVc {n: nat} (Gamma: ctx n) (B: comptype) :=
  mkCBPVc { CBPVc_c :> comp n; CBPVc_H :> Gamma ⊢ CBPVc_c : B }.


Definition value_obseq {n: nat} {A: valtype} {Gamma: ctx n} (H1 H2: CBPVv Gamma A) :=
  forall (G: groundtype) (C: cctx true 0 n),
    null [[Gamma]] ⊢ C : F G; A -> forall v, (fillc C H1 >* ret v) <-> (fillc C H2 >* ret v).


Instance equiv_value_obseq (n: nat) (A: valtype) (Gamma: ctx n): Equivalence (@value_obseq n A Gamma).
Proof.
  constructor; [firstorder.. |].
  intros X1 X2 X3 H1 H2 G C v; etransitivity; eauto.
Qed.

Notation "V1 ≈ V2" := (value_obseq V1 V2) (at level 50).

(** Unfolding for eauto *)
Lemma destruct_value_obseq {n: nat} {Gamma: ctx n} {A: valtype} (v1 v2: CBPVv Gamma A):
  v1 ≈ v2 -> forall (G: groundtype) (C: cctx true 0 n),
    null [[Gamma]] ⊢ C : F G; A -> forall v, (fillc C v1 >* ret v) -> (fillc C v2 >* ret v).
Proof. firstorder. Qed.



Definition comp_obseq {n: nat} {B: comptype} {Gamma: ctx n} (H1 H2: CBPVc Gamma B) :=
  forall (G: groundtype) (C: cctx false 0 n),
    null [[Gamma]] ⊢ C : F G; B -> forall v, (fillc C H1 >* ret v) <-> (fillc C H2 >* ret v).

Instance equiv_comp_obseq (n: nat) (B: comptype) (Gamma: ctx n): Equivalence (@comp_obseq n B Gamma).
Proof.
  constructor; [firstorder.. |].
  intros X1 X2 X3 H1 H2 G C v; etransitivity; eauto.
Qed.

Notation "C1 ≃ C2" := (comp_obseq C1 C2) (at level 50).

(** Unfolding for euato *)
Lemma destruct_comp_obseq {n: nat} {Gamma: ctx n} {B: comptype} (c1 c2: CBPVc Gamma B):
  c1 ≃ c2 -> forall (G: groundtype) (C: cctx false 0 n),
    null [[Gamma]] ⊢ C : F G; B -> forall v, (fillc C c1 >* ret v) -> (fillc C c2 >* ret v).
Proof. firstorder. Qed.


Hint Resolve CBPVv_v CBPVc_c CBPVv_H CBPVc_H
     destruct_value_obseq destruct_comp_obseq.


Lemma val_obseq_vctx_congruence {m n: nat} {Gamma: ctx n} {A A': valtype}
      (v1 v2: CBPVv Gamma A) (C: vctx true m n) (Delta: ctx m) (C' C'': CBPVv Delta A'):
    fillv C v1 = C' ->
    fillv C v2 = C'' ->
    Delta [[Gamma]] ⊩ C : A'; A ->
    v1 ≈ v2 ->
    C' ≈ C''.
Proof.
  intros H0 H1 H2 H G K H4 v'; cbn;
  repeat rewrite <- ?H0, <- ?H1, plug_fill_cctx_value.
  eapply H, cctx_vctx_plug_typing_soundness; eauto.
Qed.

Lemma val_obseq_cctx_congruence {m n: nat} {Gamma: ctx n} {A: valtype} {B: comptype}
      (v1 v2: CBPVv Gamma A) (C: cctx true m n) (Delta: ctx m) (C' C'': CBPVc Delta B):
      fillc C v1 = C' ->
      fillc C v2 = C'' ->
      Delta [[Gamma]] ⊢ C : B; A ->
      v1 ≈ v2 ->
      C' ≃ C''.
Proof.
  intros H0 H1 H2 H G K H4 v'; cbn;
  repeat rewrite <- ?H0, <- ?H1, plug_fill_cctx_comp.
  eapply H, cctx_cctx_plug_typing_soundness; eauto.
Qed.

Lemma comp_obseq_vctx_congruence {m n: nat} {Gamma: ctx n} {B: comptype} {A': valtype}
      (c1 c2: CBPVc Gamma B) (C: vctx false m n) (Delta: ctx m) (C' C'': CBPVv Delta A'):
      fillv C c1 = C' ->
      fillv C c2 = C'' ->
      Delta [[Gamma]] ⊩ C : A'; B ->
      c1 ≃ c2 ->
      C' ≈ C''.
Proof.
  intros H0 H1 H2 H G K H4 v'; cbn;
  repeat rewrite <- ?H0, <- ?H1, plug_fill_cctx_value.
  eapply H, cctx_vctx_plug_typing_soundness; eauto.
Qed.

Lemma comp_obseq_cctx_congruence {m n: nat} {Gamma: ctx n} {B B': comptype}
      (c1 c2: CBPVc Gamma B) (C: cctx false m n) (Delta: ctx m) (C' C'': CBPVc Delta B'):
      fillc C c1 = C' ->
      fillc C c2 = C'' ->
      Delta [[Gamma]] ⊢ C : B'; B ->
      c1 ≃ c2 ->
      C' ≃ C''.
Proof.
  intros H0 H1 H2 H G K H4 v'; cbn;
  repeat rewrite <- ?H0, <- ?H1, plug_fill_cctx_comp.
  eapply H, cctx_cctx_plug_typing_soundness; eauto.
Qed.
