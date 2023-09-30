(**
  We give 3 different termination proofs of syntactically welltyped terms.
*)
Set Implicit Arguments.
Require Import Psatz Logic List.
Require Import Classes.Morphisms.
Import List Notations.

Require Export CBPV.DenotationalSemantics.

From CBPV Require Export SemanticTyping StrongNormalisation 
     CBN.weakStory CBN.strongStory CBN.CBN_CBPV
     CBV.weakStory CBV.strongStory CBV.CBV_CBPV.

(** * Normalisation *)
(** ** Weak Normalisation *)
Theorem weak_normalisation_cbpv P B:
  null ⊢ P : B -> SN Semantics.step P.
Proof.
  intros H % SemanticTyping.SemanticSoundness; specialize (H 0 ids).
  mp H; [ intros []|]; destruct H as [c' [H1 H2] ];
    eapply bigstep_sn.
       rewrite idSubst_comp in H1; eauto.
Qed.

Theorem weak_normalisation_cbn P B:
  null ⊢n P : B -> SN CBN.weakStory.Step P.
Proof.
  intros H % cbn_type_pres.
  replace (eval_ctx null) with (@null valtype) in * by (fext; intros []).
  apply weak_normalisation_cbpv in H.
  eapply WN_translates; eauto using trans_eval.
Qed.

Theorem weak_normalisation_cbv P B:
  null ⊢v P : B -> SN CBV.weakStory.Step P.
Proof.
  intros H % typingExp_pres.
  replace (null >> eval_ty) with (@null valtype) in * by (fext; intros []).
  apply weak_normalisation_cbpv in H.
  now eapply WN_CBV. 
Qed.

(** ** Strong Normalisation *)
Theorem strong_normalisation_cbpv n (Gamma: ctx n) P B:
  Gamma ⊢ P : B -> SN sstep P.
Proof.
  intros H % (StrongNormalisation.SemanticSoundness Gamma).
  specialize (H _ _ (G_id Gamma)).
  apply close_sn in H.  asimpl in H.
  unfold sn in H. eapply SN_ext; [ | exact H].
  eapply sstep_strong_step.
Qed.

Theorem strong_normalisation_cbpvᵥ n (Gamma: ctx n) V A:
  Gamma ⊩ V : A -> SN sstep_value V.
Proof.
  intros H % (StrongNormalisation.SemanticSoundness Gamma).
  specialize (H _ _ (G_id Gamma)).
  asimpl in H. 
  apply VV_sn in H.
  eapply SN_ext; [ | exact H].
  eapply sstep_strong_step_value. 
Qed.


Theorem strong_normalisation_cbn n (Gamma: cbn_ctx  n) P B:
  Gamma ⊢n P : B -> SN CBN.strongStory.Step P.
Proof.
  intros H % cbn_type_pres.
  apply strong_normalisation_cbpv in H.
  now eapply SN_CBN.
Qed.

Theorem strong_normalisation_cbvᵥ n (Gamma: ctx_cbv  n) P B:
  Gamma ⊩v P : B -> SN CBV.strongStory.StepVal P.
Proof.
  intros H % typingVal_pres.
  apply strong_normalisation_cbpvᵥ in H.
  now eapply SN_CBVᵥ.
Qed.

Theorem strong_normalisation_cbv n (Gamma: ctx_cbv  n) P B:
  Gamma ⊢v P : B -> SN CBV.strongStory.Step P.
Proof.
  intros H % typingExp_pres.
  apply strong_normalisation_cbpv in H.
  now eapply SN_CBV.
Qed.


(** ** Termination by Soundness of Denotational Semantics *)
Theorem denotation_termination P (G: groundtype):
  null ⊢ P : F G -> SN step P.
Proof.
  intros H % soundness. destruct H as [v H].
  eapply bigstep_sn, eval_bigstep; split; eauto.
Qed.
