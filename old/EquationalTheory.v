Set Implicit Arguments.
Require Export ObservationalEquivalence AbstractReductionSystems
        CBN.CBN_CBPV CBV.CBV_CBPV
        CBN.strongStory CBV.strongStory
        LogicalEquivalence.


(** * Equational Theory *)

(** ** Strong Equivalence *)
Definition Equiv {n: nat} := equiv (@sstep n).
Definition Equivᵥ {n: nat} := equiv (@sstep_value n).
Definition EquivCBN {n: nat} := equiv (@CBN.strongStory.Step n).
Definition EquivCBV {n: nat} := equiv (@CBV.strongStory.Step n).
Definition EquivCBVᵥ {n: nat} := equiv (@CBV.strongStory.StepVal n).

Lemma logical_equivalence_Equiv n (Gamma: ctx n) c c' B:
  Equiv c c' -> Gamma ⊢ c : B -> Gamma ⊢ c' : B ->  Gamma ⊨ c ∼ c' : B.
Proof.
  intros [v [H1 H2] ] % church_rosser H3 H4; eauto; transitivity v; [|symmetry].
  all: eapply logical_equivalence_strong_reduction_steps; eauto.
Qed.

Lemma logical_equivalence_Equivᵥ n (Gamma: ctx n) v v' A:
  Equivᵥ v v' -> Gamma ⊩ v : A -> Gamma ⊩ v' : A ->  Gamma ⊫ v ∼ v' : A.
Proof.
  intros [v'' [H1 H2] ] % church_rosser H3 H4; eauto; transitivity v''; [| symmetry].
  all: eapply logical_equivalence_strong_reduction_value_steps; eauto.
Qed.


 


Lemma equiv_translation_CBN n (s t: CBN.exp n):
  EquivCBN s t -> Equiv (CBN_CBPV.eval s) (CBN_CBPV.eval t).
Proof.
  unfold EquivCBN, Equiv; induction 1; eauto.
  - reflexivity.
  - rewrite <-IHstar.
    destruct H; [|symmetry].
    all: apply subrel_star_equiv, subrel_star, CBN.strongStory.Step_preserved, H.
Qed.

Lemma equiv_translation_CBV n (s t: CBV.Exp n):
  EquivCBV s t -> Equiv (CBV_CBPV.eval_exp s) (CBV_CBPV.eval_exp t).
Proof.
  unfold EquivCBN, Equiv; induction 1; eauto.
  - reflexivity.
  - rewrite <-IHstar.
    destruct H; [|symmetry].
      all: apply subrel_star_equiv, subrel_star, CBV.strongStory.Step_preserved, H.
Qed.


Lemma equiv_translation_CBVᵥ n (s t: CBV.Value n):
  EquivCBVᵥ s t -> Equivᵥ (CBV_CBPV.eval_val s) (CBV_CBPV.eval_val t).
Proof.
  unfold EquivCBN, Equiv; induction 1; eauto.
  - reflexivity.
  - rewrite <-IHstar.
    destruct H; [|symmetry].
    all: apply subrel_star_equiv, subrel_star, CBV.strongStory.StepVal_preserved, H.
Qed.



Require Import CBN.DenotationalSemantics CBV.DenotationalSemantics.



Theorem equiv_soundness_CBPV n (Gamma: ctx n) A (M N: CBPVc Gamma A):
  Equiv M N -> M ≃ N.
Proof.
    intros; eapply logical_equivalence_obseq, logical_equivalence_Equiv; eauto.
Qed.

Theorem equiv_soundness_CBPVᵥ n (Gamma: ctx n) A (V W: CBPVv Gamma A):
  Equivᵥ V W -> V ≈ W.
Proof.
  intros; eapply logical_equivalence_obseq, logical_equivalence_Equivᵥ; eauto.
Qed.

Theorem equiv_soundness_CBN n (Gamma: cbn_ctx n) A (s t: CBN Gamma A):
  EquivCBN s t -> s ≃n t.
Proof.
    intros.
    now apply CBN.DenotationalSemantics.obseq_soundness, equiv_soundness_CBPV, equiv_translation_CBN.
Qed.


Theorem equiv_soundness_CBV n (Gamma: ctx_cbv n) A (s t: CBV Gamma A):
  EquivCBV s t -> s ≃v t.
Proof.
  intros.
  now apply CBV.DenotationalSemantics.obseq_soundness, equiv_soundness_CBPV, equiv_translation_CBV.
Qed.

Theorem equiv_soundness_CBVᵥ n (Gamma: ctx_cbv n) A (s t: CBVᵥ Gamma A):
  EquivCBVᵥ s t -> s ≈v t.
Proof.
  intros.
  now apply CBV.DenotationalSemantics.obseq_soundnessᵥ, equiv_soundness_CBPVᵥ, equiv_translation_CBVᵥ.
Qed.


(** ** Levy Equations **)

Definition zero {n: nat} : value (S n) := var_value var_zero: value (S n).
Definition one {n: nat} : value (S (S n)) :=
  var_value (shift var_zero): value (S (S n)).

Definition sub n (v: value (S n)) : fin (S n) -> value (S n) :=
  scons v (shift >> var_value).

Definition sub₂ n (v: value (S (S n))) : fin (S n) -> value (S (S n)) :=
  v .: shift >> shift >> var_value.

Definition swap {n}: fin (S (S n)) -> value (S (S n)) :=
  (var 1 .: (var 0 .: (↑ >> (↑ >> ids)))).


(** *** eta laws *)
Lemma eta_thunk n (v: value n) Gamma A:
  Gamma ⊩ v : U A -> Gamma ⊫ v ∼ <{ v !}> : U A.
Proof.
  intros. intros ? ? ? ?.
  destruct (fundamental_property_value X H); exintuition.
  (* TODO AS: cbn unfolds substitution here *)
  asimpl.
  rewrite H1, H0. do 2 eexists; intuition.
  expand; repeat reduce; eauto.
Qed.


Lemma eta_let n (M: Syntax.comp n) Gamma A:
  Gamma ⊢ M : F A -> Gamma ⊨ M ∼ $ <- M; ret (var 0) : F A.
Proof.
  intros. intros ? ? ? ?.
  eapply bind with (K1 := Semantics.ectxHole)
                   (K2 := ectxLetin Semantics.ectxHole (ret (var 0))).
  eapply fundamental_property_comp; eauto.
  intros ? ? []; exintuition; subst.
  expand. cbn. reflexivity. cbn. reduce. reflexivity.
  eapply subrel_C_E. do 2 eexists. intuition. 
Qed.

(* uses weak normalisation *)
Lemma eta_lambda n (M: Syntax.comp (S n)) Gamma A B:
  Gamma ⊢ M : A → B ->  Gamma ⊨ M ∼ lambda (ren_comp shift M (var 0)) : A → B.
Proof.
  intros H ????. specialize (fundamental_property_comp H H0) as H1.
  unfold var; cbn [nat_to_fin]; asimpl.
  destruct H1; exintuition.
  do 2 eexists; intuition; eauto.
  destruct H4; exintuition; subst.
  do 2 eexists; intuition; eauto.
  asimpl. eapply bigstep_soundness in H1.
  eapply closure_under_expansion. reflexivity.
  rewrite H1. reduce. reflexivity.
  now eapply H6.
Qed.

(* uses weak normalisation *)
Lemma eta_pair  n (M: Syntax.comp n) Gamma A1 A2:
  Gamma ⊢ M : Pi A1 A2 -> Gamma ⊨ M ∼ tuple (proj true M) (proj false M) : Pi A1 A2.
Proof.
  intros H ????. specialize (fundamental_property_comp H H0) as H1.
  asimpl. destruct H1; exintuition.
  destruct H4; exintuition; subst.
  do 2 eexists. intuition; eauto.
  do 4 eexists; intuition; eauto.
  all: eapply closure_under_expansion.
  1, 4: reflexivity.
  1, 3: eapply bigstep_soundness in H1; rewrite H1; reduce; reflexivity.
  all: eauto.
Qed.

Lemma eta_caseS n (V: value n) (M: Syntax.comp (S n)) Gamma A1 A2 C:
  Gamma ⊩ V : Sigma A1 A2 ->
  Sigma A1 A2 .: Gamma ⊢ M : C ->
  Gamma ⊨ subst_comp (V..) M ∼ caseS V (subst_comp (sub (inj true zero)) M) (subst_comp (sub (inj false zero)) M) : C.
Proof.
  intros X Y. 
  intros ? ? ? ?.
  asimpl.
  specialize (fundamental_property_value X H) as [].
  exintuition; subst. rewrite H1, H0.
  destruct x1.
  all: asimpl.
  all: eapply closure_under_expansion.
  1, 4: reflexivity.
  1, 3: reduce; unfold sub, zero; asimpl; reflexivity.
  all: eapply fundamental_property_comp.
  all: eauto; eapply G_cons; eauto; cbn; do 3 eexists; intuition. 
Qed.



Lemma eta_caseP n (V: value n) (M: Syntax.comp (S n)) Gamma A1 A2 C:
  Gamma ⊩ V : A1 * A2 ->
  A1 * A2 .: Gamma ⊢ M : C ->
  Gamma ⊨ subst_comp (V..) M ∼ caseP V (subst_comp (sub₂ (pair one zero)) M) : C.
Proof.
  intros X Y. 
  intros ? ? ? ?.
  asimpl.
  specialize (fundamental_property_value X H) as [].
  exintuition; subst. rewrite H1, H0.
  eapply closure_under_expansion.
  reflexivity. reduce. unfold sub₂, one, zero. asimpl. reflexivity.
  eapply fundamental_property_comp; eauto.
  eapply G_cons; eauto.
  do 4 eexists; intuition; eauto.
Qed.

(** *** sequencing laws *)

Lemma commute_let_let n (M1: Syntax.comp n) (M2 M3: Syntax.comp (S n)) Gamma  C:
  Gamma ⊢ $ <- ($ <- M1; M2); M3 : C ->
  Gamma ⊨ $ <- ($ <- M1; M2); M3 ∼ $ <- M1; ($ <- M2; subst_comp (var 0 .: (↑ >> (↑ >> ids))) M3) : C.
Proof.
  intros H. inv H. inv X.
  unfold var; cbn. 
  intros ????. asimpl.
  eapply bind with (K1 := ectxLetin (ectxLetin Semantics.ectxHole _) _)
                   (K2 := ectxLetin Semantics.ectxHole _).
  eapply fundamental_property_comp; eauto.
  intros ??[]; exintuition; subst.
  cbn. eapply closure_under_expansion.
  1 - 2: reduce; asimpl; reflexivity.
  eapply bind with (K1 := ectxLetin Semantics.ectxHole _)
                   (K2 := ectxLetin Semantics.ectxHole _).
  eapply fundamental_property_comp; eauto.
  intros ??[]; exintuition; subst; cbn.
  eapply closure_under_expansion.
  1 - 2: reduce; asimpl; reflexivity.
  eapply fundamental_property_comp; eauto.
Qed.


(** uses weak normalisation *)
Lemma commute_let_lam n (M: Syntax.comp n) (N: Syntax.comp (S (S n))) Gamma A B:
  Gamma ⊢ $ <- M; lambda N : A → B ->
  Gamma ⊨ $ <- M; lambda N ∼ lambda ($ <- ren_comp ↑ M; subst_comp swap N) : A → B.
Proof.
  intros H. inv H. inv X0.
  unfold swap, var; cbn.
  intros ????. asimpl.
  eapply fundamental_property_comp in X; eauto.
  destruct X; exintuition.
  destruct H3; exintuition; subst.
  eapply bigstep_soundness in H1.
  eapply closure_under_expansion.
  rewrite H1. reduce. asimpl. reflexivity. reflexivity.
  eapply subrel_C_E.
  do 2 eexists; intuition; eauto.
  asimpl. eapply bigstep_soundness in H0.
  eapply closure_under_expansion. reflexivity.
  rewrite H0. reduce. asimpl. reflexivity.
  eapply fundamental_property_comp; eauto.
Qed.

(** uses weak normalisation **)
Lemma commute_let_tuple n (M: Syntax.comp n) (N1 N2: Syntax.comp (S n)) Gamma C1 C2:
  Gamma ⊢ $ <- M; tuple N1 N2 : Pi C1 C2 ->
  Gamma ⊨ $ <- M; tuple N1 N2 ∼ tuple ($ <- M; N1) ($ <- M; N2) : Pi C1 C2.
Proof.
  intros H. inv H. inv X0.
  intros ????. asimpl.
  eapply fundamental_property_comp in X; eauto.
  destruct X; exintuition.
  destruct H3; exintuition; subst.
  eapply bigstep_soundness in H1.
  eapply closure_under_expansion.
  rewrite H1. reduce. asimpl. reflexivity. reflexivity.
  eapply subrel_C_E.
  do 4 eexists; intuition; eauto.
  all: asimpl; eapply bigstep_soundness in H0.
  all: eapply closure_under_expansion. 
  1, 4: reflexivity.
  1, 3: rewrite H0; reduce; asimpl; reflexivity.
  all: eapply fundamental_property_comp; eauto.
Qed.



(** *** additional equations *)

Lemma commute_let_app B n Gamma c1 (c2: Syntax.comp (S n)) v:
  Gamma ⊢ (($ <- c1; c2) v) : B ->
  Gamma ⊨ (($ <- c1; c2) v) ∼ ($ <- c1; c2 (ren_value ↑ v)) : B.
Proof.
  intros ? ? ? ? ?.  inv X. inv X0. asimpl.
  eapply bind with (K1 := ectxApp (ectxLetin Semantics.ectxHole _) _)
                   (K2 := ectxLetin Semantics.ectxHole _); eauto.
  intros ? ? (? & ? & ?); intuition; subst.
  cbn; eapply closure_under_expansion; try reduce; try reflexivity.
  asimpl. apply_congruence; eauto.
Qed.


Lemma commute_caseS_lambda A B n Gamma c1 (c2: Syntax.comp (S (S n))) v:
  Gamma ⊢ caseS v (lambda c1) (lambda c2) : A → B ->
  Gamma ⊨ caseS v (lambda c1) (lambda c2) ∼
    lambda (caseS (ren_value ↑ v) (subst_comp swap c1) (subst_comp swap c2))
  : A → B.
Proof.
  intros H ? ? ? ?. inv H.
  inv X0. inv X1. asimpl.
  eapply fundamental_property_value in X; eauto.
  destruct X; exintuition; subst.
  rewrite H1; destruct x1;
  eapply closure_under_expansion.
  1, 4: reduce; reflexivity.
  1, 3: reflexivity.
  all: eapply subrel_C_E; do 2 eexists; intuition; asimpl. 
  all: rewrite H; eapply closure_under_expansion; try reduce; try reflexivity;
    asimpl.
  all: eapply fundamental_property; eauto.
  all: intros [ [|] |]; cbn; intuition; subst; eauto.
Qed.
