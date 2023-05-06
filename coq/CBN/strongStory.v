Require Import CBN.CBN_CBPV CBN.weakStory.

(** ** Translation and substitution commute *)

Lemma subst_pointwise m n (sigma tau : fin m -> value n) s :
  (forall i, star sstep (force (sigma i)) (force (tau i))) ->
  star sstep ((eval s)[sigma]) ((eval s)[tau]).
Proof.
  revert n sigma tau. induction s; cbn; intros; eauto.
  all: try now (rewrite IHs; eauto).
  all: try now (rewrite IHs1, IHs2; eauto).
  - rewrite IHs. reflexivity. auto_case.
    asimpl. unfold funcomp.
    change ((sigma f)⟨↑⟩ !) with (((sigma f)!)⟨↑⟩).
    now rewrite H.
  - rewrite !eagerlet_substcomp, IHs1. asimpl.
    rewrite IHs2, IHs3. reflexivity.
    + auto_case.
      unfold funcomp.
      change ((sigma f)⟨fun x : fin n => ↑ (↑ x)⟩ !) with ((sigma f)! ⟨fun x : fin n => ↑ (↑ x)⟩ ).
      now rewrite H.
    + auto_case.
      unfold funcomp.
      change ((sigma f)⟨fun x : fin n => ↑ (↑ x)⟩ !) with ((sigma f)! ⟨fun x : fin n => ↑ (↑ x)⟩ ).
      now rewrite H.
    + eauto.
Qed.

Lemma subst_pres m n (sigma : fin m -> exp n) s :
  star sstep ((eval s)[eval_subst sigma]) (eval (s[sigma])).
Proof.
  revert n sigma. induction s; cbn; intros; eauto.
  - unfold eval_subst. destruct (sigma f); eauto.
  - now rewrite eval_subst_up_value_value, IHs.
  - now rewrite IHs1, IHs2.
  - now rewrite IHs1, IHs2.
  - now rewrite IHs.
  - now rewrite IHs.
  - rewrite !eagerlet_substcomp, IHs1.
    rewrite !eval_subst_up_value_value.
    eapply proper_eagerlet_star_ssstep_R. reflexivity.
    rewrite <-IHs2, <-IHs3.
    eapply refl_star. asimpl. f_equal.
    all: change (_ .: sigma >> ⟨↑⟩) with (up_exp_exp sigma).
    all: rewrite <-eval_subst_up_value_value; asimpl.
    all: reflexivity. 
Qed.

(** * Strong reduction CBN *)

Reserved Notation "s ≫ t" (at level 60).

Set Implict Arguments.

Inductive Step {n} : exp n -> exp n -> Prop :=
  | StepLam (M M' : exp (S n)) : @Step (S n) M M' -> Step (Lam M) (Lam M')

  | StepApp1 (M : exp n) M' N : Step M M' -> Step (App M N) (App M' N)
  | StepApp2 (M : exp n) N N' : Step N N' -> Step (App M N) (App M N')
  | StepAppLam (M : exp (S n)) M' (N: exp n): M' = M[N..] -> Step (App ((Lam M)) (N)) M'

  | StepPair1 (M M' N : exp n) : Step M M' -> Step (Pair M N) (Pair M' N)
  | StepPair2 (M N N' : exp n) : Step N N' -> Step (Pair M N) (Pair M N')

  | StepInj b (M M' : exp n) : Step M M' -> Step (Inj b M) (Inj b M')

  | StepProj b (M M' : exp n) : Step M M' -> Step (Proj b M) (Proj b M')
  | StepProjPair b (M M' : exp n) : Step (Proj b (Pair M M')) (if b then M else M')

  | StepCaseS1 (M : exp n) M' N1 N2 : Step M M' -> Step (CaseS M N1 N2) (CaseS M' N1 N2)
  | StepCaseS2 (M : exp n)  (N1 N1' : exp (S n)) N2 : @Step _ N1 N1' -> Step (CaseS M N1 N2) (CaseS M N1' N2)
  | StepCaseS3 (M : exp n)  N1 N2 N2' : @Step (S n) N2 N2' -> Step (CaseS M N1 N2) (CaseS M N1 N2')
  | StepCaseS b (M : exp n)  N1  N2 : Step (CaseS (Inj b M) N1 N2) (if b then N1 else N2)[M..]
where "s ≫ t" := (@Step _ s t).
Hint Constructors Step.

(** ** Forward simulation *)

(** Reduction tactic for beta reduction step *)
(* Duplicate, should remove at some point *)
Ltac reduce := econstructor 2; [ solve [eauto] | cbn ].

Ltac dostep :=
  match goal with
  | [ |- star _ _ _ ] => econstructor; [ eapply sstepPrimitive; repeat econstructor |  ]
  | [ |- plus _ _ _ ] => eapply step_star_plus; [ eapply sstepPrimitive; repeat econstructor |  ]
  end.

Lemma beta_step_preserved m (s : exp (S m)) (t : exp m) :
  star sstep ((eval s)[(thunk (eval t))..]) (eval (s[t..])).
Proof.
  rewrite <- (subst_pres _ _ (t..) s).
  erewrite subst_pointwise. reflexivity.
  intros []. cbn. reflexivity.
  cbn. destruct t; try reflexivity.
  cbn. now dostep.
Qed.

Lemma Step_preserved {n: nat} (s t : exp n) :
  Step s t ->  (plus sstep) (eval s) (eval t).
Proof.
  induction 1; cbn; asimpl;  try now trewrite IHStep.
  - dostep. subst. now rewrite beta_step_preserved.
  - destruct b; eauto.
  - trewrite IHStep; try reflexivity.
    hnf. intros.
    eapply proper_eagerlet_plus_sstep_L. eauto. intros; cbn; asimpl; eapply step_star_plus; eauto.
  - trewrite IHStep; try reflexivity.
    hnf. intros.
    eapply proper_eagerlet_plus_sstep_R; eauto.
    eapply plus_proper_sstep_caseS2; eauto.
    substify. now eapply plus_sstep_preserves.
  - trewrite IHStep; try reflexivity.
    hnf. intros.
    eapply proper_eagerlet_plus_sstep_R; eauto.
    eapply plus_proper_sstep_caseS3; eauto.
    substify. now eapply plus_sstep_preserves.
  - eapply step_star_plus. eauto.
    destruct b; now eapply beta_step_preserved.
Qed.

Lemma Steps_preserved {n: nat} (s t : exp n) :
  star Step s t ->  (star sstep) (eval s) (eval t).
Proof.
  induction 1.
  - reflexivity.
  - rewrite <- IHstar. eapply plus_star. now eapply Step_preserved.
Qed.

Lemma terminal_step n (s : exp n) :
  Normal Step s -> Normal sstep (eval s).
Proof.
  intros ? ? ?; induction s; cbn in *.
  - inv H0. inv H2. inv H1.
  - inv H0. inv H2. inv H1.
  - inv H0. eapply IHs. intros ? ?. eapply H. eauto. eauto. inv H1.
  - inv H0.
    + eapply IHs1. intros ? ?. eapply H. eauto. eauto.
    + inv H4. eapply IHs2. intros ? ?. eapply H. eauto. eauto.
    + inv H1. destruct s1; inv H0. eapply H. eauto.
      destruct (eval s1_1); inv H2.
  - inv H0.
    + eapply IHs1. intros ? ?. eapply H. eauto. eauto.
    + eapply IHs2. intros ? ?. eapply H. eauto. eauto.
    + inv H1.
  - inv H0.
    + eapply IHs. intros ? ?. eapply H. eauto. eauto.
    + inv H1. destruct s; inv H3. eapply H. eauto.
      destruct (eval s1); inv H1.
  - inv H0. inv H2. inv H4.
    + eapply IHs. intros ? ?. eapply H. eauto. eauto.
    + inv H1.
  - destruct (eagerlet_inv (eval s1) (caseS (var_value var_zero) (ren_comp ren_up (eval s2)) (ren_comp ren_up (eval s3)))) as [ [HH HHH ] | [V [] ] ].
    cbn in *. rewrite HH in H0.
    inv H0.
    + eapply IHs1. intros ? ?. eapply H. eauto. eauto.
    + inv H4. inv H5.
      * eapply step_ren_comp_inv in H5 as (? & ? & ?); subst. 2:reflexivity.
        eapply IHs2. intros ? ?. eapply H. eauto. eauto.
      * eapply step_ren_comp_inv in H5 as (? & ? & ?); subst. 2:reflexivity.
        eapply IHs3. intros ? ?. eapply H. eauto. eauto.
      * inv H0.
    + inv H1. destruct s1; inv H0.
      * eapply HHH. cbn. eauto.
      * eapply H. eauto.
      * destruct (eval s1_1); inv H2.
    + destruct s1; inv e.
      * inv e0. cbn in H0. inv H0.
        -- inv H5.
        -- asimpl in H5. eapply IHs2; eauto. intros ? ?; eapply H; eauto.
        -- asimpl in H5. eapply IHs3; eauto. intros ? ?; eapply H; eauto.
        -- inv H1.
      * eapply H. eauto.
      * destruct (eval s1_1); inv H2.
Qed.

Lemma evaluates_forward n (s t : exp n) :
  evaluates Step s t -> evaluates sstep (eval s) (eval t).
Proof.
  intros []. split.
  - clear H0. induction H.
    + reflexivity.
    + etransitivity; try eassumption.
      now eapply plus_star, Step_preserved.
  - now eapply terminal_step.
Qed.


Lemma SN_CBN n s :
  SN (@sstep n) (eval s) -> SN (@Step n) s.
Proof.
  intros. remember (eval s) as C eqn:E. revert s E.
  eapply SN_plus in H. induction H.
  econstructor. subst.
  intros ? ? % Step_preserved. eauto.
Qed.

(** ** Backward Simulation *)

Instance proper_Step_Pair n :
  Proper (star Step ==> eq ==> star Step) (@Pair n).
Proof.
  cbv. intros; subst. induction H; eauto.
Qed.


Instance proper_Step_Pair2 n :
  Proper (eq ==> star Step ==> star Step) (@Pair n).
Proof.
  cbv. intros; subst. induction H0; eauto.
Qed.

Instance proper_Step_App n :
  Proper (star Step ==> eq ==> star Step) (@App n).
Proof.
  cbv. intros; subst. induction H; eauto.
Qed.


Instance proper_Step_App2 n :
  Proper (eq ==> star Step ==> star Step) (@App n).
Proof.
  cbv. intros; subst. induction H0; eauto.
Qed.


Instance proper_Step_Lam n :
  Proper (star Step ==> star Step) (@Lam n).
Proof.
  cbv. intros; subst. induction H; eauto.
Qed.


Instance proper_Step_Proj n :
  Proper (eq ==> star Step ==> star Step) (@Proj n).
Proof.
  cbv. intros; subst. induction H0; eauto.
Qed.


Instance proper_Step_Inj n :
  Proper (eq ==> star Step ==> star Step) (@Inj n).
Proof.
  cbv. intros; subst. induction H0; eauto.
Qed.

Instance proper_Step_Case n :
  Proper (star Step ==> eq ==> eq ==> star Step) (@CaseS n).
Proof.
  cbv. intros; subst. induction H; eauto.
Qed.

Instance proper_Step_Case2 n :
  Proper (eq ==> star Step ==> eq ==> star Step) (@CaseS n).
Proof.
  cbv. intros; subst. induction H0; eauto.
Qed.

Instance proper_Step_Case3 n :
  Proper (eq ==> eq ==> star Step ==> star Step) (@CaseS n).
Proof.
  cbv. intros; subst. induction H1; eauto.
Qed.


Lemma Step_inj_inv n (s s'' : exp n) b :
  star Step (Inj b s) s'' -> exists s', s'' = Inj b s' /\ star Step s s'.
Proof.
  remember (Inj b s) as t. intros H. revert s Heqt; induction H; intros; subst.
  - eauto.
  - inv H. edestruct IHstar as (? & -> &?); eauto.
Qed.

Lemma refines_to_eval n (C : comp n) s :
  C ⋙ s -> exists t, C ↪* eval t /\ star Step s t.
Proof.
  induction 1; cbn.
  - exists (var_exp x). cbn. eauto.
  - exists One. cbn. eauto.
  - destruct IHX as (t & ? & ?). exists (Lam t).
    rewrite H, H0. eauto.
  - destruct IHX1 as (t1 & ? & ?).
    destruct IHX2 as (t2 & ? & ?). exists (App t1 t2).
    rewrite H, H0, H1, H2. eauto.
  - destruct IHX1 as (t1 & ? & ?).
    destruct IHX2 as (t2 & ? & ?). exists (Pair t1 t2).
    rewrite H, H0, H1, H2. eauto.
  - destruct IHX as (t & ? & ?). exists (Proj b t).
    rewrite H, H0. eauto.
  - destruct IHX as (t & ? & ?). exists (Inj b t).
    rewrite H, H0. eauto.
  - destruct IHX1 as (s' & ? & ?).
    destruct IHX2 as (t1' & ? & ?).
    destruct IHX3 as (t2' & ? & ?).
    exists (CaseS s' t1' t2'). subst.
    rewrite H, H1, H3, H0, H2, H4. split. 2:eauto.
    now rewrite let_to_eagerlet.
  - destruct IHX1 as (s' & ? & ?).
    destruct IHX2 as (t1' & ? & ?).
    destruct IHX3 as (t2' & ? & ?).
    inv X1.
    + eapply ret_star_inv in H as (? & ? & ?).
      inv H0. inv H. 2:inv H6. asimpl.
      eexists. split. 2: now rewrite H2, H4. cbn. asimpl. now rewrite H1, H3.
    + eapply ret_star_inv in H as (? & ? & ?). destruct s'; inv H.
      eapply inj_star_inv in H5 as (? & ? & ?). inv H.
      eapply Step_inj_inv in H0 as (? & ? & ?). inv H.
      destruct b; eexists; split.
      * rewrite H1, H3. rewrite H5 at 1. econstructor. eauto. asimpl. eapply beta_step_preserved.
      * rewrite H2, H0. eauto.
      * rewrite H1, H3. rewrite H5 at 1. econstructor. eauto. asimpl. eapply beta_step_preserved.
      * rewrite H4, H0. eauto.
      * destruct (eval s'1); inv H7.
  - destruct IHX as (t & ? & ?). eauto.
Qed.

Ltac slv HH := let H := fresh "H" in
  edestruct HH as (? & [] & H); eauto;
  try eexists; split; [ | now rewrite H]; (do 10 try econstructor); eauto.

Lemma refines_step n (C C' : comp n) s : sstep C C' -> C ⋙ s -> exists t, inhab (C' ⋙ t) /\ star Step s t.
Proof.
  intros H1 H2. revert C' H1. induction H2; cbn; intros; inv H1.
  all: try solve [invp @sstep || invp @sstep_value || invp @pstep].
  all: try now slv IHrefines.
  all: try now slv IHrefines1.
  all: try now slv IHrefines2.
  - inv H3. slv IHrefines2.
  - inv H. inv H2_. eexists. split.
    + econstructor. eapply refines_beta; eauto.
    + eauto.
  - inv H. inv H2. destruct b; eauto.
  - inv H0. inv H4. slv IHrefines.
  - edestruct IHrefines1 as (? & [] & H); eauto.
    eexists. split. 2: now rewrite H. asimpl. eauto.
  - inv H3. inv H4.
    + eapply step_ren_comp_inv in H4 as (? & ? & ->); eauto.
      edestruct IHrefines2 as (? & [] & HH); eauto.
      eexists. split. 2: now rewrite HH. asimpl. eauto.
    + eapply step_ren_comp_inv in H4 as (? & ? & ->); eauto.
      edestruct IHrefines3 as (? & [] & HH); eauto.
      eexists. split. 2: now rewrite HH. asimpl. eauto.
    + inv H.
  - inv H. inv H2_.
    + eexists. split. econstructor. repeat econstructor; eauto. reflexivity.
    + eexists. split. econstructor. repeat econstructor; eauto. reflexivity.
  - inv H2_. inv H4. inv H4. inv H2.
    edestruct IHrefines1 as (? & [] & ?). eauto. inv X0.
    eexists. split. econstructor. 2:rewrite H. 2:reflexivity.
    destruct b.
    + eapply refines_help. eapply refines_CaseS2. 4: asimpl; cbn; now asimpl. all:eauto.
    + eapply refines_help. eapply refines_CaseS2. 4: asimpl; cbn; now asimpl. all:eauto.
  - asimpl in H4. inv H2_. 
    * edestruct IHrefines2 as (? & [] & ?). eauto.
      eexists. split. econstructor. eapply refines_help.
      eapply refines_CaseS2. 4: now asimpl. all:eauto. now rewrite H.
    *  edestruct IHrefines2 as (? & [] & ?). eauto.
       eexists. split. econstructor. 2:rewrite H. 2:reflexivity. 
       destruct b.
       -- eapply refines_help. eapply refines_CaseS2. 4: asimpl; cbn; now asimpl. all:eauto.
       -- eapply refines_help. eapply refines_CaseS2. 4: asimpl; cbn; now asimpl. all:eauto.
  - asimpl in H4. inv H2_.
    + edestruct IHrefines3 as (? & [] & ?). eauto.
      eexists. split. econstructor. eapply refines_help.
      eapply refines_CaseS2. 4: now asimpl. all:eauto. now rewrite H.
    + edestruct IHrefines3 as (? & [] & ?). eauto.
      eexists. split. econstructor. 2:rewrite H. 2:reflexivity.
      destruct b.
      * eapply refines_help. eapply refines_CaseS2. 4: asimpl; cbn; now asimpl. all:eauto.
      * eapply refines_help. eapply refines_CaseS2. 4: asimpl; cbn; now asimpl. all:eauto.
  - asimpl in H. inv H. inv H2_.
    destruct b.
    + eexists. split. econstructor. eapply refines_beta; eauto. eauto.
    + eexists. split. econstructor. eapply refines_beta; eauto. eauto.
  - inv H0. eapply IHrefines in H1 as (? & [] & ?). eauto.
  - inv H. eauto.
Qed.

Lemma refines_steps n (C C' : comp n) s : star sstep C C' -> C ⋙ s -> exists t, inhab (C' ⋙ t) /\ star Step s t.
Proof.
  intros H. revert s; induction H; cbn; intros.
  - eauto.
  - eapply refines_step in H as (? & [] & ?); eauto.
    edestruct IHstar as (? & ? & ?); eauto.
Qed.

Lemma Steps_backwards {n: nat} (s : exp n) (C: comp n) :
   eval s ↪* C -> exists t : exp n, C ↪* eval t /\ star Step s t.
Proof.
  intros. pose proof (trans_refines _ _ _ (trans_eval s)).
  eapply refines_steps in X as (t & [] & ?); eauto.
  eapply refines_to_eval in X as (t' & ? & ?).  eauto.
Qed.

Require Import Confluence.

Notation "s ↪+ t" := (plus sstep s t) (at level 58).




Lemma confluence n :
  confluent (@Step n).
Proof.
  intros ? ? ? ? % Steps_preserved ? % Steps_preserved.
  eapply confluence in H0. specialize (H0 H) as [].
  eapply refines_steps in H0 as (? & [] & ?). 2:eapply trans_refines, trans_eval.
  eapply refines_steps in H1 as (? & [] & ?). 2:eapply trans_refines, trans_eval.
  assert (x1 = x2) as -> by (eapply refines_functional; eauto).
  firstorder.
Qed.

Lemma evaluates_backwards n (s : exp n) C :
  evaluates sstep (CBN_CBPV.eval s) C -> exists t, C = CBN_CBPV.eval t /\ evaluates Step s t.
Proof.
  intros []. eapply Steps_backwards in H as (t & ? & ?).
  inv H.
  + exists t; repeat split; eauto. intros ? ?. eapply Step_preserved in H. inv H; eapply H0; eauto.
  + firstorder.
Qed.
