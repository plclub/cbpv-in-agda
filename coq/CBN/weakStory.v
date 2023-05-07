Require Import CBN_CBPV.
Import CommaNotation.

(** * Weak Reduction CBN *)

Reserved Notation "s ≫ t" (at level 60).
Inductive Step {n} : exp n -> exp n -> Prop :=
  | StepApp1 (M : exp n) M' N : Step M M' -> Step (App M N) (App M' N)
  | StepAppLam (M : exp (S n)) M' (N: exp n): M' =  subst_exp (N..) M -> Step (App ((Lam M)) (N)) M'

  | StepProj b (M M' : exp n) : Step M M' -> Step (Proj b M) (Proj b M')
  | StepProjPair b (M M' : exp n) : Step (Proj b (Pair M M')) (if b then M else M')

  | StepCaseS1 (M : exp n) M' N1 N2 : Step M M' -> Step (CaseS M N1 N2) (CaseS M' N1 N2)
  | StepCaseS b (M : exp n)  N1  N2 : Step (CaseS (Inj b M) N1 N2) (subst_exp (M..) (if b then N1 else N2))
where "s ≫ t" := (Step s t).
Hint Constructors Step.

Instance proper_Step_App n :
  Proper (star Step ==> eq ==> star Step) (@App n).
Proof.
  cbv. intros; subst. induction H; eauto.
Qed.

Instance proper_Step_Proj n :
  Proper (eq ==> star Step ==> star Step) (@Proj n).
Proof.
  cbv. intros; subst. induction H0; eauto.
Qed.

Instance proper_Step_Case n :
  Proper (star Step ==> eq ==> eq ==> star Step) (@CaseS n).
Proof.
  cbv. intros; subst. induction H; eauto.
Qed.

(** ** Forward Simulation *)
Lemma trans_beta  (n : nat) (t0 : exp n) (M0 : exp (S n)) (N : comp n) (M : comp (S n)) :
            M0 ↦n M -> t0 ↦n N -> subst_exp (t0..) M0 ↦n subst_comp (<{ N }>..) M.
Proof.
  intros.
  eapply trans_subst. eauto. intros []; cbn.
  - econstructor.
  - econstructor. eassumption.
Qed.

Lemma Step_preserved (n : nat) (s t : exp n) C :
  s ≫ t -> s ↦n C -> exists C', inhab (t ↦n C') /\ C >+ C'.
Proof.
  induction 2; cbn in *; [ (inv H) .. | ].
  - eapply IHX1 in H3 as (C' & [] & ?).
    exists (app C' (thunk N)). split; eauto using inhab.
    now trewrite H.
  - clear IHX1 IHX2. remember (Lam M0). induction X1; try congruence.
    + inv Heqe. exists (subst_comp ((thunk N) ..) M). split.
      * econstructor. now eapply trans_beta.
      * eauto.
    + eapply IHX1 in Heqe as (C' & [] & ?); eauto.
      exists C'. split.
      * eauto using inhab.
      * eauto.
  - eapply IHX in H3 as (C' & [] & ?).
    exists (proj b C'). split. eauto using inhab.
    now trewrite H.
  - clear IHX. remember (Pair M0 M'). induction X; try congruence.
    + inv Heqe.
      destruct b; eexists; split; eauto using inhab.
    + eapply IHX in Heqe as (C' & [] & ?).
      destruct b; eexists; split; eauto using inhab.
  - rename M' into t. eapply IHX1 in H4 as (M' & [] & ?).
    eexists. split. 2:{ idtac. eapply proper_eagerlet_plus_step_L; eauto. }
    econstructor. econstructor; eauto.
  - clear IHX1 IHX2 IHX3. remember (Inj b M0); induction X1; try congruence.
    + inv Heqe.
      destruct b.
      * exists (subst_comp ((thunk M)..) N1); split; eauto using inhab.
        -- econstructor. now eapply trans_beta.
        -- eapply step_star_plus. cbn. eauto. now asimpl.
      * exists (subst_comp ((thunk M)..) N2); split; eauto using inhab.
        -- econstructor. now eapply trans_beta.
        -- eapply step_star_plus. cbn. eauto. now asimpl.
    + eapply (IHX1 t1 t2)  in Heqe as (C' & [] & ?); eauto.
      exists C'. split. eauto using inhab.
      eapply plus_star_step. eapply proper_eagerlet_plus_step_L; eauto.
      eapply plus_star; eauto.
  - eapply IHX in H as (C' & [] & ?).
    exists C'; eauto using inhab.
Qed.

Hint Constructors inhab.

Lemma Steps_preserved (n : nat) (s t : exp n) C :
  star Step s t -> s ↦n C -> exists C', inhab (t ↦n C') /\ star step C C'.
Proof.
  intros. revert C X; induction H; cbn; intros.
  - eauto.
  - eapply Step_preserved in H as (C' & [] & ?); eauto.
    eapply IHstar in X0 as (C'' & [] & ?); eauto.
    exists C''. split; eauto. transitivity C'. eapply subrel_star. eauto. eauto.
Qed.

Lemma WN_translates n (s : exp n) C :
  SN step C -> s ↦n C -> SN Step s.
Proof.
  intros H % SN_plus. revert s. induction H. econstructor.
  intros. eapply Step_preserved in H1 as (C' & [] & ?); eauto.
Qed.

(** ** Backward Simulation *)
Lemma Normal_preserved n (s : exp n) :
  Normal Step s -> Normal step (eval s).
Proof.
  induction s; intros.
  all: try now (intros ? Hs; inv Hs; inv H0).
  - intros ? Hs. inv Hs.
    + inv H0. destruct s1; inv H1. eapply H. eauto.
      destruct (eval s1_1); inv H2.
    + eapply IHs1. intros ? ?. eapply H. eauto. eauto.
  - intros ? Hs. inv Hs.
    + inv H0. destruct s; inv H3. eapply H. eauto.
      destruct (eval s1); inv H1.
    + eapply IHs. intros ? ?. eapply H. eauto. eauto.
  - intros ? Hs. cbn in Hs.
    destruct (eagerlet_inv (eval s1) (caseS (var_value var_zero) (ren_comp ren_up (eval s2)) (ren_comp ren_up (eval s3)))) as [ [] | (? & ? & ?) ].
    *  cbn in *. rewrite e in Hs. clear e. inv Hs.
       -- inv H0. destruct s1; inv H1.
          ++ eapply n; cbn; eauto.
          ++ eapply H.  eauto.
          ++ destruct (eval s1_1); inv H2.
       -- eapply IHs1. intros ? ?. eapply H. eauto. eauto.
    * destruct s1; inv e.
      -- inv Hs. inv e0. inv H0.
      -- eapply H; eauto.
      -- cbn in Hs. destruct (eval s1_1); inv H1.
Qed.

Lemma Normal_preserved' n (s : exp n) C :
  s ↦n C -> Normal Step s -> exists C', C >* C' /\ inhab (s ↦n C') /\ Normal step C'.
Proof.
  intros. induction X.
  all: try now (eexists; repeat split; eauto; intros ? Hs; inv Hs; inv H0).
  - destruct IHX1 as (C' & ? & [] & ?). intros ? ?. eapply H. eauto.
    exists (C' (thunk N)). repeat split.
    + now rewrite H0.
    + eauto.
    + intros ? ?. inv H2. inv H3. inv X.
      eapply H. eauto. 2:firstorder.
      destruct M0; subst; try now inv H2.
  - destruct IHX as (C' & ? & [] & ?). intros ? ?. eapply H. eauto.
    exists (proj b C'). repeat split.
    + now rewrite H0.
    + eauto.
    + intros ? ?. inv H2. inv H3. inv X0.
      eapply H. eauto. destruct M0; inv H2. firstorder.
  - destruct IHX1 as (C' & ? & [] & ?). intros ? ?. eapply H. eauto.
    eexists. repeat split. 2: eauto.
    + now rewrite H0.
    + intros ? ?. destruct C'.
      all: try (inv H2; [ inv H3 | inv H6; inv H2 ]).
      * eapply H1; firstorder.
      * inv H2. inv H3. inv H6. inv H2. eapply H1; firstorder. eapply H1; eauto.
      * inv H2. inv H3. inv X. eapply H. eauto.
        destruct M0; inv H2.
      * inv H2. inv H3. inv H6. inv H2. eapply H1; eauto. eapply H1; eauto.
      * inv H2. inv H3. inv H6. inv H2. eapply H1; eauto. eapply H1; eauto.
      * eapply H1; eauto.
      * eapply H1; eauto.
  - destruct IHX as (C' & ? & [] & ?). intros ? ?. eapply H. eauto.
    exists C'. repeat split; eauto.
Qed.


Lemma evaluates_to {n : nat} (s t : exp n) M :
  evaluates Step s t -> s ↦n M -> exists N, inhab (t ↦n N) /\ evaluates step M N.
Proof.
  intros []. intros. eapply Steps_preserved in H as (C' & [] & ?); eauto.
  eapply Normal_preserved' in H0 as (C'' & ? & [] & ?); eauto.
  exists C''. repeat split; eauto.
Qed.

Lemma refines_beta:
  forall (n : nat) (N1 : comp (S n)) (M : comp n) (t1 : exp (S n)) (s : exp n),
    N1 ⋙ t1 -> M ⋙ s -> subst_comp (<{ M }> ..) N1 ⋙ subst_exp (s..) t1.
Proof.
  intros.
  eapply refines_subst. eauto. intros []; cbn.
  - econstructor.
  - econstructor. eassumption.
Qed.

Lemma refines_step n (C C' : comp n) s : step C C' -> C ⋙ s -> exists t, inhab (C' ⋙ t) /\ star Step s t.
Proof.
  intros H. revert s. induction H; cbn; intros. inv H.
  + inv X. eauto.
  + inv X. inv X0. eexists. split. econstructor. eapply refines_beta; eauto.
    eauto.
  + inv X. inv X0. destruct b; eexists; split; eauto.
  + inv X. inv X0.
    * eexists. split. econstructor. econstructor; eauto. eauto.
    * eexists. split. econstructor. econstructor; eauto. eauto.
  + inv X. inv X0. destruct b.
    * eexists. split. econstructor. eapply refines_beta; eauto.
      asimpl. eauto. eauto.
    * eexists. split. econstructor. eapply refines_beta; eauto.
      asimpl. eauto. eauto.
  + inv X.
  + inv X. eapply IHstep in X0 as (? & [] & ?).
    eexists. split. eauto. now rewrite H0.
  + inv X. eapply IHstep in X0 as (? & [] & ?).
    eexists; split. eauto. now rewrite H0.
  + inv X. destruct (IHstep _ X0) as (? & [] & ?).
    eexists. split. econstructor. 2: now rewrite H0.
    econstructor; eauto. 
Qed.

Lemma refines_steps n (C C' : comp n) s : star step C C' -> C ⋙ s -> exists t, inhab (C' ⋙ t) /\ star Step s t.
Proof.
  intros ?. revert s. induction H; cbn; intros.
  - eauto.
  - eapply refines_step in H as (? & [] & ?); eauto.
    edestruct IHstar as (? & ? & ?); eauto.
Qed.

Lemma backwards n (C C' : comp n) s t :
  star step C C' -> s ↦n C -> t ↦n C' -> star Step s t.
Proof.
  intros ? ? % trans_refines ? % trans_refines.
  eapply refines_steps in H as (t' & [] & ?); eauto.
  now pose proof (refines_functional _ _ _ _ X1 X0) as ->.
Qed.

Lemma Step_preserved_refines (n : nat) (s t : exp n) C :
  s ≫ t -> s ⋘ C -> exists C', inhab (t ⋘ C') /\ plus step C C'.
Proof.
  induction 2; cbn in *; [ (inv H) .. | ].
  - eapply IHX1 in H3 as (C' & [] & ?).
    exists (app C' (thunk N)). split; eauto using inhab.
    now trewrite H.
  - clear IHX1 IHX2. remember (Lam M0). induction X1; try congruence.
    + inv Heqe. exists (subst_comp ((thunk N) ..) M). split.
      * econstructor. now eapply refines_beta.
      * eauto.
    + eapply IHX1 in Heqe as (C' & [] & ?); eauto.
      exists C'. split.
      * eauto using inhab.
      * eauto.
  - eapply IHX in H3 as (C' & [] & ?).
    exists (proj b C'). split. eauto using inhab.
    now trewrite H.
  - clear IHX. remember (Pair M0 M'). induction X; try congruence.
    + inv Heqe.
      destruct b; eexists; split; eauto using inhab.
    + eapply IHX in Heqe as (C' & [] & ?).
      destruct b; eexists; split; eauto using inhab.
  - eapply IHX1 in H4 as (C' & [] & ?).
    eexists. split. repeat (econstructor; try eassumption).
    now trewrite H.
  - clear IHX1 IHX2 IHX3. remember (Inj b M0); induction X1; try congruence.
    + inv Heqe.
      destruct b.
      * exists (subst_comp ((thunk M)..) N1); split; eauto using inhab.
        -- econstructor. now eapply refines_beta.
        -- econstructor 2. eauto. cbn. eapply step_star_plus. eauto. now asimpl.
      * exists (subst_comp ((thunk M)..) N2); split; eauto using inhab.
        -- econstructor. now eapply refines_beta.
        -- econstructor 2. eauto. cbn. eapply step_star_plus. eauto. now asimpl.
    + eapply (IHX1 t1 t2)  in Heqe as (C' & [] & ?); eauto.
      exists C'. split. eauto using inhab.
      econstructor 2; eauto.
  - inv X1. inv H4. inv H4.
  - inv X1. destruct b.
    + exists (subst_comp ((thunk M0)..) N1); split; eauto using inhab.
      * econstructor. now eapply refines_beta.
      * eapply step_star_plus. eauto. now asimpl.
    + exists (subst_comp ((thunk M0)..) N2); split; eauto using inhab.
      * econstructor. now eapply refines_beta.
      * eapply step_star_plus. eauto. now asimpl.
  - eapply IHX in H as (C' & [] & ?).
    exists C'; eauto using inhab.
Qed.


Lemma backwards_evaluates n (C C' : comp n) s :
  evaluates step C C' -> C ⋙ s -> exists t, inhab (C' ⋙ t) /\ evaluates Step s t.
Proof.
  intros [] ?. eapply refines_steps in H as (t & [] & ?); eauto.
  exists t. repeat split; eauto. intros ? ?.
  eapply Step_preserved_refines in H1 as (? & [] & ?); eauto.
  inv H1; firstorder.
Qed.
