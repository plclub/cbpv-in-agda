Require Import Morphisms.
Require Export CBV_CBPV.
Import CommaNotation.

(** * Weak Reduction CBN *)
Inductive Step : forall {n}, Exp n -> Exp n -> Prop :=
  | StepApp1 n (M : Exp n) M' N : Step M M' -> Step (App M N) (App M' N)
  | StepApp2 n (V : Value n) N N' : Step N N' -> Step (App (Val V) N) (App (Val V) N')
  | StepAppLam n (M : Exp (S n)) M' (N: Value n): M' = subst_Exp (N..) M -> Step (App (Val (Lam M)) (Val N)) M'

  | StepCaseS1 n (M : Exp n) M' N1 N2 : Step M M' -> Step (CaseS M N1 N2) (CaseS M' N1 N2)
  | StepCaseS n (b: bool) V (N1 N2 : Exp (S n)) M : M = subst_Exp (V..) (if b then N1 else N2) -> Step (CaseS (Val (Inj b V)) N1 N2) M

  | StepCaseP1 n (M : Exp n) M' N : Step M M' -> Step (CaseP M N) (CaseP M' N)
  | StepCaseP n N (N' : Exp n) V1 V2: N' = subst_Exp (V2,V1..) N  -> Step (CaseP (Val (Pair V1 V2)) N) N'.

Hint Constructors Step.

Instance proper_Step_App n :
  Proper (star Step ==> eq ==> star Step) (@App n).
Proof. cbv. intros; subst. induction H; eauto. Qed.

Instance proper_Step_Case n :
  Proper (star Step ==> eq ==> eq ==> star Step) (@CaseS n).
Proof.
  cbv. intros; subst. induction H; eauto.
Qed.

Instance proper_Step_CaseP n :
  Proper (star Step ==> eq ==> star Step) (@CaseP n).
Proof.
  cbv. intros; subst. induction H; eauto.
Qed.

Notation "A >+ B" := (plus step A B) (at level 60).

(** ** Forward Simulation *)

(** Weak steps of CBV can be simulated by genuine weak steps of CBPV *)
Lemma Step_preserved {n: nat} (M M' : Exp n) :
  Step M M' ->  (eval_exp M) >+ (eval_exp M').
Proof.
  induction 1; cbn; subst; asimpl.
  all: try (now apply proper_eagerlet_plus_step_L).
  all: try (rewrite !eagerlet_substcomp).
  - apply proper_eagerlet_plus_step_L; eauto.
    now asimpl.
  - eright.
    + apply stepApp. repeat constructor.
    + repeat constructor.
      rewrite trans_subst_exp; now asimpl.
  - left.
    repeat constructor.
    destruct b; rewrite trans_subst_exp; now asimpl.
  - left.
    repeat constructor.
    rewrite trans_subst_exp; now asimpl.
Qed.

(** A row of weak steps of CBN can be simulated by a row of weak steps of CBPV *)
Lemma MStep_preserved {n: nat} (M M' : Exp n) :
  star Step M M' -> star step (eval_exp M) (eval_exp M').
Proof.
  induction 1.
  - reflexivity.
  - apply Step_preserved in H. induction H; eauto.
Qed.


(** ** Termination *)
Lemma Normal_preserved n (s : Exp n) :
  Normal Step s -> Normal step (eval_exp s).
Proof.
  induction s; simpl; intros A s' H.
  - inv H. inv H0.
  - letc_step_inv.
    + inv H. inv H0. eauto.
      eapply IHs1; eauto. intros s1' H. eapply A. eauto.
    + rewrite eagerlet_substcomp in H. letc_step_inv.
      * inv H. inv H0. eauto.
        asimpl in *.
        asimpl in H3. destruct s1; inv e; try (now repeat smartinv).
        eapply IHs2; eauto. intros s2' H. eapply A. eauto.
      * asimpl in *. asimpl in e0.  
        asimpl in H.
        destruct s1, s2; inv e; inv e0; try (now repeat smartinv).
        inv H. inv H0. inv H3. inv H. destruct v; inv H1.
        eapply A. eauto.
  - letc_step_inv.
    + inv H. inv H0. eauto.
      eapply IHs1; eauto. intros s1' H. eapply A. eauto.
    + inv H. inv H0.
      destruct s1; inv e; try (now repeat smartinv).
      destruct v0; inv H0. eapply A. eauto.
  - letc_step_inv.
    + inv H. inv H0. eauto.
      eapply IHs1; eauto. intros s1' H. eapply A. eauto.
    + inv H. inv H0.
      destruct s1; inv e; try (now repeat smartinv).
      destruct v; inv H0. eapply A. eauto.
Qed.

Lemma forward_simulation {n : nat} (s t : Exp n)  :
  evaluates Step s t -> evaluates step (eval_exp s) (eval_exp t).
Proof.
  intros (H%MStep_preserved&H'%Normal_preserved).
  eexists; eauto.
Qed.


Lemma WN_CBV n s :
  SN (@step n) (eval_exp s) -> SN (@CBV.weakStory.Step n) s.
Proof.
  intros. remember (eval_exp s) as C eqn:E. revert s E.
  eapply SN_plus in H. induction H.
  econstructor. subst.
  intros ? ? % CBV.weakStory.Step_preserved.  eauto.
Qed.



(** ** Backward Simulation *)

Lemma backwards_step {n : nat} (s : Exp n) (C : Syntax.comp n):
  step (eval_exp s) C -> exists s', star step C (eval_exp s') /\ Step s s'.
Proof.
  induction s; intros.
  - inv H. inv H0.
  - simpl in H. letc_step_inv.
    + inv H. inv H0. exfalso. eauto.
      destruct (IHs1 _ H3) as (s1'&?&?).
      eexists. split; eauto.
      simpl. rewrite H. apply let_to_eagerlet.
    + rewrite eagerlet_substcomp in H.
      destruct s1; inv e; try (now repeat smartinv).
      letc_step_inv.
      * inv H. inv H0. exfalso. eauto.
        asimpl in H3. destruct (IHs2 _ H3) as (s2'&?&?).
        eexists. split; eauto.
        rewrite H. cbn. rewrite eagerlet_substcomp. asimpl. apply let_to_eagerlet.
      * asimpl in H. inv H. inv H0. inv H3. inv H.
        asimpl in e. destruct s2; inv e; try (now repeat smartinv).
        destruct v; inv H1. eexists. split; eauto.
        rewrite trans_subst_exp. asimpl. eauto.
  - simpl in H. letc_step_inv.
    + inv H. inv H0. exfalso. eauto.
      destruct (IHs1 _ H3) as (s1'&?&?).
      eexists. split; eauto.
      simpl. rewrite H. apply let_to_eagerlet.
    + inv H. inv H0. destruct s1; inv e; try (now repeat smartinv).
      destruct v0; inv H0. asimpl. eexists.
      split; eauto. rewrite trans_subst_exp. destruct b; now asimpl.
  - simpl in H. letc_step_inv.
    + inv H. inv H0. exfalso. eauto.
      destruct (IHs1 _ H3) as (s1'&?&?).
      eexists. split; eauto.
      simpl. rewrite H. apply let_to_eagerlet.
    + inv H. inv H0. destruct s1; inv e; try (now repeat smartinv).
      destruct v; inv H0. asimpl. eexists.
      split; eauto. rewrite trans_subst_exp. now asimpl.
Qed.


Lemma backwards_steps {n : nat} (s : Exp n) (M : Syntax.comp n):
  star step (eval_exp s) M -> exists t, star step M (eval_exp t) /\ star Step s t.
Proof.
  intros H % star_starL. induction H as [|M' M H IH].
  - exists s. split; reflexivity.
  - destruct IH as (t'&H1&H2).
    inv H1.
    + apply backwards_step in H0. destruct H0 as (s'&?&?).
      eauto.
    + enough (x' = M).
      * subst. eauto.
      * eapply step_functional; eassumption.
Qed.

Lemma backwards_termination {n : nat} (s  : Exp n):
  Normal step (eval_exp s) -> Normal Step s.
Proof.
  intros H. unfold Normal in H.
  intros s' A.
  apply Step_preserved in A. destruct A; eapply H; eauto.
Qed.

Lemma backward_simulation {n : nat} (s t : Exp n)  :
   evaluates step (eval_exp s) (eval_exp t) -> evaluates Step s t.
Proof.
  intros []. eapply backwards_steps in H as (s'&H1&H2).
  inv H1.
  - apply injective_eval in H4. subst.
    apply backwards_termination in H0. eexists; eauto.
  - exfalso. eapply H0. eassumption.
Qed.


(** ** Simulation *)

Lemma weak_simulation {n: nat} (s t : Exp n):
  evaluates Step s t <-> evaluates step (eval_exp s) (eval_exp t).
Proof. split; auto using backward_simulation, forward_simulation. Qed.
