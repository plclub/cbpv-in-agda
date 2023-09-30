Require Import CBV.weakStory.
Require Import CBN.strongStory.
Require Import Morphisms.
Require Import CBV_CBPV.
Import CommaNotation.

(** * Strong Reduction CBV *)
Inductive Step {n} :  Exp n -> Exp n -> Prop :=
  | StepValue (V V' : Value n): StepVal V V' -> Step (Val V) (Val V')

  | StepApp1 (M : Exp n) M' N : Step M M' -> Step (App M N) (App M' N)
  | StepApp2  (M : Exp n) N N' : Step N N' -> Step (App M N) (App M N')
  | StepAppLam  (M : Exp (S n)) M' (N: Value n): M' = (subst_Exp (N..) M) -> Step (App (Val (Lam M)) (Val N)) M'

  | StepCaseS1  (M : Exp n) M' N1 N2 : Step M M' -> Step (CaseS M N1 N2) (CaseS M' N1 N2)
  | StepCaseS2   : forall (M : Exp n)  (N1 N1' : Exp (S n)) N2,  @Step (S n) N1 N1' -> Step (CaseS M N1 N2) (CaseS M N1' N2)
  | StepCaseS3  (M : Exp n)  N1 N2 N2' : @Step (S n) N2 N2' -> Step  (CaseS M N1 N2) (CaseS M N1 N2')
  | StepCaseS  (b: bool) V (N1 N2 : Exp (S n)) M : M = subst_Exp (V..) (if b then N1 else N2) -> Step (CaseS (Val (Inj b V)) N1 N2) M

  | StepCaseP1  (M : Exp n) M' N : Step M M' -> Step (CaseP M N) (CaseP M' N)
  | StepCaseP2  (M : Exp n)  (N N' : Exp (S (S n))) : @Step (S (S n)) N N' -> Step (CaseP M N) (CaseP M N')
  | StepCaseP  N (N' : Exp n) V1 V2: N' = subst_Exp (V2,V1..) N  -> Step (CaseP (Val (Pair V1 V2)) N) N'
with StepVal {n} : Value n -> Value n -> Prop :=
  | StepLam  (M M': Exp (S n)): @Step (S n) M M' -> StepVal (Lam M) (Lam M')

  | StepPair1 (M M' N: Value n) : StepVal M M' -> StepVal (Pair M N) (Pair M' N)
  | StepPair2 (M N N': Value n) : StepVal N N' -> StepVal (Pair M N) (Pair M N')

  | StepInj b (V V': Value n) : StepVal V V' -> StepVal (Inj b V) (Inj b V')
.

Hint Constructors Step StepVal.


Module Counterexample.

Let e := @App 1 (Val (Lam (Val (var_Value var_zero)))) (App (Val (var_Value var_zero)) (Val (var_Value var_zero))).

Lemma normal_e :
  Normal Step e.
Proof.
  unfold e. intros s' H.
  inv H. inv H3. inv H0. inv H1. inv H0. inv H3. inv H2. inv H0. inv H2. inv H0.
Qed.

Let M : Syntax.comp 1 := $ <- (var_value var_zero !) (var_value var_zero);
  (lambda (ret (var_value var_zero))) (var_value var_zero).

Let M' : Syntax.comp 1 := $ <- (var_value var_zero !) (var_value var_zero);
   (ret (var_value var_zero)).

Lemma step1 : sstep (eval_exp e) M.
Proof.
  unfold e. simpl. asimpl.
  apply sstepLetinR. apply sstepAppL.
  asimpl. apply sstepPrimitive. constructor.
Qed.

Lemma step2: sstep M M'.
Proof.
  apply sstepLetinR. apply sstepPrimitive. constructor. reflexivity.
Qed.

Lemma not_normal_e :
  ~ Normal sstep (eval_exp e).
Proof.
  intros H. eapply H. apply step1.
Qed.

Goal ~ (forall  n (e: Exp n) e', star sstep (eval_exp e) e' -> exists e'', star sstep e' e'' /\ exists M, e'' = eval_exp M /\ star Step e M).
Proof.
  intros H.
  assert (H'' : star sstep (eval_exp e) M') by eauto using step1, step2.
  destruct (H _ _ _ H'') as (?&?&?&?&?). subst.
  inv H2.
  - { clear - H0. unfold M', e, eval_exp in *. simpl in *.
      inv H0.
      inv H. inv H4. inv H3. inv H0. inv H. inv H3. inv H. inv H4. inv H0. inv H.
      inv H0.
      }
  - now apply normal_e in H1.
Qed.

End Counterexample.


Scheme value_exp_ind_2 := Minimality for Value Sort Prop
  with exp_value_ind_2  := Minimality for Exp Sort Prop.

Combined Scheme mutind_value_exp from
         value_exp_ind_2, exp_value_ind_2.

Instance proper_Step_App n :
  Proper (star Step ==> star Step ==> star Step) (@App n).
Proof. cbv. intros; subst. induction H; eauto. induction H0; eauto. Qed.

Instance proper_Step_Case n :
  Proper (star Step ==> star Step ==> star Step ==> star Step) (@CaseS n).
Proof.
  cbv. intros; subst. induction H; eauto. induction H1; eauto. induction H0; eauto.
Qed.

Instance proper_Step_CaseP n :
  Proper (star Step ==> star Step ==> star Step) (@CaseP n).
Proof.
  cbv. intros; subst. induction H; eauto. induction H0; eauto.
Qed.

Instance proper_Step_Val n :
  Proper (star StepVal ==> star Step) (@Val n).
Proof. cbv. intros; subst. induction H; eauto. Qed.

Instance proper_Step_Inj n :
  Proper (eq ==> star StepVal ==> star StepVal) (@Inj n).
Proof. cbv. intros; subst. induction H0; eauto. Qed.

Instance proper_Step_Lam n :
  Proper (star Step ==> star StepVal) (@Lam n).
Proof. cbv. intros; subst. induction H; eauto. Qed.

Instance proper_Step_Pair n :
  Proper (star StepVal ==> star StepVal ==> star StepVal) (@Pair n).
Proof.
  cbv. intros; subst. induction H; eauto. induction H0; eauto.
Qed.

(** ** Forward Simulation *)

Lemma ctx_plus n m x y C :
  plus sstep x y ->
  (Proper (plus (@sstep n) ==> plus (@sstep m)) C) ->
  plus sstep (C x) (C y).
Proof.
  intros. hnf in H0. now eapply H0.
Qed.

Lemma ctx_plus_value n m x y C :
  plus sstep_value x y ->
  (Proper (plus (@sstep_value n) ==> plus (@sstep_value m)) C) ->
  plus sstep_value (C x) (C y).
Proof.
  intros. hnf in H0. now eapply H0.
Qed.


(** Proper instances for Plus *)
Instance plus_proper_sstep_letinL' n s: Proper (plus sstep ==> plus sstep) (@letin n s).
Proof.
  cbv. induction 1; intros; subst; eauto.
Qed.

Lemma ret_plus_inv n (V : value n) C :
  plus sstep (ret V) C -> exists V', C = ret V' /\ plus sstep_value V V'.
Proof.
  remember (ret V) as C'. intros H. revert V HeqC'; induction H; intros; subst.
  - inv H.
    + eauto.
    + inv H0.
  - inv H.
    + edestruct IHplus as (? & -> &?); eauto.
    + inv H1.
Qed.

Lemma pstep_value_preserves_ren n (s s': Syntax.comp n) n' (xi : fin n -> fin n'):
  pstep s s' -> pstep (ren_comp xi s) (ren_comp xi s').
Proof.
  destruct 1; simpl; try (now constructor).
  all: asimpl; constructor; try destruct b.
  all: try (rewrite <- H); cbn; asimpl.
  all: now asimpl.
Qed.

Lemma sstep_value_preserves_ren :
  forall n, (forall (c c': Syntax.comp n), sstep c c' -> forall n' (xi: fin n -> fin n'),
             sstep (ren_comp xi c) (ren_comp xi c')) /\ (forall (v v': value n), sstep_value v v' -> forall n' (xi : fin n -> fin n'),
            sstep_value (ren_value xi v) (ren_value xi v')).
Proof.
  apply mutind_sstep; intros; simpl; eauto; try now constructor.
  - constructor. now apply pstep_value_preserves_ren.
Qed.


Lemma plus_sstep_value_preserves n (v v': value n):
  plus sstep_value v v' -> plus sstep_value (ren_value shift v) (ren_value shift v').
Proof.
  induction 1; eauto using plus.
  - constructor. now apply sstep_value_preserves_ren.
  - eright. eapply sstep_value_preserves_ren; eauto. assumption.
Qed.

(** Strong steps of CBV can be simulated by genuine strong steps of CBPV *)
Fixpoint Step_preserved {n: nat} (M M' : Exp n) (H: Step M M') :
  plus sstep (eval_exp M) (eval_exp M')
with StepVal_preserved {n : nat} (V V': Value n) (H: StepVal V V') :
  plus sstep_value (eval_val V) (eval_val V').
Proof.
  - induction H; cbn; subst; asimpl.
    + apply plus_proper_sstep_ret. auto.
    + apply proper_eagerlet_plus_sstep_L; eauto.
      intros. repeat rewrite eagerlet_substcomp. asimpl.
      apply proper_eagerlet_plus_sstep_R; eauto.
      apply plus_proper_sstep_appL; eauto.
      Syntax.substify.
      apply sstepForce, plusSingle in H0.
      assert (HH := plus_sstep_preserves (↑ >> ids) H0).
      exact HH.
    + eapply proper_eagerlet_plus_sstep_R; eauto.
      eapply proper_eagerlet_plus_sstep_L.
      * Syntax.substify. now apply plus_sstep_preserves.
      * intros. asimpl. apply plus_proper_sstep_appR; eauto.
    + eright. constructor. eapply sstepPrimitive. now constructor.
      dostep. rewrite trans_subst_exp. now asimpl.
    + eapply proper_eagerlet_plus_sstep_L; eauto.
      intros. asimpl. apply plus_proper_sstep_caseS1; eauto.
    + eapply proper_eagerlet_plus_sstep_R; eauto.
      apply plus_proper_sstep_caseS2; eauto. Syntax.substify. now apply plus_sstep_preserves.
    + eapply proper_eagerlet_plus_sstep_R; eauto.
      apply plus_proper_sstep_caseS3; eauto. Syntax.substify. now apply plus_sstep_preserves.
    + dostep. rewrite trans_subst_exp. destruct b; now asimpl.
    + eapply proper_eagerlet_plus_sstep_L; eauto.
      intros. asimpl. eapply plus_proper_sstep_caseP1; eauto.
    + eapply proper_eagerlet_plus_sstep_R; eauto.
      apply plus_proper_sstep_caseP2; eauto. Syntax.substify. now apply plus_sstep_preserves.
    + dostep. rewrite trans_subst_exp. now asimpl.
   - induction H; cbn.
    + apply plus_proper_sstep_thunk, plus_proper_sstep_lambda. auto.
    + now apply plus_proper_sstep_pairL.
    + now apply plus_proper_sstep_pairR.
    + now apply plus_proper_sstep_inj.
Qed.

(** A row of strong steps of CBV can be simulated by a row of strong steps of CBPV *)
Lemma MStep_preserved {n: nat} (M M' : Exp n) :
  star Step M M' -> star sstep (eval_exp M) (eval_exp M').
Proof.
  induction 1.
  - reflexivity.
  - apply Step_preserved in H.
    induction H; eauto.
Qed.


Lemma SN_CBVᵥ n s :
  SN (@sstep_value n) (eval_val s) -> SN (@StepVal n) s.
Proof.
  intros. remember (eval_val s) as C eqn:E. revert s E.
  eapply SN_plus in H. induction H.
  econstructor. subst.
  intros ? ? % StepVal_preserved.  eauto.
Qed.

Lemma SN_CBV n s :
  SN (@sstep n) (eval_exp s) -> SN (@Step n) s.
Proof.
  intros. remember (eval_exp s) as C eqn:E. revert s E.
  eapply SN_plus in H. induction H.
  econstructor. subst.
  intros ? ? % Step_preserved.  eauto.
Qed.



(** ** Backward Simulation *)

Lemma backwards_termination {n : nat} (s  : Exp n):
  Normal sstep (eval_exp s) -> Normal Step s.
Proof.
  intros H. unfold Normal in H.
  intros s' A.
  apply Step_preserved in A. destruct A; eapply H; eauto.
Qed.
