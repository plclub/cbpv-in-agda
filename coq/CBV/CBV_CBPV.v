Require Export Eagerlet.
Require Export CBV.
Require Export CBVTypes.
Import CommaNotation.

Ltac asimpl := repeat (progress (CBV.asimpl; Syntax.asimpl)).
Tactic Notation "asimpl" "in" hyp(H) := revert H; asimpl; intros H.
(* Tactic Notation "asimpl" := CBV.auto_unfold; Syntax.auto_unfold; CBV.asimpl'; Syntax.asimpl'; CBV.auto_fold; Syntax.auto_fold. *)




(** Induction scheme for CBV expressions/values *)

Scheme Value_ind_2 := Induction for Value Sort Prop
  with Exp_ind_2  := Induction for Exp Sort Prop.

Combined Scheme ExpVal_ind from Exp_ind_2, Value_ind_2.


(** * Simply typed, Fine-Grained CBV *)

(** ** Typing **)
Definition ctx_cbv (n : nat) := fin n -> type.

Reserved Notation "Gamma ⊩v V : A # phi" (at level 80, V at level 99).
Reserved Notation "Gamma ⊢v V : A # phi" (at level 80, V at level 99).

Inductive has_typeV : forall {n} (Gamma : ctx_cbv n), Value n -> type -> effect -> Type :=
| typeVarV n (Gamma : ctx_cbv n) x phi : Gamma ⊩v var_Value x : Gamma x # phi
| typeOne n (Gamma : ctx_cbv n) phi : Gamma ⊩v One : Unit # phi
| typeLam n (Gamma : ctx_cbv n) M A B phi phi' :
  A .: Gamma ⊢v M : B # phi' ->  Gamma ⊩v Lam M : Arr A phi' B # phi
| typePair n (Gamma : ctx_cbv n) V1 V2 A B phi:
  Gamma ⊩v V1 : A # phi ->
  Gamma ⊩v V2 : B # phi ->
  Gamma ⊩v Pair V1 V2 : Cross A B # phi
| typeInjL n (Gamma : ctx_cbv n) b V A B phi :
  Gamma  ⊩v V : (match b with |true => A |_ => B end) # phi ->
  Gamma ⊩v Inj b V : Plus A B # phi
where "Gamma ⊩v V : A # phi" := (has_typeV Gamma V A phi)
with has_typeE : forall {n} (Gamma : ctx_cbv n), Exp n -> type -> effect -> Type :=
| typeVal n (Gamma : ctx_cbv n) V A phi : Gamma ⊩v V : A # phi -> Gamma ⊢v Val V : A # phi
| typeApp n (Gamma : ctx_cbv n) M N A B phi1 phi2 phi3 phi :
  Gamma ⊢v M : Arr A phi3 B # phi1 ->
  Gamma ⊢v N : A # phi2 ->
  subeff (add phi1 (add phi2 phi3)) phi ->
  Gamma ⊢v App M N : B # phi
| typeCaseS n (Gamma : ctx_cbv n) M N1 N2 A B C phi1 phi2 phi :
    Gamma ⊢v M : Plus A B # phi1 ->
    A, Gamma ⊢v N1 : C # phi2 ->
    B, Gamma ⊢v N2 : C # phi2 ->
    subeff (add phi1 phi2) phi ->
    Gamma ⊢v CaseS M N1 N2 : C # phi
| typeCaseP n (Gamma : ctx_cbv n) M N A B C phi1 phi2 phi:
    Gamma ⊢v M : Cross A B # phi1 ->
    B, A, Gamma ⊢v N : C # phi2 ->
    subeff (add phi1 phi2) phi ->
    Gamma ⊢v CaseP M N : C # phi
where "Gamma ⊢v E : A # phi" := (has_typeE Gamma E A phi).


(** ** Translation CBV - CBPV *)

Fixpoint eval_ty (A : type) : valtype :=
  match A with
  | Unit => one
  | Arr A phi B => U phi (arrow  (eval_ty A) (F (eval_ty B)))
  | Cross A B => cross (eval_ty A) (eval_ty B)
  | Plus A B => Sigma (eval_ty A) (eval_ty B)
  end.

Notation up_ren := (var_zero .: shift >> shift).
Notation up2_ren := (var_zero .: (shift (var_zero) .: shift >> shift >> shift)).

Fixpoint eval_val {n: nat} (V : Value n) : value n :=
  match V with
  | One => u
  | var_Value x => var_value x
  | Lam M => thunk (lambda (eval_exp M))
  | Pair V1 V2 => pair (eval_val V1) (eval_val V2)
  | Inj b V => inj b (eval_val V)
  end
with eval_exp {n: nat} (M: Exp n) : Syntax.comp n :=
  match M with
  | Val V => ret (eval_val V)
  | Tock => tock
  | App M N => $$ <- eval_exp M;
              $$ <- (ren_comp shift (eval_exp N));
             (* Need to explicitly qualify app because app is used in List *)
              Syntax.app (force (var_value (shift var_zero))) (var_value var_zero)
  | CaseS M N1 N2 => $$ <- eval_exp M;
                      caseS (var_value var_zero) (ren_comp up_ren (eval_exp N1)) (ren_comp up_ren (eval_exp N2))
  | CaseP M N => $$ <- eval_exp M;
                  caseP (var_value var_zero) (ren_comp up2_ren (eval_exp N))
  end.

Fixpoint typingVal_pres {n} (Gamma : ctx_cbv n) V A phi (H : Gamma ⊩v V : A # phi) :
  value_typing (Gamma >> eval_ty) (eval_val V) (eval_ty A)
with typingExp_pres {n} (Gamma : ctx_cbv n) M A phi (H:  Gamma ⊢v M : A # phi) :
  computation_typing (Gamma >> eval_ty) (eval_exp M) (F (eval_ty A)) phi.
Proof.
  - destruct H; cbn;  try (now (repeat constructor)).
    + constructor.
      constructor.
      specialize (typingExp_pres _ _ _ _ phi' h).
      now asimpl in *.
    + constructor; eapply typingVal_pres; eauto.
    + constructor. destruct b; eapply typingVal_pres; eauto.
  - destruct H; cbn.
    + specialize (typingVal_pres _ _ _ _ phi h).
      constructor. assumption.
    + simpl. eapply eagerlet_ty; eauto.
      eapply eagerlet_ty; eauto using comp_typepres_renaming.
      econstructor.
      * cbv; eauto.
      * cbn; eauto.
    + eapply eagerlet_ty; eauto.
      econstructor; cbn; eauto; simpl.
      * cbv; eauto.
      * eapply comp_typepres_renaming; eauto.
        auto_case.
      *  eapply comp_typepres_renaming; eauto.
        auto_case.
    + eapply eagerlet_ty; eauto.
      econstructor; eauto.
      * cbv; eauto.
      * eapply comp_typepres_renaming; eauto.
        auto_case.
Qed.

(** *** Translation and Substiution Commute *)

Lemma trans_ren_val':
  forall m,
    (forall (M: Exp m), forall n (xi : fin m -> fin n), eval_exp (ren_Exp xi M) = ren_comp xi (eval_exp M))
    /\ (forall (V: Value m), forall n (xi : fin m -> fin n), eval_val (ren_Value xi V) = ren_value xi (eval_val V)).
Proof.
  apply ExpVal_ind; intros; simpl; asimpl; try congruence.
  + rewrite H, H0, !eagerlet_rencomp.
    now asimpl.
  + rewrite H, H0, H1, !eagerlet_rencomp.
    now asimpl.
  + rewrite H, H0, !eagerlet_rencomp.
    now asimpl.
Qed.

Lemma trans_ren_val :
  forall m,
    (forall (V: Value m), forall n (xi : fin m -> fin n), eval_val (ren_Value xi V) = ren_value xi (eval_val V)).
Proof. now apply trans_ren_val'. Qed.

Lemma trans_ren_exp :
  forall m,
    (forall (M: Exp m), forall n (xi : fin m -> fin n), eval_exp (ren_Exp xi M) = ren_comp xi (eval_exp M)).
Proof. now apply trans_ren_val'. Qed.

Lemma trans_subst_val':
  forall m,
    (forall (M: Exp m), forall n (sigma : fin m -> Value n), eval_exp (subst_Exp sigma M) = subst_comp (sigma >> eval_val) (eval_exp M))
    /\ (forall (V: Value m), forall n (sigma : fin m -> Value n), eval_val (subst_Value sigma V) = subst_value (sigma >> eval_val) (eval_val V)).
Proof.
  apply ExpVal_ind; intros; simpl; asimpl; try congruence.
  + repeat f_equal. rewrite H.
    asimpl. repeat f_equal.
    fext. intros x. apply trans_ren_val.
  + rewrite H, H0, !eagerlet_substcomp.
    now asimpl.
  + rewrite H, H0, H1, !eagerlet_substcomp.
    asimpl. repeat f_equal.
    * fext. intros x. unfold funcomp. rewrite trans_ren_val. now asimpl.
    * fext. intros x. unfold funcomp. rewrite trans_ren_val. now asimpl.
  + rewrite H, H0, !eagerlet_substcomp.
    asimpl; repeat f_equal.
    fext. intros x. unfold funcomp. simpl. rewrite trans_ren_val. now asimpl.
Qed.

Lemma trans_subst_val:
  forall m,
    (forall (V: Value m), forall n (sigma : fin m -> Value n), eval_val (subst_Value sigma V) = subst_value (sigma >> eval_val) (eval_val V)).
Proof.
  apply trans_subst_val'.
Qed.

Lemma trans_subst_exp:
  forall m,
    (forall (M: Exp m), forall n (sigma : fin m -> Value n), eval_exp (subst_Exp sigma M) = subst_comp (sigma >> eval_val) (eval_exp M)).
Proof.
  apply trans_subst_val'.
Qed.


(** *** Translation injective *)
Require Import CBN.CBN_CBPV.

Lemma injective_shift n: injective (@shift n).
Proof. intros x y H. unfold shift in *. congruence. Qed.

Lemma injective_renup n: injective (@var_zero (S n) .: shift >> shift).
Proof. intros [] [] H; unfold shift, funcomp in *; simpl in *; try congruence.
       inv H. inv H. Qed.

Ltac smartinv := match goal with
                 | [ H : context [($$ <- ?M; ?N)] |- _] => destruct M; inv H
                 end.

Ltac letc_step_inv := match goal with
                        [ H: context [$$ <- ?M; ?N] |- _] =>   ( destruct (eagerlet_inv M N) as [ [HH ?] | (? & ? & HH) ]); [rewrite HH in H; clear HH|rewrite HH in H; clear HH]
                      end.


Lemma injective_eval:
 forall n, (forall (M N: Exp n), eval_exp M = eval_exp N -> M = N) /\ (forall (U V: Value n), eval_val U = eval_val V -> U = V).
Proof with try (now repeat smartinv).
  apply ExpVal_ind; intros; try (destruct V; simpl in *; try congruence; inv H; f_equal; auto);  simpl in *.
  all: try (destruct V; cbn in *; try (inv H0); try (inv H1); repeat f_equal; eauto).
  - destruct N; cbn in *...
  - destruct N; cbn in *...
   inv H0. f_equal. eauto.
  - destruct N; cbn in *...
    repeat letc_step_inv; try discriminate; asimpl in H1.
    all: inv H1; f_equal; eauto.
    all: try (eapply H0); try eapply H.
    all: try (now ( eapply ren_inj; eauto using injective_shift; congruence)).
    all: try now (try (destruct x0); try (destruct x); inv H4).
    + eapply ren_inj in H4; eauto using injective_shift.
      subst; congruence.
    + clear - e2 e4 H4.
      destruct e0; inv e2; asimpl in H4; try (repeat letc_step_inv; discriminate).
      destruct N2; inv e4; asimpl in H4; try (repeat letc_step_inv; discriminate).
      cbn. congruence.
  - destruct N; cbn in *...
    repeat letc_step_inv; try discriminate.
    + inv H2. f_equal; eauto using ren_inj.
      * eapply H0. eapply ren_inj; eauto using injective_renup.
      * eapply H1. eapply ren_inj; eauto using injective_renup.
    + inv H2. rewrite <- e3 in e2.  asimpl in H5. asimpl in H6. f_equal; eauto.
  - destruct N; cbn in *...
    letc_step_inv; letc_step_inv; try discriminate.
    + inv H1. f_equal; eauto using ren_inj. eapply H0. eapply ren_inj; eauto.
      intros [ []|] [ [] |] ?H; now try inv H1.
    + inv H1. rewrite <- e2 in e1.  asimpl in H4. f_equal; eauto.
Qed.
