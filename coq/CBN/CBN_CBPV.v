Require Export CBN.
Require Export Eagerlet.
Import CommaNotation.

Ltac asimpl := repeat (progress (CBN.asimpl; Syntax.asimpl)).
Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.



Lemma computation_typing_ext n Gamma Gamma' (C : comp n) A :
  Gamma ⊢ C : A -> Gamma = Gamma' -> Gamma' ⊢ C : A.
Proof.
  now intros ? ->.
Qed.

Hint Constructors sstep star.

(** * Simply typed CBN *)

(** ** Typing *)

Definition cbn_ctx (n : nat) := fin n -> type.
Reserved Notation "Gamma ⊢n c : A" (at level 80, c at level 99).

Inductive cbn_typing {n : nat} (Gamma : cbn_ctx n) : exp n -> type -> Type :=
| cbn_typeVar i : Gamma ⊢n var_exp i : Gamma i
| cbn_typeUnit : Gamma ⊢n One : Unit
| cbn_typeLam (s: exp (S n)) A B:
    A, Gamma ⊢n s : B -> (Gamma ⊢n Lam s : Arr A B)
| cbn_typePair s1 s2 B1 B2:
    Gamma ⊢n s1 : B1  -> Gamma ⊢n s2 : B2 -> Gamma ⊢n Pair s1 s2 : Cross B1 B2
| cbn_typeProj b s B1 B2:
    Gamma ⊢n s : Cross B1 B2 -> Gamma ⊢n Proj b s : (if b then B1 else B2)
| cbn_typeInj (b : bool) s B1 B2 :
    Gamma ⊢n s : (if b then B1 else B2) -> Gamma ⊢n Inj b s : Plus B1 B2
| cbn_typeCaseS s t1 t2 A1 A2 C:
    Gamma ⊢n s : Plus A1 A2 ->
    A1, Gamma ⊢n t1 : C ->
    A2, Gamma ⊢n t2 : C ->
    Gamma ⊢n CaseS s t1 t2 : C
| cbn_typeApp s t A B:
    Gamma ⊢n s : Arr A B -> Gamma ⊢n t : A -> Gamma ⊢n App s t : B

where "Gamma ⊢n s : A" := (@cbn_typing _ Gamma s A).

(** ** Typing under renaming and substitution *)

Lemma cbn_typeVar' n (Gamma : cbn_ctx n) A i : Gamma i = A -> Gamma ⊢n var_exp i : A.
Proof. intros <-; constructor. Qed.
Hint Resolve cbn_typeVar'.

Fixpoint cbn_typepres_renaming n Gamma s A (H: Gamma ⊢n s : A)  m (delta: fin n -> fin m) Delta {struct H}:
  (forall i, Gamma i = Delta (delta i)) -> Delta ⊢n (ren_exp delta s) : A.
Proof.
  all: destruct H; cbn; intros; eauto; econstructor; eauto;
  eapply cbn_typepres_renaming; eauto.
  all: intros i; destruct i as [i|]; cbn; eauto; destruct i; cbn; eauto.
Qed.

Fixpoint cbn_typepres_substitution n (Gamma: cbn_ctx n) s A (H: Gamma ⊢n s : A)  m (sigma: fin n -> exp  m) Delta {struct H}:
  (forall i, Delta ⊢n sigma i : Gamma i) -> Delta ⊢n (subst_exp sigma s) : A.
Proof.
  all: destruct H; cbn; intros; eauto; econstructor; eauto.
  all: eapply cbn_typepres_substitution; eauto.
  all: intros i; destruct i as [i|]; cbn; eauto.
  all: eapply cbn_typepres_renaming; eauto.
Qed.

(** ** Translation relation from CBN to CBPV *)


Fixpoint eval_ty (A : type) : comptype :=
  match A with
  | Unit => F (one)
  | Arr A B => arrow (U (eval_ty A)) (eval_ty B)
  | Cross A B => Pi (eval_ty A) (eval_ty B)
  | Plus A B => F (Sigma (U (eval_ty A)) (U (eval_ty B)))
  end.

Notation ren_up := ((var_zero .: (shift >> shift))).
Reserved Notation "s ↦n C" (at level 40).

Inductive trans {n} : exp n -> comp n -> Type :=
  trans_var (x : fin n) : var_exp x ↦n force (var_value x)
| trans_One : @One n ↦n ret u
| trans_Lam (s : exp (S n)) M : s ↦n M -> Lam s ↦n lambda M
| trans_App (s t : exp n) M N : s ↦n M -> t ↦n N -> App s t ↦n app M (thunk N)
| trans_Pair (s t : exp n) M N : s ↦n M -> t ↦n N -> Pair s t ↦n tuple M N
| trans_Proj b (s : exp n) M : s ↦n M -> Proj b s ↦n proj b M
| trans_Inj b (s : exp n) M : s ↦n M -> Inj b s ↦n ret (inj b (thunk M))
| trans_CaseS (s : exp n) t1 t2 M N1 N2 N1' N2' :
    s ↦n M -> t1 ↦n N1 -> t2 ↦n N2 ->
    N1' = ren_comp ren_up N1 -> N2' = ren_comp ren_up N2 ->
    CaseS s t1 t2 ↦n $$ <- M; caseS (var_value var_zero) N1' N2'
| trans_FT (s : exp n) M : s ↦n M -> s ↦n force (thunk M)
where "s ↦n C" := (@trans _ s C).
Hint Constructors trans.
Remove Hints trans_FT.

Definition eval_ctx {n} (Gamma : cbn_ctx n) := Gamma >> eval_ty >> U.

Lemma eval_ctx_cons {n : nat} (Gamma: cbn_ctx n) (A: type) :
  eval_ctx (A, Gamma) = U (eval_ty A), eval_ctx Gamma.
Proof.
  fext; intros []; unfold eval_ctx, funcomp; cbn; reflexivity.
Qed.

Lemma trans_preserves {n : nat} (s : exp n) A Gamma M :
  s ↦n M -> Gamma ⊢n s : A -> eval_ctx Gamma ⊢ M : eval_ty A.
Proof.
  intros H. revert A; induction H; intros; cbn in *; [(inv X) .. |]; eauto.
  - repeat econstructor.
  - simpl. econstructor. rewrite <- eval_ctx_cons. eauto.
  - econstructor; eauto. eapply  (IHtrans1 Gamma (Arr A0 A)); eauto.
  -  econstructor; eauto.
  - replace (eval_ty (if b then B1 else B2)) with (if b then eval_ty B1 else eval_ty B2) by (now destruct b).
    firstorder.
  - destruct b; econstructor; firstorder.
  - eapply IHtrans1 in X0. eapply IHtrans2 in X1. eapply IHtrans3 in X2.
    eapply eagerlet_ty. eassumption. all:fold (eval_ty). econstructor.
    + cbv; eauto.
    + fold eval_ty. eapply comp_typepres_renaming; eauto. now intros [].
    + fold eval_ty. eapply comp_typepres_renaming; eauto. now intros [].
Qed.

Ltac prv_eq := intros; asimpl; f_equal; fext; now intros [].

(** *** Translation and substitution commute *)

Lemma trans_ren (n m : nat) (M : exp n) M' (sigma : fin n -> fin m) :
      M ↦n M' ->
      ren_exp sigma M ↦n ren_comp sigma M'.
Proof.
  intros. revert m sigma; induction X; try now (cbn; intros; eauto; try econstructor; eauto).
  intros. asimpl. rewrite eagerlet_rencomp. asimpl.
  econstructor; eauto; subst; try (now asimpl).
Qed.

Lemma trans_subst (n m : nat) (M : exp n) M' (sigma : fin n -> exp m) sigma' :
      M ↦n M' -> (forall i, sigma i ↦n force (sigma' i)) ->
      subst_exp sigma M ↦n subst_comp sigma' M'.
Proof.
  intros. revert m sigma sigma' X0; induction X; try now (cbn; intros; eauto).
  - cbn; intros. econstructor. eapply IHX. intros []; cbn; eauto.
    eapply trans_ren with (1 := (X0 f)).
  - intros. subst. asimpl. rewrite eagerlet_substcomp. asimpl.
    eapply trans_CaseS with (N1 := subst_comp (up_value_value sigma') N1) (N2 := subst_comp (up_value_value sigma') N2); try (now asimpl); eauto.
    + eapply IHX2. auto_case. unfold funcomp. 
      asimpl. eapply (trans_ren m (S m) (sigma f) ((sigma' f) !) shift). eauto.
    + eapply IHX3. auto_case. unfold funcomp.
      asimpl. eapply (trans_ren m (S m) (sigma f) ((sigma' f) !) shift). eauto.
  - intros. asimpl. econstructor. eauto.
Qed.

(** ** Translation functions from CBN to CBPV *)

Fixpoint eval {n: nat} (s : exp n) : comp n :=
  match s with
  | var_exp x => force (var_value x)
  | One => ret u
  | Lam M => lambda (eval M) (* Rename in our signature. *)
  | App M N => app (eval M) (thunk (eval N))
  | Pair M N => tuple (eval M) (eval N)
  | Proj b M => proj b (eval M)
  | Inj b M => ret (inj b (thunk (eval M)))
  | CaseS M N1 N2 => eagerlet (eval M) (caseS (var_value var_zero) (ren_comp ren_up (eval N1)) (ren_comp ren_up (eval N2)))
  end.

Lemma trans_eval {n : nat} (s : exp n) :
  s ↦n eval s.
Proof.
  induction s; cbn; eauto.
Qed.

(** *** Translation is well-behaved *)

Lemma cbn_type_pres {n : nat} (s : exp n) A Gamma :
  Gamma ⊢n s : A -> eval_ctx Gamma ⊢ eval s : eval_ty A.
Proof.
  intros. eapply trans_preserves; eauto. eapply trans_eval.
Qed.

(** *** Translation of substitutions *)

Definition eval_subst {m n} (I : fin m -> exp n) :=
  fun r : fin m => match I r with var_exp n => var_value n | s => thunk (eval s) end.

(** *** Translation of substitutions is well-behaved for renamings *)

(* Yiyun: ids v is the type class method for var_exp v / var_value v *)
(* rewriting might struggle with the method *)
Lemma eval_subst_cons {m n} (sigma : fin m -> exp n) v :
  eval_subst (var_exp v, sigma) = var_value v, eval_subst sigma.
Proof.
  unfold eval_subst. fext. cbn. now intros [].
Qed.

Hint Extern 0 => asimpl : autosubst.
Ltac autosubst := auto with autosubst.

Lemma ren_comp_eval n m (rho : fin n -> fin m) (s : exp n) :
  ren_comp rho (eval s) = eval (ren_exp rho s).
Proof.
  revert m rho; induction s; cbn; intros.
  all: try reflexivity.
  all: try now rewrite IHs.
  all: try now rewrite IHs1, IHs2.
  rewrite eagerlet_rencomp. rewrite IHs1. cbn. repeat f_equal.
  - rewrite <- IHs2. now asimpl.
  - rewrite <- IHs3. now asimpl.
Qed.

Lemma evaL_subst_ren m n k (sigma : fin m -> exp n) (tau : fin n -> fin k) :
  eval_subst (sigma >> ren_exp tau) = eval_subst sigma >> ren_value tau.
Proof.
  fext. intros. unfold eval_subst.
  cbn. unfold funcomp. destruct (sigma x); cbn.
  all: try rewrite eagerlet_rencomp; cbn.
  all: try rewrite !ren_comp_eval.
  all: try reflexivity.
  now asimpl.
Qed.

Lemma eval_subst_up_value_value m n (sigma : fin m -> exp n):
  up_value_value (eval_subst sigma) = eval_subst (up_exp_exp sigma).
Proof.
  asimpl.
  rewrite eval_subst_cons.
  Syntax.asimpl.
  now rewrite evaL_subst_ren.
Qed.

(** ** Extended translation relation *)

Reserved Notation "s ⋘ C" (at level 50).

Inductive refines {n} : exp n -> comp n -> Type :=
  refines_var (x : fin n) : var_exp x ⋘ force (var_value x)
| refines_One : @One n ⋘ ret u
| refines_Lam (s : exp (S n)) M : s ⋘ M -> Lam s ⋘ lambda M
| refines_App (s t : exp n) M N : s ⋘ M -> t ⋘ N -> App s t ⋘ app M (thunk N)
| refines_Pair (s t : exp n) M N : s ⋘ M -> t ⋘ N -> Pair s t ⋘ tuple M N
| refines_Proj b (s : exp n) M : s ⋘ M -> Proj b s ⋘ proj b M
| refines_Inj b (s : exp n) M : s ⋘ M -> Inj b s ⋘ ret (inj b (thunk M))
| refines_CaseS (s : exp n) t1 t2 M N1 N2 N1' N2':
    s ⋘ M -> t1 ⋘ N1 -> t2 ⋘ N2 -> N1' = ren_comp ren_up N1 -> N2' = ren_comp ren_up N2 ->
    CaseS s t1 t2 ⋘ $ <- M; caseS (var_value var_zero) N1' N2'
| refines_CaseS2 (s : exp n) t1 t2 V N1 N2 :
    s ⋘ ret V -> t1 ⋘ N1 -> t2 ⋘ N2 ->
    CaseS s t1 t2 ⋘ subst_comp (V..) (caseS (var_value var_zero) (ren_comp ren_up N1) (ren_comp ren_up N2))
| refines_FT (s : exp n) M : s ⋘ M -> s ⋘ force (thunk M)
where "s ⋘ C" := (@refines _ s C).
Hint Constructors refines.
Remove Hints trans_FT.

Notation "s ⋙ t" := (t ⋘ s) (at level 50).

Lemma trans_refines : forall n (C : comp n) s, s ↦n C -> C ⋙ s.
Proof.
  induction 1; eauto; subst.
  destruct (eagerlet_inv M (caseS (var_value var_zero) (ren_comp ren_up N1) (ren_comp ren_up N2))) as [ [-> ] | (? & -> & ?) ].
  - eapply refines_CaseS; subst; firstorder; eauto.
  - rewrite e. eapply refines_CaseS2; eauto.
Qed.

Lemma refines_help n (C1 C2 : comp n) s1 s2 :
  C1 ⋙ s1 -> C1 = C2 -> s1 = s2  -> C2 ⋙ s2.
Proof.
  intros. now subst.
Qed.

Lemma refines_ren (n m : nat) (M : exp n) M' (sigma : fin n -> fin m) :
      M ⋘ M' ->
      ren_exp sigma M ⋘ ren_comp sigma M'.
Proof.
  intros. revert m sigma; induction X; try now (cbn; intros; eauto; try econstructor; eauto).
  - intros. subst. asimpl. econstructor; eauto; now asimpl.
  - intros. asimpl.
    assert (H := refines_CaseS2 _ _ _ _  _ _ (IHX1 _ sigma) (IHX2 _ (up_ren sigma)) (IHX3 _ (up_ren sigma))).
    now asimpl in H.
Qed.

Lemma refines_subst (n m : nat) (M : exp n) M' (sigma : fin n -> exp m) sigma' :
  M ⋘ M' -> (forall i, sigma i ⋘ force (sigma' i)) ->
  subst_exp sigma M ⋘ subst_comp sigma' M'.
Proof.
  intros. revert m sigma sigma' X0; induction X; try now (cbn; intros; eauto; try econstructor; eauto).
  - intros. asimpl. econstructor. apply IHX.
    auto_case. asimpl. unfold funcomp.
    apply refines_ren with (M' := (sigma' f) !) (sigma := ↑). eauto.
  - intros. subst. cbn. asimpl. eapply refines_CaseS with (N1 := subst_comp (up_value_value sigma') N1) (N2 := subst_comp (up_value_value sigma') N2); eauto;
                                  try now asimpl.
    + apply IHX2. auto_case; asimpl; eauto.
      unfold funcomp.
      apply refines_ren with (M' := (sigma' f) !) . eauto.
    + apply IHX3. auto_case; asimpl; eauto.
      unfold funcomp.
      apply refines_ren with (M' := (sigma' f) !) . eauto.
  - intros. eapply refines_help.
    eapply refines_CaseS2.
    4, 5 : now asimpl.
    + eauto.
    + apply IHX2. auto_case. asimpl.
      unfold funcomp.
      apply refines_ren with (M' := (sigma' f) !) . eauto.
    + apply IHX3. auto_case; asimpl; eauto.
      unfold funcomp.
      apply refines_ren with (M' := (sigma' f) !) . eauto.
Qed.


(** *** Translation injective *)

Notation injective f := (forall x1 x2, f x1 = f x2 -> x1 = x2).

Lemma ren_inj n   :
  (forall (s t : value n) m (rho : fin n -> fin m), injective rho -> ren_value rho s = ren_value rho t -> s = t) /\
  (forall (s t: comp n) m (rho : fin n -> fin m), injective rho -> ren_comp rho s = ren_comp rho t -> s = t).
Proof.
  revert n. eapply mutind_val_comp; cbn; asimpl; intros.
  all: try now (destruct t; inv H0; firstorder congruence).
  all: try now (destruct t; inv H2; f_equal; firstorder congruence).
  all: try now (destruct t; inv H1; f_equal; firstorder congruence).
  - destruct t; inv H1; f_equal. eapply H; try eassumption.
    intros [] []; cbv; try congruence. intros. f_equal. inv H1. eauto.
  - destruct t; inv H2; f_equal; eauto. eapply H0; try eassumption.
    intros [] []; cbv; try congruence. intros. f_equal. inv H2. eauto.
  - destruct t; inv H3; f_equal; eauto. eapply H0; try eassumption.
    intros [] []; cbv; try congruence. intros. f_equal. inv H3. eauto.
    eapply H1; try eassumption.
    intros [] []; cbv; try congruence. intros. f_equal. inv H3. eauto.
  - destruct t; inv H2; f_equal; eauto. eapply H0; try eassumption.
    intros [ [] | ] [ [] | ]; cbv; try congruence. intros. repeat f_equal. inv H2. eauto.
Qed.

Lemma ren_up_inj n :
  injective (@ren_comp (S n) _ ren_up).
Proof.
  intros ? ? ?.  eapply ren_inj; eauto. intros [] []; cbv; congruence.
Qed.

Lemma refines_functional : forall n (C : comp n) s1 s2, C ⋙ s1 -> C ⋙ s2 -> s1 = s2.
Proof.
  intros. revert s2 X0. induction X; intros; subst; inv X0; f_equal; eauto.
  - eapply IHX2. eapply ren_up_inj in H2. now subst.
  - eapply IHX3. eapply ren_up_inj in H4. now subst.
  - eapply IHX2. asimpl in H2. now subst.
  - eapply IHX3. asimpl in H3. now subst.
Qed.


Lemma trans_inj {n : nat} (s t : exp n) (C : comp n) :
  s ↦n C -> t ↦n C -> s = t.
Proof.
  intros. eapply refines_functional; eapply trans_refines; eauto.
Qed.

Theorem injective_eval n (s t : exp n) :
  eval s = eval t -> s = t.
Proof.
  intros. eapply trans_inj. eapply trans_eval. rewrite H. eapply trans_eval.
Qed.
