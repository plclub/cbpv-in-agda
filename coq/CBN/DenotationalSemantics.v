Set Implicit Arguments.
Require Import Psatz  Logic List Classes.Morphisms Setoid FinFun Morphisms.
Import List Notations.


Require Export CBPV.DenotationalSemantics Confluence
        CBPV.StrongReduction CBPV.LogicalEquivalence
        CBN CBN_CBPV CBN.weakStory.

(** * Denotational Semantics CBN  *)

(** ** Contexts *)
Inductive ectx (m: nat) : nat -> Type :=
  | ectxHole :  ectx m m
  | ectxPairL n: ectx m n -> exp m -> ectx m n
  | ectxPairR n : exp m -> ectx m n -> ectx m n
  | ectxInj n : bool -> ectx m n -> ectx m n
  | ectxLambda n: ectx (S m) n -> ectx m n
  | ectxAppL n:  ectx m n -> exp m -> ectx m n
  | ectxAppR n:  exp m -> ectx m n -> ectx m n
  | ectxProj n: bool -> ectx m n -> ectx m n
  | ectxCaseSV n: ectx m n -> exp (S m) -> exp (S m) -> ectx m n
  | ectxCaseSL n: exp m -> ectx (S m) n -> exp (S m) -> ectx m n
  | ectxCaseSR n: exp m -> exp (S m) -> ectx (S m) n -> ectx m n.


Notation "•" := (ectxHole _).

Fixpoint fille {m n: nat} (C: ectx m n)  : exp n -> exp m :=
  match C with
  | • => fun e => e
  | ectxPairL C e' => fun e => Pair (fille C e) e'
  | ectxPairR e' C => fun e => Pair e' (fille C e)
  | ectxInj b C => fun e => Inj b (fille C e)
  | ectxLambda C => fun e =>  Lam (fille C e)
  | ectxAppL C e' => fun e => App (fille C e) e'
  | ectxAppR e' C => fun e => App e' (fille C e)
  | ectxProj b C => fun e => Proj b (fille C e)
  | ectxCaseSV C e1 e2 => fun e => CaseS (fille C e) e1 e2
  | ectxCaseSL e' C e2 => fun e => CaseS e' (fille C e) e2
  | ectxCaseSR e' e1 C => fun e => CaseS e' e1 (fille C e)
  end.

Reserved Notation "Gamma [[ Delta ]] ⊢n C : B ; T" (at level 53, C at level 99).


Inductive ectxTyping {m: nat} (Gamma: cbn_ctx m) : forall n, cbn_ctx n -> ectx m n -> type -> type -> Type :=
| ectxTypingHole A:
    Gamma [[ Gamma ]] ⊢n • : A; A
| ectxTypingPairL n (Delta: cbn_ctx n) (C: ectx m n) A A1 A2 v:
    Gamma[[Delta]] ⊢n C : A1; A ->
    Gamma ⊢n v : A2  ->
    Gamma[[Delta]] ⊢n ectxPairL C v : Cross A1 A2; A
| ectxTypingPairR n (Delta: cbn_ctx n) (C: ectx m n) A A1 A2 v:
    Gamma ⊢n v : A1  ->
    Gamma[[Delta]] ⊢n C : A2; A ->
    Gamma[[Delta]] ⊢n ectxPairR v C : Cross A1 A2; A
| ectxTypingInj n (Delta: cbn_ctx n) (C: ectx m n) A A1 A2 (b: bool):
    Gamma[[Delta]] ⊢n C : (if b then A1 else A2); A ->
    Gamma[[Delta]] ⊢n ectxInj b C : Plus A1 A2; A
| ectxTypingLambda n (Delta: cbn_ctx n) (C: ectx (S m) n) A A' B:
    (A .: Gamma) [[Delta]] ⊢n C : B; A' ->
      Gamma [[Delta]] ⊢n ectxLambda C : Arr A B; A'
| ectxTypingAppL n (Delta: cbn_ctx n) (C: ectx m n) A A' B v:
    Gamma[[Delta]] ⊢n C : Arr A B; A' ->
    Gamma ⊢n v : A  ->
    Gamma[[Delta]] ⊢n ectxAppL C v : B; A'
| ectxTypingAppR n (Delta: cbn_ctx n) c (C: ectx m n) A A' B :
    Gamma ⊢n c : Arr A B  ->
    Gamma[[Delta]] ⊢n C : A; A' ->
    Gamma[[Delta]] ⊢n ectxAppR c C : B; A'
| ectxTypingProj n (Delta: cbn_ctx n) (C: ectx m n) A B1 B2 (b: bool):
    Gamma[[Delta]] ⊢n C : Cross B1 B2; A ->
    Gamma[[Delta]] ⊢n ectxProj b C : (if b then B1 else B2); A
| ectxTypingCaseSV n (Delta: cbn_ctx n) (C: ectx m n) A1 A2 A' B c1 c2:
    Gamma[[Delta]] ⊢n C : Plus A1 A2; A' ->
    A1 .: Gamma ⊢n c1 : B  ->
    A2 .: Gamma ⊢n c2 : B  ->
    Gamma[[Delta]] ⊢n ectxCaseSV C c1 c2 : B; A'
| ectxTypingCaseSL n (Delta: cbn_ctx n) (C: ectx (S m) n) A1 A2 A' B v c2:
    Gamma ⊢n v : Plus A1 A2  ->
    (A1 .: Gamma)[[Delta]] ⊢n C : B; A' ->
    A2 .: Gamma ⊢n c2 : B  ->
    Gamma[[Delta]] ⊢n ectxCaseSL v C c2 : B; A'
| ectxTypingCaseSR n (Delta: cbn_ctx n) (C: ectx (S m) n) A1 A2 A' B v c1:
    Gamma ⊢n v : Plus A1 A2  ->
    A1 .: Gamma ⊢n c1 : B  ->
    (A2 .: Gamma)[[Delta]] ⊢n C : B; A' ->
    Gamma[[Delta]] ⊢n ectxCaseSR v c1 C : B; A'
where "Gamma [[ Delta ]] ⊢n C : B ; T " := (@ectxTyping _ Gamma _ Delta C B T).



Hint Constructors ectx ectxTyping.


Fixpoint ectx_typing_soundness m  Gamma n Delta (C: ectx m n) A A' (H: Gamma[[Delta]] ⊢n C : A; A'):
  forall v, Delta ⊢n v : A' -> (Gamma ⊢n fille C v : A).
Proof.
  all: destruct H; intros; cbn; eauto; econstructor; eauto.
Qed.

(** ** Alternative translation *)
Definition caseScott {m: nat} : comp (S m) :=
  caseS (var 0) (lambda (lambda ((var 1 !) (var 2))))  (lambda (lambda ((var 0 !) (var 2)))).

Fixpoint eval' {n: nat} (s : exp n) : comp n :=
  match s with
  | var_exp x => force (var_value x)
  | One => ret u
  | Lam M => lambda (eval' M)
  | App M N => app (eval' M) (thunk (eval' N))
  | Pair M N => tuple (eval' M) (eval' N)
  | Proj b M => proj b (eval' M)
  | Inj b M => ret (inj b (thunk (eval' M)))
  | CaseS M N1 N2 =>
    (letin (eval' M) caseScott) (<{ lambda (eval' N1) }>) (<{ lambda (eval' N2) }>)
  end.


Lemma cbn_type_pres' {n : nat} (s : exp n) A Gamma :
  Gamma ⊢n s : A -> eval_ctx Gamma ⊢ eval' s : eval_ty A.
Proof.
  induction 1; cbn in *; eauto.
  - econstructor. eapply computation_typing_ext;
                    eauto. unfold eval_ctx. now asimpl.
  - replace (eval_ty (if b then B1 else B2)) with (if b then eval_ty B1 else eval_ty B2) by (now destruct b).
    now econstructor.
  - destruct b; now repeat econstructor.
  - repeat econstructor; eauto.
    all: try solve [eapply typeVar'; cbn; eauto].
    all: rewrite eval_ctx_cons in IHX2, IHX3; eauto.
Qed.


Fixpoint eval_ectx {m n: nat} (C : ectx m n) : cctx false m n :=
  match C with
  | • => •__c
  | ectxLambda C => cctxLambda (eval_ectx C)
  | ectxAppL C e' => cctxAppL (eval_ectx C) (thunk (eval' e'))
  | ectxAppR e' C => cctxAppR (eval' e') (vctxThunk (eval_ectx  C))
  | ectxPairL C e' => cctxTupleL (eval_ectx C) (eval' e')
  | ectxPairR e' C => cctxTupleR (eval' e') (eval_ectx C)
  | ectxInj b C => cctxRet (vctxInj b (vctxThunk (eval_ectx C)))
  | ectxProj b C => cctxProj b (eval_ectx C)
  | ectxCaseSV C e1 e2 =>
    cctxAppL (cctxAppL (cctxLetinL (eval_ectx C) caseScott)
                       (<{ lambda (eval' e1) }>))
             (<{ lambda (eval' e2) }>)

  | ectxCaseSL e' C e2 =>
    cctxAppL (cctxAppR (letin (eval' e') caseScott)
                       (vctxThunk (cctxLambda (eval_ectx C))))
             (<{ lambda (eval' e2) }>)

  | ectxCaseSR e' e1 C =>
    cctxAppR ((letin (eval' e') caseScott) (<{ lambda (eval' e1) }>))
             (vctxThunk (cctxLambda (eval_ectx C)))
  end.

Lemma ectx_cctx {m n: nat} (C: ectx m n) (e: exp n) :
  eval' (fille C e) = fillc (eval_ectx C) (eval' e).
Proof.
  induction C; cbn; congruence.
Qed.


Lemma ectx_cctx_typing {m n: nat} Gamma Delta (C: ectx m n) A B:
   Gamma [[Delta]] ⊢n C : A; B -> (eval_ctx Gamma) [[eval_ctx Delta]] ⊢ eval_ectx C : eval_ty A; eval_ty B.
Proof.
  induction 1; cbn; intros;  repeat econstructor;  eauto using cbn_type_pres'.
  all: try solve [eapply typeVar'; cbn; reflexivity].
  all: try solve [rewrite <-eval_ctx_cons; eauto using cbn_type_pres'].
  + destruct b; econstructor; eauto.
  + exact (cbn_type_pres'  c0).
  + replace (eval_ty (if b then B1 else B2))
      with (if b then eval_ty B1 else eval_ty B2) by (destruct b; reflexivity); eauto.
  + exact (cbn_type_pres' c).
  + exact (cbn_type_pres' c).
Qed.

Definition Bool := Plus Unit Unit.
Definition tt {n: nat} := @Inj n true One.
Definition ff {n: nat} := @Inj n false One.




Record CBN {n: nat} (Gamma: cbn_ctx n) (A: type) :=
  mkCBN { CBN_e :> exp n; CBN_H :> Gamma ⊢n CBN_e : A }.


(** Expression Contextual Equivalence *)
Notation "s ≫* t" := (star Step s t) (at level 60).

Definition exp_obseq {n: nat} {B: type} {Gamma: cbn_ctx n} (H1 H2: CBN Gamma B) :=
  forall (C: ectx 0 n), null [[Gamma]] ⊢n C : Bool; B ->
    (CaseS (fille C H1) tt ff ≫* tt) <-> (CaseS (fille C H2) tt ff ≫* tt).

Instance equiv_exp_obseq (n: nat) (B: type) (Gamma: cbn_ctx n):
  Equivalence (@exp_obseq n B Gamma).
Proof.
  constructor; [firstorder.. |].
  intros X1 X2 X3 H1 H2 C H; etransitivity; eauto.
Qed.

Notation "C1 '≃n' C2" := (exp_obseq C1 C2) (at level 50).





Definition eval_CBN (n: nat) (Gamma: cbn_ctx n) (A: type) :
  CBN Gamma A -> CBPVc (eval_ctx Gamma) (eval_ty A) :=
  fun H => @mkCBPVc _ (eval_ctx Gamma) (eval_ty A) (eval H) (cbn_type_pres _ _ _ H).




Lemma eval_eval' {n: nat} (s: exp n) (Gamma: cbn_ctx n) A:
   Gamma ⊢n s : A -> eval_ctx Gamma ⊨ eval s ∼ eval' s : eval_ty A.
Proof.
  induction s in Gamma, A |-*; cbn; intros X'.
  all: try solve [eapply fundamental_property, trans_preserves; eauto].
  1 - 6: inv X'. 
  - eapply logical_equivalence_congruent_cctx_comp with (C := cctxLambda •__c).
    2: eapply IHs; eauto.
    rewrite eval_ctx_cons. repeat econstructor.
  - intros ? ? ? ?. asimpl.
    repeat apply_congruence.
    eapply IHs1 with (A := Arr A0 A); eauto.
    eapply IHs2; eauto.
  - intros ? ? ? ?. asimpl.
    repeat apply_congruence.
    eapply IHs1; eauto. eapply IHs2; eauto.
  - intros ? ? ? ?.
    replace (eval_ty _) with (if b then eval_ty B1 else eval_ty B2)
      by now destruct b.
    asimpl; repeat apply_congruence.
    eapply IHs with (A := Cross B1 B2); eauto. 
  - intros ? ? ? ?. asimpl. destruct b; repeat apply_congruence.
    all: eapply IHs; eauto.
  - intros ? ? ? ?. asimpl. 
    rewrite eagerlet_substcomp. asimpl.
    eapply closure_under_reduction.
    rewrite <-let_to_eagerlet. reflexivity. reflexivity.
    eapply bind with
        (K1 := ectxLetin Semantics.ectxHole _)
        (K2 := ectxApp (ectxApp (ectxLetin Semantics.ectxHole _) _) _).
    eapply IHs1; eauto.
    intros c1 c2 (? & ? & ?); intuition; subst; cbn.
    eapply closure_under_expansion; try reduce;
      try reflexivity.
    destruct H3 as (? & ? & [] & ?); intuition; subst;
      eapply closure_under_expansion; repeat reduce;
        try reflexivity.
    all: asimpl; cbn.
    all: (eapply IHs2 || eapply IHs3); eauto; rewrite eval_ctx_cons; eauto.
Qed.


Hint Resolve CBN_H.

Lemma normal_tt n:
  Normal (@Step n) tt.
Proof.
  intros y H; inv H. 
Qed.

Hint Resolve normal_tt. 


(** ** Observational Equivalence by translation *)
Section ObservationalEquivalenceSoundness.
  (* ground returner context, converting booleans to ground returners *)

  Local Definition K : cctx false 0 0 :=
    cctxLetinL •__c (caseS (var 0)
                         (ret (inj true u))
                         (ret (inj false u))).

  Local Definition gbool := gsum gone gone.

  Lemma K_typed : null[[null]] ⊢ K : F gbool; eval_ty Bool.
  Proof.
    unfold Bool; cbn; repeat econstructor; eauto.
    1: eapply @cctxTypingHole with (t := false).
    all: eapply typeVar'; reflexivity.
  Qed.


  Lemma K_filled_typed n (C: ectx 0 n) P:
    null ⊢n fille C P : Bool -> null ⊢ fillc K (eval' (fille C P)) : F gbool.
  Proof.
    intros; eapply cctx_comp_typing_soundness; eauto using K_typed.
      replace null with (eval_ctx null); eauto using cbn_type_pres'.
      fext; intros [].
  Qed.


  Ltac normal := intros ? ?; repeat (invp @sstep || invp @sstep_value || invp @pstep).


  Hint Resolve trans_eval. 


  Definition eta_if n (s: exp n) := CaseS s tt ff.
  Definition eta_if' n m (C: ectx n m) := ectxCaseSV C tt ff. 

   Lemma eta_if_typed n Gamma (s: exp n):
    Gamma ⊢n s : Bool -> Gamma ⊢n eta_if s : Bool.
  Proof.
    repeat econstructor; eauto.
  Qed.


  Lemma eta_if'_typed n m Gamma Delta (C: ectx n m) A:
    Gamma[[Delta]] ⊢n C : Bool; A -> Gamma[[Delta]] ⊢n eta_if' C : Bool; A.
  Proof.
    repeat econstructor; eauto.
  Qed.

 


   Lemma eval_eval'_true b (s: exp 0) :
     null ⊢n s : Bool ->
     fillc K (eval s) >* ret (inj b u) <-> fillc K (eval' s) >* ret (inj b u).
   Proof.
     intros. specialize (eval_eval'  X) as H.
     eapply logical_equivalence_congruent_cctx_comp with (C := K) in H;
       replace (eval_ctx null) with (@null valtype) by (fext; intros []);
       [| eapply K_typed].
     specialize (H 0 ids ids). mp H; [intros []|].
     asimpl in H.
     destruct H as (? & ? & ? & ? & ?). destruct H1 as (? & ? & ? & ? & ?); subst.
     eapply groundtypes_are_simple in H3 as H4; subst.
     split; intros H1 % steps_nf_eval; eauto; eapply eval_bigstep in H1.
     all: eapply bigstep_soundness.
     1: now rewrite <-(bigstep_functional H H1).
     1: now rewrite <-(bigstep_functional H0 H1).
   Qed.  
     


  Lemma obseq_soundness' n (Gamma : cbn_ctx n) (B : type) (P Q : CBN Gamma B) :
    eval_CBN P ≃ eval_CBN Q ->
    forall (C: ectx 0 n), null [[Gamma]] ⊢n C : Bool; B ->
     (CaseS (fille C P) tt ff ≫* tt) -> (CaseS (fille C Q) tt ff ≫* tt). 
  Proof.
    intros H.
    assert (eval_ctx Gamma ⊢ eval' P : eval_ty B) as T1 by eauto using cbn_type_pres'.
    assert (eval_ctx Gamma ⊢ eval' Q : eval_ty B) as T2 by eauto using cbn_type_pres'.
    assert (eval_ctx Gamma ⊨ eval P ∼ eval' P: eval_ty B) as S1 by (eapply eval_eval'; eauto).
    assert (eval_ctx Gamma ⊨ eval Q ∼ eval' Q: eval_ty B) as S2 by (eapply eval_eval'; eauto).
    assert (mkCBPVc T1 ≃ mkCBPVc T2) as H'.
    { transitivity (eval_CBN P). eapply logical_equivalence_obseq; symmetry; eauto. 
      etransitivity; eauto.      eapply logical_equivalence_obseq; eauto. 
    }
    intros C H1.
    intros H2. assert (evaluates Step (eta_if (fille C P)) tt) by (split; eauto). 
    eapply evaluates_to in H0 as (N & [] & ?); eauto.
    assert (N = ret (inj true <{ ret u }>)) as ->.
    { inv X. 
      2: destruct H0; exfalso; eapply H3; eauto.
      eapply eval_evaluates in H0; eauto.
      eapply eval_bigstep in H0. cbn in H0.
      eapply bigstep_prepend in H0.
      2: eapply let_to_eagerlet. 
      inv H0. asimpl in H7. inv H7.
      destruct b; asimpl in H8; [| inv H8].
      inv H8. reflexivity.
    } 
    assert (fillc K (eval (eta_if (fille C P))) >* ret (inj true u)).
    cbn; destruct H0. rewrite H0. repeat reduce. reflexivity.
    eapply eval_eval'_true in H3.
    2: eapply eta_if_typed, ectx_typing_soundness; eauto.
    replace (eta_if (fille C P)) with (fille (eta_if' C) P) in * by reflexivity. 
    rewrite ectx_cctx, plug_fill_cctx_comp in H3.
    edestruct H' with (G := gbool). eapply cctx_cctx_plug_typing_soundness.
    eapply K_typed. replace null with (eval_ctx null) by (fext; intros []).
    eapply ectx_cctx_typing, eta_if'_typed; eauto.
    clear H5. 
    unfold CBPVc_c in H4; mp H4. eapply H3.
    rewrite <-plug_fill_cctx_comp, <-ectx_cctx in H4.
    eapply eval_eval'_true in H4.
    2: eapply eta_if_typed, ectx_typing_soundness; eauto.
    eapply backwards.
    2 - 3: eauto.
    eapply steps_nf_eval in H4; eauto.
    eapply eval_bigstep in H4.
    cbn. cbn in H4. 
    inv H4. eapply bigstep_soundness in H7 as H10.
    rewrite H10. 
    cbn in H9; asimpl in H9. inv H9.
    destruct b; asimpl in H10.
    2: inv H11.
    eapply bigstep_prepend in H7.
    2: eapply let_to_eagerlet.
    inv H7. asimpl in H9. inv H9. destruct b; asimpl in H12.
    2: inv H12.
    inv H12. reflexivity. 
  Qed.


  Theorem obseq_soundness n (Gamma : cbn_ctx n) (B : type) (P Q : CBN Gamma B):
    eval_CBN P ≃ eval_CBN Q -> P ≃n Q.
  Proof.
    intros H; split; [| symmetry in H]; eauto using obseq_soundness'.
  Qed.


End ObservationalEquivalenceSoundness.

(** ** Denotational Semantics *)
Section Denotation.
  Variable T: Monad.
  Variable mono_requirement: forall X, Injective (@mreturn T X).

  Definition denote_type (A: type) :=
    denote_comptype T (eval_ty A).

  Definition denote_exp {n: nat} (Gamma: cbn_ctx n) (A: type) (M: CBN Gamma A) :=
    denote_comptyping (cbn_type_pres _ _ _ M).

  Definition denote_cbn_ctx {n: nat} (Gamma: cbn_ctx n) :=
    denote_context T (eval_ctx Gamma).

  Theorem Adequacy n (Gamma: cbn_ctx n) B (P Q: CBN Gamma B):
    (forall (gamma: denote_cbn_ctx Gamma), denote_exp P gamma = denote_exp Q gamma) -> P ≃n Q.
  Proof.
    intros H.
    specialize (adequacy mono_requirement (eval_CBN P) (eval_CBN Q) H).
    clear H. eauto using obseq_soundness.
  Qed.

End Denotation.
