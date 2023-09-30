Set Implicit Arguments.
Require Import Psatz  Logic List Classes.Morphisms Setoid FinFun Morphisms.
Import List Notations.


Require Export CBPV.DenotationalSemantics Confluence
        CBPV.StrongReduction CBPV.LogicalEquivalence
        CBV CBV_CBPV CBV.weakStory.


(** * Denotational Semantics CBV  *)
(** ** Contexts  *)

Inductive vctxᵥ (t: bool) (m: nat): nat -> Type :=
  | vctxᵥHole : (if t then True else False) -> vctxᵥ t m m
  | vctxᵥPairL n: vctxᵥ t m n -> Value m -> vctxᵥ t m n
  | vctxᵥPairR n : Value m -> vctxᵥ t m n -> vctxᵥ t m n
  | vctxᵥInj n : bool -> vctxᵥ t m n -> vctxᵥ t m n
  | vctxᵥLambda n: cctxᵥ t (S m) n -> vctxᵥ t m n

with cctxᵥ (t: bool) (m: nat) : nat -> Type :=
  | cctxᵥHole: (if t then False else True) -> cctxᵥ t m m
  | cctxᵥVctx n: vctxᵥ t m n -> cctxᵥ t m n
  | cctxᵥAppL n:  cctxᵥ t m n -> Exp m -> cctxᵥ t m n
  | cctxᵥAppR n:  Exp m -> cctxᵥ t m n -> cctxᵥ t m n
  | cctxᵥCaseSV n: cctxᵥ t m n -> Exp (S m) -> Exp (S m) -> cctxᵥ t m n
  | cctxᵥCaseSL n: Exp m -> cctxᵥ t (S m) n -> Exp (S m) -> cctxᵥ t m n
  | cctxᵥCaseSR n: Exp m -> Exp (S m) -> cctxᵥ t (S m) n -> cctxᵥ t m n
  | cctxᵥCasePV n: cctxᵥ t m n -> Exp (S (S m)) -> cctxᵥ t m n
  | cctxᵥCasePC n: Exp m -> cctxᵥ t (S (S m)) n -> cctxᵥ t m n.

Scheme vctxᵥ_ind_2 := Induction for vctxᵥ Sort Prop
  with cctxᵥ_ind_2  := Induction for cctxᵥ Sort Prop.

Combined Scheme mutind_cbv_ctx from vctxᵥ_ind_2, cctxᵥ_ind_2.


Fixpoint fillvᵥ {m n: nat} {t: bool} (C: vctxᵥ t m n) : (if t then Value n else Exp n) -> Value m :=
  match C in vctxᵥ _ _ n return (if t then Value n else Exp n) -> Value m with
  | vctxᵥHole _ _ H =>
    (match t return (if t then True else False) -> (if t then Value m else Exp m) -> Value m with
    | true => fun _ v' => v'
    | false => fun f _ => match f with end
    end) H
  | vctxᵥPairL C v => fun v' => Pair (fillvᵥ C v') v
  | vctxᵥPairR v C => fun v' => Pair v (fillvᵥ C v')
  | vctxᵥInj b C => fun v' => Inj b (fillvᵥ C v')
  | vctxᵥLambda C => fun v' => Lam (fillcᵥ C v')
  end
with fillcᵥ {m n: nat} {t: bool} (C: cctxᵥ t m n) : (if t then Value n else Exp n) -> Exp m :=
  match C in cctxᵥ _ _ n return (if t then Value n else Exp n) -> Exp m with
  | cctxᵥHole _ _ H =>
    (match t return (if t then False else True) -> (if t then Value m else Exp m) -> Exp m with
     | false => fun _ v' => v'
     | true => fun f _ => match f with end
     end) H
  | cctxᵥVctx C => fun v' => Val (fillvᵥ C v')
  | cctxᵥAppL C v => fun v' => App (fillcᵥ C v') v
  | cctxᵥAppR c C => fun v' => App c (fillcᵥ C v')
  | cctxᵥCaseSV C c1 c2 => fun v' => CaseS (fillcᵥ C v') c1 c2
  | cctxᵥCaseSL v C c2 => fun v' => CaseS v (fillcᵥ C v') c2
  | cctxᵥCaseSR v c1 C => fun v' => CaseS v c1 (fillcᵥ C v')
  | cctxᵥCasePV C c => fun v' => CaseP (fillcᵥ C v') c
  | cctxᵥCasePC v C => fun v' => CaseP v (fillcᵥ C v')
  end.




Reserved Notation "Gamma [[ Delta ]] ⊩v C : B ; T" (at level 53, C at level 99).
Reserved Notation "Gamma [[ Delta ]] ⊢v C : B ; T" (at level 53, C at level 99).


Inductive vctxᵥTyping {m: nat} {t: bool} (Gamma: ctx_cbv m) : forall n, ctx_cbv n -> vctxᵥ t m n -> type -> type -> Type :=
| vctxᵥTypingHole A H:
    Gamma [[ Gamma ]] ⊩v vctxᵥHole t m H : A; A
| vctxᵥTypingPairL n (Delta: ctx_cbv n) (C: vctxᵥ t m n) A A1 A2 (v: Value m):
    Gamma[[Delta]] ⊩v C : A1; A ->
    Gamma ⊩v v : A2  ->
    Gamma[[Delta]] ⊩v vctxᵥPairL C v : Cross A1 A2; A
| vctxᵥTypingPairR n (Delta: ctx_cbv n) (C: vctxᵥ t m n) A A1 A2 v:
    Gamma ⊩v v : A1  ->
    Gamma[[Delta]] ⊩v C : A2; A ->
    Gamma[[Delta]] ⊩v vctxᵥPairR v C : Cross A1 A2; A
| vctxᵥTypingInj n (Delta: ctx_cbv n) (C: vctxᵥ t m n) A A1 A2 (b: bool):
    Gamma[[Delta]] ⊩v C : (if b then A1 else A2); A ->
    Gamma[[Delta]] ⊩v vctxᵥInj b C : Plus A1 A2; A
| vctxᵥTypingLambda n (Delta: ctx_cbv n) (C: cctxᵥ t (S m) n) A A' B:
    (A .: Gamma) [[Delta]] ⊢v C : B; A' ->
      Gamma [[Delta]] ⊩v vctxᵥLambda C : Arr A B; A'
where "Gamma [[ Delta ]] ⊩v C : A ; T" := (@vctxᵥTyping _ _ Gamma _  Delta C A T)

with  cctxᵥTyping {m: nat} {t: bool} (Gamma: ctx_cbv m) :  forall n, ctx_cbv n -> cctxᵥ t m n -> type -> type -> Type :=
| cctxᵥTypingHole A H:
    Gamma [[Gamma]] ⊢v cctxᵥHole t m H : A; A
| cctxᵥTypingVctx n (Delta: ctx_cbv n) (C: vctxᵥ t m n) A A':
    Gamma [[Delta]] ⊩v C : A; A' -> Gamma [[Delta]] ⊢v cctxᵥVctx C : A; A'
| cctxᵥTypingAppL n (Delta: ctx_cbv n) (C: cctxᵥ t m n) A A' B v:
    Gamma[[Delta]] ⊢v C : Arr A B; A' ->
    Gamma ⊢v v : A  ->
    Gamma[[Delta]] ⊢v cctxᵥAppL C v : B; A'
| cctxᵥTypingAppR n (Delta: ctx_cbv n) c (C: cctxᵥ t m n) A A' B :
    Gamma ⊢v c : Arr A B  ->
    Gamma[[Delta]] ⊢v C : A; A' ->
    Gamma[[Delta]] ⊢v cctxᵥAppR c C : B; A'
| cctxᵥTypingCaseSV n (Delta: ctx_cbv n) (C: cctxᵥ t m n) A1 A2 A' B c1 c2:
    Gamma[[Delta]] ⊢v C : Plus A1 A2; A' ->
    A1 .: Gamma ⊢v c1 : B  ->
    A2 .: Gamma ⊢v c2 : B  ->
    Gamma[[Delta]] ⊢v cctxᵥCaseSV C c1 c2 : B; A'
| cctxᵥTypingCaseSL n (Delta: ctx_cbv n) (C: cctxᵥ t (S m) n) A1 A2 A' B v c2:
    Gamma ⊢v v : Plus A1 A2  ->
    (A1 .: Gamma)[[Delta]] ⊢v C : B; A' ->
    A2 .: Gamma ⊢v c2 : B  ->
    Gamma[[Delta]] ⊢v cctxᵥCaseSL v C c2 : B; A'
| cctxᵥTypingCaseSR n (Delta: ctx_cbv n) (C: cctxᵥ t (S m) n) A1 A2 A' B v c1:
    Gamma ⊢v v : Plus A1 A2  ->
    A1 .: Gamma ⊢v c1 : B  ->
    (A2 .: Gamma)[[Delta]] ⊢v C : B; A' ->
    Gamma[[Delta]] ⊢v cctxᵥCaseSR v c1 C : B; A'
| cctxᵥTypingCasePV n (Delta: ctx_cbv n) (C: cctxᵥ t m n) A1 A2 A' B c:
    Gamma[[Delta]] ⊢v C : Cross A1 A2; A' ->
    (A2 .: (A1 .: Gamma)) ⊢v c : B  ->
    Gamma[[Delta]] ⊢v cctxᵥCasePV C c : B; A'
| cctxᵥTypingCasePC n (Delta: ctx_cbv n) (C: cctxᵥ t (S (S m)) n) A1 A2 A' B v:
    Gamma ⊢v v : Cross A1 A2  ->
    (A2 .: (A1 .: Gamma))[[Delta]] ⊢v C : B; A' ->
    Gamma[[Delta]] ⊢v cctxᵥCasePC v C : B; A'
where "Gamma [[ Delta ]] ⊢v C : B ; T" := (@cctxᵥTyping _ _ Gamma _ Delta C B T).

Scheme vctxᵥ_typing_ind_2 := Minimality for vctxᵥTyping Sort Prop
  with cctxᵥ_typing_ind_2  := Minimality for cctxᵥTyping Sort Prop.

Combined Scheme mutind_vctxᵥ_cctxᵥ_typing from
         vctxᵥ_typing_ind_2, cctxᵥ_typing_ind_2.

Scheme vctxᵥ_typing_ind_3 := Induction for vctxᵥTyping Sort Prop
  with cctxᵥ_typing_ind_3  := Induction for cctxᵥTyping Sort Prop.

Combined Scheme mutindt_vctxᵥ_cctxᵥ_typing from
          vctxᵥ_typing_ind_3, cctxᵥ_typing_ind_3.


Hint Constructors vctxᵥ cctxᵥ vctxᵥTyping cctxᵥTyping.


(** Whenever we have a typed context and a correspondingly typed term,
    the result after inserting the term is well typed *)
Fixpoint vctxᵥ_value_typing_soundness m  Gamma n Delta (C: vctxᵥ true m n) A A' (H: Gamma[[Delta]] ⊩v C : A; A'):
  forall v, Delta ⊩v v : A' -> (Gamma ⊩v fillvᵥ C v : A)
with vctxᵥ_comp_typing_soundness m  Gamma n Delta (C: vctxᵥ false m n) A A' (H: Gamma[[Delta]] ⊩v C : A; A'):
  forall c, Delta ⊢v c : A' -> (Gamma ⊩v fillvᵥ C c : A)
with cctxᵥ_value_typing_soundness m Gamma n Delta (C: cctxᵥ true m n) B A' (H: Gamma[[Delta]] ⊢v C : B; A'):
  forall v, Delta ⊩v v : A' -> (Gamma ⊢v fillcᵥ C v : B)
with cctxᵥ_comp_typing_soundness m Gamma n Delta (C: cctxᵥ false m n) B A' (H: Gamma[[Delta]] ⊢v C : B; A'):
  forall c, Delta ⊢v c : A' -> (Gamma ⊢v fillcᵥ C c : B).
Proof.
  all: destruct H; intros; cbn; try econstructor; eauto; intuition.
Defined.


(** ** Alternative translation *)

Fixpoint eval'_val {n: nat} (V : Value n) : value n :=
  match V with
  | One => u
  | var_Value x => var_value x
  | Pair V1 V2 => pair (eval'_val V1) (eval'_val V2)
  | Inj b V => inj b (eval'_val V)
  | Lam M => thunk (lambda (eval'_exp M))
  end
with eval'_exp {n: nat} (M: Exp n) : Syntax.comp n :=
  match M with
  | Val V => ret (eval'_val V)
  | App M N => (lambda (lambda ($ <- var 1!; $ <- var 1!; (var 1)! (var 0)))) (<{ eval'_exp M }>) (<{ eval'_exp N }>)
  | CaseP M N => (lambda (lambda ($ <- var 1!; caseP (var 0) ((var 3)! (var 1) (var 0)))))
                  (<{eval'_exp M}>)
                  (<{ lambda (lambda (eval'_exp N)) }>)
  | CaseS M N1 N2 =>
    (lambda (lambda (lambda ($ <- var 2!; caseS (var 0) ((var 3)! (var 0)) ((var 2)! (var 0))))))
      (<{ eval'_exp M }>)
      (<{ lambda (eval'_exp N1) }>)
      (<{ lambda (eval'_exp N2) }>)
  end.



Scheme has_typeV_2 := Induction for has_typeV Sort Prop
  with has_typeE_2  := Induction for has_typeE Sort Prop.

Combined Scheme has_type_ind from has_typeE_2, has_typeV_2.


Lemma eval_ctx_cons {n : nat} (Gamma: ctx_cbv n) (A: type) :
   (A .: Gamma) >> eval_ty = (eval_ty A) .: Gamma >> eval_ty.
Proof.
  fext; intros []; cbn; reflexivity.
Qed.


Fixpoint typingVal_pres' {n} (Gamma : ctx_cbv n) V A (H : Gamma ⊩v V : A) :
  value_typing (Gamma >> eval_ty) (eval'_val V) (eval_ty A)
with typingExp_pres' {n} (Gamma : ctx_cbv n) M A (H:  Gamma ⊢v M : A) :
  computation_typing (Gamma >> eval_ty) (eval'_exp M) (F (eval_ty A)).
Proof.
  - destruct H; unfold eval_val, eval_exp; try (now (repeat constructor)); cbn; eauto. 
    + simpl.  constructor.
    constructor. specialize (typingExp_pres' _ _ _ _ h).
    revert typingExp_pres'. asimpl. auto. 
    + simpl. constructor. destruct b; apply typingVal_pres'; assumption.
  - destruct H.
    + econstructor. now eapply typingVal_pres'. 
    + simpl; repeat econstructor; eauto; eapply typeVar'; cbn; reflexivity. 
    + cbn; repeat econstructor; eauto.
      1 - 4: eapply typeVar'; cbn; reflexivity.
      all: rewrite <-eval_ctx_cons; eauto.
    + cbn; repeat econstructor; eauto.
      1 - 3: eapply typeVar'; cbn; try reflexivity.
      rewrite <-!eval_ctx_cons; eauto.
Qed.


Ltac expand' := LogicalEquivalence.expand.
Ltac VC := match goal with
         | [H: LogicalEquivalence.V ?A ?v1 ?v2 |- _] =>
           destruct H as (? & ? & ?); intuition; subst
         | [H: LogicalEquivalence.C ?B ?c1 ?c2 |- _] =>
           destruct H as (? & ? & ?); intuition; subst
         end.

Lemma eval_eval':
    (forall m (Gamma: ctx_cbv m) (M: Exp m) A, (Gamma ⊢v M : A) -> (comp_semeq (Gamma >> eval_ty) (F (eval_ty A)) (eval_exp M) (eval'_exp M)))
    /\ (forall m (Gamma: ctx_cbv m) (V: Value m) A, (Gamma ⊩v V : A) -> (val_semeq (Gamma >> eval_ty) (eval_ty A) (eval_val V) (eval'_val V))).
Proof.
  eapply has_type_ind; cbn; intros; try eapply fundamental_property; eauto.
  - eapply logical_equivalence_congruent_vctx_comp with (C := vctxThunk (cctxLambda •__c)); eauto.
    cbn. rewrite <-eval_ctx_cons. assumption.
  - etransitivity.
    eapply logical_equivalence_congruent_vctx_value with (C := vctxPairL •__v (eval_val V2)); eauto.
    { repeat constructor. now eapply typingVal_pres. } cbn.
    eapply logical_equivalence_congruent_vctx_value with (C := vctxPairR (eval'_val V1) •__v); eauto.
    repeat constructor. now eapply typingVal_pres'.
  - eapply logical_equivalence_congruent_vctx_value with (C := vctxInj b •__v); eauto.
    cbn; now destruct b.
  - eapply logical_equivalence_congruent_cctx_value with (C := cctxRet •__v); eauto.
  - intros m gamma gamma' H1. rewrite eagerlet_substcomp. 
    eapply LogicalEquivalence.closure_under_reduction.
    eapply let_to_eagerlet. reflexivity.
    eapply LogicalEquivalence.closure_under_expansion.
    reflexivity. repeat (asimpl; reduce); reflexivity. 
    eapply bind with
        (K1 := ectxLetin Semantics.ectxHole _)
        (K2 := ectxLetin Semantics.ectxHole _); semeq_solve.
    intros c1 c2 []; exintuition; subst.
    destruct H5; exintuition; subst; cbn [fill].
    eapply LogicalEquivalence.closure_under_expansion.
    1 - 2: repeat reduce; asimpl; rewrite ?eagerlet_substcomp; asimpl; reflexivity.
    eapply LogicalEquivalence.closure_under_reduction.
    eapply let_to_eagerlet. reflexivity.
    eapply bind with
        (K1 := ectxLetin Semantics.ectxHole _)
        (K2 := ectxLetin Semantics.ectxHole _); semeq_solve.
    intros ? ? []; exintuition; subst; cbn [fill].
    eapply LogicalEquivalence.closure_under_expansion.
    1 - 2: repeat reduce; asimpl; reflexivity. 
    eapply congruence_app; eauto.
  -  intros m gamma gamma' H2. rewrite eagerlet_substcomp. 
    eapply LogicalEquivalence.closure_under_reduction.
    eapply let_to_eagerlet. reflexivity.
    eapply LogicalEquivalence.closure_under_expansion.
    reflexivity. repeat (asimpl; reduce); reflexivity.
    eapply bind with
        (K1 := ectxLetin Semantics.ectxHole _)
        (K2 := ectxLetin Semantics.ectxHole _); semeq_solve.
    intros ? ? []; exintuition; subst.
    destruct H6; exintuition; subst. 
    cbn [fill].
    destruct x3; eapply LogicalEquivalence.closure_under_expansion.
    all: try solve [repeat (asimpl; reduce); reflexivity].
    all: asimpl. 
     + eapply H0; semeq_solve.
       replace ((A .: Gamma) >> _) with (eval_ty A .: (Gamma >> eval_ty)); semeq_solve.
       unfold funcomp; fext; intros [|]; cbn; reflexivity.
     + eapply H1; semeq_solve.
       replace ((B .: Gamma) >> _) with (eval_ty B .: (Gamma >> eval_ty)); semeq_solve.
       unfold funcomp; fext; intros [|]; cbn; reflexivity.
  -  intros m gamma gamma' H2. rewrite eagerlet_substcomp. 
    eapply LogicalEquivalence.closure_under_reduction.
    eapply let_to_eagerlet. reflexivity.
    eapply LogicalEquivalence.closure_under_expansion.
    reflexivity. repeat (asimpl; reduce); reflexivity.
    eapply bind with
        (K1 := ectxLetin Semantics.ectxHole _)
        (K2 := ectxLetin Semantics.ectxHole _); semeq_solve.
    intros ? ? []; exintuition; subst.
    destruct H5; exintuition; subst. 
    cbn [fill].
    eapply LogicalEquivalence.closure_under_expansion.
    1, 2: repeat (asimpl; reduce); reflexivity.
    asimpl.
    eapply H0. replace (_ >> eval_ty) with (eval_ty B .: (eval_ty A .: Gamma >> eval_ty)); semeq_solve.
    fext; intros [ [|] |]; cbn; reflexivity.
Qed.


Fixpoint eval'_vctx {m n: nat} t (C : vctxᵥ t m n) : vctx t m n :=
  match C in vctxᵥ _ _ n return vctx t m n with
  | vctxᵥHole _ _ H => vctxHole t m H
  | vctxᵥPairL C v => vctxPairL (eval'_vctx  C) (eval'_val v)
  | vctxᵥPairR v C => vctxPairR (eval'_val v) (eval'_vctx C)
  | vctxᵥInj b C => vctxInj b (eval'_vctx C)
  | vctxᵥLambda C => vctxThunk (cctxLambda (eval'_cctx  C))
  end
with eval'_cctx {m n: nat} t (C: cctxᵥ t m n) : cctx t m n :=
  match C in cctxᵥ _ _ n return cctx t m n with
  | cctxᵥHole _ _ H => cctxHole t m H
  | cctxᵥVctx C => cctxRet (eval'_vctx C)
  | cctxᵥAppL C v =>
    cctxAppL (cctxAppR (lambda (lambda ($ <- var 1!; $ <- var 1!; (var 1)! (var 0))))
        (vctxThunk (eval'_cctx C))) (<{ eval'_exp v }>)
  | cctxᵥAppR c C => cctxAppR
        ((lambda (lambda ($ <- var 1!; $ <- var 1!; (var 1)! (var 0)))) (<{ eval'_exp c }>))
        (vctxThunk (eval'_cctx C))
  | cctxᵥCaseSV C c1 c2 =>
        cctxAppL
          (cctxAppL
             (cctxAppR
                (lambda (lambda (lambda ($ <- var 2!; caseS (var 0) ((var 3)! (var 0)) ((var 2)! (var 0))))))
                (vctxThunk (eval'_cctx C)))
             (<{ lambda (eval'_exp c1) }>))
          (<{ lambda (eval'_exp c2) }>)
  | cctxᵥCaseSL v C c2 =>
    cctxAppL
      (cctxAppR
         ((lambda (lambda (lambda ($ <- var 2!; caseS (var 0) ((var 3)! (var 0)) ((var 2)! (var 0))))))
            (<{ eval'_exp v }>))
         (vctxThunk (cctxLambda (eval'_cctx C))))
      (<{ lambda (eval'_exp c2) }>)
  | cctxᵥCaseSR v c1 C =>
    cctxAppR
      ((lambda (lambda (lambda ($ <- var 2!; caseS (var 0) ((var 3)! (var 0)) ((var 2)! (var 0))))))
         (<{ eval'_exp v }>)
         (<{ lambda (eval'_exp c1) }>))
      (vctxThunk (cctxLambda (eval'_cctx C)))
  | cctxᵥCasePV C c =>
    cctxAppL
      (cctxAppR (lambda (lambda ($ <- var 1!; caseP (var 0) ((var 3)! (var 1) (var 0)))))
                (vctxThunk (eval'_cctx C)))
      (<{ lambda (lambda (eval'_exp c)) }>)
  | cctxᵥCasePC v C =>
    cctxAppR
      ((lambda (lambda ($ <- var 1!; caseP (var 0) ((var 3)! (var 1) (var 0)))))
         (<{ eval'_exp v }>))
      (vctxThunk (cctxLambda (cctxLambda (eval'_cctx C))))
  end.


Fixpoint vctxᵥ_vctx_value {m n} (C: vctxᵥ true m n) (e: Value n):
  eval'_val (fillvᵥ C e) = fillv (eval'_vctx C) (eval'_val e)
with  vctxᵥ_vctx_comp {m n} (C: vctxᵥ false m n) (e: Exp n):
  eval'_val (fillvᵥ C e) = fillv (eval'_vctx C) (eval'_exp e)
with cctxᵥ_cctx_value {m n} (C: cctxᵥ true m n) (e: Value n):
  eval'_exp (fillcᵥ C e) = fillc (eval'_cctx C) (eval'_val e)
with cctxᵥ_cctx_comp {m n} (C: cctxᵥ false m n) (e: Exp n):
  eval'_exp (fillcᵥ C e) = fillc (eval'_cctx C) (eval'_exp e).
Proof.
  all: destruct C; cbn; intuition; congruence.
Qed.


Fixpoint eval'_cctx_value_typing {m n: nat} Gamma Delta (C: cctxᵥ true m n) A B (H: Gamma [[Delta]] ⊢v C : A;  B):
  (Gamma >> eval_ty) [[Delta >> eval_ty]] ⊢ eval'_cctx C : F (eval_ty A); eval_ty B
with eval'_cctx_comp_typing {m n: nat} Gamma Delta (C: cctxᵥ false m n) A B (H: Gamma [[Delta]] ⊢v C : A; B):
  (Gamma >> eval_ty) [[Delta >> eval_ty]] ⊢ eval'_cctx C : F (eval_ty A); F (eval_ty B)
with eval'_vctx_value_typing {m n: nat} Gamma Delta (C: vctxᵥ true m n) A B (H: Gamma [[Delta]] ⊩v C : A; B):
  (Gamma >> eval_ty) [[Delta >> eval_ty]] ⊩ eval'_vctx C : eval_ty A; eval_ty B
with eval'_vctx_comp_typing {m n: nat} Gamma Delta (C: vctxᵥ false m n) A B (H: Gamma [[Delta]] ⊩v C : A; B):
  (Gamma >> eval_ty) [[Delta >> eval_ty]] ⊩ eval'_vctx C : eval_ty A; F (eval_ty B).
Proof.
  all: destruct H; cbn; intros; repeat econstructor; eauto using typingExp_pres', typingVal_pres'.
  all: try solve [eapply typeVar'; cbn; reflexivity].
  all: try solve [rewrite <-!eval_ctx_cons; eauto using typingExp_pres', typingVal_pres'].
  all: intuition.
  all: destruct b; eauto.
Qed.

Definition Bool := Plus Unit Unit.
Definition tt {n: nat}: Exp n := Val (Inj true One).
Definition ff {n: nat}: Exp n := Val (Inj false One).



Record CBV {n: nat} (Gamma: ctx_cbv n) (A: type) :=
  mkCBV { CBV_e :>  Exp n; CBV_H :> Gamma ⊢v CBV_e : A }.


Record CBVᵥ {n: nat} (Gamma: ctx_cbv n) (A: type) :=
  mkCBVᵥ { CBV_v :> Value n; CBV_Hᵥ :> Gamma ⊩v CBV_v : A }.

Hint Resolve CBV_H CBV_Hᵥ.

(** Expression Contextual Equivalence *)
Notation "s ≫* t" := (star Step s t) (at level 60).

Definition exp_obseq {n: nat} {B: type} {Gamma: ctx_cbv n} (H1 H2: CBV Gamma B) :=
  forall (C: cctxᵥ false 0 n), null [[Gamma]] ⊢v C : Bool; B -> (fillcᵥ C H1 ≫* tt) <-> (fillcᵥ C H2 ≫* tt).

Instance equiv_exp_obseq (n: nat) (B: type) (Gamma: ctx_cbv n):
  Equivalence (@exp_obseq n B Gamma).
Proof.
  constructor; [firstorder.. |].
  intros X1 X2 X3 H1 H2 C H; etransitivity; eauto.
Qed.


Definition value_obseq {n: nat} {B: type} {Gamma: ctx_cbv n} (H1 H2: CBVᵥ Gamma B) :=
  forall (C: cctxᵥ true 0 n), null [[Gamma]] ⊢v C : Bool; B -> (fillcᵥ C H1 ≫* tt) <-> (fillcᵥ C H2 ≫* tt).

Instance equiv_value_obseq (n: nat) (B: type) (Gamma: ctx_cbv n):
  Equivalence (@value_obseq n B Gamma).
Proof.
  constructor; [firstorder.. |].
  intros X1 X2 X3 H1 H2 C H; etransitivity; eauto.
Qed.



Notation "C1 '≃v' C2" := (exp_obseq C1 C2) (at level 50).
Notation "C1 '≈v' C2" := (value_obseq C1 C2) (at level 50).



Definition eval_CBV (n: nat) (Gamma: ctx_cbv n) (A: type) :
  CBV Gamma A -> CBPVc (Gamma >> eval_ty) (F (eval_ty A)) :=
  fun H => @mkCBPVc _ (Gamma >> eval_ty) (F (eval_ty A)) (eval_exp H) (typingExp_pres _ _ _ H).

Definition eval_CBVᵥ (n: nat) (Gamma: ctx_cbv n) (A: type) :
  CBVᵥ Gamma A -> CBPVv (Gamma >> eval_ty) (eval_ty A) :=
  fun H => @mkCBPVv _ (Gamma >> eval_ty) (eval_ty A) (eval_val H) (typingVal_pres _ _ _ H).




(** ** Observational Equivalence by translation *)
Section ObservationalEquivalenceSoundness.

  (* ground returner context, converting booleans to ground returners *)

  Local Definition gbool := gsum gone gone.

  Lemma eval_eval'_tt  s :
    null ⊢v s : Bool -> (eval'_exp s >* eval'_exp tt <-> eval_exp s >* eval_exp tt).
  Proof.
    intros; destruct eval_eval' as [S _];
      destruct (S _ _ _ _ X 0 ids ids) as (? & ? & ? & ? & ?); [intros []|].
    asimpl in H; asimpl in H0.
    destruct H1 as (? & ? & ? & ? & ?); subst.
    eapply groundtypes_are_simple with (G := gbool) in H3 as H4; subst.
    cbn. 
    split; cbn; intros H1 % steps_nf_eval; eauto; eapply eval_bigstep in H1.
     all: eapply bigstep_soundness.
     1: now rewrite <-(bigstep_functional H0 H1).
     1: now rewrite <-(bigstep_functional H H1).
  Qed.


  Lemma obseq_soundness' n (Gamma : ctx_cbv n) (B : type) (P Q : CBV Gamma B) :
    eval_CBV P ≃ eval_CBV Q ->
    forall (C: cctxᵥ false 0 n), null [[Gamma]] ⊢v C : Bool; B ->
     (fillcᵥ C P ≫* tt) -> (fillcᵥ C Q ≫* tt).
  Proof.
    intros H.
  assert (Gamma >> eval_ty ⊢ eval'_exp P : F (eval_ty B)) as T1 by eauto using typingExp_pres'.
  assert (Gamma >> eval_ty ⊢ eval'_exp Q : F (eval_ty B)) as T2 by eauto using typingExp_pres'.
  assert (mkCBPVc T1 ≃ mkCBPVc T2) as H'.
  { transitivity (eval_CBV P). eapply logical_equivalence_obseq; cbn. symmetry.
    now eapply eval_eval'.
    etransitivity; eauto. eapply logical_equivalence_obseq; cbn; now eapply eval_eval'.
  }
  intros C H1 H2.
  apply MStep_preserved in H2.
  eapply eval_eval'_tt in H2; eauto using cctxᵥ_comp_typing_soundness.
  eapply backward_simulation. split; [|eapply nf_normal; repeat econstructor].
  eapply eval_eval'_tt; eauto using cctxᵥ_comp_typing_soundness.
  rewrite cctxᵥ_cctx_comp in *.
  eapply eval'_cctx_comp_typing in H1.
  replace (null >> eval_ty) with (@null valtype) in H1 by (fext; intros []).
  replace (eval_ty Bool) with (gsum gone gone: valtype) in H1 by reflexivity. 
  specialize (H' _ _ H1). 
  cbn in H'. eapply H'. assumption.
  Qed.


  Lemma obseq_soundnessᵥ' n (Gamma : ctx_cbv n) (B : type) (P Q : CBVᵥ Gamma B) :
  eval_CBVᵥ P ≈ eval_CBVᵥ Q ->
  forall (C: cctxᵥ true 0 n), null [[Gamma]] ⊢v C : Bool; B ->
  (fillcᵥ C P ≫* tt) -> (fillcᵥ C Q ≫* tt).
  Proof.
    intros H.
    assert (Gamma >> eval_ty ⊩ eval'_val P : eval_ty B) as T1 by eauto using typingVal_pres'.
    assert (Gamma >> eval_ty ⊩ eval'_val Q : eval_ty B) as T2 by eauto using typingVal_pres'.
    assert (mkCBPVv T1 ≈ mkCBPVv T2) as H'.
    { transitivity (eval_CBVᵥ P). eapply logical_equivalence_obseq; cbn. symmetry.
      now eapply eval_eval'.
      etransitivity; eauto. eapply logical_equivalence_obseq; cbn; now eapply eval_eval'.
    }
    intros C H1 H2.
    apply MStep_preserved in H2.
    eapply eval_eval'_tt in H2; eauto using cctxᵥ_value_typing_soundness.
    eapply backward_simulation. split; [|eapply nf_normal; repeat econstructor].
    eapply eval_eval'_tt; eauto using cctxᵥ_value_typing_soundness.
    rewrite cctxᵥ_cctx_value in *.
    eapply eval'_cctx_value_typing in H1.
    replace (null >> eval_ty) with (@null valtype) in H1 by (fext; intros []).
    replace (eval_ty Bool) with (gsum gone gone: valtype) in H1 by reflexivity. 
    specialize (H' _ _ H1). 
    cbn in H'. eapply H'. assumption.
  Qed.
  
  
  Theorem obseq_soundness n (Gamma : ctx_cbv n) (B : type) (P Q : CBV Gamma B):
    eval_CBV P ≃ eval_CBV Q -> P ≃v Q.
  Proof.
    intros H; split; [| symmetry in H]; eauto using obseq_soundness'.
  Qed.
  
  
  Theorem obseq_soundnessᵥ n (Gamma : ctx_cbv n) (B : type) (P Q : CBVᵥ Gamma B):
    eval_CBVᵥ P ≈ eval_CBVᵥ Q -> P ≈v Q.
  Proof.
    intros H; split; [| symmetry in H]; eauto using obseq_soundnessᵥ'.
  Qed.
  

End ObservationalEquivalenceSoundness.

(** ** Denotational Semantics *)
Section Denotation.
  Variable T: Monad.
  Variable mono_requirement: forall X, Injective (@mreturn T X).
  Variable (n: nat) (Gamma: ctx_cbv n) (A: type).

  Definition denote_type  :=
    denote_comptype T (F (eval_ty A)).

  Definition denote_exp  (M: CBV Gamma A) :=
    denote_comptyping (typingExp_pres _ _ _ M).


  Definition denote_val  (M: CBVᵥ Gamma A) :=
    denote_valtyping (typingVal_pres _ _ _ M).


  Definition denote_cbv_ctx  :=
    denote_context T (Gamma >> eval_ty).

  Theorem Adequacy (P Q: CBV Gamma A):
    (forall (gamma: denote_cbv_ctx), denote_exp P gamma = denote_exp Q gamma) -> P ≃v Q.
  Proof.
    intros H.
    specialize (adequacy mono_requirement (eval_CBV P) (eval_CBV Q) H).
    clear H. eauto using obseq_soundness.
  Qed.


  Theorem Adequacyᵥ (P Q: CBVᵥ Gamma A):
    (forall (gamma: denote_cbv_ctx), denote_val P gamma = denote_val Q gamma) -> P ≈v Q.
  Proof.
    intros H.
    specialize (adequacyᵥ mono_requirement (eval_CBVᵥ P) (eval_CBVᵥ Q) H).
    clear H. eauto using obseq_soundnessᵥ.
  Qed.


End Denotation.
