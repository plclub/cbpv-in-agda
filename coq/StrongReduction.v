Set Implicit Arguments.
Require Import Psatz Logic List Classes.Morphisms.
Import List Notations.

Require Export CBPV.ProgramContexts CBPV.Semantics.
Import CommaNotation.

(** * Strong Reduction *)

Reserved Notation "C1 ⇒ C2" (at level 60).
Reserved Notation "V1 ⇒ᵥ V2" (at level 60).

(** ** Context Semantics *)
Inductive strong_step {n: nat} : comp n -> comp n -> Prop :=
| strong_reduce  m (c1 c2: comp m) (K: cctx false n m):
    c1 ≽ c2 -> fillc K c1 ⇒ fillc K c2
where "C1 ⇒ C2" := (strong_step C1 C2).

Inductive strong_step_value {n : nat} : value n -> value n -> Prop :=
| strong_reduce_value k (c1 c2 : comp k) (K : vctx false n k) :
    c1 ≽ c2 -> fillv K c1 ⇒ᵥ fillv K c2
where "V1 ⇒ᵥ V2" := (strong_step_value V1 V2).


(** ** Recursive Semantics *)
Reserved Notation "C1 ↪ C2" (at level 60).
Reserved Notation "V1 ↪ᵥ V2" (at level 60).

Inductive sstep {n: nat} : comp n -> comp n -> Prop :=
| sstepForce (v v': value n): v ↪ᵥ v' -> v ! ↪ v' !
| sstepLambda (c c': comp (S n)): c ↪ c' -> lambda c ↪ lambda c'
| sstepAppL (c c': comp n) v: c ↪ c' -> c v ↪ c' v
| sstepAppR (c: comp n) (v v': value n): v ↪ᵥ v' -> c v ↪ c v'
| sstepTupleL (c1 c1': comp n) c2: c1 ↪ c1' -> tuple c1 c2 ↪ tuple c1' c2
| sstepTupleR c1 (c2 c2': comp n): c2 ↪ c2' -> tuple c1 c2 ↪ tuple c1 c2'
| sstepRet (v v': value n): v ↪ᵥ v' -> ret v ↪ ret v'
| sstepLetinL (c1 c1': comp n) c2: c1 ↪ c1' -> letin c1 c2 ↪ letin c1' c2
| sstepLetinR c1 (c2 c2': comp (S n)): c2 ↪ c2' -> letin c1 c2 ↪ letin c1 c2'
| sstepProj (c c': comp n) b: c ↪ c' -> proj b c ↪ proj b c'
| sstepCaseZ (v v': value n): v ↪ᵥ v' -> caseZ v ↪ caseZ v'
| sstepCaseSV (v v': value n) c1 c2: v ↪ᵥ v' -> caseS v c1 c2 ↪ caseS v' c1 c2
| sstepCaseSL (v: value n) c1 c1' c2: c1 ↪ c1' -> caseS v c1 c2 ↪ caseS v c1' c2
| sstepCaseSR (v: value n) c1 c2 c2': c2 ↪ c2' -> caseS v c1 c2 ↪ caseS v c1 c2'
| sstepCasePV (v v': value n) c: v ↪ᵥ v' -> caseP v c ↪ caseP v' c
| sstepCasePC (v: value n) c c': c ↪ c' -> caseP v c ↪ caseP v c'
| sstepPrimitive (c c': comp n) : c ≽ c' -> c ↪ c'
where "C1 ↪ C2" := (@sstep _ C1 C2)
with sstep_value {n: nat} : value n -> value n -> Prop :=
| sstepValuePairL (v1 v1' v2: value n) : v1 ↪ᵥ v1' -> pair v1 v2 ↪ᵥ pair v1' v2
| sstepValuePairR (v1 v2 v2': value n) : v2 ↪ᵥ v2' -> pair v1 v2 ↪ᵥ pair v1 v2'
| sstepValueInj b (v v': value n) : v ↪ᵥ v' -> inj b v ↪ᵥ inj b v'
| sstepValueThunk (c c': comp n) : c ↪ c' -> <{ c }> ↪ᵥ <{ c' }>
where "V1 ↪ᵥ V2" := (@sstep_value _ V1 V2).


Scheme sstep_value_ind_2 := Induction for sstep_value Sort Prop
  with sstep_ind_2  := Induction for sstep Sort Prop.

Combined Scheme mutind_sstep from sstep_ind_2, sstep_value_ind_2.


Notation "M ↪* N" := (star sstep M N) (at level 60).
Notation "M ↪ᵥ* N" := (star sstep_value M N) (at level 60).

Hint Constructors strong_step strong_step_value sstep sstep_value.


(** Strong Step Congruence Lemmas *)
Lemma strong_step_congruence {n m: nat} (K: cctx false m n) (c1 c2: comp n):
  c1 ⇒ c2 -> fillc K c1 ⇒ fillc K c2.
Proof.
  intros []; repeat rewrite plug_fill_cctx_comp; eauto.
Qed.

Lemma strong_step_congruence_value {n m: nat} (K: cctx true m n) (v1 v2: value n):
  v1 ⇒ᵥ v2 -> fillc K v1  ⇒ fillc K v2.
Proof.
  intros []; repeat rewrite plug_fill_cctx_value; eauto.
Qed.

Lemma strong_step_value_congruence {n m: nat} (K: vctx false m n) (c1 c2: comp n):
  c1 ⇒ c2 -> fillv K c1 ⇒ᵥ fillv K c2.
Proof.
  intros []; repeat rewrite plug_fill_vctx_comp; eauto.
Qed.

Lemma strong_step_value_congruence_value {n m: nat} (K: vctx true m n) (v1 v2: value n):
  v1 ⇒ᵥ v2 -> fillv K v1  ⇒ᵥ fillv K v2.
Proof.
  intros []; repeat rewrite plug_fill_vctx_value; eauto.
Qed.


(** Strong Step Congruence Lemmas *)
Fixpoint sstep_congruence {n m: nat} (c1 c2: comp n)  (K: cctx false m n):
  c1 ↪ c2 -> fillc K c1 ↪ fillc K c2

with sstep_congruence_value {n m: nat} (v1 v2: value n) (K: cctx true m n):
  v1 ↪ᵥ v2 -> fillc K v1  ↪ fillc K v2

with sstep_value_congruence {n m: nat} (c1 c2: comp n) (K: vctx false m n) :
  c1 ↪ c2 -> fillv K c1 ↪ᵥ fillv K c2

with sstep_value_congruence_value {n m: nat}  (v1 v2: value n) (K: vctx true m n):
  v1 ↪ᵥ v2 -> fillv K v1  ↪ᵥ fillv K v2.
Proof.
  all: destruct K; intros; cbn; eauto.
  all: try solve [destruct y].
Qed.

Hint Resolve sstep_congruence sstep_congruence_value sstep_value_congruence
     sstep_value_congruence_value.

Fixpoint sstep_lemma n (c c': comp n) (H: c ↪ c') :
  c ⇒ c'
with  sstep_value_lemma n (v v': value n) (H: v ↪ᵥ v') :
  v ⇒ᵥ v'.
Proof.
  all: destruct H.
  - eapply strong_step_congruence_value with (K := cctxForce •__v); eauto.
  - eapply strong_step_congruence with (K := cctxLambda •__c); eauto.
  - eapply strong_step_congruence with (K := cctxAppL •__c _); eauto.
  - eapply strong_step_congruence_value with (K := cctxAppR _ •__v); eauto.
  - eapply strong_step_congruence with (K := cctxTupleL •__c _); eauto.
  - eapply strong_step_congruence with (K := cctxTupleR _ •__c); eauto.
  - eapply strong_step_congruence_value with (K := cctxRet •__v); eauto.
  - eapply strong_step_congruence with (K := cctxLetinL •__c _); eauto.
  - eapply strong_step_congruence with (K := cctxLetinR _  •__c); eauto.
  - eapply strong_step_congruence with (K := cctxProj b •__c); eauto.
  - eapply strong_step_congruence_value with (K := cctxCaseZ •__v); eauto.
  - eapply strong_step_congruence_value with (K := cctxCaseSV •__v _ _); eauto.
  - eapply strong_step_congruence with (K := cctxCaseSL _ •__c _); eauto.
  - eapply strong_step_congruence with (K := cctxCaseSR _ _ •__c); eauto.
  - eapply strong_step_congruence_value with (K := cctxCasePV •__v _); eauto.
  - eapply strong_step_congruence with (K := cctxCasePC _ •__c); eauto.
  - eapply strong_reduce with (K := •__c); eauto.
  - eapply strong_step_value_congruence_value with (K := vctxPairL •__v _); eauto.
  - eapply strong_step_value_congruence_value with (K := vctxPairR  _ •__v); eauto.
  - eapply strong_step_value_congruence_value with (K := vctxInj b •__v); eauto.
  - eapply strong_step_value_congruence with (K := vctxThunk •__c); eauto.
Qed.

(** *** Strong Step Equivalence Lemmas *)
Lemma sstep_strong_step {n: nat} (c1 c2: comp n):
  c1 ↪ c2 <-> c1 ⇒ c2.
Proof.
  split.
  - eapply sstep_lemma.
  - intros []; eapply sstep_congruence; eauto.
Qed.

Lemma sstep_strong_step_value {n: nat} (v1 v2: value n):
  v1 ↪ᵥ v2 <-> v1 ⇒ᵥ v2.
Proof.
  split.
  - eapply sstep_value_lemma.
  - intros []; eapply sstep_value_congruence; eauto.
Qed.


Global Instance subrel_step_sstep {n: nat}: subrelation (@step n) (@sstep n).
Proof.
  intros x y H; induction H; eauto.
Qed.

(** *** Strong Step Progress *)
Lemma sstep_progress n:
  (forall (v: value n), (exists v', v ↪ᵥ v') \/ Normal sstep_value v) /\
  (forall (e: comp n), (exists e', e ↪ e') \/ Normal sstep e).
Proof with intros ? S; inv S; eauto.
  revert n; eapply mutind_val_comp; intros; unfold Normal in *.
  all: exintuition; eauto.
  all: try solve [right; intros ? S; inv S; eauto; inv H || inv H1 ].
  - destruct v; [ right.. | left]; eauto; intros ? S;
      inv S; inv H || inv H1; eauto.
  - destruct c; try solve [left; eauto]; right...
    all: inv H0.
  - right... inv H0.
  - destruct c; try solve [left; eauto]; right...
    all: inv H0.
  - destruct c; try solve [left; eauto]; right...
    all: inv H.
  - destruct v; try solve [left; eauto]; right...
    all: inv H1.
  - destruct v; try solve [left; eauto]; right...
    all: inv H0.
Qed.

(** *** Weak to Strong *)
Lemma step_strong {n: nat} (c1 c2: comp n):
  c1 > c2 -> c1 ⇒ c2.
Proof.
  induction 1.
  - eapply strong_reduce with (K := •__c); eauto.
  - eapply strong_step_congruence with (K := cctxAppL •__c v); eauto.
  - eapply strong_step_congruence with (K := cctxProj b •__c); eauto.
  - eapply strong_step_congruence with (K := cctxLetinL •__c c2); eauto.
Qed.

Lemma strong_step_progress (e: comp 0) (B: comptype) :
  null ⊢ e : B -> (exists e', e ⇒ e') \/ nf e.
Proof.
    intros [ [] | H2] % progress; eauto.
  left; eexists; eapply step_strong; eauto.
Qed.

(** *** Strong Step Preservation *)
Lemma strong_step_preservation {n: nat} (c1 c2: comp n) (Gamma: ctx n) B:
  c1 ⇒ c2 -> inhab (Gamma ⊢ c1 : B) -> inhab (Gamma ⊢ c2 : B).
Proof.
  intros [] [];
  destruct (context_typing_decomposition_cctx_comp _  _ X) as (Delta & B' & H1 & H2);
  destruct (primitive_preservation H H2);
  constructor; apply (cctx_comp_typing_soundness H1 X0).
Qed.

Lemma strong_step_value_preservation {n: nat} (v1 v2: value n) (Gamma: ctx n) A:
  v1 ⇒ᵥ v2 -> inhab (Gamma ⊩ v1 : A) -> inhab (Gamma ⊩ v2 : A).
Proof.
  intros [] [];
  destruct (context_typing_decomposition_vctx_comp _  _ X) as (Delta & B' & H1 & H2);
  destruct (primitive_preservation H H2);
  constructor; apply (vctx_comp_typing_soundness H1 X0).
Qed.

Lemma sstep_preservation {n: nat} (c1 c2: comp n) (Gamma: ctx n) B:
  c1 ↪ c2 -> inhab (Gamma ⊢ c1 : B) -> inhab (Gamma ⊢ c2 : B).
Proof.
  intros H % sstep_lemma. now apply strong_step_preservation.
Qed.

Lemma ssteps_preservation {n: nat} (c1 c2: comp n) (Gamma: ctx n) B:
  star sstep c1 c2 -> inhab (Gamma ⊢ c1 : B) -> inhab (Gamma ⊢ c2 : B).
Proof.
  induction 1; eauto.
  intros H1. eapply sstep_preservation in H; eauto.
Qed.



(** ** Compatibility with substitutions *)
Fixpoint primitive_step_subst m n k (f : fin m -> value n) (C1 C2 : comp k) (K: cctx false m k):
  C1 ≽ C2 -> (fillc K C1)[f] ↪ (fillc K C2)[f]
with primitive_step_subst_value m n k (f : fin m -> value n) (C1 C2 : comp k) (K: vctx false m k):
  C1 ≽ C2 -> (fillv K C1)[f] ↪ᵥ (fillv K C2)[f].
Proof.
  all: destruct K; cbn; intros; eauto.
  - constructor; eapply pstep_subst; eauto.
  - destruct y.
Qed.


Lemma strong_step_subst m n (f : fin m -> value n) (C1 C2 : comp m) :
  C1 ⇒ C2 -> C1[f] ⇒ C2[f].
Proof.
  intros []; rewrite <-sstep_strong_step; eapply primitive_step_subst; assumption.
Qed.

Lemma strong_step_value_subst m n (f : fin m -> value n) (V1 V2 : value m) :
  V1 ⇒ᵥ V2 -> V1[f] ⇒ᵥ V2[f].
Proof.
    intros []; rewrite <-sstep_strong_step_value;  eapply primitive_step_subst_value; assumption.
Qed.


Lemma pstep_anti_renaming m n (f: fin m -> fin n) (c : comp m) (d: comp n) :
 c⟨f⟩ ≽ d -> exists2 d', c ≽ d' & d = d'⟨f⟩.
Proof with eexists; eauto; now asimpl.
  destruct c; asimpl; intros H; inv H.
  - destruct v; try discriminate; cbn in *; injection H1 as ->...
  - destruct c; try discriminate; cbn in *; injection H0 as ->.
    eexists; eauto. now asimpl.
  - destruct c1; try discriminate; cbn in *; injection H0 as ->...
  - destruct b, c; try discriminate; cbn in *; injection H2 as ->...
  - destruct v; try discriminate; cbn in *; injection H0 as -> ->; destruct b0...
  -  destruct v; try discriminate; cbn in *. injection H0 as -> ->...
Qed.


Fixpoint sstep_anti_renaming m n (f : fin m -> fin n) (c : comp m) (d : comp n) :
  c⟨f⟩ ↪ d ->
  exists2 d', c ↪ d' & d = d'⟨f⟩
with sstep_value_anti_renaming m n (f : fin m -> fin n) (v : value m) (w : value n) :
  v⟨f⟩ ↪ᵥ w ->
  exists2 w', v ↪ᵥ  w' & w = w'⟨f⟩.
Proof.
  1: destruct c.
  12: destruct v.
  all: cbn; intros H; inv H.
  all: try solve [intros; edestruct sstep_anti_renaming; eauto; subst; eexists; eauto].
  all: try solve [intros; edestruct sstep_value_anti_renaming; eauto; subst; eexists; eauto].
  all: try solve [inv H0].
  1: specialize (pstep_anti_renaming f (v !) H0) as []; eexists; eauto.
  1: specialize (pstep_anti_renaming f (c v) H0) as []; eexists; eauto.
  1: specialize (pstep_anti_renaming f ($ <- c1; c2) H0) as []; eexists; eauto.
  1: specialize (pstep_anti_renaming f (proj b c) H0) as []; eexists; eauto.
  1: specialize (pstep_anti_renaming f (caseS v c1 c2) H0) as []; eexists; eauto.
  1: specialize (pstep_anti_renaming f (caseP v c) H0) as []; eexists; eauto.
Qed.


Lemma strong_step_anti_renaming m n (f : fin m -> fin n) (c : comp m) (d : comp n) :
  c⟨f⟩ ⇒ d -> exists2 d', c ⇒ d' & d = d'⟨f⟩.
Proof.
  rewrite <-sstep_strong_step; intros [] % sstep_anti_renaming;
  eexists; eauto; rewrite <-sstep_strong_step; eauto.
Qed.

Lemma strong_step_value_anti_renaming m n (f : fin m -> fin n) (v1 : value m) (v2 : value n) :
  v1⟨f⟩⇒ᵥ v2 -> exists2 v2', v1 ⇒ᵥ v2' & v2 = v2'⟨f⟩.
Proof.
  repeat rewrite <-sstep_strong_step_value; intros H.
  edestruct sstep_value_anti_renaming; eauto; eexists; rewrite <-?sstep_strong_step_value; eauto.
Qed.

(** ** Strong normalisation *)

Definition sn {n : nat} (C : comp n) : Prop :=
  SN (@strong_step n) C.

Definition snv {n : nat} (V : value n) : Prop :=
  SN (@strong_step_value n) V.

(** ** Proper lemmas *)

Instance proper_sstep_pairL n : Proper (star sstep_value ==> eq ==> star sstep_value) (@pair n).
Proof.
  cbv. induction 1; intros; subst; eauto.
Qed.

Instance proper_sstep_pairR n : Proper (eq ==> star sstep_value ==> star sstep_value) (@pair n).
Proof.
  cbv. induction 2; intros; subst; eauto.
Qed.

Instance proper_sstep_inj n b : Proper (star sstep_value ==> star sstep_value) (@inj n b).
Proof.
  cbv. induction 1; eauto.
Qed.

Instance proper_sstep_thunk n : Proper (star sstep ==> star sstep_value) (@thunk n).
Proof.
  cbv. induction 1; eauto.
Qed.

Instance proper_sstep_force n : Proper (star sstep_value ==> star sstep) (@force n).
Proof.
  cbv. induction 1; eauto.
Qed.

Instance proper_sstep_lambda n : Proper (star sstep ==> star sstep) (@lambda n).
Proof.
  cbv. induction 1; eauto.
Qed.

Instance proper_sstep_appL n : Proper (star sstep ==> eq ==> star sstep) (@app n).
Proof.
  cbv. induction 1; intros; subst; eauto.
Qed.

Instance proper_sstep_appR n : Proper (eq ==> star sstep_value ==> star sstep) (@app n).
Proof.
  cbv. induction 2; intros; subst; eauto.
Qed.

Instance proper_sstep_tupleL n : Proper (star sstep ==> eq ==> star sstep) (@tuple n).
Proof.
  cbv. induction 1; intros; subst; eauto.
Qed.

Instance proper_sstep_tupleR n : Proper (eq ==> star sstep ==> star sstep) (@tuple n).
Proof.
  cbv. induction 2; intros; subst; eauto.
Qed.

Instance proper_sstep_ret n : Proper (star sstep_value ==> star sstep) (@ret n).
Proof.
  cbv. induction 1; eauto.
Qed.

Instance proper_sstep_letinL n : Proper (star sstep ==> eq ==> star sstep) (@letin n).
Proof.
  cbv. induction 1; intros; subst; eauto.
Qed.

Instance proper_sstep_letinR n : Proper (eq ==> star sstep ==> star sstep) (@letin n).
Proof.
  cbv. induction 2; intros; subst; eauto.
Qed.

Instance proper_sstep_proj n b : Proper (star sstep ==> star sstep) (@proj n b).
Proof.
  cbv. induction 1; intros; subst; eauto.
Qed.


(* caseZ *)
Instance proper_sstep_caseZ n : Proper (star sstep_value  ==> star sstep) (@caseZ n).
Proof. cbv. induction 1; intros; subst; eauto.  Qed.

(* caseS *)
Instance proper_sstep_caseS1 n : Proper (star sstep_value ==> eq ==> eq ==> star sstep) (@caseS n).
Proof.
  cbv. induction 1; intros; subst; eauto.
Qed.

Instance proper_sstep_caseS2 n : Proper (eq ==> star sstep ==> eq ==> star sstep) (@caseS n).
Proof.
  cbv. induction 2; intros; subst; eauto.
Qed.

Instance proper_sstep_caseS3 n : Proper (eq ==> eq ==> star sstep ==> star sstep) (@caseS n).
Proof.
  cbv. induction 3; intros; subst; eauto.
Qed.


(* caseP *)
Instance proper_sstep_caseP1 n : Proper (star sstep_value ==> eq ==> star sstep) (@caseP n).
Proof.
  cbv. induction 1; intros; subst; eauto.
Qed.

Instance proper_sstep_caseP2 n : Proper (eq ==> star sstep ==> star sstep) (@caseP n).
Proof.
  cbv. induction 2; intros; subst; eauto.
Qed.

Instance star_sstep_preserves n m (sigma : fin m -> value n)  :
  Proper (star sstep ==> star sstep) (subst_comp sigma).
Proof.
  intros ? ? ?.
  induction H; eauto.
  econstructor. eapply sstep_strong_step, strong_step_subst, sstep_strong_step; eauto. eassumption.
Qed.

Instance ren_comp_proper n m (rho: fin n -> fin m) : Proper (star sstep ==> star sstep) (@ren_comp n m rho).
Proof.
  intros ? ? ?. substify. now rewrite H.
Qed.


Instance star_sstep_preserves_value n m (sigma : fin m -> value n)  :
  Proper (star sstep_value ==> star sstep_value) (subst_value sigma).
Proof.
  intros ? ? ?.
  induction H; eauto.
  econstructor. eapply sstep_strong_step_value, strong_step_value_subst, sstep_strong_step_value; eauto. eassumption.
Qed.

Instance ren_value_proper n m rho : Proper (star sstep_value ==> star sstep_value) (@ren_value n m rho).
Proof.
  intros ? ? ?. substify. now rewrite H.
Qed.

Lemma proper_subst_comp n  :
  (forall V, forall m (sigma tau : fin n -> value m), (forall x, star sstep_value (sigma x) (tau x)) ->
                                       star sstep_value (subst_value sigma V) (subst_value tau V)) /\
  (forall M, forall m (sigma tau : fin n -> value m), (forall x, star sstep_value (sigma x) (tau x)) ->
                                       star sstep (subst_comp sigma M) (subst_comp tau M)).
Proof.
  revert n. eapply mutind_val_comp; cbn; intros; eauto.
  all: try now rewrite H; eauto.
  all: try now rewrite H, H0; eauto.
  - rewrite H; eauto. intros []; cbn; eauto.
    eapply ren_value_proper. eauto.
  - rewrite H, H0; eauto. intros []; cbn; eauto.
    eapply ren_value_proper. eauto.
  - rewrite H, H0, H1; eauto.
    all: intros []; cbn; eauto; eapply ren_value_proper; eauto.
  - rewrite H, H0; eauto.
    intros [ [] | ]; cbn; eauto;
    eapply ren_value_proper; eauto.
    eapply ren_value_proper; eauto.
Qed.

(** ** Proper lemmas for plus *)

Instance plus_proper_sstep_pairL n : Proper (plus sstep_value ==> eq ==> plus sstep_value) (@pair n).
Proof.
  cbv. induction 1; intros; subst; eauto.
Qed.

Instance plus_proper_sstep_pairR n : Proper (eq ==> plus sstep_value ==> plus sstep_value) (@pair n).
Proof.
  cbv. induction 2; intros; subst; eauto.
Qed.

Instance plus_proper_sstep_inj n b : Proper (plus sstep_value ==> plus sstep_value) (@inj n b).
Proof.
  cbv. induction 1; eauto.
Qed.

Instance plus_proper_sstep_thunk n : Proper (plus sstep ==> plus sstep_value) (@thunk n).
Proof.
  cbv. induction 1; eauto.
Qed.

Instance plus_proper_sstep_force n : Proper (plus sstep_value ==> plus sstep) (@force n).
Proof.
  cbv. induction 1; eauto.
Qed.

Instance plus_proper_sstep_lambda n : Proper (plus sstep ==> plus sstep) (@lambda n).
Proof.
  cbv. induction 1; eauto.
Qed.

Instance plus_proper_sstep_appL n : Proper (plus sstep ==> eq ==> plus sstep) (@app n).
Proof.
  cbv. induction 1; intros; subst; eauto.
Qed.

Instance plus_proper_sstep_appR n : Proper (eq ==> plus sstep_value ==> plus sstep) (@app n).
Proof.
  cbv. induction 2; intros; subst; eauto.
Qed.

Instance plus_proper_sstep_tupleL n : Proper (plus sstep ==> eq ==> plus sstep) (@tuple n).
Proof.
  cbv. induction 1; intros; subst; eauto.
Qed.

Instance plus_proper_sstep_tupleR n : Proper (eq ==> plus sstep ==> plus sstep) (@tuple n).
Proof.
  cbv. induction 2; intros; subst; eauto.
Qed.

Instance plus_proper_sstep_ret n : Proper (plus sstep_value ==> plus sstep) (@ret n).
Proof.
  cbv. induction 1; eauto.
Qed.

Instance plus_proper_sstep_letinL n : Proper (plus sstep ==> eq ==> plus sstep) (@letin n).
Proof.
  cbv. induction 1; intros; subst; eauto.
Qed.

Instance plus_proper_sstep_letinR n : Proper (eq ==> plus sstep ==> plus sstep) (@letin n).
Proof.
  cbv. induction 2; intros; subst; eauto.
Qed.

Instance plus_proper_sstep_proj n b : Proper (plus sstep ==> plus sstep) (@proj n b).
Proof.
  cbv. induction 1; intros; subst; eauto.
Qed.

(* caseS *)
Instance plus_proper_sstep_caseS1 n : Proper (plus sstep_value ==> eq ==> eq ==> plus sstep) (@caseS n).
Proof.
  cbv. induction 1; intros; subst; eauto.
Qed.

Instance plus_proper_sstep_caseS2 n : Proper (eq ==> plus sstep ==> eq ==> plus sstep) (@caseS n).
Proof.
  cbv. induction 2; intros; subst; eauto.
Qed.

Instance plus_proper_sstep_caseS3 n : Proper (eq ==> eq ==> plus sstep ==> plus sstep) (@caseS n).
Proof.
  cbv. induction 3; intros; subst; eauto.
Qed.


(* caseP *)
Instance plus_proper_sstep_caseP1 n : Proper (plus sstep_value ==> eq ==> plus sstep) (@caseP n).
Proof.
  cbv. induction 1; intros; subst; eauto.
Qed.

Instance plus_proper_sstep_caseP2 n : Proper (eq ==> plus sstep ==> plus sstep) (@caseP n).
Proof.
  cbv. induction 2; intros; subst; eauto.
Qed.

Instance plus_sstep_preserves n m (sigma : fin m -> value n)  :
  Proper (plus sstep ==> plus sstep) (subst_comp sigma).
Proof.
  intros ? ? ?.
  induction H.
  - econstructor. eapply sstep_strong_step, strong_step_subst, sstep_strong_step; eauto.
  - econstructor 2. eapply sstep_strong_step, strong_step_subst, sstep_strong_step; eauto. eassumption.
Qed.

Instance pstep_subrel n : subrelation (@pstep n) (@sstep n).
Proof.
  cbv. intros. eauto.
Qed.

(** ** Inversion lemmas *)

Lemma stepv_var_inv n (i : fin n) (v : value n) :
  ~var_value i ⇒ᵥ v.
Proof.
  intros st. inv st. destruct K; try discriminate; contradiction.
Qed.

Lemma stepv_u_inv n (v : value n) :
  ~u ⇒ᵥ v.
Proof.
  intros st. inv st. destruct K; try discriminate; eauto.
Qed.

Lemma stepv_pair_inv n (P : value n -> Prop) (v1 v2 : value n) :
  (forall v', v1 ⇒ᵥ v' -> P (pair v' v2)) ->
  (forall v', v2 ⇒ᵥ v' -> P (pair v1 v')) ->
  (forall v', pair v1 v2 ⇒ᵥ v' -> P v').
Proof.
  intros H1 H2 v' st. inv st. destruct K; try discriminate; try contradiction;
    cbn in *; injection H; intros E1 E2; subst; clear H.
  now apply H1. now apply H2.
Qed.

Lemma stepv_inj_inv n (P : value n -> Prop) b (v : value n) :
  (forall v', v ⇒ᵥ v' -> P (inj b v')) ->
  (forall v', inj b v ⇒ᵥ v' -> P v').
Proof.
  intros H v' st. inv st. destruct K; try discriminate; try contradiction; cbn in *.
  injection H0. intros E1 E2. subst. apply H. constructor. exact H1.
Qed.

Lemma stepv_thunk_inv n (P : value n -> Prop) (c : comp n) :
  (forall c', c ⇒ c' -> P (thunk c')) ->
  (forall v', thunk c ⇒ᵥ v' -> P v').
Proof.
  intros H v' st. inv st. destruct K; try discriminate; try contradiction; cbn in *.
  injection H0. intros E. subst. apply H. constructor. assumption.
Qed.

Lemma step_cu_inv n (c : comp n) :
  ~cu ⇒ c.
Proof.
  intros st. inv st. destruct K; try discriminate; try contradiction.
  cbn in H. subst. inv H0.
Qed.

Lemma step_force_inv n (P : comp n -> Prop) (v : value n) :
  (forall c, v = thunk c -> P c) ->
  (forall v', v ⇒ᵥ v' -> P (force v')) ->
  (forall c, force v ⇒ c -> P c).
Proof.
  intros H1 H2 c st. inv st. destruct K; try discriminate; cbn in *; subst; cbn.
  - inv H0. now apply H1.
  - injection H. intros; subst. apply H2. constructor. assumption.
Qed.

Lemma step_lambda_inv n (P : comp n -> Prop) (c : comp (S n)) :
  (forall c', c ⇒ c' -> P (lambda c')) ->
  (forall c', lambda c ⇒ c' -> P c').
Proof.
  intros H c' st. inv st. destruct K; try discriminate; cbn in *; subst; cbn.
  - now inv H1.
  - injection H0. intros; subst. apply H. constructor. assumption.
Qed.

Lemma step_app_inv n (P : comp n -> Prop) (c : comp n) (v : value n) :
  (forall (b : comp (S n)), c = lambda b -> P b[v..]) ->
  (forall c', c ⇒ c' -> P (app c' v)) ->
  (forall v', v ⇒ᵥ v' -> P (app c v')) ->
  (forall c', app c v ⇒ c' -> P c').
Proof.
  intros H1 H2 H3 c' st. inv st. destruct K; try discriminate; cbn in *; subst; cbn.
  - inv H0. now apply H1.
  - injection H; intros; subst. apply H2. constructor. assumption.
  - injection H; intros; subst. apply H3. constructor. assumption.
Qed.

Lemma step_tuple_inv n (P : comp n -> Prop) (c1 c2 : comp n) :
  (forall c', c1 ⇒ c' -> P (tuple c' c2)) ->
  (forall c', c2 ⇒ c' -> P (tuple c1 c')) ->
  (forall c', tuple c1 c2 ⇒ c' -> P c').
Proof.
  intros H1 H2 c' st. inv st. destruct K; try discriminate; cbn in *; subst; cbn.
  - now inv H0.
  - injection H; intros; subst. apply H1. constructor. assumption.
  - injection H; intros; subst. apply H2. constructor. assumption.
Qed.

Lemma step_ret_inv n (P : comp n -> Prop) (v : value n) :
  (forall v', v ⇒ᵥ v' -> P (ret v')) ->
  (forall c, ret v ⇒ c -> P c).
Proof.
  intros H c st. inv st; destruct K; try discriminate.
  - cbn in *. subst. inv H1.
  - cbn in *. injection H0; intros E; subst. apply H. constructor. exact H1.
Qed.

Lemma step_letin_inv n (P : comp n -> Prop) (c1 : comp n) c2 :
  (forall v, c1 = ret v -> P (c2[v..])) ->
  (forall c', c1 ⇒ c' -> P ($ <- c'; c2)) ->
  (forall c', c2 ⇒ c' -> P ($ <- c1; c')) ->
  (forall c', $ <- c1; c2 ⇒ c' -> P c').
Proof.
  intros H1 H2 H3 c' st. inv st; destruct K; try discriminate; cbn in *.
  - subst. inv H0. now apply H1.
  - injection H. intros E1 E2. subst. apply H2. constructor. assumption.
  - injection H. intros E1 E2. subst. apply H3. constructor. assumption.
Qed.

Lemma step_proj_inv n (P : comp n -> Prop) (b : bool) (c : comp n) :
  (forall c1 c2, c = tuple c1 c2 -> P (if b then c1 else c2)) ->
  (forall c', c ⇒ c' -> P (proj b c')) ->
  (forall c', proj b c ⇒ c' -> P c').
Proof.
  intros H1 H2 c' st. inv st; destruct K; try discriminate; cbn in *.
  - subst. inv H0. now apply H1.
  - injection H; intros; subst. apply H2. constructor. assumption.
Qed.

Lemma step_caseZ_inv n (P : comp n -> Prop) (v : value n) :
  (forall v', v ⇒ᵥ v' -> P (caseZ v')) ->
  (forall c, caseZ v ⇒ c -> P c).
Proof.
  intros H c st. inv st. destruct K; try discriminate; cbn in *.
  - subst. inv H1.
  - injection H0. intros E; subst. apply H. constructor. assumption.
Qed.

Lemma step_caseS_inv n (P : comp n -> Prop) v c1 c2 :
  (forall b v', v = inj b v' -> P ((if b then c1 else c2)[v'..])) ->
  (forall v', v ⇒ᵥ v' -> P (caseS v' c1 c2)) ->
  (forall c', c1 ⇒ c' -> P (caseS v c' c2)) ->
  (forall c', c2 ⇒ c' -> P (caseS v c1 c')) ->
  (forall d, caseS v c1 c2 ⇒ d -> P d).
Proof.
  intros H1 H2 H3 H4 d st. inv st. destruct K; try discriminate; cbn in *.
  - subst. inv H0. now apply H1.
  - injection H. intros; subst. apply H2. constructor. assumption.
  - injection H. intros; subst. apply H3. constructor. assumption.
  - injection H. intros; subst. apply H4. constructor. assumption.
Qed.

Lemma step_caseP_inv n (P : comp n -> Prop) (v : value n) c :
  (forall v1 v2, v = pair v1 v2 -> P (c[v2, v1..])) ->
  (forall v', v ⇒ᵥ v' -> P (caseP v' c)) ->
  (forall c', c ⇒ c' -> P (caseP v c')) ->
  (forall d, caseP v c ⇒ d -> P d).
Proof.
  intros H1 H2 H3 d st. inv st; destruct K; try discriminate; cbn in *; subst.
  - inv H0. now apply H1.
  - injection H. intros E1 E2; subst. apply H2. constructor. assumption.
  - injection H. intros E1 E2; subst. apply H3. constructor. assumption.
Qed.

Lemma step_ren_comp_inv m :
  (forall D C', D ↪ C' -> forall n C (rho : fin n -> fin m), D = C⟨rho⟩ -> exists C'', C ↪ C'' /\ C' = C''⟨rho⟩) /\
  (forall V1 V', sstep_value V1 V' -> forall n V (rho : fin n -> fin m), V1 = V⟨rho⟩ -> exists V'', sstep_value V V'' /\ V' = V''⟨rho⟩).
Proof with intros; asimpl; f_equal; fext; now intros [].
  revert m. eapply mutind_sstep; cbn; intros.
  all: try now (destruct V; inv H0; edestruct H as (? & ? & ->); eauto).
  all: try now (destruct C; inv H0; edestruct H as (? & ? & ->); eauto).
  subst. inv p.
  - destruct C; inv H0; destruct v; inv H1; eauto.
  - destruct C; inv H. destruct C; inv H1. eexists; split; eauto.
    now asimpl.
  - destruct C; inv H. destruct C; inv H2. eexists; split; eauto.
    now destruct b0.
  - destruct C; inv H. destruct C1; inv H1. eexists; split; eauto.
    now asimpl.
  - destruct C; inv H. destruct v0; inv H1. eexists; split; eauto.
    destruct b0; now asimpl.
  - destruct C; inv H. destruct v; inv H1. eexists; split; eauto.
    now asimpl.
Qed.

Lemma ret_star_inv n (V : value n) C :
  ret V ↪* C -> exists V', C = ret V' /\ star sstep_value V V'.
Proof.
  remember (ret V) as C'. intros H. revert V HeqC'; induction H; intros; subst.
  - eauto.
  - inv H.
    + edestruct IHstar as (? & -> &?); eauto.
    + inv H1.
Qed.

Lemma inj_star_inv n (V : value n) b C :
  star sstep_value (inj b V) C -> exists V', C = inj b V' /\ star sstep_value V V'.
Proof.
  remember (inj b V) as C'. intros H. revert V HeqC'; induction H; intros; subst.
  - eauto.
  - inv H. edestruct IHstar as (? & -> &?); eauto.
Qed.

Lemma thunk_star_inv n (V : value n) C :
  star sstep_value (thunk C) V -> exists C', V = thunk C' /\ star sstep C C'.
Proof.
  remember (thunk C) as V'. intros H. revert C HeqV'; induction H; intros; subst.
  - eauto.
  - inv H. edestruct IHstar as (? & -> &?); eauto.
Qed.
