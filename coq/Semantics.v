(**
  Master Thesis, Page 10
  This file contains operational semantics, context semantics and bigstep semantics as well as the definition of normal forms, normality and
  evaluation
*)

Set Implicit Arguments.
Require Import Psatz Logic List Classes.Morphisms.
Import List Notations.

Require Export CBPV.Terms CBPV.Base CBPV.AbstractReductionSystems.
Import CommaNotation.


(** * Semantics *)

Reserved Notation "A '≽' B" (at level 80).
Reserved Notation "A '⇝' B" (at level 80).

(** ** Primitive Reduction  *)
Inductive pstep {n: nat}: comp n -> comp n -> Prop :=
| pstepForce (c: comp n):
    <{c}>! ≽ c
| pstepApp (c: comp (S n)) (c': comp n) v:
    subst_comp (v..) c = c' -> (lambda c) v ≽ c'
| pstepProj (b: bool) (c c1 c2: comp n) :
    (c = if b then c1 else c2) -> proj b (tuple c1 c2) ≽ c
| pstepLetin (c: comp (S n)) c' v:
    subst_comp (v..) c = c' -> $ <- (ret v); c ≽ c'
| pstepCaseS v (b: bool) c (c1 c2: comp (S n)):
    subst_comp (v..) (if b then c1 else c2) = c -> caseS (inj b v) c1 c2 ≽ c
| pstepCaseP v1 v2 (c: comp (S (S n))) c':
    subst_comp (v2,v1..) c = c' -> caseP (pair v1 v2) c ≽ c'
where "A '≽' B" := (pstep A B).


(** ** Operational Semantics *)
Inductive step {n: nat}: comp n -> comp n -> Prop :=
| stepPrimitive (c c': comp n) : c ≽ c' -> c > c'
| stepApp (c c': comp n) v: c > c' -> c v > c' v
| stepProj (c c': comp n)  b: c > c' -> proj b c > proj b c'
| stepLetin (c1 c1': comp n) c2: c1 > c1' -> $ <- c1; c2 > $ <- c1'; c2
where "A > B" := (step A B).

Hint Constructors pstep step.

Notation "A >* B" := (star step A B) (at level 60).
Notation "A >+ B" := (plus step A B) (at level 60).


(** ** Context Semantics *)
(** Evaluation context *)
Inductive ectx {n: nat}: Type :=
| ectxHole : ectx
| ectxApp : ectx -> value n -> ectx
| ectxProj : bool -> ectx -> ectx
| ectxLetin : ectx -> comp (S n) -> ectx.

(** Context filling *)
Fixpoint fill {n: nat} (K: ectx) (c: comp n) :=
  match K with
  | ectxHole => c
  | ectxApp K v => (fill K c) v
  | ectxProj b K => proj b (fill K c)
  | ectxLetin K c' => letin (fill K c) c'
  end.

(** Context Semantics *)
Inductive cstep {n: nat}: comp n -> comp n -> Prop :=
| contextStep C c c' (c'' c''': comp n):
    c ≽ c' -> fill C c = c'' -> fill C c' = c''' -> c'' ⇝ c'''
where "A '⇝' B" := (cstep A B).

(** ** Bigstep Semantics *)
Reserved Notation "A ▷ B" (at level 80).

Inductive bigstep {n: nat}: comp n -> comp n -> Prop :=
| bigstepCu: @cu n ▷ cu
| bigstepReturn (v: value n) : ret v ▷ ret v
| bigstepLambda (c: comp (S n)) : lambda c ▷ lambda c
| bigstepTuple (c1 c2: comp n): tuple c1 c2 ▷ tuple c1 c2
| bigstepForce (c c': comp n): c ▷ c' -> <{c}>! ▷ c'
| bigstepApp (c c'': comp n) c' v: c ▷ lambda c' -> subst_comp (v..) c' ▷ c'' -> c v ▷ c''
| bigstepProj c c' (c1 c2: comp n) (b: bool):
    c ▷ tuple c1 c2 -> (if b then c1 else c2) ▷ c' -> proj b c ▷ c'
| bigstepLetin c1 (v: value n) c2 c: c1 ▷ ret v -> subst_comp (v..) c2 ▷ c -> $ <- c1; c2 ▷ c
| bigstepCaseS c c1 c2 (b: bool) (v: value n):
  subst_comp (v..) (if b then c1 else c2) ▷ c -> caseS (inj b v) c1 c2 ▷ c
| bigstepCaseP c c' (v1 v2: value n):
    subst_comp (v2,v1..) c ▷ c' -> caseP (pair v1 v2) c ▷ c'
where "A ▷ B" := (bigstep A B).

Hint Constructors bigstep.

(** ** Normal Form *)
Inductive nf {n: nat}: comp n -> Prop :=
| nfCu: nf cu
| nfLam c: nf (lambda c)
| nfTup c1 c2: nf (tuple c1 c2)
| nfRet v: nf (ret v).

Hint Constructors nf.


(** ** Evaluation *)
Definition eval {n: nat} (c c': comp n) := c >* c' /\ nf c'.
Hint Transparent  eval.

(** ** Properties *)

Instance proper_letin {n: nat}: Proper (star step ++> eq ++> star step) (@letin n).
Proof.
  intros c1 c1' H ? c2 ->.
  induction H; eauto.
Qed.


Instance proper_app {n: nat}: Proper (star step ++> eq ++> star step) (@app n).
Proof.
  intros c1 c1' H ? c2 ->.
  induction H; eauto.
Qed.


Instance proper_proj {n: nat}: Proper (eq ++> star step ++> star step) (@proj n).
Proof.
  intros ? i -> c c' H.
  induction H; eauto.
Qed.


Hint Resolve proper_letin proper_app proper_proj.

(** Reduction tactic for beta reduction step *)
Ltac reduce := econstructor 2; [ solve [eauto] | cbn ].



(** Substitution Primitive Step *)
Lemma pstep_subst m n (C1 C2: comp m) (f: fin m -> value n):
  C1 ≽ C2 -> subst_comp f C1 ≽ subst_comp f C2.
Proof.
  intros H; inv H; cbn; constructor; try destruct b; asimpl; reflexivity.
Qed.

(** The operational semantic we defined is functional *)
Lemma step_functional {n: nat} (c1 c2 c2': comp n) : c1 > c2 -> c1 > c2' -> c2 = c2'.
Proof.
  induction 1 in c2' |-*; intros H1; inv H1.
  1: inv H; inv H0; reflexivity.
  all: try (inv H; inv H0; inv H).
  all: try (inv H0; inv H; inv H0).
  all: firstorder congruence.
Qed.


Lemma confluence_steps (n: nat):
  confluent (@step n).
Proof.
  apply confluent_semi.
  intros x y z H1 H2.
  destruct H2.
  - exists y; eauto.
  - exists y0; eauto. specialize (step_functional H1 H) as ->; eauto.
Qed.

Hint Resolve confluence_steps.




(** The operational semantic and the context semantic agree *)
Lemma step_equiv {n: nat} (c c': comp n): c > c' <->  c ⇝ c'.
Proof.
  split.
  - induction 1.
    + eapply (contextStep ectxHole); eauto.
    + inv IHstep; eapply (contextStep (ectxApp C v)); eauto.
    + inv IHstep; eapply (contextStep (ectxProj b C)); eauto.
    + inv IHstep; eapply (contextStep (ectxLetin C c2)); eauto.
  - destruct 1; subst c''; subst c'''.
    induction C in c, c', H |-*; cbn; eauto.
Qed.



(** The bigstep semantic is sound w.r.t the operational semantic *)
Lemma bigstep_soundness {n: nat} (c c': comp n): c ▷ c' -> c >* c'.
Proof.
  induction 1; eauto.
  - rewrite IHbigstep1; reduce; rewrite IHbigstep2; reflexivity.
  - rewrite IHbigstep1; reduce; assumption.
  - rewrite IHbigstep1; reduce; rewrite IHbigstep2; reflexivity.
Qed.


(** The bigstep semantic is closed under expasion by the operational semantics *)
Lemma bigstep_primitive_cons {n: nat} (c c' c'': comp n): c ≽ c' -> c' ▷ c'' -> c ▷ c''.
Proof.
  intros H; inv H; intros H; econstructor; eauto.
Qed.


Lemma bigstep_cons {n: nat} (c c' c'': comp n): c > c' -> c' ▷ c'' -> c ▷ c''.
Proof.
  induction 1 in c'' |-*.
  1: now apply bigstep_primitive_cons.
  all: intros H1; inv H1; eauto.
Qed.

Lemma bigstep_prepend {n: nat} (c c' c'': comp n): c >* c' -> c' ▷ c'' -> c ▷ c''.
Proof.
  induction 1 in c'' |-*; intros; eauto using bigstep_cons.
Qed.

Hint Resolve bigstep_cons bigstep_prepend.



(** The bigstep semantic is functional *)
Lemma bigstep_functional {n: nat} (c1 c2 c2': comp n) : c1 ▷ c2 -> c1 ▷ c2' -> c2 = c2'.
Proof.
  induction 1 in c2' |-*; intros H1; inv H1; eauto.
  all: specialize (IHbigstep1 _ H4); injection IHbigstep1; repeat intros ->; apply IHbigstep2; eauto.
Qed.

(** Normal forms are normal *)
Lemma nf_normal {n: nat} (c: comp n) : nf c -> Normal step c.
Proof. intros [] c' H; inv H; inv H0. Qed.

(** Terms bigstep evaluate to normal forms *)
Lemma bigstep_normal {n: nat} (c c': comp n): c ▷ c' -> nf c'.
Proof.
  induction 1; eauto.
Qed.

(** Normal forms bigstep evaluate *)
Lemma normal_bigstep {n: nat} (c: comp n): nf c -> c ▷ c.
Proof.
  intros []; eauto.
Qed.

(** Bigstep evaluation is evaluation *)
Lemma eval_bigstep {n: nat} (c c': comp n): eval c c' <-> c ▷ c'.
Proof.
  split.
  - intros [H1 H2]; induction H1; eauto using normal_bigstep, bigstep_cons.
  - intros H; split; eauto using bigstep_normal, bigstep_soundness.
Qed.



Lemma ectx_decompose {n: nat} (K : @ectx n) c c':
  fill K c ▷ c' -> exists c'', c ▷ c'' /\ fill K c'' ▷ c'.
Proof.
  induction K in c, c' |-*; cbn; intros H.
  1: eexists; intuition; eauto; induction H; eauto.
  all: inv H; edestruct IHK; eauto; intuition.
  all: eexists; intuition; eauto.
Qed.

Lemma ectx_compose {n: nat} (K : @ectx n) c c' c'':
  c ▷ c' -> fill K c' ▷ c'' -> fill K c ▷ c''.
Proof.
  intros H1 H2.
  eapply eval_bigstep in H1.
  eapply eval_bigstep in H2.
  eapply eval_bigstep.
  unfold eval in *; intuition.
  rewrite <-H1.
  clear H0 H3 H1; induction K; cbn in *; eauto;
    now rewrite IHK.
Qed.



Lemma eval_evaluates n (c c': comp n):
  evaluates step c c' -> nf c' -> eval c c'.
Proof.
  split; eauto. destruct H; eauto. 
Qed.

Lemma steps_nf_eval n (c c': comp n):
    c >* c' -> nf c' ->  eval c c'.
Proof.
  split; eauto.
Qed.


Lemma steps_bigstep n (c c': comp n):
    c >* c' -> nf c' -> c ▷ c'.
Proof.
  intros; eapply eval_bigstep, steps_nf_eval; eauto.
Qed.


(** Star Steps are functional if the term steps to a term in normal form *)
Lemma starstep_functional_nf {n: nat} (c c1 c2: comp n):
   c >* c1 -> c >* c2 -> nf c1 -> nf c2 -> c1 = c2.
Proof.
  intros; eapply bigstep_functional; eapply eval_bigstep; unfold eval; split; eauto.
Qed.


(** Strong Normaliation is closed under expansion *)
Lemma normalizing_extension {n: nat} (c c': comp n):
  c >* c' -> SN step c' -> SN step c.
Proof.
  induction 1.
  - now intros.
  - intros H1 % IHstar. constructor. intros x'' H2.
    enough (x' = x'') as -> by assumption.
    eapply step_functional; eassumption.
Qed.

(** Bigstep Semantics implies termination *)
Lemma bigstep_sn' {n: nat} (c c': comp n) : c ▷ c' -> SN step c'.
Proof.
  intros H % eval_bigstep; destruct H; now apply Normal_SN, nf_normal.
Qed.


Lemma bigstep_sn {n: nat} (c c': comp n) : c ▷ c' -> SN step c.
Proof.
  intros H; eapply normalizing_extension; [| eapply bigstep_sn'; eassumption].
  enough (eval c c') by firstorder. now apply eval_bigstep.
Qed.
