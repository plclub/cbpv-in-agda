(** Master Thesis, Page 10 This file contains operational semantics, context
  semantics and bigstep semantics as well as the definition of normal forms,
  normality and evaluation *)

Set Implicit Arguments.
Require Import Psatz Logic List Classes.Morphisms.
Import List Notations.

Require Export CBPV.Terms CBPV.Base.
Import CommaNotation.

Ltac esimpl := autorewrite with core.

(** * Semantics *)

Reserved Notation "A '≽' B '#' phi" (at level 80).
Reserved Notation "A '⇝' B '#' phi" (at level 80).
Reserved Notation "A '≻' B '#' phi" (at level 80).

(** ** Primitive Reduction  *)
Inductive pstep {n: nat}: comp n -> comp n -> effect -> Prop :=
| pstepForce (c: comp n):
    <{c}>! ≽ c # pure
| pstepApp (c: comp (S n)) (c': comp n) v:
    subst_comp (v..) c = c' -> (lambda c) v ≽ c' # pure
| pstepProj (b: bool) (c c1 c2: comp n) :
    (c = if b then c1 else c2) -> proj b (tuple c1 c2) ≽ c # pure
| pstepLetin (c: comp (S n)) c' v:
    subst_comp (v..) c = c' -> $ <- (ret v); c ≽ c' # pure
| pstepCaseS v (b: bool) c (c1 c2: comp (S n)):
    subst_comp (v..) (if b then c1 else c2) = c -> caseS (inj b v) c1 c2 ≽ c # pure
| pstepCaseP v1 v2 (c: comp (S (S n))) c':
    subst_comp (v2,v1..) c = c' -> caseP (pair v1 v2) c ≽ c' # pure
| pstepTock :  tock ≽ ret u # tick
where "A '≽' B '#' phi" := (pstep A B phi).


(** ** Operational Semantics *)
Inductive step {n: nat} : comp n -> comp n -> effect -> Prop :=
| stepPrimitive (c c': comp n) phi : c ≽ c' # phi -> (c ≻ c' # phi)
| stepApp (c c': comp n) v phi  : c ≻ c' # phi -> c v ≻ c' v # phi
| stepProj (c c': comp n)  b phi : c ≻ c' # phi -> proj b c ≻ proj b c' # phi
| stepLetin (c1 c1': comp n) c2 phi: 
  c1 ≻ c1' # phi -> $ <- c1; c2 ≻ $ <- c1'; c2 # phi
where "A '≻' B '#' phi" := (step A B phi).

#[export] Hint Constructors pstep step : core.

Inductive eff_star (X : Type) (R : X -> X -> effect -> Prop) : X -> X -> effect -> Prop :=
  | eff_starRefl : forall x, eff_star R x x pure
  | eff_starStep : forall x x' y p1 p2 p, 
      R x x' p1 
        -> eff_star R x' y p2 
        -> add p1 p2 = p
        -> eff_star R x y p.

Inductive eff_plus (X : Type) (R : X -> X -> effect -> Prop) : X -> X -> effect -> Prop :=
    eff_plusSingle : forall x y phi, R x y phi -> eff_plus R x y phi 
  | eff_plusStep : forall x x' y p1 p2 p, 
      R x x' p1 
      -> eff_plus R x' y p2 
      -> add p1 p2 = p
      -> eff_plus R x y p.

#[export] Hint Constructors eff_star eff_plus : core.

Notation "A >* B # phi " := (eff_star step A B phi) (at level 60).
Notation "A >+ B # phi" := (eff_plus step A B phi) (at level 60).

Lemma eff_starTrans  (X : Type) (R : X -> X -> effect -> Prop) : 
  forall x1 x2 p1, 
    eff_star R x1 x2 p1 
    -> forall x3 p2 p, eff_star R x2 x3 p2 
    -> add p1 p2 = p 
    -> eff_star R x1 x3 p.
Proof.
  induction 1; intros; esimpl; subst; eauto.
  esimpl. auto.
Qed.

#[export] Hint Resolve eff_starTrans : core.

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
Inductive cstep {n: nat}: comp n -> comp n -> effect -> Prop :=
| contextStep C c c' (c'' c''': comp n) phi :
    (c ≽ c' # phi) -> fill C c = c'' -> fill C c' = c''' -> (c'' ⇝ c''' # phi)
where "A '⇝' B '#' phi" := (cstep A B phi).

(** ** Bigstep Semantics *)
Reserved Notation "A ▷ B # phi" (at level 80).

Inductive bigstep {n: nat}: comp n -> comp n -> effect -> Prop :=
| bigstepCu: @cu n ▷ cu # pure
| bigstepReturn (v: value n) : ret v ▷ ret v # pure 
| bigstepLambda (c: comp (S n)) : lambda c ▷ lambda c # pure
| bigstepTuple (c1 c2: comp n): tuple c1 c2 ▷ tuple c1 c2 # pure
| bigstepForce (c c': comp n) phi: c ▷ c' # phi -> <{c}>! ▷ c' # phi
| bigstepApp (c c'': comp n) c' v phi1 phi2  phi: 
  c ▷ lambda c' # phi1 
  -> subst_comp (v..) c' ▷ c'' # phi2
  -> add phi1 phi2 = phi
  -> c v ▷ c'' # phi
| bigstepProj c c' (c1 c2: comp n) (b: bool) phi1 phi2 phi:
    c ▷ tuple c1 c2 # phi1 
    -> (if b then c1 else c2) ▷ c' # phi2 
    -> add phi1 phi2 = phi
    -> proj b c ▷ c' # phi
| bigstepLetin c1 (v: value n) c2 c phi1 phi2 phi: 
  c1 ▷ ret v #phi1 
  -> subst_comp (v..) c2 ▷ c # phi2
  -> add phi1 phi2 = phi
  -> $ <- c1; c2 ▷ c # phi
| bigstepCaseS c c1 c2 (b: bool) (v: value n) phi:
  subst_comp (v..) (if b then c1 else c2) ▷ c # phi
  -> caseS (inj b v) c1 c2 ▷ c # phi
| bigstepCaseP c c' (v1 v2: value n) phi:
    subst_comp (v2,v1..) c ▷ c' # phi
    -> caseP (pair v1 v2) c ▷ c' # phi
| bigstepTock :
    tock ▷ ret u # tick
where "A ▷ B  # phi" := (bigstep A B phi).

#[export] Hint Constructors bigstep : core.

(** ** Normal Form *)
Inductive nf {n: nat}: comp n -> Prop :=
| nfCu: nf cu
| nfLam c: nf (lambda c)
| nfTup c1 c2: nf (tuple c1 c2)
| nfRet v: nf (ret v).

#[export] Hint Constructors nf : core.


(** ** Evaluation *)
Definition eval {n: nat} (c c': comp n) phi := c >* c' # phi /\ nf c'.
#[export] Hint Transparent eval : core.

(** ** Properties *)

(*
Definition eff_respectful :=
  fun {A:Type}
    (R : A -> A -> effect -> Prop) (R' : A -> A -> effect -> Prop) (f g : A -> A)
  => (forall (x y : A) phi, R x y phi -> R' (f x) (g y) phi).

Notation "R +++> R'" := (eff_respectful R R') (at level 55).

Instance proper_letin {n: nat}{phi: effect} : Proper (eff_star step +++> (fun c1 c2 phi => eq c1 c2) +++> eff_star step) (@letin n).
Proof.
  intros c1 c1' H ? c2 ->. unfold eff_star_step.
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
*)

Lemma step_letin {n:nat} (c1 c1' : comp n) (c2 : comp (S n)) phi : 
  eff_star step c1 c1' phi ->
  eff_star step (letin c1 c2) (letin c1' c2) phi.
Proof.
  induction 1; eauto. 
Qed.


Lemma step_app {n:nat} (c1 c1' : comp n) (v : value n) phi : 
  eff_star step c1 c1' phi ->
  eff_star step (app c1 v) (app c1' v) phi.
Proof.
  induction 1; eauto. 
Qed.

Lemma step_proj {n:nat} (c1 c1' : comp n) b phi : 
  eff_star step c1 c1' phi ->
  eff_star step (proj b c1) (proj b c1') phi.
Proof.
  induction 1; eauto. 
Qed.


#[export] Hint Resolve step_letin step_app step_proj : core.
#[export] Hint Rewrite @step_letin @step_app @step_proj : core.


(** Reduction tactic for beta reduction step *)
Ltac reduce := econstructor 2; [ solve [eauto] | cbn ].



(** Substitution Primitive Step *)
Lemma pstep_subst m n (C1 C2: comp m) (f: fin m -> value n) phi:
  C1 ≽ C2 # phi -> subst_comp f C1 ≽ subst_comp f C2 # phi.
Proof.
  intros H; inv H; cbn; constructor; try destruct b; asimpl; reflexivity.
Qed.

(** The operational semantic we defined is functional *)
Lemma step_functional {n: nat} (c1 c2 c2': comp n) phi1 phi2 : 
  c1 ≻ c2 # phi1 -> c1 ≻ c2' # phi2  -> c2 = c2'.
Proof.
  induction 1 in c2' |-*; intros H1; inv H1.
  1: inv H; inv H0; reflexivity.
  all: try (inv H; inv H0; inv H).
  all: try (inv H0; inv H; inv H0).
  all: firstorder congruence.
Qed.

Lemma step_functional_eff {n: nat} (c1 c2 c2': comp n) phi1 phi2 : 
  c1 ≻ c2 # phi1 -> c1 ≻ c2' # phi2  -> phi1 = phi2.
Proof.
  induction 1 in c2' |-*; intros H1; inv H1.
  1: inv H; inv H0; reflexivity.
  all: try (inv H; inv H0; inv H).
  all: try (inv H0; inv H; inv H0).
  all: firstorder congruence.
Qed.


(*
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
*)



(** The operational semantic and the context semantic agree *)
Lemma step_equiv {n: nat} (c c': comp n) phi : c ≻ c' # phi <->  c ⇝ c' # phi.
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
Lemma bigstep_soundness {n: nat} (c c': comp n) phi: c ▷ c' # phi -> c >* c' # phi.
Proof.
  induction 1; eauto.
  - apply step_app with (v:=v) in IHbigstep1.
    eapply eff_starTrans; eauto.
  - apply step_proj with (b := b) in IHbigstep1.
    eapply eff_starTrans; eauto.
  - apply step_letin with (c2 := c2) in IHbigstep1.
    eauto.
Qed.


(** The bigstep semantic is closed under expansion by the operational semantics *)
Lemma bigstep_primitive_cons {n: nat} (c c' c'': comp n) phi1 phi2: 
  c ≽ c' # phi1
  -> c' ▷ c'' # phi2 
  -> c ▷ c''  # add phi1 phi2.
Proof.
  intros H; inv H; try intros H; esimpl; try econstructor; eauto. 
  inv H; esimpl; eauto.
Qed.


Lemma bigstep_cons {n: nat} (c c' c'': comp n) phi1 phi2 : 
  c ≻ c' # phi1 -> c' ▷ c'' # phi2 -> c ▷ c'' # add phi1 phi2.
Proof.
  induction 1 in c'', phi2 |-*.
  1: now apply bigstep_primitive_cons.
  all: intros H1; inv H1; esimpl; eauto.
Qed.

Lemma bigstep_prepend {n: nat} (c c' c'': comp n) phi1 phi2:  
  c >* c' # phi1 -> c' ▷ c'' # phi2 -> c ▷ c'' # (add phi1 phi2).
Proof.
  induction 1 in c'', phi2 |-*; intros; subst; esimpl; eauto using bigstep_cons.
Qed.

#[export] Hint Resolve bigstep_cons bigstep_prepend : core.



(** The bigstep semantic is functional *)
Lemma bigstep_functional {n: nat} (c1 c2 c2': comp n) phi1 phi2 : 
  c1 ▷ c2 # phi1 -> c1 ▷ c2' # phi2 -> c2 = c2'.
Proof.
  induction 1 in c2' , phi2 |-*; intros h1; inv h1; eauto.
  all: specialize (IHbigstep1 _ _ H4); injection IHbigstep1; repeat intros ->; eapply IHbigstep2; eauto.
Qed.

Definition eff_Normal {X : Type} (R : X -> X -> effect -> Prop) (x : X) :=
  forall (y : X) phi,  ~ R x y phi.

(** Normal forms are normal *)
Lemma nf_normal {n: nat} (c: comp n) : nf c -> eff_Normal step c.
Proof. intros [] c' eff H; inv H; inv H0. Qed.

(** Terms bigstep evaluate to normal forms *)
Lemma bigstep_normal {n: nat} (c c': comp n) eff : c ▷ c' # eff -> nf c'.
Proof.
  induction 1; eauto.
Qed.

(** Normal forms bigstep evaluate *)
Lemma normal_bigstep {n: nat} (c: comp n): nf c -> c ▷ c # pure.
Proof.
  intros []; eauto.
Qed.


(** Bigstep evaluation is evaluation *)
Lemma eval_bigstep {n: nat} (c c': comp n) phi : eval c c' phi<-> c ▷ c' # phi.
Proof.
  split.
  - intros [H1 H2]; induction H1; subst; eauto using normal_bigstep, bigstep_cons.
  - intros H; split; eauto using bigstep_normal, bigstep_soundness.
Qed.


Lemma ectx_decompose {n: nat} (K : @ectx n) c c' phi:
  fill K c ▷ c' # phi -> exists c'' phi1 phi2, c ▷ c'' # phi1  /\ fill K c'' ▷ c' # phi2 /\ phi = add phi1 phi2.
Proof.
  induction K in c, c', phi |-*; cbn; intros H.
  1: { exists c'. exists phi. exists pure. repeat split; eauto using bigstep_normal, normal_bigstep. }
  all: inv H; edestruct IHK as [c'' [phi1' [phi2' h]]]; eauto; intuition.
  all: eexists; eexists; eexists.
  split. eauto. split. eauto. subst. esimpl. reflexivity.
  split. eauto. split. eauto. subst. esimpl. reflexivity.
  split. eauto. split. eauto. subst. esimpl. reflexivity.
Qed.

Lemma ectx_compose {n: nat} (K : @ectx n) c c' c'' phi1 phi2:
  c ▷ c' # phi1 -> fill K c' ▷ c'' # phi2  -> fill K c ▷ c'' # add phi1 phi2.
Proof.
  intros H1 H2.
  eapply eval_bigstep in H1.
  eapply eval_bigstep in H2.
  eapply eval_bigstep.
  unfold eval in *; intuition.
  eapply eff_starTrans with (x2 := fill K c'); eauto.
  clear H0 H3 H1; induction K; cbn in *; eauto;
    now rewrite IHK.
Qed.

Definition eff_evaluates := fun (X : Type) (R : X -> X -> effect -> Prop) (s t : X) phi => 
                             eff_star R s t phi /\ eff_Normal R t.

Lemma eval_evaluates n (c c': comp n) phi:
  eff_evaluates step c c' phi -> nf c' -> eval c c' phi.
Proof.
  split; eauto. destruct H; eauto. 
Qed.

Lemma steps_nf_eval n (c c': comp n) phi:
    c >* c' # phi -> nf c' ->  eval c c' phi.
Proof.
  split; eauto.
Qed.


Lemma steps_bigstep n (c c': comp n) phi:
    c >* c' # phi -> nf c' -> c ▷ c' # phi.
Proof.
  intros; eapply eval_bigstep, steps_nf_eval; eauto.
Qed.


(** Star Steps are functional if the term steps to a term in normal form *)
Lemma starstep_functional_nf {n: nat} (c c1 c2: comp n) phi1 phi2 :
   c >* c1 # phi1 -> c >* c2 # phi2 -> nf c1 -> nf c2 -> c1 = c2.
Proof.
  intros; eapply bigstep_functional; eapply eval_bigstep; unfold eval; split; eauto.
Qed.

Inductive eff_SN (X : Type) (R : X -> X -> effect -> Prop) : X -> Prop :=  
  eff_SNC : forall (x : X), (forall (y : X) phi, R x y phi -> eff_SN R y) -> eff_SN R x.


(** Strong Normaliation is closed under expansion *)
Lemma normalizing_extension {n: nat} (c c': comp n) phi :
  c >* c' # phi -> eff_SN step c' -> eff_SN step c.
Proof.
  induction 1.
  - now intros.
  - intros h1 % IHeff_star. constructor. intros x'' p3 h2.    
    enough (x' = x'') as -> by assumption.
    eapply step_functional; eassumption. 
Qed.

Definition eff_Normal_eff_SN := 
fun (X : Type) (R : X -> X -> effect -> Prop) (x : X) (H : eff_Normal R x) => 
  eff_SNC x (fun (y : X) phi (H1 : R x y phi) => False_ind (eff_SN R y) (H y phi H1)).

(** Bigstep Semantics implies termination *)
Lemma bigstep_sn' {n: nat} (c c': comp n) phi : c ▷ c' # phi -> eff_SN step c'.
Proof.
  intros H % eval_bigstep; destruct H; now apply eff_Normal_eff_SN, nf_normal.
Qed.


Lemma bigstep_sn {n: nat} (c c': comp n) phi : c ▷ c' # phi -> eff_SN step c.
Proof.
  intros H; eapply normalizing_extension; [| eapply bigstep_sn'; eassumption].
  enough (eval c c' phi). 
  eapply bigstep_soundness.  eauto. 
  rewrite -> eval_bigstep. auto.
Qed.
