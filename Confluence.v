(** * Confluence *)
(** We show confluence of CBPV using the technique of Tait- Martin-Löf, refined by Takahashi. *)
Set Implicit Arguments.
Require Import Psatz  Logic List Classes.Morphisms Coq.Program.Tactics.
Import List Notations.
Require Export CBPV.StrongReduction CBPV.TMT.
Import CommaNotation.

Reserved Notation "A '>>v' B" (at level 60).
Reserved Notation "A '>>c' B" (at level 60).

(** ** Parallel Reduction *)
Class ParallelReduction (A: Type) := { parstep : A -> A -> Prop }.
Notation "A >> B" := (parstep A B).

Inductive parstepv (n: nat) : value n -> value n -> Prop :=
| parstepvVar (i: fin n): (var_value i) >>v (var_value i)
| parstepvU : (@u n) >>v u
| parstepvPair (v1 : value n) v1' v2 v2': v1 >>v v1' -> v2 >>v v2' -> pair v1 v2 >>v pair v1' v2'
| parstepvInj b (v: value n) v': v >>v v' -> inj b v >>v inj b v'
| parstepvThunk (c: comp n) c': c >>c c' -> <{ c }> >>v <{ c' }>
where "M >>v N" := (parstepv M N)
with parstepc (n: nat) : comp n -> comp n -> Prop :=
| parstepcCu : @cu n >>c cu
| parstepcForce (v: value n) v': v >>v v' -> v ! >>c v' !
| parstepcForceBeta (c c': comp n): c >>c c' -> <{ c }> ! >>c c'
| parstepcLambda (c c': comp (S n)): c >>c c' -> lambda c >>c lambda c'
| parstepcApp (c: comp n) c' v v': c >>c c' -> v >>v v' -> c v >>c c' v'
| parstepcAppBeta (c c': comp (S n)) v v': c >>c c' -> v >>v v' -> (lambda c) v >>c subst_comp (v'..) c'
| parstepcTuple (c1 c1' c2 c2': comp n):
    c1 >>c c1' -> c2 >>c c2' -> tuple c1 c2 >>c tuple c1' c2'
| parstepcRet (v: value n) v': v >>v v'-> ret v >>c ret v'
| parstepcLetin c1 c1' (c2 c2': comp (S n)) :
    c1 >>c c1' -> c2 >>c c2' -> $ <- c1; c2 >>c $ <- c1'; c2'
| parstepcLetinBeta (c c': comp (S n)) v v':
    c >>c c' -> v >>v v' -> $ <- ret v; c >>c subst_comp (v'..) c'
| parstepcProj (c c': comp n) b: c >>c c' -> proj b c >>c proj b c'
| parstepcProjBeta (c1 c1': comp n) (c2 c2': comp n) b:
    c1 >>c c1' -> c2 >>c c2' -> proj b (tuple c1 c2) >>c (if b then c1' else c2')
| parstepcCaseZ (v v': value n):  v >>v v'-> caseZ v >>c caseZ v'
| parstepcCaseS (v v': value n) c1 c1' c2 c2':
    v >>v v'-> c1 >>c c1' -> c2 >>c c2' ->  caseS v c1 c2 >>c caseS v' c1' c2'
| parstepcCaseSBeta (v v': value n) c1 c1' c2 c2' b:
    v >>v v'-> c1 >>c c1' -> c2 >>c c2' ->
    caseS (inj b v) c1 c2 >>c subst_comp (v' ..) (if b then c1' else c2')
| parstepcCaseP (v v': value n) c c':
    v >>v v'-> c >>c c' -> caseP v c >>c caseP v' c'
| parstepcCasePBeta (v1 v1': value n) v2 v2' c c':
    v1 >>v v1' -> v2 >>v v2' -> c >>c c' ->
    caseP (pair v1 v2) c >>c subst_comp (v2',v1'..) c'
where "M >>c N" := (@parstepc _ M N).

Scheme parstepv_ind_2 := Induction for parstepv Sort Prop
  with parstepc_ind_2  := Induction for parstepc Sort Prop.

Combined Scheme mutind_parstep from parstepv_ind_2, parstepc_ind_2.


Instance parstep_value (n: nat) : ParallelReduction (value n) :=
  { parstep := @parstepv n }.

Instance parstep_comp (n: nat) : ParallelReduction (comp n) :=
  { parstep := @parstepc n }.

Hint Constructors parstepv parstepc.
Hint Unfold parstep parstep_comp parstep_value.


(** ** Reduction Function *)
Fixpoint rhoᵥ (n: nat) (v: value n) :=
  match v with
  | var_value i => var_value i
  | u => u
  | pair v1 v2 => pair (rhoᵥ v1) (rhoᵥ v2)
  | inj b v => inj b (rhoᵥ v)
  | thunk c => thunk (rho c)
  end
with rho (n: nat) (c: comp n) :=
  match c with
  | cu => cu
  | force (thunk c) => rho c
  | force v => force (rhoᵥ v)
  | lambda c => lambda (rho c)
  | app (lambda c) v => subst_comp ((rhoᵥ v) ..) (rho c)
  | app c v => app (rho c) (rhoᵥ v)
  | tuple c1 c2 => tuple (rho c1) (rho c2)
  | ret v => ret (rhoᵥ v)
  | letin (ret v) c => subst_comp ((rhoᵥ v)..) (rho c)
  | letin c1 c2 => letin (rho c1) (rho c2)
  | proj b (tuple c1 c2) => if b then rho c1 else rho c2
  | proj b c => proj b (rho c)
  | caseZ v => caseZ (rhoᵥ v)
  | caseS (inj b v) c1 c2 => subst_comp ((rhoᵥ v)..) (if b then rho c1 else rho c2)
  | caseS v c1 c2 => caseS (rhoᵥ v) (rho c1) (rho c2)
  | caseP (pair v1 v2) c => subst_comp (rhoᵥ v2,(rhoᵥ v1)..) (rho c)
  | caseP v c => caseP (rhoᵥ v) (rho c)
  end.


(** ** Properties *)
Lemma parstep_refl:
  forall n, (forall (v: value n), v >> v) /\ (forall (c: comp n), c >> c).
Proof.
  eapply mutind_val_comp; autounfold; eauto.
Qed.


Lemma parstepv_refl n (v: value n): v >>v v. Proof. apply parstep_refl. Qed.
Lemma parstepc_refl n (c: comp n): c >>c c. Proof. apply parstep_refl. Qed.


Hint Resolve parstepv_refl parstepc_refl.

Fixpoint sstep_parstepc n (c1 c2: comp n) (H: c1 ↪ c2) {struct H}: c1 >> c2
with sstep_value_parstepv n (v1 v2: value n) (H: v1 ↪ᵥ v2) {struct H}: v1 >> v2.
Proof.
  all: destruct H;  autounfold in *.
  17: {
        idtac.
        destruct H; subst; econstructor; apply parstep_refl.
  }
  all: econstructor; eauto.
Qed.

Ltac sstep_rewrite :=
  match goal with
  | [ H: ?X ↪ᵥ* ?Y |- _] => rewrite H
  | [ H: ?X ↪* ?Y |- _] => rewrite H
  end.


Lemma parstep_star_sstep:
  forall n,
    (forall (v v' : value n) (p : v >>v v'), v ↪ᵥ* v') /\
    (forall (c c' : comp n) (p : c >>c c'), c ↪* c').
Proof.
  eapply mutind_parstep; intros; eauto.
  all: try destruct b; eauto.
  all: repeat sstep_rewrite.
  all: eauto.
Qed.


Lemma ren_lift n m (s: comp (S n)) (t: value n) (sigma: fin n -> fin m):
  ren_comp sigma (subst_comp (t..) s) = subst_comp ((ren_value sigma t)..) (ren_comp (up_ren sigma) s).
Proof.
  now asimpl.
Qed.

Lemma ren₂_lift n m s t1 t2 (sigma: fin n -> fin m):
  ren_comp sigma (subst_comp (t2,t1..)s) = subst_comp ((ren_value sigma t2), (ren_value sigma t1)..) (ren_comp (up_ren (up_ren sigma)) s).
Proof.
  now asimpl.
Qed.

Lemma beta_lift n m s t (sigma: fin n -> value m):
  subst_comp sigma (subst_comp (t..) s) = subst_comp ((subst_value sigma t)..) (subst_comp (up_value_value sigma) s).
Proof. now asimpl. Qed.

Lemma beta₂_lift n m s t1 t2 (sigma: fin n -> value m):
  subst_comp sigma (subst_comp (t1, t2..) s) =
  subst_comp ((subst_value sigma t1), (subst_value sigma t2)..) (subst_comp (up_value_value (up_value_value sigma)) s).
Proof. now asimpl. Qed.

Fixpoint parstepc_renaming n m (c c': comp n) (H: c >>c c') {struct H}:
  forall  (f: fin n -> fin m), ren_comp f c >>c ren_comp f c'
with parstepv_renaming n m (v v': value n) (H: v >>v v') {struct H}:
  forall  (f: fin n -> fin m),  ren_value f v >>v ren_value f v'.
Proof.
  all: destruct H; asimpl; intros; eauto.
  all: rewrite ?ren_lift, ?ren₂_lift.
  all: eauto.
  - destruct b; [ econstructor 12 with (b := true) | econstructor 12 with (b := false) ]; eauto.
  - destruct b; [ econstructor 15 with (b := true) | econstructor 15 with (b := false) ]; eauto.
Qed.

Hint Resolve parstepv_renaming parstepc_renaming.

Fixpoint parstepc_subst n m (c c': comp n) (H: c >>c c') {struct H}:
  forall  (f g: fin n -> value m), (forall i, f i >>v g i) -> subst_comp f c >>c subst_comp g c'
with parstepv_subst n m (v v': value n) (H: v >>v v') {struct H}:
  forall  (f g: fin n -> value m), (forall i, f i >>v g i) -> subst_value f v >>v subst_value g v'.
Proof with eauto; intros []; cbn; unfold funcomp; eauto.
  all: destruct H; intros; cbn; eauto.
  - constructor; apply parstepc_subst...
  - rewrite beta_lift. constructor; eauto; eapply parstepc_subst...
  - constructor; eauto; eapply parstepc_subst...
  - rewrite beta_lift. constructor; eauto; eapply parstepc_subst...
  - destruct b.
    + eapply parstepcProjBeta with (b := true);  eauto.
    + eapply parstepcProjBeta with (b := false);  eauto.
  - constructor; eauto; eapply parstepc_subst...
  - rewrite beta_lift. destruct b.
    + eapply parstepcCaseSBeta with (b := true); eauto.
      eapply parstepc_subst...
    + eapply parstepcCaseSBeta with (b := false); eauto.
      eapply parstepc_subst...
  - constructor; eauto; eapply parstepc_subst; eauto;  intros [ []|]; cbn; unfold funcomp; eauto.
  - rewrite beta₂_lift.
    constructor; eauto.
    eapply parstepc_subst. eauto.
    intros [ []|]; cbn; eauto.
    unfold funcomp. do 2 eapply parstepv_renaming. apply H2.
Qed.

Fact takahashi :
  forall n,
    (tak_fun (@parstepv n) (@rhoᵥ n) /\ tak_fun (@parstepc n) (@rho n)).
Proof with eapply parstepc_subst; eauto; auto_case.
  eapply mutind_parstep; intros; asimpl; cbn; eauto.
  - destruct v; eauto. inv p. inv H. eauto.
  - destruct c; eauto. inv p. cbn in H. inv H. constructor; eauto.
  - cbn...
  - destruct c1; eauto. inv p. cbn in H. inv H. eauto.
  - cbn...
  - destruct c; eauto. inv p. cbn in H. inv H. eauto.
  - destruct b; eauto.
  - destruct v; eauto. cbn in H. inv H. eauto.
  - destruct b...
  - destruct v; eauto. inv p. cbn in H. inv H. eauto.
  - cbn...
Qed.

Theorem confluence n:
   confluent (@sstep n) /\ confluent (@sstep_value n).
Proof.
  split; eapply TMT.
  - apply sstep_parstepc.
  - apply parstep_star_sstep.
  - intros c. apply parstepc_refl.
  - apply takahashi.
  - apply sstep_value_parstepv.
  - apply parstep_star_sstep.
  - intros c. apply parstepv_refl.
  - apply takahashi.
Qed.


Lemma sstep_confluent n: confluent (@sstep n).
Proof.
  apply confluence.
Qed.

Lemma sstep_value_confluent n: confluent (@sstep_value n).
Proof.
  apply confluence.
Qed.

Hint Immediate sstep_confluent sstep_value_confluent.
