(**
   We define a semantic typing judgement on values and computations.
   Values in V[A] and computations in C[B] are safe but not necessarily
   syntactically well typed. However they behave like syntactically well typed
   terms.
*)

Set Implicit Arguments.
Require Import Psatz  Logic List.
Require Import Classes.Morphisms.
Import List Notations.

Require Export CBPV.Semantics CBPV.Terms CBPV.SyntacticTyping CBPV.Base.

(** * Semantic Typing *)

(** ** Semantic Types *)
Definition E' {n: nat} (C: comp n -> Prop) (c: comp n) := exists c', c ▷ c' /\ C c'.

Fixpoint V {n: nat} (A: valtype) (v: value n) :=
  match A with
  | zero => False
  | one => v = u
  | U B => exists c, v = <{ c }> /\ E' (C B) c
  | Sigma A1 A2 => exists b v', v = inj b v' /\ V (if b then A1 else A2) v'
  | A1 * A2 => exists v1 v2, v = pair v1 v2 /\ V A1 v1 /\ V A2 v2
  end

with C {n: nat} (B: comptype) (c: comp n) :=
  match B with
  | cone => c = cu
  | F A => exists v, c = ret v /\ V A v
  | Pi B1 B2 => exists c1 c2, c = tuple c1 c2 /\ E' (C B1) c1 /\ E' (C B2) c2
  | A → B => exists c', c = lambda c' /\ forall v, V A v -> E' (C B) (c'[v..])
  end.


Notation E B c := (E' (C B) c).

Definition G  {n m: nat} (Gamma : ctx n) (gamma: fin n -> value m) :=
 forall i A, Gamma i = A -> V A (gamma i).

Definition val_semtype {n: nat} (Gamma: ctx n) (v: value n) (A: valtype) :=
  forall m (gamma: fin n -> value m), G Gamma gamma -> V A (v[gamma]).

Notation "Gamma ⊫ v : A" := (val_semtype Gamma v A) (at level 80, v at level 99).

Definition comp_semtype {n: nat} (Gamma: ctx n) (c: comp n) (B: comptype) :=
  forall m (gamma: fin n -> value m), G Gamma gamma -> E B (c[gamma]).

Notation "Gamma ⊨ c : B" := (comp_semtype Gamma c B) (at level 80, c at level 99).


(** Computations in C[B] have normal form *)
Lemma comp_nf {n: nat} (c: comp n) B: C B c -> nf c.
Proof.
  destruct B; cbn; intros H; [ idtac | repeat (destruct H as [? H])..].
  all: intuition; subst c; eauto.
Qed.

(** Computations in C[B] evaluate, explicitly C[B] ⊆ E[B] *)
Lemma comp_evaluates {n: nat} (c: comp n) B: C B c -> E B c.
Proof.
  intros H; unfold E, E'; eexists c; split; [|assumption].
  apply eval_bigstep; split; [reflexivity|]; eapply comp_nf; eassumption.
Qed.

(** E[B] is closed under reduction *)
Lemma closure_under_expansion {n: nat} (c c': comp n) B: c >* c' -> E B c' -> E B c.
Proof.
  intros ? [c'' []] ; unfold E'; exists c''; split; eauto.
Qed.


Ltac expand := eapply closure_under_expansion.

(** ** Semantic Soundness *)
(** *** Compatibility Lemmas  *)
Section compatibility_lemmas.

  Variable (n: nat) (Gamma: ctx n) (A A1 A2: valtype) (B B1 B2: comptype).

  Lemma compat_var i :  Gamma i = A -> Gamma ⊫ var_value i : A.
  Proof. firstorder. Qed.

  Lemma compat_unit : Gamma ⊫ u : one.
  Proof. now intros gamma H. Qed.

  Lemma compat_pair v1 v2:
    Gamma ⊫ v1 : A1 -> Gamma ⊫ v2 : A2 -> Gamma ⊫ pair v1 v2 : cross A1 A2.
  Proof.
    intros H1 H2 gamma H; specialize (H1 gamma H); specialize (H2 gamma H);
      firstorder.
  Qed.

  Lemma compat_sum (b: bool) v:
    Gamma ⊫ v : (if b then A1 else A2) -> Gamma ⊫ inj b v : Sigma A1 A2.
  Proof.
    intros H' gamma H; specialize (H' gamma H); firstorder.
  Qed.

  Lemma compat_thunk c:
  Gamma ⊨ c : B -> Gamma ⊫ thunk c : U B.
  Proof.
    intros H' gamma H; specialize (H' gamma H); firstorder.
  Qed.

  Lemma compat_cone : Gamma ⊨ cu : cone.
  Proof. intros m gamma H; cbn; unfold E'; eauto. Qed.

  Lemma compat_lambda c:
    A .: Gamma ⊨ c : B -> Gamma ⊨ lambda c : A → B.
  Proof.
    intros H' m gamma H; apply comp_evaluates; cbn; eexists; split; [reflexivity |].
    intros v H1; pose (gamma' := v .: gamma); specialize (H' m gamma').
    mp H'; [intros [i|]; cbn; eauto; intros ? ->; eauto |].
    now asimpl.
  Qed.

  Lemma compat_letin c1 c2:
    Gamma ⊨ c1 : F A -> A .: Gamma ⊨ c2 : B -> Gamma ⊨ $ <- c1; c2 : B.
  Proof.
    intros H' H'' m gamma H; destruct (H' m gamma H) as [c' [H1 H2]]; cbn.
    destruct H2 as [v [-> H2]]; expand;
      [ apply bigstep_soundness in H1; rewrite H1; reduce; reflexivity |].
    pose (gamma' := v .: gamma); specialize (H'' m gamma').
    mp H''; [intros [i|]; cbn; eauto; intros ? ->; eauto |].
    now asimpl.
  Qed.

  Lemma compat_ret v:
    Gamma ⊫ v : A -> Gamma ⊨ ret v : F A.
  Proof.
    intros H' m gamma H; specialize (H' m gamma H); apply comp_evaluates; firstorder.
  Qed.

  Lemma compat_app c v:
    Gamma ⊨ c : A → B -> Gamma ⊫ v : A -> Gamma ⊨ c v : B.
  Proof.
    intros H1 H2 m gamma H; specialize (H1 m gamma H); specialize (H2 m gamma H); cbn.
    destruct H1 as [? [H1 [c' [-> H3]]]]; apply bigstep_soundness in H1.
    expand; [rewrite H1; reduce; reflexivity |].
    eauto.
  Qed.

  Lemma compat_tuple c1 c2:
    Gamma ⊨ c1 : B1 -> Gamma ⊨ c2 : B2 -> Gamma ⊨ tuple c1 c2 : Pi B1 B2.
  Proof.
    intros H' H'' m gamma H. apply comp_evaluates. cbn.
    eexists; eexists; split; [reflexivity |].
    split; cbn; eauto.
  Qed.

  Lemma compat_proj c b:
    Gamma ⊨ c : Pi B1 B2 -> Gamma ⊨ proj b c : if b then B1 else B2.
  Proof.
    intros H m gamma H1; specialize (H m gamma H1).
    destruct H as [c' [H2 [c1 [c2 [H4 [H5 H6]]]]]]; cbn;
      apply bigstep_soundness in H2; destruct b;
        expand.
    all: try eassumption.
    all: rewrite H2; subst c'; reduce; reflexivity.
  Qed.

  Lemma compat_force v:
    Gamma ⊫ v : U B -> Gamma ⊨ v! : B.
  Proof.
    intros H' m gamma H; asimpl; specialize (H' m gamma H).
    destruct H' as [c [-> H']]; now expand; [reduce; reflexivity|].
  Qed.

  Lemma compat_caseZ v:
    Gamma ⊫ v : zero -> Gamma ⊨ caseZ v : B.
  Proof.
    intros H1 m gamma H; destruct (H1 m gamma H).
  Qed.

  Lemma compat_caseS v c1 c2:
    Gamma ⊫ v : Sigma A1 A2 ->
    A1 .: Gamma ⊨ c1 : B ->
    A2 .: Gamma ⊨ c2 : B ->
    Gamma ⊨ caseS v c1 c2 : B.
  Proof.
    intros H' H1 H2 m gamma H; specialize (H' m gamma H); cbn in H'.
    destruct H' as [[] [v' [H3 H4]]].
    all: asimpl; rewrite H3; expand; try (reduce; reflexivity).
    all: pose (gamma' := v' .: gamma); specialize (H1 m gamma'); specialize (H2 m gamma').
    all: [> mp H1 | mp H2].
    1, 3: intros [i|]; cbn; eauto; intros ? ->; eauto.
    all: now asimpl.
  Qed.

  Lemma compat_caseP v c:
      Gamma ⊫ v : A1 * A2 ->
      A2 .: (A1 .: Gamma) ⊨ c : B ->
      Gamma ⊨ caseP v c : B.
  Proof.
    intros H' H1 m gamma H; specialize (H' m gamma H).
    destruct H' as [v1 [v2 [H2 [H3 H4]]]]; asimpl.
    rewrite H2; expand; [reduce; reflexivity |].
    pose (gamma' := v2 .: (v1 .: gamma)); specialize (H1  m gamma').
    mp H1; [intros [[]|] A0 ?; cbn; subst A0; eauto |].
    now asimpl.
  Qed.


End compatibility_lemmas.

Hint Resolve
    compat_var compat_unit compat_pair compat_sum compat_thunk compat_cone
    compat_lambda compat_letin compat_ret compat_app compat_tuple compat_proj
    compat_force compat_caseZ compat_caseS compat_caseP : compatibility_lemmas.


(** *** Semantic Soundness *)
(** Syntactically well typed terms are semantically well typed *)
Theorem SemanticSoundness n (Gamma: ctx n):
  (forall v A, Gamma ⊩ v : A -> Gamma ⊫ v : A) /\ (forall c B, Gamma ⊢ c : B -> Gamma ⊨ c : B).
Proof.
  eapply mutind_value_computation_typing; eauto with compatibility_lemmas.
Qed.

Lemma ClosedSemanticSoundness:
    (forall P A, null ⊩ P : A -> V A P) /\ (forall P A, null ⊢ P : A -> E A P).
Proof.
    destruct (SemanticSoundness null) as [H1 H2].
    split; intros P A; [intros H % H1 | intros H % H2].
    all: specialize (H 0 ids); mp H; try now intros [].
    all: now asimpl in H.
Qed.


Lemma Normal_nf M A:
  null ⊢ M : A -> Normal step M -> nf M.
Proof.
  destruct ClosedSemanticSoundness as [_ sem].
  intros ? % sem N.
  destruct X. intuition.
  eapply bigstep_soundness in H0.
  inv H0. eapply comp_nf; eauto.
  firstorder.
Qed.


