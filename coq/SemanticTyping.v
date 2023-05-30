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
Definition E' {n: nat} (C: comp n -> Prop) (c: comp n) phi := exists c', c ▷ c' # phi /\ C c'.

Fixpoint V {n: nat} (A: valtype) (v: value n) :=
  match A with
  | zero => False
  | one => v = u
  | U phi B => exists c, v = <{ c }> /\ E' (C B) c phi
  | Sigma A1 A2 => exists b v', v = inj b v' /\ V (if b then A1 else A2) v'
  | A1 * A2 => exists v1 v2, v = pair v1 v2 /\ V A1 v1 /\ V A2 v2
  end

with C {n: nat} (B: comptype) (c: comp n) :=
  match B with
  | cone => c = cu 
  | F A => exists v, c = ret v /\ V A v 
  | Pi B1 B2 => exists c1 c2 phi, c = tuple c1 c2 /\ E' (C B1) c1 phi /\ E' (C B2) c2 phi
  | A → B => exists c' phi, c = lambda c' /\ forall v, V A v -> E' (C B) (subst_comp (v..) c') phi
  end.


Notation E B c phi := (E' (C B) c phi).

Definition G  {n m: nat} (Gamma : ctx n) (gamma: fin n -> value m) :=
 forall i A, Gamma i = A -> V A (gamma i).

Definition val_semtype {n: nat} (Gamma: ctx n) (v: value n) (A: valtype) :=
  forall m (gamma: fin n -> value m), G Gamma gamma -> V A (subst_value gamma v).

Notation "Gamma ⊫ v : A" := (val_semtype Gamma v A) (at level 80, v at level 99).

Definition comp_semtype {n: nat} (Gamma: ctx n) (c: comp n) (B: comptype) (phi : effect) :=
  forall m (gamma: fin n -> value m), G Gamma gamma -> E B (subst_comp gamma c) phi.

Notation "Gamma ⊨ c : B # phi" := (comp_semtype Gamma c B phi) (at level 80, c at level 99).


(** Computations in C[B] have normal form *)
Lemma comp_nf {n: nat} (c: comp n) B: C B c -> nf c.
Proof.
  destruct B; cbn; intros H; [ idtac | repeat (destruct H as [? H])..].
  all: intuition; subst c; eauto.
Qed.

(** Computations in C[B] evaluate, explicitly C[B] ⊆ E[B] *)
Lemma comp_evaluates {n: nat} (c: comp n) B: C B c -> E B c pure.
Proof.
  intros H; unfold E, E'; eexists c; split; [|assumption].
  apply eval_bigstep. split; [auto|]; eapply comp_nf; eassumption.
Qed.

(** E[B] is closed under reduction *)
Lemma closure_under_expansion {n: nat} (c c': comp n) phi B: c >* c' # phi -> E B c' phi -> E B c phi.
Proof.
  intros ? [c'' []] ; unfold E'; exists c''; split; eauto. 
Admitted.


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

  Lemma compat_thunk c phi:
  Gamma ⊨ c : B # phi -> Gamma ⊫ thunk c : U phi B.
  Proof.
    intros H' gamma H; specialize (H' gamma H); firstorder.
  Qed.

  Lemma compat_cone phi : Gamma ⊨ cu : cone # phi.
  Proof. intros m gamma H; cbn; unfold E'; eauto. Admitted.

  Lemma compat_lambda c phi:
    A .: Gamma ⊨ c : B # phi -> Gamma ⊨ lambda c : A → B # phi.
  Proof.
  Admitted.
    (*
    intros H' m gamma H; apply comp_evaluates; cbn; eexists; split; [reflexivity |].
    intros v H1; pose (gamma' := v .: gamma); specialize (H' m gamma').
    mp H'; [intros [i|]; cbn; eauto; intros ? ->; eauto |].
    now asimpl.
  Qed.
*)

  Lemma compat_letin c1 c2 phi1 phi2 phi:
    Gamma ⊨ c1 : F A # phi1 -> A .: Gamma ⊨ c2 : B # phi2 -> Gamma ⊨ $ <- c1; c2 : B # phi.
  Proof.
    intros H' H'' m gamma H; destruct (H' m gamma H) as [c' [H1 H2]]; cbn.
    Admitted.
(*
    destruct H2 as [v [-> H2]]; expand;
      [ apply bigstep_soundness in H1; rewrite H1; reduce; reflexivity |].
    pose (gamma' := v .: gamma); specialize (H'' m gamma').
    mp H''; [intros [i|]; cbn; eauto; intros ? ->; eauto |].
    now asimpl.
  Qed.
*)

  Lemma compat_ret v phi:
    Gamma ⊫ v : A -> Gamma ⊨ ret v : F A # phi.
  Proof.
    Admitted.
    (*
    intros H' m gamma H; specialize (H' m gamma H); apply comp_evaluates; firstorder.
  Qed.
*)

  Lemma compat_app c v phi:
    Gamma ⊨ c : A → B # phi -> Gamma ⊫ v : A -> Gamma ⊨ c v : B # phi.
  Proof.
    intros H1 H2 m gamma H; specialize (H1 m gamma H); specialize (H2 m gamma H); cbn.
    Admitted.
(*
    destruct H1 as [? [H1 [c' [-> H3]]]]; apply bigstep_soundness in H1.
    expand; [rewrite H1; reduce; reflexivity |].
    eauto.
  Qed.
*)

  Lemma compat_tuple c1 c2 phi:
    Gamma ⊨ c1 : B1 # phi -> Gamma ⊨ c2 : B2 # phi -> Gamma ⊨ tuple c1 c2 : Pi B1 B2 #phi.
  Proof.
    intros H' H'' m gamma H.
  Admitted.
(*
    apply comp_evaluates. cbn.
    eexists; eexists; split; [reflexivity |].
    split; cbn; eauto.
  Qed.
*)

  Lemma compat_proj c b phi:
    Gamma ⊨ c : Pi B1 B2 # phi -> Gamma ⊨ proj b c : if b then B1 else B2 # phi.
  Proof.
    intros H m gamma H1; specialize (H m gamma H1).
    destruct H as [c' [H2 [c1 [c2 [H4 [H5 H6]]]]]]; cbn;
      apply bigstep_soundness in H2; destruct b;
        expand.
    all: try eassumption.
  Admitted.
  (*
    all: rewrite H2; subst c'; reduce; reflexivity.
  Qed.
  *)

  Lemma compat_force v phi:
    Gamma ⊫ v : U phi B -> Gamma ⊨ v! : B # phi.
  Proof.
    intros H' m gamma H; asimpl; specialize (H' m gamma H).
  Admitted.
  (*
    destruct H' as [c [-> H']]; now expand; [reduce; reflexivity|].
  Qed.
  *)

  Lemma compat_caseZ v phi:
    Gamma ⊫ v : zero -> Gamma ⊨ caseZ v : B # phi.
  Proof.
    intros H1 m gamma H; destruct (H1 m gamma H).
  Qed.

  Lemma compat_caseS v c1 c2 phi :
    Gamma ⊫ v : Sigma A1 A2 ->
    A1 .: Gamma ⊨ c1 : B # phi ->
    A2 .: Gamma ⊨ c2 : B # phi ->
    Gamma ⊨ caseS v c1 c2 : B # phi.
  Proof.
    intros H' H1 H2 m gamma H; specialize (H' m gamma H); cbn in H'.
    destruct H' as [[] [v' [H3 H4]]].
    all: asimpl; rewrite H3; expand; try (reduce; reflexivity).
    all: pose (gamma' := v' .: gamma); specialize (H1 m gamma'); specialize (H2 m gamma').
    Admitted.
(*
    all: [> mp H1 | mp H2].
    1, 3: intros [i|]; cbn; eauto; intros ? ->; eauto.
    all: now asimpl.
  Qed.
*)

  Lemma compat_caseP v c phi:
      Gamma ⊫ v : A1 * A2 ->
      A2 .: (A1 .: Gamma) ⊨ c : B # phi ->
      Gamma ⊨ caseP v c : B # phi.
  Proof.
    intros H' H1 m gamma H; specialize (H' m gamma H).
    destruct H' as [v1 [v2 [H2 [H3 H4]]]]; asimpl.
  Admitted.
  (*
    rewrite H2; expand; [reduce; reflexivity |].
    pose (gamma' := v2 .: (v1 .: gamma)); specialize (H1  m gamma').
    mp H1; [intros [[]|] A0 ?; cbn; subst A0; eauto |].
    now asimpl.
  Qed.
  *)


End compatibility_lemmas.

Hint Resolve
    compat_var compat_unit compat_pair compat_sum compat_thunk compat_cone
    compat_lambda compat_letin compat_ret compat_app compat_tuple compat_proj
    compat_force compat_caseZ compat_caseS compat_caseP : compatibility_lemmas.



(* 
 forall (m : nat) (Gamma : ctx m),
       value_typing Gamma <<= P m Gamma /\
       (forall c : comp m,
        computation_typing Gamma c <<= P0 m Gamma c)
*)

(** *** Semantic Soundness *)
(** Syntactically well typed terms are semantically well typed *)
Theorem SemanticSoundness  n (Gamma: ctx n):
  (forall  v A, Gamma ⊩ v : A -> Gamma ⊫ v : A) /\ (forall c B phi, Gamma ⊢ c : B # phi -> Gamma ⊨ c : B # phi).
Proof.
  eapply mutind_value_computation_typing; eauto with compatibility_lemmas.
Admitted.

Lemma ClosedSemanticSoundness:
    (forall P A, null ⊩ P : A -> V A P) /\ (forall P A phi, null ⊢ P : A # phi -> E A P phi).
Proof.
    destruct (SemanticSoundness null) as [H1 H2].
    split; intros P A; [intros H % H1 | intros phi H % H2].
    all: specialize (H 0 ids); mp H; try now intros [].
    all: now asimpl in H.
Qed.

Check step.

Lemma Normal_nf M A phi:
  null ⊢ M : A # phi -> Normal (fun x y => step x y phi) M -> nf M.
Proof.
  destruct ClosedSemanticSoundness as [_ sem].
  intros ? % sem N.
  destruct X. intuition.
  eapply bigstep_soundness in H0.
  inv H0. eapply comp_nf; eauto.
  firstorder.
Admitted.
