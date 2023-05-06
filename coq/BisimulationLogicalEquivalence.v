(**
  We give relations on values and computations that relate semantically equivalent terms.
  The relations V, C and E are analogous to the ones in Semantic Typing, just taking two arguemtns everywhere.
  This method is then used to show that logical equivalence implies observational equivalence
  and that logical equivalence is closed under reduction. Combinig these two facts we get,
  that observational equivalence is closed under reduction.
*)

Set Implicit Arguments.
Require Import Psatz  Logic List.
Require Import Classes.Morphisms .
Import List Notations.

Require Export CBPV.Terms CBPV.ObservationalEquivalence
        CBPV.StrongReduction CBPV.ProgramContexts CBPV.Confluence
        CBPV.AbstractReductionSystems Eagerlet.

Import CommaNotation.

(** * Logical Equivalence *)

(** ** Logical Eqivalence *)

Definition Inverse {X: Type} (R: X -> X -> Prop) (x1 x2: X) := R x2 x1.
Definition Simulation {n: nat} (C: comp n -> comp n -> Prop) (c1 c2: comp n) :=
  forall c1', c1 ▷ c1' -> exists c2', c2 ▷ c2' /\  C c1' c2'.

Definition E' {n: nat} (C: comp n -> comp n -> Prop) (c1 c2: comp n) :=
  Simulation C c1 c2 /\ Simulation (Inverse C) c2 c1.

Fixpoint V  (A: valtype) {n: nat} (v1 v2: value n) :=
  match A with
  | zero => False
  | one => v1 = u /\ v2 = u
  | Sigma A1 A2 => exists v1' v2' b, v1 = inj b v1' /\ v2 = inj b v2' /\ V (if b then A1 else A2) v1' v2'
  | cross A1 A2 => exists v1' v1'' v2' v2'', v1 = pair v1' v1'' /\ v2 = pair v2' v2'' /\ V A1 v1' v2' /\ V A2 v1'' v2''
  | U B => exists c1 c2, v1 = <{ c1 }> /\ v2 = <{ c2 }> /\ E' (C B) c1 c2
  end

with C (B: comptype) {n: nat} (c1 c2: comp n) :=
  match B with
  | cone => c1 = cu /\ c2 = cu
  | Pi B1 B2 => exists c1' c1'' c2' c2'', c1 = tuple c1' c1'' /\ c2 = tuple c2' c2'' /\ E' (C B1) c1' c2' /\ E' (C B2) c1'' c2''
  | A → B => exists c1' c2', c1 = lambda c1' /\ c2 = lambda c2' /\ forall v1 v2, V A v1 v2 -> E' (C B) (c1'[v1..]) (c2'[v2..])
  | F A => exists v1 v2, c1 = ret v1 /\ c2 = ret v2 /\ V A v1 v2
  end.



Notation E B := (E' (C B)).

Definition G {n: nat} (Gamma : ctx n) {m: nat} (gamma gamma': fin n -> value m) :=
 forall i A, Gamma i = A -> V A (gamma i) (gamma' i).

(** ** Semantic Eqivalence Judgement *)
(** *** Logical Equivalencedgement *)
Definition val_semeq {n: nat} (Gamma: ctx n) (A: valtype) (v1 v2: value n)  :=
  forall m (gamma gamma': fin n -> value m), G Gamma gamma gamma' -> V A (v1[gamma]) (v2[gamma']).

Notation "Gamma ⊫ v1 ∼ v2 : A" := (val_semeq Gamma A v1 v2) (at level 80, v2 at level 99).

(** *** Logical Equivalenceion Judgement *)
Definition comp_semeq {n: nat} (Gamma: ctx n) (B: comptype) (c1 c2: comp n) :=
  forall m (gamma gamma': fin n -> value m), G Gamma gamma gamma' -> E B (c1[gamma]) (c2[gamma']).

Notation "Gamma ⊨ c1 ∼ c2 : B" := (comp_semeq Gamma B c1 c2) (at level 80, c2 at level 99).

Hint Transparent comp_semeq val_semeq.





(** ** Properties of Logical Equivalence *)

(** *** Symmetry and Transitivity **)

Lemma V_C_symmetry:
  (forall A, forall n (M N: value n), V A M N -> V A N M) /\ (forall A, forall n (M N: comp n), C A M N -> C A N M).
Proof with eauto; intuition; eexists; eauto.
  eapply mutind_valtype_comptype; cbn; intros; exintuition.
  all: unfold E, Simulation, Inverse in *; exintuition.
  all: try solve [repeat eexists; eauto].
  - do 2 eexists. intuition; eauto.
    + edestruct H4...
    + edestruct H2...
  - repeat eexists; eauto; destruct x1; eauto.
  - do 4 eexists; repeat split; eauto; intros.
    + edestruct H6...
    + edestruct H4...
    + edestruct H7...
    + edestruct H3...
  - do 2 eexists; exintuition; eauto; apply H in H3; edestruct H4; eauto.
    + edestruct H7...
    + edestruct H6...
Qed.

Lemma E_symmetry:
  forall B, forall n (M N: comp n), E B M N -> E B N M.
Proof.
  intros; unfold E, Simulation, Inverse in *; exintuition.
  + edestruct H1; eauto; intuition; eexists; split; eauto; now eapply V_C_symmetry.
  + edestruct H0; eauto; intuition; eexists; split; eauto; now eapply V_C_symmetry.
Qed.

Lemma G_symmetry:
  forall n m (Gamma: ctx n) (gamma gamma': fin n -> value m), G Gamma gamma gamma' -> G Gamma gamma' gamma.
Proof.
  intros;  unfold G in *; intros; eapply V_C_symmetry; eauto.
Qed.

Lemma val_semeq_symmetry (n: nat) (Gamma: ctx n) (A: valtype) :
  forall (v1 v2: value n),  Gamma ⊫ v1 ∼ v2 : A -> Gamma ⊫ v2 ∼ v1 : A.
Proof.
  unfold val_semeq; intros; eapply V_C_symmetry; eauto using G_symmetry.
Qed.

Lemma comp_semeq_symmetry (n: nat) (Gamma: ctx n) (B: comptype) :
  forall (c1 c2: comp n), Gamma ⊨ c1 ∼ c2 : B -> Gamma ⊨ c2 ∼ c1 : B.
Proof.
  unfold comp_semeq; intros; eapply E_symmetry; eauto using G_symmetry.
Qed.


Global Instance V_symm {n: nat} (A: valtype): Symmetric (@V A n).
Proof. intros ? ? ?; eapply V_C_symmetry; eauto. Qed.

Global Instance C_symm {n: nat} (B: comptype): Symmetric (@C B n).
Proof. intros ? ? ?; eapply V_C_symmetry; eauto. Qed.

Global Instance E_symm {n: nat} (B: comptype): Symmetric (E' (@C B n)).
Proof. intros ? ? ?; eapply E_symmetry; eauto. Qed.

Global Instance G_symm {n m: nat} (Gamma: ctx n): Symmetric (@G n Gamma m).
Proof. intros ? ? ?; eapply G_symmetry; eauto. Qed.

Global Instance val_semeq_symm {n: nat} (Gamma: ctx n) (A: valtype): Symmetric (val_semeq Gamma A).
Proof. intros ? ? ?; eapply val_semeq_symmetry; eauto. Qed.

Global Instance comp_semeq_symm {n: nat} (Gamma: ctx n) (B: comptype): Symmetric (comp_semeq Gamma B).
Proof. intros ? ? ?; eapply comp_semeq_symmetry; eauto. Qed.


Instance simulation_transitive {n: nat} B :
  Transitive (@C B n) -> Transitive (Simulation (@C B n)).
Proof.
  intros ? ? ?; unfold Simulation; intuition.
  edestruct H0; eauto; intuition.
  edestruct H1; eauto; intuition.
  eexists; intuition eauto.
Qed.

Instance simulation_inverse_transitive {n: nat} B :
  Transitive (@C B n) -> Transitive (Simulation (Inverse (@C B n))).
Proof.
  intros ? ? ?; unfold Simulation; intuition.
  edestruct H0; eauto; intuition.
  edestruct H1; eauto; intuition.
  eexists; intuition eauto.
  unfold Inverse in *; eauto.
Qed.



Lemma V_C_transitive:
  (forall A, forall n (x y z: value n), V A x y -> V A y z -> V A x z) /\
  (forall A, forall n (x y z: comp n), C A x y -> C A y z -> C A x z).
Proof.
  eapply mutind_valtype_comptype; cbn; intros; exintuition.
  all: unfold E in *; exintuition; subst.
  - do 2 eexists; eauto; intuition; injection H1 as ->.
    eapply simulation_transitive; eauto.
    eapply simulation_inverse_transitive; eauto.
  - injection H2 as ->; destruct x5; subst; repeat eexists; eauto .
  - injection H2 as ->; subst; repeat eexists; eauto.
  - injection H1 as ->; subst; repeat eexists; eauto.
  - injection H2 as -> ->.
    do 4 eexists; intuition; eauto.
    all: try eapply simulation_transitive; eauto.
    all: try eapply simulation_inverse_transitive; eauto.
  - do 2 eexists; repeat split; eauto; injection H2 as ->; intros.
    all: destruct (V_C_symmetry) as [H2 _]; specialize (H2 _ _ _ _ H1).
    all: assert (V v v1 v1) as H4 by eauto.
    all: assert (V v v2 v2) as H5 by eauto.
    all: specialize (H6 _ _ H1) as H8; specialize (H7 _ _ H5) as H9.
    all: exintuition.
    eapply simulation_transitive; eauto.
    eapply simulation_inverse_transitive; eauto.
Qed.

Lemma E_transitive:
  forall B, forall n (x y z: comp n), E B x y -> E B y z -> E B x z.
Proof.
  intros; unfold E in *; exintuition.
  + eapply simulation_transitive; unfold Transitive; destruct  V_C_transitive; eauto.
  + eapply simulation_inverse_transitive; unfold Transitive; destruct  V_C_transitive; eauto.
Qed.

Lemma G_transitive:
  forall n m (Gamma: ctx n) (gamma gamma' gamma'': fin n -> value m), G Gamma gamma gamma' -> G Gamma gamma' gamma'' -> G Gamma gamma gamma''.
Proof.
  intros;  unfold G in *; intros; eapply V_C_transitive; eauto.
Qed.


Lemma val_semeq_transitive (n: nat) (Gamma: ctx n) (A: valtype) :
  forall (v1 v2 v3: value n),  Gamma ⊫ v1 ∼ v2 : A -> Gamma ⊫ v2 ∼ v3 : A -> Gamma ⊫ v1 ∼ v3 : A.
Proof.
  unfold val_semeq; intros; eapply V_C_transitive;  eauto using G_transitive, G_symmetry.
Qed.


Lemma comp_semeq_transitive (n: nat) (Gamma: ctx n) (B: comptype) :
  forall (c1 c2 c3: comp n), Gamma ⊨ c1 ∼ c2 : B -> Gamma ⊨ c2 ∼ c3 : B -> Gamma ⊨ c1 ∼ c3 : B.
Proof.
  unfold comp_semeq; intros; eapply E_transitive; eauto using G_transitive, G_symmetry.
Qed.





Global Instance V_trans {n: nat} (A: valtype): Transitive (@V A n).
Proof. intros ? ? ?; eapply V_C_transitive; eauto. Qed.

Global Instance C_trans {n: nat} (B: comptype): Transitive (@C B n).
Proof. intros ? ? ?; eapply V_C_transitive; eauto. Qed.

Global Instance E_trans {n: nat} (B: comptype): Transitive (E' (@C B n) ).
Proof. intros ? ? ?; eapply E_transitive; eauto. Qed.

Global Instance G_trans {n m: nat} (Gamma: ctx n): Transitive (@G n Gamma m).
Proof. intros ? ? ?; eapply G_transitive; eauto. Qed.

Global Instance val_semeq_trans {n: nat} (Gamma: ctx n) (A: valtype): Transitive (val_semeq Gamma A).
Proof. intros ? ? ?; eapply val_semeq_transitive; eauto. Qed.

Global Instance comp_semeq_trans {n: nat} (Gamma: ctx n) (B: comptype): Transitive (comp_semeq Gamma B).
Proof. intros ? ? ?; eapply comp_semeq_transitive; eauto. Qed.





(** Logical Equivalenced under expansion *)
Lemma closure_under_expansion n (c1 c1' c2 c2': comp n) B:
  c1 >* c1' -> c2 >* c2' -> E B c1' c2' -> E B c1 c2.
Proof.
  intros; destruct H1; split; intuition.
  all: intros s ?.
  1: assert (c1' ▷ s).
  3: assert (c2' ▷ s).
  1, 3: eapply eval_bigstep in H3 as [];
      eapply eval_bigstep; split; eauto;
      eapply nf_normal in H4 as H5;
      eapply confluence_normal_left; eauto.
  edestruct H1; intuition eauto.
  edestruct H2; intuition eauto.
Qed.

Lemma closure_under_reduction n (c1 c1' c2 c2': comp n) B:
  c1 >* c1' -> c2 >* c2' -> E B c1 c2 -> E B c1' c2'.
Proof.
  intros; destruct H1; split; intuition.
  - intros t ?.
    assert (c1 ▷ t) by eauto.
    destruct (H1 _ H4); intuition.
    exists x; intuition.
    specialize (confluence_steps H0 (bigstep_soundness H6)) as [].
    assert (nf x) by (eapply bigstep_normal; eauto).
    enough (x0 = x) as -> by (apply eval_bigstep; split; eauto).
    inv H8. reflexivity.
    exfalso. eapply nf_normal; eauto.
  - intros t ?.
    assert (c2 ▷ t) by eauto.
    destruct (H2 _ H4); intuition.
    exists x; intuition.
    specialize (confluence_steps H (bigstep_soundness H6)) as [].
    assert (nf x) by (eapply bigstep_normal; eauto).
    enough (x0 = x) as -> by (apply eval_bigstep; split; eauto).
    inv H8. reflexivity.
    exfalso. eapply nf_normal; eauto.
Qed.



Lemma subrel_C_E {n: nat} B:
  subrelation (@C B n) (E' (@C B n)).
Proof.
  induction B; intros x y H;
    cbn in H; exintuition; subst; cbn; unfold E', Simulation, Inverse.
  all: split; intros ? H0; inv H0; eexists; split; eauto.
  all: unfold E, Simulation, Inverse in *; intuition.
  all: do 4 eexists; intuition.
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

Lemma bind {n: nat} (K1 K2: @ectx n)  B B' c1 c2:
  E B' c1 c2 ->
  (forall c1 c2, C B' c1 c2 -> E B (fill K1 c1) (fill K2 c2)) ->
  E B (fill K1 c1) (fill K2 c2).
Proof.
  intros; split; intros ? ? % ectx_decompose.
  all: exintuition; destruct H.
  - specialize (H _ H2); exintuition.
    edestruct H0; eauto.
    specialize (H _ H3).
    exintuition.
    eexists; split; eauto.
    eapply ectx_compose; eauto.
  - specialize (H1 _ H2); exintuition.
    edestruct H0; eauto.
    specialize (H6 _ H3).
    exintuition.
    eexists; split; eauto.
    eapply ectx_compose; eauto.
Qed.



Lemma groundtypes_are_simple:
  forall (G: groundtype) n (v1 v2: value n), V G v1 v2 -> v1 = v2.
Proof.
  intros G; induction G; cbn; intuition.
  - congruence.
  - destruct H as (v1' & v2' & [] & -> & -> & ?); f_equal; eauto.
  - destruct H as (v1' & v1'' & v2' & v2'' & -> & -> & ? & ?); f_equal; eauto.
Qed.


Section CompatibilityLemmas.

  Variable (A A1 A2: valtype) (B B1 B2: comptype)
           (n: nat) (v1 v2 v1' v2': value n)
           (c1 c1' c2 c2': comp n)
           (c3 c4 c5 c6: comp (S n))
           (c7 c8: comp (S (S n))).
  Lemma congruence_u:
    @V one n u u.
  Proof.
    cbn; intuition.
  Qed.

  Lemma congruence_pair:
    V A1 v1 v1' -> V A2 v2 v2' -> V (A1 * A2) (pair  v1 v2) (pair v1' v2').
  Proof.
    intros ; do 4 eexists; intuition.
  Qed.

  Lemma congruence_inj (b: bool):
    V (if b then A1 else A2) v1 v2 -> V (Sigma A1 A2) (inj b v1) (inj b v2).
  Proof.
    destruct b; cbn; do 3 eexists; intuition.
  Qed.


  Lemma congruence_thunk:
    E B c1 c2 -> V (U B) (<{ c1 }>) (<{ c2 }>).
  Proof.
    intros H; do 2 eexists; intuition.
  Qed.


  Lemma congruence_cu:
    E cone (@cu n) cu.
  Proof.
    eapply subrel_C_E; cbn; intuition.
  Qed.

  Lemma congruence_force:
    V (U B) v1 v2 -> E B (v1 !) (v2 !).
  Proof.
    intros (? & ? & ?); intuition; subst.
    eapply closure_under_expansion; try reduce; try reflexivity; eauto.
  Qed.


  Lemma congruence_lambda:
    (forall v v', V A v v' -> E B (c3[v..]) (c4[v'..])) -> (E (A → B) (lambda c3) (lambda c4)).
  Proof.
    intros H; eapply subrel_C_E; cbn; do 2 eexists; intuition.
  Qed.

  Lemma congruence_app:
    E (A → B) c1 c2 -> V A v1 v2 -> E B (c1 v1) (c2 v2).
  Proof.
    intros.
    eapply bind with (K1 := ectxApp ectxHole _) (K2 := ectxApp ectxHole _); eauto.
    clear c1 c2 H. intros c1 c2 (? & ? & ?); intuition; subst; cbn.
    eapply closure_under_expansion; try reduce; try reflexivity.
    now apply H3.
  Qed.

  Lemma congruence_tuple:
    E B1 c1 c1' -> E B2 c2 c2' -> E (Pi B1 B2) (tuple c1 c2) (tuple c1' c2').
  Proof.
    intros.
    eapply subrel_C_E. do 4 eexists; intuition.
  Qed.

  Lemma congruence_ret:
    V A v1 v2 -> E (F A) (ret v1) (ret v2).
  Proof.
    intros; eapply subrel_C_E; do 2 eexists; intuition.
  Qed.

  Lemma congruence_letin:
    E (F A) c1 c2 -> (forall v v', V A v v' -> E B (c3[v..]) (c4[v'..])) ->
    E B ($ <- c1; c3) ($ <- c2; c4).
  Proof.
    intros.
    eapply bind with (K1 := ectxLetin ectxHole _) (K2 := ectxLetin ectxHole _);
      eauto.
    clear c1 c2 H.
    intros c1 c2 (? & ? & ?); intuition; subst; cbn.
    eapply closure_under_expansion; try reduce; try reflexivity.
    now eapply H0.
  Qed.


  Lemma congruence_eagerlet:
    E (F A) c1 c2 -> (forall v v', V A v v' -> E B (c3[v..]) (c4[v'..])) ->
    E B ($$ <- c1; c3) ($$ <- c2; c4).
  Proof.
    intros.
    eapply closure_under_reduction.
    eapply let_to_eagerlet.
    eapply let_to_eagerlet.
    eapply congruence_letin; eauto.
  Qed.


  Lemma congruence_proj (b: bool):
    E (Pi B1 B2) c1 c2 -> E (if b then B1 else B2) (proj b c1) (proj b c2).
  Proof.
    intros; eapply bind with (K1 := ectxProj b ectxHole)
                             (K2 := ectxProj b ectxHole); eauto.
    clear c1 c2 H; intros c1 c2 (? & ? & ? & ? & ?).
    intuition; subst; cbn; destruct b;
      eapply closure_under_expansion; try reduce; try reflexivity; eauto.
  Qed.


  Lemma congruence_caseZ :
    V zero v1 v2 -> E B (caseZ v1) (caseZ v2).
  Proof.
    intros [].
  Qed.

  Lemma congruence_caseS:
    V (Sigma A1 A2) v1 v2 ->
    (forall v v', V A1 v v' -> E B (c3[v..]) (c4[v'..])) ->
    (forall v v', V A2 v v' -> E B (c5[v..]) (c6[v'..])) ->
    E B (caseS v1 c3 c5) (caseS v2 c4 c6).
  Proof.
    intros (? & ? & b & ?); intuition; subst.
    destruct b; eapply closure_under_expansion; try reduce; try reflexivity;
      eauto.
  Qed.


  Lemma congruence_caseP:
    V (A1 * A2) v1 v2 ->
    (forall v1 v1' v2 v2', V A1 v1 v1' -> V A2 v2 v2' -> E B (c7[v2,v1..]) (c8[v2',v1'..])) ->
    E B (caseP v1 c7) (caseP v2 c8).
  Proof.
    intros (? & ? & ? & ? & ?); intuition; subst.
    eapply closure_under_expansion; try reduce; try reflexivity;
      eauto.
  Qed.


End CompatibilityLemmas.



(** Lemma used in the next proof *)
Lemma G_cons n m A v1 v2 Gamma (gamma gamma': fin n -> value m):
  V A v1 v2 -> G Gamma gamma gamma' -> G (A .: Gamma) (v1 .: gamma) (v2 .: gamma').
Proof.
  intros; intros []; eauto.
  intros ? <-; cbn; eauto.
Qed.

Hint Resolve G_cons.


Ltac apply_congruence :=
  eapply congruence_u ||
  eapply congruence_pair ||
  eapply congruence_inj ||
  eapply congruence_thunk ||
  eapply congruence_cu ||
  eapply congruence_force ||
  eapply congruence_lambda ||
  eapply congruence_app ||
  eapply congruence_tuple ||
  eapply congruence_ret ||
  eapply congruence_letin ||
  eapply congruence_proj ||
  eapply congruence_caseZ ||
  eapply congruence_caseS ||
  eapply congruence_caseP.

Ltac inject :=
  repeat match goal with
  | [H: ?C _ = ?C _ |- _] => injection H as ->
  | [H: ?C _ _ = ?C _ _ |- _] => injection H as -> ->
  | [H: ?C _ _ _ = ?C _ _ _ |- _] => injection H as -> -> ->
  | [H: ?C _ _ _ _ = ?C _ _ _ _ |- _] => injection H as -> -> -> ->
  | [H: ?C _ _ _ _ _ = ?C _ _ _ _ _ |- _] => injection H as -> -> -> -> ->
  end.






(** *** Fundamental Property *)
(** Syntactically welltyped terms are semantically equivialent to themselves *)
Lemma fundamental_property n:
  (forall (v: value n) (Gamma: ctx n) (A: valtype), Gamma ⊩ v : A -> Gamma ⊫ v ∼ v : A) /\
  (forall (c: comp n) (Gamma: ctx n) (B: comptype), Gamma ⊢ c : B -> Gamma ⊨ c ∼ c : B).
Proof.
  revert n; eapply mutind_val_comp; intros; invt; intros m gamma gamma' H';
    cbn [subst_value subst_comp]; eauto.
  all: apply_congruence.
  all: try solve [eapply H || eapply H0; eauto].
  all: intros; asimpl.
  all: eapply H || eapply H0 || eapply H1; eauto.
Qed.

Lemma fundamental_property_value n m
      (v: value n) (Gamma: ctx n) (A: valtype) (gamma gamma': fin n -> value m):
  Gamma ⊩ v : A -> G Gamma gamma gamma' -> V A v[gamma] v[gamma'].
Proof.  destruct (fundamental_property n); intros; eapply H; eauto. Qed.

Lemma fundamental_property_comp n m (c: comp n) (Gamma: ctx n) (B: comptype)  (gamma gamma': fin n -> value m):
  Gamma ⊢ c : B ->  G Gamma gamma gamma' -> E B c[gamma] c[gamma'].
Proof. destruct (fundamental_property n); intros; eapply H0; eauto.  Qed.


Hint Resolve fundamental_property_comp fundamental_property_value.


(** *** Logical Equivalence  *)

(** Automation for the next proof *)
Ltac semeq :=
  match goal with
     | [H: ?Gamma ⊢ ?C : ?B |- _] => is_var Gamma; eapply fundamental_property_comp in H; eauto
     | [H: ?Gamma ⊩ ?V : ?A |- _] => is_var Gamma; eapply fundamental_property_value in H; eauto
     | [H1: ?A .: ?Gamma ⊨ ?C1 ∼ ?C2 : ?B |- _] =>
       match goal with
         [H2: V ?A ?V1 ?V2 |- _] =>
         match goal with
           [H3: G ?Gamma ?gamma ?gamma' |- _] => specialize (H1 _ _ _ (G_cons _ _ _ H2 H3))                              
         end
       end
     | [H1: forall v1 v2, ?Gamma ⊫ v1 ∼ v2 : ?A -> _ |- _] =>
       match goal with
         [H2: ?Gamma ⊫ ?V1 ∼ ?V2 : ?A |- _] => specialize (H1 _ _ H2)
       end
     | [H1: ?Gamma ⊫ ?V1 ∼ ?V2 : ?A |- _] =>
       match goal with
         [H2: G ?Gamma ?gamma ?gamma' |- _] => specialize (H1 _ _ _ H2)
       end
     | [H1: forall c1 c2, ?Gamma ⊨ c1 ∼ c2 : ?B -> _ |- _] =>
       match goal with
         [H2: ?Gamma ⊨ ?C1 ∼ ?C2 : ?B |- _] => specialize (H1 _ _ H2)
       end
     | [H1: ?Gamma ⊨ ?C1 ∼ ?C2 : ?B |- _] =>
       match goal with
         [H2: G ?Gamma ?gamma ?gamma' |- _] => specialize (H1 _ _ _ H2)
       end
     end.


Ltac semeq_solve := repeat progress semeq; eauto.


Ltac expand :=
  eapply closure_under_expansion; try (reduce; reflexivity).


(** Logical Equivalence under context filling *)
Lemma logical_equivalence_congruent:
  forall m t (Gamma: ctx m),
    (forall n Delta (C: vctx t m n) A' A,
        Gamma[[Delta]] ⊩ C : A'; A ->
        match t return (if t then valtype else comptype) -> vctx t m n -> Prop with
        | true => fun A C => forall v1 v2, Delta ⊫ v1 ∼ v2 : A -> Gamma ⊫ fillv C v1 ∼ fillv C v2 : A'
        | false => fun B C => forall c1 c2, Delta ⊨ c1 ∼ c2 : B -> Gamma ⊫ fillv C c1 ∼ fillv C c2 : A'
        end A C
    ) /\
    (forall n Delta (C: cctx t m n) A' A,
        Gamma[[Delta]] ⊢ C : A'; A ->
        match t return (if t then valtype else comptype) -> cctx t m n -> Prop with
        | true => fun A C => forall v1 v2, Delta ⊫ v1 ∼ v2 : A -> Gamma ⊨ fillc C v1 ∼ fillc C v2 : A'
        | false => fun B C => forall c1 c2, Delta ⊨ c1 ∼ c2 : B -> Gamma ⊨ fillc C c1 ∼ fillc C c2 : A'
        end A C).
Proof.
  eapply (mutind_vctx_cctx_typing); intros; destruct t; cbn; intros; eauto;
    intros p gamma gamma' H'; cbn [subst_value subst_comp]; intuition eauto.
  all: apply_congruence.
  all: try solve [semeq_solve].
  all: intros; asimpl.
  all: try solve [eapply H; eauto].
  1, 2, 3, 5, 9, 10, 11, 12: eapply fundamental_property_comp in X0; eauto.
  all: eapply fundamental_property_comp in X1; eauto.
Qed.

Lemma logical_equivalence_congruent_vctx_value m (Gamma: ctx m)  n Delta (C: vctx true m n) A' A:
  Gamma[[Delta]] ⊩ C : A'; A ->  forall v1 v2, Delta ⊫ v1 ∼ v2 : A -> Gamma ⊫ fillv C v1 ∼ fillv C v2 : A'.
Proof.
  intros; eapply (logical_equivalence_congruent true); eauto.
Qed.

Lemma logical_equivalence_congruent_vctx_comp  m (Gamma: ctx m)  n Delta (C: vctx false m n) A' B:
  Gamma[[Delta]] ⊩ C : A'; B ->  forall c1 c2, Delta ⊨ c1 ∼ c2 : B -> Gamma ⊫ fillv C c1 ∼ fillv C c2 : A'.
Proof.
  intros; eapply (logical_equivalence_congruent false); eauto.
Qed.

Lemma logical_equivalence_congruent_cctx_value  m (Gamma: ctx m)  n Delta (C: cctx true m n) A B:
  Gamma[[Delta]] ⊢ C : B; A -> forall v1 v2, Delta ⊫ v1 ∼ v2 : A -> Gamma ⊨ fillc C v1 ∼ fillc C v2 : B.
Proof.
  intros; eapply (logical_equivalence_congruent true); eauto.
Qed.

Lemma logical_equivalence_congruent_cctx_comp m (Gamma: ctx m)  n Delta (C: cctx false m n) B B':
  Gamma[[Delta]] ⊢ C : B'; B -> forall c1 c2, Delta ⊨ c1 ∼ c2 : B -> Gamma ⊨ fillc C c1 ∼ fillc C c2 : B'.
Proof.
  intros; eapply (logical_equivalence_congruent false); eauto.
Qed.


(** ** Logical Equivalences *)
(** Semantically equivalent terms are observationally equivalent *)
Lemma logical_equivalence_obseq (n: nat) (Gamma: ctx n):
  (forall (A: valtype)  (v1 v2: CBPVv Gamma A), Gamma ⊫ v1 ∼ v2 : A -> v1 ≈ v2) /\
  (forall (B: comptype) (c1 c2: CBPVc Gamma B), Gamma ⊨ c1 ∼ c2 : B -> c1 ≃ c2).
Proof.
  split; intros; intros G C H' v;
    [
      specialize (logical_equivalence_congruent_cctx_value) as sem_sound |
      specialize (logical_equivalence_congruent_cctx_comp) as sem_sound
    ]; specialize (sem_sound _ _ _ _ _ _ _ H' _ _ H 0 null null);
      mp sem_sound; try intros [];
        do 2 rewrite idSubst_comp in sem_sound; try intros [].
  all: destruct sem_sound.
  all: assert (nf (ret v)) by eauto.
  all: split; intros; eapply bigstep_soundness.
  1: assert (fillc C v1 ▷ ret v) as H4 by (eapply eval_bigstep; split; eauto).
  2: assert (fillc C v2 ▷ ret v) as H4 by (eapply eval_bigstep; split; eauto).
  4: assert (fillc C c2 ▷ ret v) as H4 by (eapply eval_bigstep; split; eauto).
  1, 3: edestruct H0; intuition eauto.
  3, 4: edestruct H1; intuition eauto.
  all: cbn in *; exintuition; subst; inject.
  now rewrite (groundtypes_are_simple _ _ _ H9).
  now rewrite (groundtypes_are_simple _ _ _ H8).
  now rewrite <-(groundtypes_are_simple _ _ _ H9).
  now rewrite <-(groundtypes_are_simple _ _ _ H9).
Qed.



(** ** Reduction contained in equivalence *)
(** *** Reduction is contained in logical equivalence **)
Lemma logical_equivalence_primitive_reduction n (Gamma: ctx n) c c' B:
  c ≽ c' -> Gamma ⊢ c : B -> Gamma ⊨ c ∼ c' : B.
Proof.
  intros H1 H2 m gamma gamma' H3.
  destruct(fundamental_property n) as [_ H].
  specialize (H c Gamma B H2 m gamma gamma' H3).
  split; intros ?; destruct H.
  - intros ? % H; exintuition; eexists; intuition eauto.
    eapply eval_bigstep; split; eapply eval_bigstep in H5 as []; intuition.
    assert (c[gamma'] ≽ c'[gamma']) as H7 % stepPrimitive
        by now eapply pstep_subst.
    inv H4.
    + eapply nf_normal in H5; firstorder.
    + now rewrite (step_functional H7 H8).
  - intros ?. eapply H0.
    eapply bigstep_primitive_cons; eauto.
    now eapply pstep_subst.
Qed.

Lemma logical_equivalence_weak_reduction n (Gamma: ctx n) c c' B:
  c > c' -> Gamma ⊢ c : B -> Gamma ⊨ c ∼ c' : B.
Proof.
  intros; intros m gamma gamma' H'.
  induction H in B, X |-*.
  1: eapply logical_equivalence_primitive_reduction; eauto.
  all: invt; specialize (IHstep _ X0); clear X0; semeq_solve; cbn.
  all: apply_congruence; eauto.
  intros; asimpl; eauto.
Qed.

Lemma logical_equivalence_strong_reduction n (Gamma: ctx n) c c' B:
  c ↪ c' -> Gamma ⊢ c : B -> Gamma ⊨ c ∼ c' : B.
Proof.
  intros [] % sstep_lemma
         (Delta & C & H1 & H2) % context_typing_decomposition_cctx_comp.
  eapply logical_equivalence_congruent_cctx_comp; eauto.
  eapply logical_equivalence_primitive_reduction; eauto.
Qed.

Lemma logical_equivalence_strong_reduction_value n (Gamma: ctx n) v v' A:
  v ↪ᵥ v' -> Gamma ⊩ v : A -> Gamma ⊫ v ∼ v' : A.
Proof.
  intros [] % sstep_value_lemma
         (Delta & C & H1 & H2) % context_typing_decomposition_vctx_comp.
  eapply logical_equivalence_congruent_vctx_comp; eauto.
  eapply logical_equivalence_primitive_reduction; eauto.
Qed.

Lemma logical_equivalence_weak_reduction_steps n (Gamma: ctx n) c c' B:
  c >* c' -> Gamma ⊢ c : B -> Gamma ⊨ c ∼ c' : B.
Proof.
  induction 1.
  - eapply fundamental_property.
  - intros H1. edestruct (preservation H H1).
    transitivity x'; eauto.
    apply logical_equivalence_weak_reduction; eauto.
Qed.


Lemma logical_equivalence_strong_reduction_steps n (Gamma: ctx n) c c' B:
  c ↪* c' -> Gamma ⊢ c : B -> Gamma ⊨ c ∼ c' : B.
Proof.
  induction 1.
  - eapply fundamental_property.
  - intros H1. apply sstep_lemma in H as H2.
    edestruct (strong_step_preservation H2 (inhabited H1)).
    transitivity x'; eauto.
    apply logical_equivalence_strong_reduction; eauto.
Qed.


Lemma logical_equivalence_strong_reduction_value_steps n (Gamma: ctx n) v v' A:
  v ↪ᵥ* v' -> Gamma ⊩ v : A -> Gamma ⊫ v ∼ v' : A.
Proof.
  induction 1.
  - eapply fundamental_property.
  - intros H1. apply sstep_value_lemma in H as H2.
    edestruct (strong_step_value_preservation H2 (inhabited H1)).
    transitivity x'; eauto.
    apply logical_equivalence_strong_reduction_value; eauto.
Qed.


(** *** 2.14 (3) - Reduction is contained in observational equivalence *)

(** Observational equivalence contains primitive steps *)
Lemma obseq_contains_pstep n (Gamma: ctx n) (B: comptype) (c1 c2: CBPVc Gamma B):
  c1 ≽ c2 -> c1 ≃ c2.
Proof.
  intros; eapply logical_equivalence_obseq, logical_equivalence_primitive_reduction; eauto.
Qed.

(** Observational equivalence contains reduction steps *)
Lemma obseq_contains_step n (Gamma: ctx n) (B: comptype) (c1 c2: CBPVc Gamma B):
  c1 > c2 -> c1 ≃ c2.
Proof.
  intros; eapply logical_equivalence_obseq,
          logical_equivalence_weak_reduction; eauto.
Qed.

(** Observational equivalence contains star steps *)
Lemma obseq_contains_steps n (Gamma: ctx n) (B: comptype) (c1 c2: CBPVc Gamma B):
  c1 >* c2 -> c1 ≃ c2.
Proof.
  intros; eapply logical_equivalence_obseq,
          logical_equivalence_weak_reduction_steps; eauto.
Qed.
