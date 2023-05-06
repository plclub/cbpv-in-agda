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

Require Export CBPV.Semantics CBPV.Terms CBPV.SyntacticTyping CBPV.Base CBPV.StrongReduction.
Import CommaNotation.

(** * Strong Semantic Typing *)

(** ** Saturation *)

Definition active {n} (c : comp n) : Prop :=
  match c with
  | cu | ret _ | lambda _ | tuple _ _ => True
  | _ => False
  end.

Definition activev {n} (v : value n) : Prop :=
  match v with var_value _ => False | _ => True end.

Inductive close {n} (C : comp n -> Prop) (c : comp n) : Prop :=
| close_step :
    (active c -> C c) ->
    (forall d, c ⇒ d -> close C d) ->
    close C c.

Inductive closev {n} (V : value n -> Prop) : value n -> Prop :=
| closev_var (i : fin n) : closev V (var_value i)
| closev_V v : V v -> closev V v.

Lemma close_sn n (C : comp n -> Prop) (c : comp n) :
  close C c -> sn c.
Proof. induction 1; constructor; eauto. Qed.

Lemma close_red n (C : comp n -> Prop) (c d : comp n) :
  c ⇒ d -> close C c -> close C d.
Proof. intros ?[]; eauto. Qed.

Lemma close_base n (C : comp n -> Prop) (c : comp n) :
  active c -> close C c -> C c.
Proof. intros ?[]; eauto. Qed.

Lemma closev_base n (V : value n -> Prop) (v : value n) :
  activev v -> closev V v -> V v.
Proof. intros H1 H2. inv H2. contradiction. assumption. Qed.

Lemma close_ren (C : forall n, comp n -> Prop) :
  (forall m n (f : fin m -> fin n) (c : comp m), C m c -> C n c⟨f⟩) ->
  (forall m n (f : fin m -> fin n) (c : comp m), close (C m) c -> close (C n) c⟨f⟩).
Proof.
  intros H1 m n f c. induction 1 as [c H2 H3 ih]. constructor.
  - intros H4. apply H1. apply H2. destruct c; cbn in *; eauto.
  - intros d H4. destruct (strong_step_anti_renaming _ _ H4) as [d' H5 H6]; subst d. now apply ih.
Qed.

Lemma closev_ren (V : forall n, value n -> Prop) :
  (forall m n (f : fin m -> fin n) (v : value m), V m v -> V n (ren_value f v)) ->
  (forall m n (f : fin m -> fin n) (v : value m), closev (V m) v -> closev (V n) v⟨f⟩).
Proof.
  intros H1 m n f c H2. inv H2. constructor. constructor. now apply H1.
Qed.

(** ** Semantic Types *)

Fixpoint V {n: nat} (A: valtype) (v: value n) :=
  match A with
  | zero =>
    False
  | one =>
    match v with u => True | _ => False end
  | U B =>
    match v with <{ c }> => close (C B) c | _ => False end
  | Sigma A1 A2 =>
    match v with inj b v' => closev (V (if b then A1 else A2)) v' | _ => False end
  | A1 * A2 =>
    match v with pair v1 v2 => closev (V A1) v1 /\ closev (V A2) v2 | _ => False end
  end

with C {n: nat} (B: comptype) (c: comp n) :=
  match B with
  | cone =>
    match c with cu => True | _ => False end
  | F A =>
    match c with ret v => closev (V A) v | _ => False end
  | Pi B1 B2 =>
    match c with tuple c1 c2 => close (C B1) c1 /\ close (C B2) c2 | _ => False end
  | A → B =>
    match c with
    | lambda c' => forall k (f : fin n -> fin k) (v : value k),
        closev (V A) v -> close (C B) (c'[v, f >> ids])
    | _ => False
    end
  end.

Notation E B c := (close (C B) c).
Notation VV A v := (closev (V A) v).

Definition G  {n m: nat} (Gamma : ctx n) (gamma: fin n -> value m) :=
 forall i, VV (Gamma i) (gamma i).

Definition val_semtype {n: nat} (Gamma: ctx n) (v: value n) (A: valtype) :=
  forall m (gamma: fin n -> value m), G Gamma gamma -> VV A (subst_value gamma v).

Notation "Gamma ⊫ v ::: A" := (val_semtype Gamma v A) (at level 80).

Definition comp_semtype {n: nat} (Gamma: ctx n) (c: comp n) (B: comptype) :=
  forall m (gamma: fin n -> value m), G Gamma gamma -> E B (subst_comp gamma c).

Notation "Gamma ⊨ c ::: B" := (comp_semtype Gamma c B) (at level 80).


(** *** Properties of Semantic Types **)

(** The logical relation is closed under renaming. *)

Lemma VC_ren :
  (forall (A : valtype), forall m n (f : fin m -> fin n) (v : value m),
        V A v -> V A v⟨f⟩) /\
  (forall (A : comptype), forall m n (f : fin m -> fin n) (c : comp m),
        C A c -> C A c⟨f⟩).
Proof.
  apply mutind_valtype_comptype.
  - now eauto.
  - intros m n f []; now eauto.
  - intros A ih m n f []; cbn; eauto. revert m n f c.
    apply close_ren. exact ih.
  - intros A ihA B ihB m n f []; cbn; eauto. revert m n f v.
    apply closev_ren. destruct b. exact ihA. exact ihB.
  - intros A ihA B ihB m n f []; cbn; eauto; intros [L R]. split.
    + clear v0 R. revert m n f v L. apply closev_ren. exact ihA.
    + clear v L. revert m n f v0 R. apply closev_ren. exact ihB.
  - intros m n f []; cbn; now eauto.
  - intros A ih m n f []; cbn; eauto. revert m n f v.
    apply closev_ren. exact ih.
  - intros A ihA B ihB m n f []; cbn; eauto; intros [L R]. split.
    + clear c0 R. revert m n f c L. apply close_ren. exact ihA.
    + clear c L. revert m n f c0 R. apply close_ren. exact ihB.
  - intros A ihA B ihB m n f []; cbn; eauto; intros H k g v Hv.

    asimpl.
    now apply H.
Qed.

Lemma VV_ren m n (f : fin m -> fin n) (v : value m) (A : valtype) :
  VV A v -> VV A v⟨f⟩.
Proof.
  revert m n f v. apply closev_ren. destruct VC_ren as [H _]. apply H.
Qed.

Lemma E_ren m n (f : fin m -> fin n) (c : comp m) (A : comptype) :
  E A c -> E A c⟨f⟩.
Proof.
  revert m n f c. apply close_ren. destruct VC_ren as [_ H]. apply H.
Qed.

(** G is closed under context extension *)

Lemma VV_var n (A : valtype) (i : fin n) :
  VV A (ids i).
Proof. constructor. Qed.

Lemma G_id n (Gamma : ctx n) :
  G Gamma var_value.
Proof.
  intros i. apply VV_var.
Qed.

Lemma G_scons m n (A : valtype) (Gamma : ctx m) (f : fin m -> value n) (v : value n) :
  VV A v -> G Gamma f -> G (A, Gamma) (v, f).
Proof.
  intros Vv Gf. hnf. cbn. intros [i|]; cbn. now apply Gf. exact Vv.
Qed.

Lemma G_ren m n k (Gamma : ctx m) (f : fin m -> value n) (g : fin n -> fin k) :
  G Gamma f -> G Gamma (f >> ⟨g⟩).
Proof.
  intros Gf i. apply VV_ren. apply Gf.
Qed.

Lemma G_ext {m n : nat} (A : valtype) (Gamma : ctx m) (f : fin m -> value n) :
  G Gamma f -> G (A, Gamma) (up_value_value f).
Proof.
  intros H. apply G_scons. now apply VV_var. apply G_ren. exact H.
Qed.

(** ** Induction lemmas for closure *)

Lemma E_ind n (P : comp n -> Prop) A :
  (forall c, E A c -> (forall c', c ⇒ c' -> P c') -> P c) ->
  (forall c, E A c -> P c).
Proof.
  intros H c. induction 1. apply H. now constructor. apply H2.
Qed.

Lemma E_ind2 m n (P : comp m -> comp n -> Prop) A B :
  (forall c1 c2,
      (forall c', c1 ⇒ c' -> P c' c2) ->
      (forall c', c2 ⇒ c' -> P c1 c') ->
      E A c1 -> E B c2 -> P c1 c2) ->
  (forall c1 c2, E A c1 -> E B c2 -> P c1 c2).
Proof.
  intros H c1 c2 Ec1. revert c1 Ec1 c2.
  refine (E_ind _ _ _). intros c1 Ec1 ih1.
  refine (E_ind _ _ _). intros c2 Ec2 ih2.
  apply H; eauto.
Qed.

Lemma V_red_to_VV_red n A :
  (forall (v1 v2 : value n), v1 ⇒ᵥ v2 -> V A v1 -> V A v2) ->
  (forall (v1 v2 : value n), v1 ⇒ᵥ v2 -> VV A v1 -> VV A v2).
Proof.
  intros H v1 v2 st vv. inv vv. destruct (stepv_var_inv st).
  constructor. revert H0. now apply H.
Qed.

Lemma V_red n A (v1 v2 : value n) :
  v1 ⇒ᵥ v2 -> V A v1 -> V A v2.
Proof with try now eauto.
  revert v1 v2. induction A; cbn; intros...
  - destruct v1... destruct (stepv_u_inv H).
  - destruct v1... revert v2 H. apply stepv_thunk_inv. intros c1 st. revert H0. now apply close_red.
  - destruct v1... revert v2 H. apply stepv_inj_inv. intros v2 st.
    revert v1 v2 st H0. apply V_red_to_VV_red. destruct b. exact IHA1. exact IHA2.
  - destruct v1... destruct H0. revert v2 H. apply stepv_pair_inv.
    + intros v' st. split... revert v' st H0. apply V_red_to_VV_red. exact IHA1.
    + intros v' st. split... revert v' st H1. apply V_red_to_VV_red. exact IHA2.
Qed.

Lemma VV_red n A (v1 v2 : value n) :
  v1 ⇒ᵥ v2 -> VV A v1 -> VV A v2.
Proof.
  revert v1 v2. apply V_red_to_VV_red. apply V_red.
Qed.

Lemma V_sn_to_VV_sn n A :
  (forall (v : value n), V A v -> snv v) ->
  (forall (v : value n), VV A v -> snv v).
Proof.
  intros H v []. constructor. intros v' st. destruct (stepv_var_inv st). now apply H.
Qed.

Lemma V_sn n A (v : value n) :
  V A v -> snv v.
Proof with try contradiction.
  revert v. induction A; cbn; intros...
  - destruct v... constructor. intros v st. destruct (stepv_u_inv st).
  - destruct v... apply close_sn in H. induction H. constructor.
    apply stepv_thunk_inv. apply H0.
  - destruct v... assert (snv_v : snv v). revert v H. apply V_sn_to_VV_sn. now destruct b.
    clear H. induction snv_v. constructor. apply stepv_inj_inv. apply H0.
  - destruct v... destruct H.
    assert (snv_v1 : snv v1). revert v1 H. now apply V_sn_to_VV_sn.
    assert (snv_v2 : snv v2). revert v2 H0. now apply V_sn_to_VV_sn.
    clear A1 A2 IHA1 IHA2 H H0. revert v2 snv_v2. induction snv_v1 as [v1 _ ih1].
    intros v2 snv_v2. induction snv_v2 as [v2 sn2 ih2]. constructor. apply stepv_pair_inv.
    intros. apply ih1; auto. constructor; now eauto. now apply ih2.
Qed.

Lemma VV_sn n A (v : value n) :
  VV A v -> snv v.
Proof.
  apply V_sn_to_VV_sn. intros v'. apply V_sn.
Qed.

(** ** Semantic Soundness *)

(** *** Compatibility lemmas *)
Section CompatibilityLemmas.
  Variables (n : nat) (A A1 A2 : valtype) (B B1 B2 : comptype).

  Lemma compat_pair_E (v1 v2 : value n) :
    VV A1 v1 -> VV A2 v2 -> VV (A1 * A2) (pair v1 v2).
  Proof.
    intros H1 H2. constructor. now split.
  Qed.

  Lemma compat_sum_E (b : bool) (v : value n) :
    VV (if b then A1 else A2) v -> VV (Sigma A1 A2) (inj b v).
  Proof.
    intros H. constructor. exact H.
  Qed.

  Lemma compat_thunk_E (c : comp n) :
    E B c -> VV (U B) <{ c }>.
  Proof.
    revert c. apply E_ind. intros c Ec ih. hnf. cbn. constructor. exact Ec.
  Qed.

  Lemma compat_lambda_E (c : comp (S n)) :
    sn c ->
    (forall k (f : fin n -> fin k) (v : value k),
        VV A v -> E B (subst_comp (v .: f >> var_value) c)) ->
    E (A → B) (lambda c).
  Proof.
    induction 1 as [c _ ih]. intros H. constructor.
    - cbn. intros _ k f v Vv. apply H. exact Vv.
    - apply step_lambda_inv. intros c' st. apply ih. assumption.
      intros k f v Vv. specialize (H _ f _ Vv). revert H. apply close_red.
      apply strong_step_subst. exact st.
  Qed.

  Lemma compat_letin_E (c1 : comp n) c2 :
    E (F A) c1 -> sn c2 -> (forall v, VV A v -> E B (c2[v..])) ->
    E B ($ <- c1; c2).
  Proof.
    intros Ec1. revert c1 Ec1 c2. refine (E_ind _ _ _).
    intros c1 Ec1 ih1 c2. induction 1 as [c2 snc2 ih2]. intros H.
    constructor. contradiction. apply step_letin_inv.
    - intros v E. subst c1. apply H. revert Ec1. now apply close_base.
    - intros c' st. apply ih1; auto. constructor. exact snc2.
    - intros c' st. apply ih2; auto. intros v Vv. generalize (H v Vv).
      apply close_red. apply strong_step_subst. exact st.
  Qed.

  Lemma compat_ret_E (v : value n) :
    VV A v -> E (F A) (ret v).
  Proof.
    intros vv. generalize (VV_sn A vv). intros snv_v. induction snv_v.
    constructor. intros _. apply vv. apply step_ret_inv. intros v' st.
    apply H0. exact st. now apply (VV_red _ st).
  Qed.

  Lemma compat_app_E (c : comp n) v :
    E (A → B) c -> VV A v -> E B (app c v).
  Proof.
    intros Ec. revert c Ec v. refine (E_ind _ _ _).
    intros c Ec ih1 v vv. induction (VV_sn _ vv).
    constructor. contradiction. apply step_app_inv.
    - intros; subst. apply (close_base (I : active (lambda b)) Ec _ _ x vv).
    - intros. now apply ih1.
    - intros. apply H0; auto. revert vv. now apply VV_red.
  Qed.

  Lemma compat_tuple_E (c1 c2 : comp n) :
    E B1 c1 -> E B2 c2 -> E (Pi B1 B2) (tuple c1 c2).
  Proof.
    revert c1 c2. refine (E_ind2 _ _ _ _). intros c1 c2 ih1 ih2 e1 e2. constructor.
    - cbn. intros _. split. exact e1. exact e2.
    - apply step_tuple_inv. exact ih1. exact ih2.
  Qed.

  Lemma compat_proj_E (b : bool) (c : comp n) :
    E (Pi B1 B2) c -> E (if b then B1 else B2) (proj b c).
  Proof.
    revert c. refine (E_ind _ _ _). intros c Ec ih. constructor. contradiction.
    apply step_proj_inv.
    - intros; subst. apply close_base in Ec; try exact I. destruct Ec as [H1 H2]. now destruct b.
    - exact ih.
  Qed.

  Lemma compat_force_E (v : value n) :
    VV (U B) v -> E B (v !).
  Proof.
    intros vv. induction (VV_sn _ vv). constructor. contradiction.
    apply step_force_inv.
    - intros c E. subst. apply closev_base in vv. assumption. exact I.
    - intros. apply H0; auto. revert vv. now apply VV_red.
  Qed.

  Lemma compat_caseZ_E (v : value n) :
    VV zero v -> E B (caseZ v).
  Proof.
    intros vv. induction (VV_sn _ vv). constructor. contradiction.
    apply step_caseZ_inv. intros. apply H0; auto. revert vv. now apply VV_red.
  Qed.

  Lemma compat_caseS_E (v : value n) c1 c2 :
    VV (Sigma A1 A2) v ->
    sn c1 -> sn c2 ->
    (forall v', VV A1 v' -> E B (c1[v'..])) ->
    (forall v', VV A2 v' -> E B (c2[v'..])) ->
    E B (caseS v c1 c2).
  Proof.
    intros vv. revert c1 c2. induction (VV_sn _ vv) as [v _ ih1].
    intros c1 c2 snc1. revert c2. induction snc1 as [c1 snc1 ih2].
    intros c2 snc2. induction snc2 as [c2 snc2 ih3]. intros HL HR.
    constructor. contradiction. apply step_caseS_inv.
    - intros b v' E; subst. apply closev_base in vv. cbn in *.
      destruct b. now apply HL. now apply HR. exact I.
    - intros v' st. apply ih1; eauto; try now (constructor; eauto).
      revert vv. now apply VV_red.
    - intros c' st. apply ih2; auto. constructor; assumption.
      intros v' Vv'. generalize (HL v' Vv'). apply close_red.
      apply strong_step_subst. exact st.
    - intros c' st. apply ih3; auto. intros v' Vv'.
      generalize (HR v' Vv'). apply close_red.
      apply strong_step_subst. exact st.
  Qed.

  Lemma compat_caseP_E (v : value n) c :
    VV (A1 * A2) v ->
    sn c ->
    (forall v1 v2, VV A2 v1 -> VV A1 v2 -> E B (c[v1, v2..])) ->
    E B (caseP v c).
  Proof.
    intros Vv. revert c. induction (VV_sn _ Vv) as [v _ ih1]. intros c snc.
    induction snc as [c snc ih2]. intros H. constructor. contradiction.
    apply step_caseP_inv.
    - intros v1 v2 E; subst. apply closev_base in Vv. destruct Vv as [V1 V2].
      apply H. exact V2. exact V1. exact I.
    - intros v' st. apply ih1; auto. revert Vv. now apply VV_red. constructor; eauto.
    - intros c' st. apply ih2; auto. intros v1 v2 V1 V2. generalize (H v1 v2 V1 V2).
      apply close_red. apply strong_step_subst. exact st.
  Qed.
End CompatibilityLemmas.

(** *** Typing Lemmas  *)
Section TypingLemmas.

  Variable (n: nat) (Gamma: ctx n) (A A1 A2: valtype) (B B1 B2: comptype).

  Lemma compat_var i : Gamma ⊫ var_value i ::: Gamma i.
  Proof. intros k gamma H. now apply H. Qed.

  Lemma compat_unit : Gamma ⊫ u ::: one.
  Proof.
    intros k f Hf. constructor; cbn; auto; intros v' st.
  Qed.

  Lemma compat_pair v1 v2:
    Gamma ⊫ v1 ::: A1 -> Gamma ⊫ v2 ::: A2 -> Gamma ⊫ pair v1 v2 ::: cross A1 A2.
  Proof.
    intros H1 H2 k gamma H. asimpl. apply compat_pair_E. now apply H1. now apply H2.
  Qed.

  Lemma compat_sum (b: bool) v:
    Gamma ⊫ v ::: (if b then A1 else A2) -> Gamma ⊫ inj b v ::: Sigma A1 A2.
  Proof.
    intros H1 k gamma H. asimpl. apply compat_sum_E. now apply H1.
  Qed.

  Lemma compat_thunk c:
    Gamma ⊨ c ::: B -> Gamma ⊫ thunk c ::: U B.
  Proof.
    intros H1 k gamma H. asimpl. apply compat_thunk_E. now apply H1.
  Qed.

  Lemma compat_cone : Gamma ⊨ cu ::: cone.
  Proof.
    intros m gamma H. constructor. trivial.
    cbn. intros d st. destruct (step_cu_inv st).
  Qed.

  Lemma compat_lambda c:
    A .: Gamma ⊨ c ::: B -> Gamma ⊨ lambda c ::: A → B.
  Proof.
    intros H' m gamma H. asimpl. apply compat_lambda_E.
    - specialize (H' _ _ (G_ext _ H)). apply close_sn in H'.
      now asimpl in H'.
    - intros k f v Vv. asimpl. apply H'. apply G_scons. exact Vv.
      intros i. rewrite <-rinstInst_value. apply G_ren. exact H.
  Qed.

  Lemma compat_letin c1 c2:
    Gamma ⊨ c1 ::: F A -> A .: Gamma ⊨ c2 ::: B -> Gamma ⊨ $ <- c1; c2 ::: B.
  Proof.
    intros H1 H2 m gamma H3. asimpl. apply (compat_letin_E (A := A)).
    - now apply H1.
    - generalize (H2 _ _ (G_ext A H3)). asimpl. apply close_sn.
    - intros v Vv. asimpl. apply H2. apply G_scons. exact Vv. exact H3.
  Qed.

  Lemma compat_ret v:
    Gamma ⊫ v ::: A -> Gamma ⊨ ret v ::: F A.
  Proof.
    intros H1 m gamma H. asimpl. apply compat_ret_E. now apply H1.
  Qed.

  Lemma compat_app c v:
    Gamma ⊨ c ::: A → B -> Gamma ⊫ v ::: A -> Gamma ⊨ c v ::: B.
  Proof.
    intros H1 H2 m gamma H. asimpl. apply (compat_app_E (A := A)).
    now apply H1. now apply H2.
  Qed.

  Lemma compat_tuple c1 c2:
    Gamma ⊨ c1 ::: B1 -> Gamma ⊨ c2 ::: B2 -> Gamma ⊨ tuple c1 c2 ::: Pi B1 B2.
  Proof.
    intros H1 H2 m gamma H. asimpl. apply compat_tuple_E.
    now apply H1. now apply H2.
  Qed.

  Lemma compat_proj c b:
    Gamma ⊨ c ::: Pi B1 B2 -> Gamma ⊨ proj b c ::: (if b then B1 else B2).
  Proof.
    intros H1 m gamma H. asimpl. apply compat_proj_E. now apply H1.
  Qed.

  Lemma compat_force v:
    Gamma ⊫ v ::: U B -> Gamma ⊨ v! ::: B.
  Proof.
    intros H1 m gamma H. asimpl. apply compat_force_E. now apply H1.
  Qed.

  Lemma compat_caseZ v:
    Gamma ⊫ v ::: zero -> Gamma ⊨ caseZ v ::: B.
  Proof.
    intros H1 m gamma H. asimpl. apply compat_caseZ_E. now apply H1.
  Qed.

  Lemma compat_caseS v c1 c2:
    Gamma ⊫ v ::: Sigma A1 A2 ->
    A1 .: Gamma ⊨ c1 ::: B ->
    A2 .: Gamma ⊨ c2 ::: B ->
    Gamma ⊨ caseS v c1 c2 ::: B.
  Proof.
    intros H' H1 H2 m gamma H; specialize (H' m gamma H). asimpl.
    apply (compat_caseS_E (A1 := A1) (A2 := A2)).
    - assumption.
    - specialize (H1 _ _ (G_ext _ H)). asimpl in H1.  eapply close_sn, H1.
    - specialize (H2 _ _ (G_ext _ H)). asimpl in H2. eapply close_sn, H2.
    - intros v' Vv'.  asimpl. apply H1. now apply G_scons.
    - intros v' Vv'.  asimpl. apply H2. now apply G_scons.
  Qed. 


  Lemma compat_caseP v c:
      Gamma ⊫ v ::: A1 * A2 ->
      A2 .: (A1 .: Gamma) ⊨ c ::: B ->
      Gamma ⊨ caseP v c ::: B.
  Proof.
    intros H' H1 m gamma H; specialize (H' m gamma H). asimpl.
    apply (compat_caseP_E (A1 := A1) (A2 := A2)).
    - exact H'.
    - generalize (H1 _ _ (G_ext _ (G_ext _ H))). asimpl. now apply close_sn.
    - intros v1 v2 V1 V2. asimpl. apply H1. apply G_scons; auto. now apply G_scons.
  Qed.
End TypingLemmas.

Hint Resolve
    compat_var compat_unit compat_pair compat_sum compat_thunk compat_cone
    compat_lambda compat_letin compat_ret compat_app compat_tuple compat_proj
    compat_force compat_caseZ compat_caseS compat_caseP : compatibility_lemmas.

(** *** Semantic Soundness *)
(** Syntactically well typed terms are semantically well typed *)
Theorem SemanticSoundness n (Gamma: ctx n):
  (forall v A, Gamma ⊩ v : A -> Gamma ⊫ v ::: A) /\ (forall c B, Gamma ⊢ c : B -> Gamma ⊨ c ::: B).
Proof.
  eapply mutind_value_computation_typing; eauto with compatibility_lemmas.
Qed.

Theorem strong_normalisation n (Gamma : ctx n) (c : comp n) (B : comptype) :
  Gamma ⊢ c : B -> sn c.
Proof.
  destruct (SemanticSoundness Gamma) as [_ H]. intros HH. apply H in HH.
  specialize (HH _ _ (G_id Gamma)).
  apply close_sn in HH. revert HH. asimpl. intros HH. apply HH.
Qed.
