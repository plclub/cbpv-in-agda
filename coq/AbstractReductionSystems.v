(**
Parts of this file are copied and modified from the Coq Demos 
of the lecture Semantics at Saarland University
http://www.ps.uni-saarland.de/courses/sem-ws17/confluence.v
**)

Set Implicit Arguments.
Require Import Morphisms FinFun Base.

Notation "R <<= S" := (forall x y, R x y -> S x y) (at level 70).
Notation "R === S" := (R <<= S /\ S <<= R) (at level 70).

Section ClosureRelations.
  Variables (X: Type) (R: X -> X -> Prop).
  Implicit Types x y z : X.

  Definition functional := forall x y z, R x y -> R x z -> y = z.

  Inductive star : X -> X -> Prop :=
  | starRefl x     : star x x
  | starStep x x' y : R x x' -> star x' y -> star x y.

  Inductive plus : X -> X -> Prop :=
  | plusSingle x y: R x y -> plus x y
  | plusStep x x' y: R x x' -> plus x' y -> plus x y.

  Inductive counted : nat -> X -> X -> Prop :=
  | countedRefl x: counted 0 x x
  | countedStep x x' y n: R x x' -> counted n x' y -> counted (S n) x y.

  Inductive sym: X -> X -> Prop :=
  | symId x y: R x y -> sym x y 
  | symInv x y: R y x -> sym x y.


  Hint Constructors star plus counted.

  Lemma star_trans x y z :
    star x y -> star y z -> star x z.
  Proof.
    induction 1; eauto.
  Qed.


  Lemma plus_trans x y z :
    plus x y -> plus y z -> plus x z.
  Proof.
    induction 1; eauto.
  Qed.


  Fact counted_trans x y z m n:
    counted m x y -> counted n y z -> counted (m + n) x z.
  Proof.
    induction 1; cbn; eauto.
  Qed.



  Fact star_exp :
    R <<= star.
  Proof.
    eauto.
  Qed.

  Fact plus_exp :
    R <<= plus.
  Proof.
    eauto.
  Qed.

  Fact counted_exp :
    R === counted 1.
  Proof.
    split; eauto.
    intros x y H; inv H; inv H2; eauto.
  Qed.


  Lemma plus_star : plus <<= star.
  Proof.
    induction 1; eauto.
  Qed.

  Lemma plus_destruct x y: plus x y <-> exists2 x', (R x x') & (star x' y).
  Proof.
    split.
    - induction 1; eauto.
      destruct IHplus; eexists; eauto.
    - intros [? H1 H2]; revert x H1; induction H2; eauto.
  Qed.


  Lemma step_star_plus x y z:
    R x y -> star y z -> plus x z.
  Proof.
    intros H1 H2; apply plus_destruct; eauto.
  Qed.

  Lemma plus_star_step x y z :
    plus x y -> star y z -> plus x z.
  Proof.
    intros [] % plus_destruct ?. eapply plus_destruct.
    eexists; eauto using star_trans.
  Qed.

End ClosureRelations.


Definition equiv X (R: X -> X -> Prop) := star (sym R).



Hint Constructors star plus counted.
Hint Resolve star_trans plus_trans counted_trans star_exp plus_exp counted_exp.




Section Properties.
  Variable X: Type.
  Implicit Types (x y z : X) (R S : X -> X -> Prop).

  Fact star_mono R S :
    R <<= S -> star R <<= star S.
  Proof.
    intros H x y.
    induction 1; eauto.
  Qed.

  Fact plus_mono R S :
    R <<= S -> plus R <<= plus S.
  Proof.
    intros H x y.
    induction 1; eauto.
  Qed.


  Fact star_closure R S :
    PreOrder S -> R <<= S -> star R <<= S.
  Proof.
    intros H1 H2 x y.
    induction 1 as [x|x x' y H4 _ IH].
    - reflexivity.
    - transitivity x'; auto.
  Qed.

  Fact star_idem R :
    star (star R) === star R.
  Proof.
    split.
    - induction 1; eauto.
    - apply star_mono, star_exp.
  Qed.

  Fact plus_idem R :
    plus (plus R) === plus R.
  Proof.
    split; eauto.
    induction 1; eauto.
  Qed.

  Fact plus_fixpoint R :
    plus (star R) === star R.
  Proof.
    split.
    - induction 1; eauto.
    - eauto.
  Qed.

  Fact star_absorbtion R :
    star (plus R) === star R.
  Proof.
    split.
    - induction 1; eauto.
      apply plus_destruct in H. destruct H. eauto.
    - eapply star_mono. eauto.
  Qed.


  Lemma sym_symmetric R x y:
    sym R x y -> sym R y x.
  Proof.
    intros []; eauto using sym.
  Qed.

  Lemma refl_star R x y:
    x = y -> star R x y.
  Proof.
    intros ->; eauto.
  Qed.

  Lemma refl_equiv R x:
    equiv R x x.
  Proof.
    constructor.
  Qed.

  Lemma equiv_trans R x y z:
    equiv R x y -> equiv R y z -> equiv R x z.
  Proof. eapply star_trans. Qed. 

  Lemma equiv_symm R x y:
    equiv R x y -> equiv R y x.
  Proof.
    induction 1.
    constructor; eauto.
    eapply star_trans; eauto. 
    econstructor 2; eauto using refl_equiv, sym_symmetric. 
  Qed.


  Lemma equiv_star R x y:
    star R x y -> equiv R x y.
  Proof.
    induction 1; unfold equiv in *; eauto using sym, star.
  Qed.

End Properties.


(** Strong normalisation *)
Section StrongNormalisation.

  Variables (X A: Type).
  Variables (R: X -> X -> Prop) (S: A -> A -> Prop).

  Definition Normal x := forall y, ~ R x y.
  Definition evaluates s t := star R s t /\ Normal t.

  Inductive SN {X} (R: X -> X -> Prop) : X -> Prop :=
  | SNC x : (forall y, R x y -> SN R y) -> SN R x.

  Lemma SN_ext Q x :
    (forall x y, R x y <-> Q x y) ->
    SN R x <-> SN Q x.
  Proof.
    split; induction 1; econstructor; firstorder.
  Qed.

  Fact SN_unfold x :
    SN R x <-> forall y, R x y -> SN R y.
  Proof.
    split.
    - destruct 1 as [x H]. exact H.
    - intros H. constructor. exact H.
  Qed.

  Fact Normal_SN x :
    Normal x -> SN R x.
  Proof.
    intros H. constructor. intros y H1.
    exfalso. eapply H; eauto.
  Qed.


  Fact Normal_star_stops x:
    Normal x -> forall y, star R x y -> x = y.
  Proof.
    destruct 2; firstorder.
  Qed.


  Fact SN_plus x :
    SN R x <-> SN (plus R) x.
  Proof.
    split.
    - induction 1 as [x _ IH].
      constructor. induction 1; eauto.
      apply IHplus. intros z H1 % plus_exp.
      destruct (IH x' H) as [H2].
      apply H3. eauto.
    - induction 1 as [x _ IH].
      constructor. intros y H1. apply IH. eauto.
  Qed.

  Definition morphism  (f: X -> A) := forall x y, R x  y -> S (f x) (f y).

  Fact SN_morphism f x :
    morphism f -> SN S (f x) -> SN R x.
  Proof.
    intros H H1.
    remember (f x) as a eqn:H2. revert x H2.
    induction H1 as [a _ IH]. intros x ->.
    constructor. intros y H1 % H.
    apply (IH _ H1). reflexivity.
  Qed.

  Fact SN_finite_steps:
     (forall x, (exists y, R x y) \/ Normal x) -> forall x, SN R x -> exists2 y, star R x y & Normal y.
  Proof.
    intros H; induction 1 as [x H1 IH]. destruct (H x) as [[y H2]|].
    + edestruct IH as [z H3 H4]; eauto.
    + eexists; eauto.
  Qed.


End StrongNormalisation.

Section Confluence.

  Variable X: Type.
  Implicit Types (x y z : X) (R S : X -> X -> Prop).


  Definition joinable R x y := exists2 z, R x z & R y z.
  Definition diamond R := forall x y z, R x y -> R x z -> joinable R y z.
  Definition confluent R := diamond (star R).
  Definition semi_confluent R :=
    forall x y z, R x y -> star R x z -> joinable (star R) y z.


  Fact diamond_semi_confluent R :
    diamond R -> semi_confluent R.
  Proof.
    intros H x y1 y2 H1 H2. revert y1 H1.
    induction H2 as [x|x x' y2 H2 _ IH]; intros y1 H1.
    - exists y1; eauto.
    - assert (joinable R y1 x') as [z H3 H4].
      { eapply H; eauto. }
      assert (joinable (star R) z y2) as [u H5 H6].
      { apply IH; auto. }
      exists u; eauto.
  Qed.

  Fact confluent_semi R :
    confluent R <-> semi_confluent R.
  Proof.
    split.
    - intros H x y1 y2 H1 H2.
      eapply H; [|exact H2]. auto.
    - intros H x y1 y2 H1 H2. revert y2 H2.
      induction H1 as [x|x x' y1 H1 _ IH]; intros y2 H2.
      + exists y2; auto.
      + assert (joinable (star R) x' y2) as [z H3 H4].
        { eapply H; eauto. }
        assert (joinable (star R) y1 z) as [u H5 H6].
        { apply IH; auto. }
        exists u; eauto.
  Qed.

  Fact diamond_confluent R :
    diamond R -> confluent R.
  Proof.
    intros H.
    apply confluent_semi, diamond_semi_confluent, H.
  Qed.

  Fact joinable_ext R S x y:
    R === S -> joinable R x y -> joinable S x y.
  Proof.
    firstorder.
  Qed.

  Fact diamond_ext R S:
    R === S -> diamond S -> diamond R.
  Proof.
    intros H1 H2 x y z H3 H4.
    assert (joinable S y z); firstorder.
  Qed.

  Lemma confluence_normal_left R x y z:
    confluent R -> Normal R y ->
    star R x y -> star R x z ->
    star R z y.
  Proof.
    intros H1 H2 H3 H4. destruct (H1 _ _ _ H3 H4) as [x' A B].
    enough (x' = y) by congruence.
    destruct A; eauto; exfalso; eapply H2; eauto.
  Qed.

  Lemma confluence_normal_right R x y z:
    confluent R -> Normal R z ->
    star R x y -> star R x z ->
    star R y z.
  Proof.
    intros H1 H2 H3 H4. destruct (H1 _ _ _ H3 H4) as [x' A B].
    enough (x' = z) by congruence.
    destruct B; eauto; exfalso; eapply H2; eauto.
  Qed.


  Lemma confluence_unique_normal_forms R x y z:
    confluent R -> Normal R y -> Normal R z ->
    star R x y -> star R x z -> y = z.
  Proof.
    intros H1 H2 H3 H4 H5. destruct (H1 _ _ _ H4 H5) as [x' A B].
    destruct A; [destruct B | ]; eauto; exfalso; [ eapply H3 | eapply H2 ];  eauto.
  Qed.


  Lemma church_rosser (R: X -> X -> Prop) s t:
    confluent R -> equiv R s t -> exists v: X, star R s v /\ star R t v.
  Proof.
    induction 2.
    - now (exists x).
    - inv H0.
      + destruct IHstar as [v];  exists v; intuition;  eauto. 
      + destruct IHstar; intuition.
        edestruct H.
        eapply H3. econstructor 2; eauto.
        exists x1; split; eauto.
  Qed.

 
End Confluence.


(** Right-recursive version of star. *)

Inductive starL {X: Type} (R: X -> X -> Prop) (x : X):  X -> Prop :=
| starReflL : starL R x x
| starStepL  y y':  starL R x y -> R y y' -> starL R x y'.

Hint Constructors starL.

Lemma star_starL X (R : X -> X -> Prop) x y :
  starL R x y <-> star R x y .
Proof.
  split.
  - induction 1; auto. induction IHstarL; eauto.
  - induction 1; eauto. clear H0. induction IHstar; eauto.
Qed.



(**  Typeclass Instances **)
Global Instance subrel_star {X} (R : X -> X -> Prop) :
  subrelation (plus R) (star R).
Proof.
  intros ?; eapply plus_star.
Qed.

Global Instance subrel_star_mono {X} (R S: X -> X -> Prop) (H: subrelation R S) :
  subrelation (star R) (star S).
Proof.
  exact (star_mono _ H).
Qed.

Global Instance subrel_plus_mono {X} (R S: X -> X -> Prop) (H: subrelation R S) :
  subrelation (plus R) (plus S).
Proof.
  exact (plus_mono _ H).
Qed.

Global Instance subrel_star_equiv {X} (R: X -> X -> Prop) :
  subrelation (star R) (equiv R).
Proof.
  exact (@equiv_star _ R). 
Qed.


Global Instance star_preorder {X} (R: X -> X -> Prop):
  PreOrder (star R).
Proof.
  constructor; hnf; eauto using star_trans.
Qed.

Global Instance star_expansive {X} (R: X -> X -> Prop):
  subrelation R (star R).
Proof.
  intros ?; eapply star_exp.
Qed.


Global Instance plus_expansive {X} (R: X -> X -> Prop):
  subrelation R (plus R).
Proof.
  intros?; eapply plus_exp.
Qed.

Global Instance plus_transitive {X} (R: X -> X -> Prop):
  Transitive (plus R).
Proof.
  intros ?; eapply plus_trans.
Qed.

Global Instance sym_Symmetric {X} (R: X -> X -> Prop):
  Symmetric (sym R).
Proof.
  firstorder using sym_symmetric.
Qed.


Global Instance equiv_Equivalence {X} (R: X -> X -> Prop):
  Equivalence (equiv R).
Proof.
  constructor; try firstorder using refl_equiv, equiv_trans, equiv_symm.
  intros ? ? ? ; eapply equiv_trans.
Qed.


