(**
  We define monads, T-Algebras,
  the identity monad as well as
  the free, the singleton,
  the product and the exponential T-Algebra.
  We define a logical relation, relating denotations and terms as in the paper
  of Forster. Using this relation we show the denotational semantics adequate and sound.
*)

Set Implicit Arguments.
Require Import Psatz  Logic List Classes.Morphisms Setoid FinFun Coq.Program.Tactics.
Import List Notations.

Require Export CBPV.LogicalEquivalence CBPV.ProgramContexts.


(** * Denotational Semantics *)

(** ** Monads and Algebras *)

(** *** Monad *)
Structure Monad :=
  {
    T:> Type -> Type;
    mbind {X Y}: T X -> (X -> T Y) -> T Y;
    mreturn {X}:  X -> T X;

    monad1 {X Y}: forall (x: X) (f: X -> T Y), mbind (mreturn x) f = f x;
    monad2 {X}: forall (x: T X), x = mbind x mreturn;
    monad3 {X Y Z}: forall (x: T X) (f: X -> T Y) (g: Y -> T Z),
        mbind (mbind x f) g = mbind x (fun x => mbind (f x) g)
  }.

Existing Class Monad.

Local Arguments mbind {_ _ _} _ _.
Local Arguments mreturn {_ _} _.

Notation "x >>= f" := (mbind x f) (at level 50).
Notation η m := (mreturn m).

Definition fmap {X Y: Type} {M: Monad} (f: X -> Y): M X -> M Y :=
  fun x => mbind x (f >> mreturn).

Notation "f @ x" := (fmap f x) (at level 50).

Program Definition IdMonad :=
  {| T := fun X => X; mbind := fun _ _ x f => f x; mreturn := fun _ x => x |}.

(** Parameterized over a monad T *)
Section TAlgebra.

  Variable (T: Monad).

  (** *** T-Algebra *)
  Structure TAlgebra  :=
  {
    Carrier :> Type;
    algstruct: T Carrier -> Carrier;

    t_algebra1: forall x, algstruct (mreturn x) = x;
    t_algebra2: forall xs, algstruct (fmap algstruct xs) = algstruct (mbind xs id)

  }.

  Local Arguments algstruct {_} _.

  (** *** Free T-Algebra *)
  Program Definition free_t_algebra (X: Type) :=
  {| Carrier := T X; algstruct := fun x => mbind x id  |}.
  Next Obligation. now rewrite monad1. Qed.
  Next Obligation.
    unfold fmap, funcomp; rewrite monad3, monad3; f_equal; fext; intros;
    rewrite monad1; reflexivity.
  Qed.

  Definition mu {T : Monad} {A} (x : T (T A)) :=
    x >>= id.

  Lemma fmap_funct {M : Monad} {A B C} (g : A -> B) (f : B -> C) x :
    f @ (g @ x) = (g >> f) @ x.
  Proof.
    unfold fmap, ">>". rewrite !monad3. f_equal.
    fext; intros. now rewrite monad1.
  Qed.

  Lemma mu_fmap {M : Monad} {A B} (f : A -> M B) xs :
    mu (f @ xs) = xs >>= f.
  Proof.
    unfold mu, fmap, ">>". rewrite monad3. f_equal. fext. intros. now rewrite monad1.
  Qed.

  (** *** Singleton T-Algebra *)
  Program Definition singleton_t_algebra (X: Type) (x: X) :=
    {| Carrier := { y | x = y }; algstruct := fun _ => x |}.

  (** *** Product T-Algebra *)
  
  Program Definition product_t_algebra (C1 C2: TAlgebra)  :=
    {| Carrier := C1 * C2;
       algstruct := fun cs => (algstruct (fst @ cs), algstruct  (snd @ cs)) |}.
  Next Obligation.
    unfold fmap, funcomp; f_equal;
      rewrite monad1; unfold fst, snd; now rewrite t_algebra1.
  Qed.
  Next Obligation.
    f_equal.
    - fold (mu xs). rewrite fmap_funct. unfold ">>". cbn.
      fold (fmap (fst (B := C2)) >> @algstruct C1).
      rewrite <- fmap_funct. rewrite t_algebra2.
      fold (mu (fmap fst @ xs)).
      rewrite mu_fmap.
      unfold mu, fmap. now rewrite monad3.
    - fold (mu xs). rewrite fmap_funct. unfold ">>". cbn.
      fold (fmap (snd (A := C1)) >> @algstruct C2).
      rewrite <- fmap_funct. rewrite t_algebra2.
      fold (mu (fmap snd @ xs)).
      rewrite mu_fmap.
      unfold mu, fmap. now rewrite monad3.
  Qed.


  (** *** Exponential T-Algebra *)
  Program Definition exponential_t_algebra (C: TAlgebra) A :=
    {| Carrier := A -> C;
       algstruct := fun f => fun x => algstruct (fmap (fun f => f x) f) |}.
  Next Obligation.
    fext; intros; unfold fmap, funcomp; rewrite monad1, t_algebra1; reflexivity.
  Qed.
  Next Obligation.
    fext; intros. fold (mu xs).
    rewrite fmap_funct. unfold ">>".
    fold (fmap (fun f => f x)  >> @algstruct C).
    rewrite <- fmap_funct. rewrite t_algebra2.
    f_equal. unfold mu, fmap, ">>". rewrite !monad3.
    f_equal. fext. intros. now rewrite monad1.
  Qed.

End TAlgebra.


Import CommaNotation.
(** ** Denotational Semantics *)
Section DenotationalSemantics.

  Variable (T: Monad).

  (** *** Denotation of Value Types *)
  Fixpoint denote_valtype (A: valtype) : Type :=
    match A with
    | zero => Empty_set
    | one => unit
    | Sigma A1 A2 => denote_valtype A1 + denote_valtype A2
    | A1 * A2 => denote_valtype A1 * denote_valtype A2
    | U B => Carrier (denote_comptype B)
    end
  (** *** Denotation of Computation Types *)
  with denote_comptype (B: comptype) : TAlgebra T :=
    match B with
    | cone => singleton_t_algebra T tt
    | Pi B1 B2 => product_t_algebra (denote_comptype B1) (denote_comptype B2)
    | A → B => exponential_t_algebra (denote_comptype B) (denote_valtype A)
    | F A => free_t_algebra T (denote_valtype A)
    end.

  (** *** Denotation of Typing Contexts *)
  Definition denote_context {n: nat} (Gamma: ctx n) := forall i, denote_valtype (Gamma i).


  Definition extend {n: nat} {Gamma: ctx n} {A: valtype} (gamma: denote_context Gamma) (a: denote_valtype A):
    denote_context (A .: Gamma) :=
    fun (i: fin (S n)) => match i with None => a | Some i => gamma i end.

  (** *** Denotation of Values *)
  Fixpoint denote_valtyping {n: nat} {Gamma : ctx n} {v: value n} {A: valtype}
           (H: Gamma ⊩ v : A) (gamma: denote_context Gamma) {struct H} : denote_valtype A :=
    match H with
    | typeVar _ i => gamma i
    | typeUnit _ => tt
    | typePair H1 H2 =>( Datatypes.pair (denote_valtyping H1 gamma) (denote_valtyping H2 gamma))
    | @typeSum _ _ A1 A2 b v H =>
      match b return
            (Gamma ⊩ v : if b then A1 else A2) -> _
      with
      | true => fun H' => inl (denote_valtyping H' gamma)
      | false => fun H' => inr (denote_valtyping H' gamma)
      end H
    | typeThunk H => denote_comptyping H gamma
    end
  (** *** Denotation of Computations *)
  with denote_comptyping {n: nat} {Gamma : ctx n} {c: comp n} {B: comptype}
       (H: Gamma ⊢ c : B) (gamma: denote_context Gamma) {struct H} : denote_comptype B :=

     match H in _ ⊢ _ : B return denote_comptype B with
     | typeCone _  => exist _ tt eq_refl
     | @typeLambda _ _ c A B H =>
       fun (a: denote_valtype A) =>
         denote_comptyping H (extend gamma a)
     | typeLetin H1 H2 =>
       algstruct _ (mbind (denote_comptyping H1 gamma)
                   (fun a =>  mreturn (denote_comptyping H2 (extend gamma a))))
     | typeRet H =>  mreturn (denote_valtyping H gamma)
     | typeApp H1 H2 => (denote_comptyping H1 gamma) (denote_valtyping H2 gamma)
     | typeTuple H1 H2 => Datatypes.pair (denote_comptyping H1 gamma) (denote_comptyping H2 gamma)
     | @typeProj _ _ b c B1 B2 H =>
       match b return  denote_comptype (if b then B1 else B2) with
       | true => fst (denote_comptyping H gamma)
       | false => snd (denote_comptyping H gamma)
       end
     | typeForce H => denote_valtyping H gamma
     | typeCaseZ _ H => match denote_valtyping H gamma with end
     | typeCaseS  H1 H2 H3 =>
       match denote_valtyping H1 gamma with
       | inl a => denote_comptyping H2 (extend gamma a)
       | inr a => denote_comptyping H3 (extend gamma a)
       end
     | typeCaseP H1 H2 =>
       let (a1, a2) := denote_valtyping H1 gamma in
       denote_comptyping H2 (extend (extend gamma a1) a2)
     end.




  (** Denotation of groundtypes inhabited *)
  Lemma denotation_of_groundtypes_inhabited:
  forall (G: groundtype) (a: denote_valtype G),
        exists v (H: null ⊩ v : G), a = denote_valtyping H (fun (i: fin 0) => match i with end).
  Proof.
    induction G; intros [].
    - exists u; exists (typeUnit _); reflexivity.
    - destruct (IHG1 d) as [v [H H1] ].
      exists (inj true v). exists (typeSum _ _ true H); cbn; f_equal; assumption.
    - destruct (IHG2 d) as [v [H H1] ].
      exists (inj false v). exists (typeSum _ _ false H); cbn; f_equal; assumption.
    - destruct (IHG1 d) as [v1 [H1 H1'] ]; destruct (IHG2 d0) as [v2 [H2 H2'] ]; exists (pair v1 v2).
      exists (typePair H1 H2); cbn; f_equal; assumption.
  Qed.



End DenotationalSemantics.



(** *** Preservation of denotational equality in contexts *)
(**  [[ P ]] = [[Q]] ⇒ [[X[P]]] = [[X[Q]]] *)
Lemma denotation_context (T: Monad):
  forall m t Delta,
    (forall n Gamma (C: vctx t m n) A X (H: Delta [[Gamma]] ⊩ C : A;X),
    match t return forall (C: vctx t m n) (X: if t then valtype else comptype), Delta [[Gamma]] ⊩ C : A;X -> Prop with
    | true => fun C X H => forall P Q (H1: Gamma ⊩ P : X) (H2: Gamma ⊩ Q : X),
        (forall gamma, denote_valtyping (T := T) H1 gamma = denote_valtyping H2 gamma) ->
            forall delta, denote_valtyping (T := T) (vctx_value_typing_soundness H H1) delta =
          denote_valtyping (T := T) (vctx_value_typing_soundness H H2) delta
    | false => fun C X H => forall P Q  (H1: Gamma ⊢ P : X) (H2: Gamma ⊢ Q : X),
            (forall gamma, denote_comptyping (T := T) H1 gamma = denote_comptyping H2 gamma) ->
            forall delta, denote_valtyping (T := T) (vctx_comp_typing_soundness H H1) delta =
            denote_valtyping (T := T) (vctx_comp_typing_soundness H H2) delta
    end C X H) /\
    (forall n Gamma (C: cctx t m n) B X (H: Delta [[Gamma]] ⊢ C : B;X),
    match t return forall (C: cctx t m n) (X: if t then valtype else comptype), Delta [[Gamma]] ⊢ C : B;X -> Prop  with
    | true => fun C X H =>  forall P Q (H1: Gamma ⊩ P : X) (H2: Gamma ⊩ Q : X),
        (forall gamma, denote_valtyping (T := T) H1 gamma = denote_valtyping H2 gamma) ->
          forall delta,  denote_comptyping (T := T) (cctx_value_typing_soundness H H1) delta =
        denote_comptyping (T := T) (cctx_value_typing_soundness H H2) delta
    | false => fun C X H =>  forall P Q (H1: Gamma ⊢ P : X) (H2: Gamma ⊢ Q : X),
        (forall gamma, denote_comptyping (T := T) H1 gamma = denote_comptyping H2 gamma) ->
        forall delta, denote_comptyping (T := T) (cctx_comp_typing_soundness H H1) delta =
        denote_comptyping (T := T) (cctx_comp_typing_soundness H H2) delta
    end C X H).
Proof.
  eapply mutindt_vctx_cctx_typing; intros; destruct t; intros;
    cbn [cctx_comp_typing_soundness
            vctx_comp_typing_soundness
            cctx_value_typing_soundness
            vctx_value_typing_soundness]; intuition.
  all: try destruct b.
  1 - 10, 13 - 14, 17 - 24, 29 - 32: (now (cbn; f_equal; eauto)).
  1, 2: cbn; fext; intros; eauto.
  1, 2: cbn; erewrite H; eauto.
  1, 2: cbn; do 2 f_equal; eauto.
  1, 2: cbn; do 2 f_equal; fext; intros; f_equal; eauto.
  1: destruct (denote_valtyping (vctx_value_typing_soundness v H1) delta).
  1: destruct (denote_valtyping (vctx_comp_typing_soundness v H1) delta).
  1, 2, 7, 8:  cbn; erewrite H; eauto.
  all: cbn; fold (denote_valtyping v0 delta); destruct (denote_valtyping v0 delta); eauto.
Qed.



(** ** Logical Relation  *)

(** Closed CBPV Terms with typing judgements *)
Definition CCBPVv := CBPVv null.
Definition CCBPVc := CBPVc null.


Section LogicalRelation.
  Variable (T: Monad).

  (** *** Value Relations *)
  Fixpoint RV (A: valtype) : denote_valtype T A -> CCBPVv A -> Prop :=
    match A with
    | zero => fun _ _ => False
    | one => fun a H => H ≈ (mkCBPVv (typeUnit null))
    | cross A1 A2 => fun a H =>
      let (a1, a2) := a in exists (H1: CCBPVv A1) (H2: CCBPVv A2),
        RV a1 H1 /\ RV a2 H2 /\ H ≈ (mkCBPVv (typePair H1 H2))
    | Sigma A1 A2 => fun a H =>
      match a with
      | inl a1 => exists (H': CCBPVv A1), RV a1 H' /\ H ≈ (mkCBPVv (typeSum A1 A2 true H'))
      | inr a2 => exists (H': CCBPVv A2), RV a2 H' /\ H ≈ (mkCBPVv (typeSum A1 A2 false H'))
      end
    | U B => fun a H => exists (H': CCBPVc B), RC a H' /\ H ≈ (mkCBPVv (typeThunk H'))
    end

  (** *** Computation Relations *)
  with RC (B: comptype) : denote_comptype T B -> CCBPVc B -> Prop :=
    match B return denote_comptype T B -> CCBPVc B -> Prop  with
    | cone => fun f H => H ≃ mkCBPVc (typeCone null)
    | F A => fun (f: T (denote_valtype T A)) H =>
              exists a, f = mreturn a /\ exists H', RV a H' /\ H ≃ mkCBPVc (typeRet H')
    | Pi B1 B2 => fun (f: denote_comptype T B1 * denote_comptype T B2) H =>
                  let (f1, f2) := f in  exists (H1: CCBPVc B1) (H2: CCBPVc B2),
                  RC f1 H1 /\ RC  f2 H2 /\ H ≃ mkCBPVc (typeTuple H1 H2)
    | A → B => fun f H => (forall a H', RV a H' -> RC (f a) (mkCBPVc (typeApp H H')))
    end.



  (** ** Adequacy *)
  (** Closure under Contextual Equivalence *)
  Lemma closure_ctx_eqv:
    (forall (A: valtype), forall a (P Q: CCBPVv A), RV a P -> P ≈ Q -> RV a Q) /\
    (forall (B: comptype), forall a (P Q: CCBPVc B), RC a P -> P ≃ Q -> RC a Q).
  Proof.
    eapply mutind_valtype_comptype; cbn; intros; eauto.
    - rewrite <-H0; eauto.
    - destruct H0 as [H' ?]; exists H'; intuition; rewrite <-H1; eauto.
    - destruct a; destruct H1 as [H' ?]; exists H'; intuition; rewrite <-H2; eauto.
    - destruct a; destruct H1 as [H' [H'' ?] ]; exists H'; exists H'';  intuition; rewrite <-H2; eauto.
    - rewrite <-H0; eauto.
    - destruct H0 as [a' [? [H' ?] ] ]; exists a'; intuition; exists H'; intuition; rewrite <-H1; eauto.
    - destruct a; destruct H1 as [H' [H'' ?] ]; exists H'; exists H''; intuition; rewrite <-H2; eauto.
    - eapply H0.
      + apply H1; eauto.
      + eapply comp_obseq_cctx_congruence with (C := (cctxAppL •__c H')); cbn; eauto.
        econstructor; eauto; econstructor.
  Qed.

  (** Closure under reduction *)
  Lemma closure_ctx_red:
    forall (B: comptype), forall a (P Q: CCBPVc B),  Q >* P -> RC a P -> RC a Q.
  Proof.
    intros; eapply closure_ctx_eqv; [eassumption |].
    symmetry; eapply obseq_contains_steps; eauto.
  Qed.



  (** *** Grountypes Contextual Equivalence  **)
  (** Values of groundtypes, related with the same denotation are observationally equivalent *)
  Lemma ground_equiv:
    forall (G: groundtype) (a: denote_valtype T G) (V1 V2: CCBPVv G),
      RV a V1 -> RV a V2 -> V1 ≈ V2.
  Proof.
    induction G; cbn; intros; eauto.
    - rewrite H, H0; reflexivity.
    - destruct a, H, H0; intuition; rewrite H2, H3;
        eapply val_obseq_vctx_congruence with (C := (vctxInj _ •__v)); cbn; eauto;
      do 2 econstructor.
    - destruct a, H, H, H0, H0; intuition; rewrite H4, H5.
      transitivity (mkCBPVv (typePair x1 x0)).
      eapply val_obseq_vctx_congruence with (C := (vctxPairL •__v x0)); cbn; eauto.
      econstructor; eauto; econstructor.
      eapply val_obseq_vctx_congruence with (C := (vctxPairR x1 •__v)); cbn; eauto.
      econstructor; eauto; econstructor.
  Qed.



  (** ***  Basic Lemma *)
  (** Extending a context denotation with an additional element *)
  Definition extend' {n : nat} {Gamma : ctx n} (V : forall i, CCBPVv (Gamma i)) {A: valtype} (a: CCBPVv A) (i: fin (S n)) :=
    match i return (CCBPVv ((A .: Gamma) i)) with
    | Some i0 => V i0
    | None => a
    end.


  Lemma refl_steps n (c1 c2: comp n): c1 = c2 -> c1 >* c2. Proof. intros ->; constructor. Qed.

  (** We can substitutute underneath cons *)
  Lemma cons_ctx_subst m c A C Gamma:
    forall (V:  (forall (i : fin m), CCBPVv (Gamma i))),
      A, Gamma ⊢ c : C ->
                 A, null ⊢ c[up_value_value (fun i : fin m => V i)]  : C.
  Proof.
    intros; eapply comp_typepres_substitution; eauto.
    intros []; cbn; eauto.
    eapply value_typepres_renaming; eauto.
  Qed.


  Lemma cons_twice_ctx_subst m c A1 A2 C Gamma:
    forall (V:  (forall (i : fin m), CCBPVv (Gamma i))),
      A1, A2, Gamma ⊢ c : C ->
      A1, A2, null ⊢ c[up_value_value (up_value_value (fun i : fin m => V i))] : C.
  Proof.
    intros; eapply comp_typepres_substitution; eauto.
    intros [ [] | ]; cbn; eauto.
    eapply value_typepres_renaming with (Gamma := A2, null); eauto.
    eapply value_typepres_renaming; eauto.
  Qed.

  Hint Resolve cons_ctx_subst cons_twice_ctx_subst.


  (** Basic Lemma - the denotation of a term is logically related to the closed version of its self
      if we substitutute all variables by logically related terms.
   *)
  Lemma basic_lemma n (Gamma: ctx n):
      (
        forall v A (H: Gamma ⊩ v : A), forall (gamma: denote_context T Gamma) (V: forall i, CCBPVv (Gamma i)),
            (forall i, RV (gamma i) (V i)) ->
            RV (denote_valtyping H gamma) (mkCBPVv (value_typepres_substitution H (fun i => V i) (fun i => V i)))
      ) /\ (
        forall c B (H: Gamma ⊢ c : B), forall (gamma: denote_context T Gamma) (V: forall i, CCBPVv (Gamma i)),
            (forall i, RV (gamma i) (V i)) ->
            RC (denote_comptyping H gamma) (mkCBPVc (comp_typepres_substitution H (fun i => V i) (fun i => V i)))
      ).
  Proof with cbn; intuition; eauto; intros ? ? ?; reflexivity.
    revert n Gamma; eapply mutindt_value_computation_typing; intros; cbn [RV RC].
    - eapply closure_ctx_eqv...
    - idtac...
    - do 2 eexists...
    - destruct b; eexists...
    - eexists...
    - idtac...
    - intros; specialize (H (extend gamma a)).
      specialize (H (extend' V H')).
      mp H; [ intros []; cbn; eauto |].
      eapply closure_ctx_red; [| eassumption]; cbn; reduce.
      eapply refl_steps; asimpl; unfold extend'; f_equal; fext.
        now intros [].
    - specialize (H gamma V H1); cbn; destruct H as [a [-> H] ].
      rewrite monad1, t_algebra1.
      destruct H as [H' [H ?] ].
      specialize (H0 (extend gamma a) (extend' V H')).
      mp H0; [ intros []; cbn; eauto |].
      eapply closure_ctx_eqv; [eassumption | clear H0]; cbn; symmetry.
      enough (null ⊢ $ <- ret H'; subst_comp (up_value_value (fun i : fin m => V i)) c2 : B).
      transitivity (mkCBPVc X).
      + eapply comp_obseq_cctx_congruence with
            (C := (cctxLetinL •__c (subst_comp (up_value_value (fun i : fin m => V i)) c2)));
        cbn; eauto; cbn; eauto.
      + eapply obseq_contains_pstep; cbn; constructor.
        asimpl. f_equal. fext.
        intros []; cbn; eauto.
      +  eauto.
    - eexists; intuition; eexists...
    - intros; specialize (H0 gamma V H1).
      specialize (H gamma V H1).  cbn in H. specialize (H _ _ H0).
      eapply closure_ctx_eqv; [ apply H |]...
    - do 2 eexists...
    - specialize (H gamma V H0); cbn; destruct (denote_comptyping c0 gamma).
      destruct H as [H1 [H2 ?] ]; intuition.
      assert (null ⊢ proj b (tuple H1 H2) : if b then B1 else B2) as X by eauto.
      destruct b; cbn; eapply closure_ctx_eqv;  eauto; symmetry; transitivity (mkCBPVc X).
      1:  eapply comp_obseq_cctx_congruence with (C := (cctxProj true •__c)).
      4: apply H5.
      1 - 4: cbn; eauto.
      1: refine (cctxTypingProj (B2 := B2) true _); econstructor.
      2: eapply comp_obseq_cctx_congruence with (C := (cctxProj false •__c)).
      5: apply H5.
      2 - 5: cbn; eauto.
      2: refine (cctxTypingProj (B1 := B1) false _); econstructor.
      1, 2: eapply obseq_contains_pstep; cbn; eauto.
    - specialize (H gamma V H0); destruct H as [H' ?]; intuition.
      eapply closure_ctx_eqv; eauto; cbn; symmetry.
      assert (null ⊢  <{ H' }> ! : A) as X by eauto.
      transitivity (mkCBPVc X).
      + eapply val_obseq_cctx_congruence with (C := (cctxForce •__v )); cbn; eauto; cbn; eauto.
      + eapply obseq_contains_pstep; cbn; eauto.
    - destruct (H gamma V H0).
    - specialize (H gamma V H2); cbn; destruct (denote_valtyping v0 gamma) eqn: H42; cbn in H;
        destruct H as [H' H]; intuition;
          [ specialize (H0 (extend gamma d) (extend' V H')); mp H0 |
            specialize (H1 (extend gamma d) (extend' V H')); mp H1]; try (intros []; cbn; eauto);
      unfold denote_valtyping in H42; rewrite H42; clear H42;
        eapply closure_ctx_eqv; eauto; cbn; symmetry.
      assert (null ⊢ caseS (inj true H') (subst_comp (up_value_value (fun i : fin m => V i)) c1)
                   (subst_comp (up_value_value (fun i : fin m => V i)) c2) : C) as X by eauto.
      transitivity (mkCBPVc X).
      eapply val_obseq_cctx_congruence with (C := cctxCaseSV •__v _ _).
      4: apply H4.
      1 - 4: cbn; eauto.
      1: econstructor; eauto; econstructor.
      eapply obseq_contains_pstep; cbn; constructor; asimpl; unfold extend'; f_equal.
      fext; intros []; cbn; reflexivity.
     +   assert (null ⊢ caseS (inj false H') (subst_comp (up_value_value (fun i : fin m => V i)) c1)
                   (subst_comp (up_value_value (fun i : fin m => V i)) c2) : C) as X by eauto.
      transitivity (mkCBPVc X).
      eapply val_obseq_cctx_congruence with (C := cctxCaseSV •__v _ _).
      4: apply H4.
      1 - 4: cbn; eauto.
      1: econstructor; eauto; econstructor.
      eapply obseq_contains_pstep; cbn; constructor; asimpl; unfold extend';  f_equal.
      fext; intros []; cbn; reflexivity.
    - specialize (H gamma V H1); destruct (denote_valtyping v0 gamma) eqn: H42; cbn;
      unfold denote_valtyping in H42; rewrite H42; clear H42; cbn in H.
      destruct H as [H2 [H3 ?] ]; intuition.
      specialize (H0 (extend (extend gamma d) d0) (extend' (extend' V H2) H3)).
      mp H0; [intros [ []|]; cbn; eauto|].
      eapply closure_ctx_eqv; eauto; cbn; symmetry.
      assert (null ⊢ caseP (⟨ H2; H3 ⟩)(subst_comp (up_value_value (up_value_value (fun i : fin m => V i))) c) : C)
             as X by eauto.
      transitivity (mkCBPVc X).
      eapply val_obseq_cctx_congruence with (C := cctxCasePV •__v _); cbn.
      4: apply H6.
      1 - 4: eauto.
      econstructor; eauto; constructor.
      eapply obseq_contains_pstep.
      cbn. constructor. unfold extend'; asimpl;
      f_equal. fext.
      intros [ []|]; cbn; reflexivity.
  Qed.



  Variable (mono_requirement: forall X, Injective (@mreturn T X)).


  (** *** Adequacy *)
  Theorem adequacy n (Gamma: ctx n) B (P Q: CBPVc Gamma B):
      (forall (gamma: denote_context T Gamma), denote_comptyping P gamma = denote_comptyping Q gamma) -> P ≃ Q.
  Proof.
    intros. intros G C H' v.
      set (gamma := (fun (i: fin 0) => match i with end):  denote_context T null).
      set (V :=  (fun (i: fin 0) => match i with end): (forall (i : fin 0), CCBPVv (null i))).

      destruct (denotation_context T false null) as [_ denc].
      specialize (denc _ _ _ _ _ H' _ _ P Q H).
      destruct (basic_lemma null) as [_ basic].
      specialize (basic _ _ (cctx_comp_typing_soundness H' P) gamma V) as H1.
      mp H1; [intros [] |].
      specialize (basic _ _ (cctx_comp_typing_soundness H' Q) gamma V) as H2.
      mp H2; [intros [] |].
      destruct H1 as (a1 & H1 & V1 & H1' & ?).
      destruct H2 as (a2 & H2 & V2 & H2' & ?).
      rewrite denc in H1. rewrite H1 in H2. apply mono_requirement in H2.
      rewrite H2 in H1'.
      specialize (ground_equiv G _ _ _ H1' H2') as H4'.
      assert (mkCBPVc (typeRet V1) ≃ mkCBPVc (typeRet V2)).
      eapply val_obseq_cctx_congruence with (C := cctxRet •__v); cbn; eauto.
      do 2 constructor.
      rewrite H4 in H0. rewrite <- H0 in H3.
      specialize (H3 _ _ (@cctxTypingHole _ false null _ I) v).
      cbn in H3. revert H3. repeat rewrite idSubst_comp; intros []; tauto.
  Qed.

   Theorem adequacyᵥ n (Gamma: ctx n) B (P Q: CBPVv Gamma B):
      (forall (gamma: denote_context T Gamma), denote_valtyping P gamma = denote_valtyping Q gamma) -> P ≈ Q.
  Proof.
    intros. intros G C H' v.
      set (gamma := (fun (i: fin 0) => match i with end):  denote_context T null).
      set (V :=  (fun (i: fin 0) => match i with end): (forall (i : fin 0), CCBPVv (null i))).

      destruct (denotation_context T true null) as [_ denc].
      specialize (denc _ _ _ _ _ H' _ _ P Q H).
      destruct (basic_lemma null) as [_ basic].
      specialize (basic _ _ (cctx_value_typing_soundness H' P) gamma V) as H1.
      mp H1; [intros [] |].
      specialize (basic _ _ (cctx_value_typing_soundness H' Q) gamma V) as H2.
      mp H2; [intros [] |].
      destruct H1 as (a1 & H1 & V1 & H1' & ?).
      destruct H2 as (a2 & H2 & V2 & H2' & ?).
      rewrite denc in H1. rewrite H1 in H2. apply mono_requirement in H2.
      rewrite H2 in H1'.
      specialize (ground_equiv G _ _ _ H1' H2') as H4'.
      assert (mkCBPVc (typeRet V1) ≃ mkCBPVc (typeRet V2)).
      eapply val_obseq_cctx_congruence with (C := cctxRet •__v); cbn; eauto.
      do 2 constructor.
      rewrite H4 in H0. rewrite <- H0 in H3.
      specialize (H3 _ _ (@cctxTypingHole _ false null _ I) v).
      cbn in H3. revert H3. repeat rewrite idSubst_comp; intros []; tauto.
  Qed.


End LogicalRelation.

(** ***  Soundness *)
Theorem soundness P (G: groundtype):
    null ⊢ P : F G -> exists (v: CCBPVv G), P >* ret v.
Proof.
  intros H.
  pose (gamma := (fun f => match f with end) : denote_context IdMonad null).
  pose (V := (fun f => match f with end) : forall (i : fin 0), CCBPVv (null i)).
  destruct (basic_lemma IdMonad null) as [_ H'].
  specialize (H' _ _ H gamma V). mp H'; [intros [] |].
  destruct H' as (a & H1 & H2 & H3 & H4); exists H2.
  specialize (H4 G •__c) ; mp H4; [ constructor |].
  specialize (H4 H2); cbn in H4.
  erewrite idSubst_comp in H4; firstorder.
  destruct x.
Qed.
