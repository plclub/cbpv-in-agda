(**
  This file contains the syntactic typing judegment,
  as well as type preservation under substitution and
  progress and preservation proofs
*)
Set Implicit Arguments.
Require Import Psatz  Logic List Classes.Morphisms.
Import List Notations.

Require Export CBPV.Terms CBPV.Base CBPV.Semantics.
Import CommaNotation.

(** * Syntactic Typing Judement  *)
Reserved Notation "Gamma ⊢ c : A" (at level 80, c at level 99).
Reserved Notation "Gamma ⊩ v : A" (at level 80, v at level 99).

(** Syntactic typing judgement using DeBrujin indices *)
Definition ctx (n: nat) := fin n -> valtype.

(** ** Value Typing Judgement *)
Inductive value_typing {m: nat} (Gamma: ctx m) : value m -> valtype -> Type :=
| typeVar i : Gamma ⊩ var_value i : Gamma i
| typeUnit: Gamma ⊩ u : one
| typePair v1 v2 A1 A2:
    Gamma ⊩ v1 : A1 -> Gamma ⊩ v2 : A2 -> Gamma ⊩ pair v1 v2 : cross A1 A2
| typeSum A1 A2 (b: bool) v:
    Gamma ⊩ v : (if b then A1 else A2) -> Gamma ⊩ inj b v : Sigma A1 A2
| typeThunk c A:
    Gamma ⊢ c : A -> Gamma ⊩ thunk c : U A
where "Gamma ⊩ v : A" := (value_typing Gamma v A)

(** ** Computation Typing Judgement *)
with computation_typing {m: nat} (Gamma: ctx m) : comp m -> comptype -> Type :=
| typeCone: Gamma ⊢ cu : cone
| typeLambda (c: comp (S m)) A B:
    A .: Gamma ⊢ c : B -> (Gamma ⊢ lambda c : A → B)
| typeLetin c1 c2 A B:
    Gamma ⊢ c1 : F A -> A .: Gamma ⊢ c2 : B -> Gamma ⊢ $ <- c1; c2 : B
| typeRet v A:
    Gamma ⊩ v : A -> Gamma ⊢ ret v : F A
| typeApp c v A B:
    Gamma ⊢ c : A → B -> Gamma ⊩ v : A -> Gamma ⊢ c v : B
| typeTuple c1 c2 B1 B2:
    Gamma ⊢ c1 : B1  -> Gamma ⊢ c2 : B2 -> Gamma ⊢ tuple c1 c2 : Pi B1 B2
| typeProj b c B1 B2:
    Gamma ⊢ c : Pi B1 B2 -> Gamma ⊢ proj b c : (if b then B1 else B2)
| typeForce v A:
    Gamma ⊩ v : U A -> Gamma ⊢ v! : A
| typeCaseZ v A: Gamma ⊩ v : zero -> Gamma ⊢ caseZ v : A
| typeCaseS v c1 c2 A1 A2 C:
    Gamma ⊩ v : Sigma A1 A2 ->
    A1, Gamma ⊢ c1 : C ->
    A2, Gamma ⊢ c2 : C ->
    Gamma ⊢ caseS v c1 c2 : C
| typeCaseP v c A B C:
    Gamma ⊩ v : A * B ->
    B, A, Gamma  ⊢ c : C ->
    Gamma ⊢ caseP v c : C
where "Gamma ⊢ c : A" := (@computation_typing _ Gamma c A).

Scheme value_typing_ind_2 := Minimality for value_typing Sort Prop
  with computation_typing_ind_2  := Minimality for computation_typing Sort Prop.

Scheme value_typing_ind_3 := Minimality for value_typing Sort Type
  with computation_typing_ind_3  := Minimality for computation_typing Sort Type.

Combined Scheme mutind_value_computation_typing from
         value_typing_ind_2, computation_typing_ind_2.

Scheme value_typing_ind_4 := Induction for value_typing Sort Prop
    with computation_typing_ind_4  := Induction for computation_typing Sort Prop.

Combined Scheme mutindt_value_computation_typing from
          value_typing_ind_4, computation_typing_ind_4.

Hint Constructors computation_typing value_typing.


(** Type judgement inversion *)
Ltac invt :=
  match goal with
  | [H: (_ ⊢ cu : _) |- _] => inv H
  | [H: (_ ⊢ lambda _ : _) |- _] => inv H
  | [H: (_ ⊢ _ ! : _) |- _] => inv H
  | [H: (_ ⊢ $ <- _; _ : _) |- _] => inv H
  | [H: (_ ⊢ ret _ : _) |- _] => inv H
  | [H: (_ ⊢ app _ _ : _) |- _] => inv H
  | [H: (_ ⊢ tuple _ _ : _) |- _] => inv H
  | [H: (_ ⊢ proj _ _ : _) |- _] => inv H
  | [H: (_ ⊢ _ ! : _) |- _] => inv H
  | [H: (_ ⊢ proj _ _ : _) |- _] => inv H
  | [H: (_ ⊢ caseZ _ : _) |- _] => inv H
  | [H: (_ ⊢ caseS _ _ _ : _) |- _] => inv H
  | [H: (_ ⊢ caseP _ _ : _) |- _] => inv H
  | [H: (_ ⊩ var_value _ : _) |- _] => inv H
  | [H: (_ ⊩ u : _) |- _] => inv H
  | [H: (_ ⊩ pair _ _  : _) |- _] => inv H
  | [H: (_ ⊩ inj _ _  : _) |- _] => inv H
  | [H: (_ ⊩ <{ _ }>  : _) |- _] => inv H
  | [H: (_ ⊩ _ : zero) |- _] => inv H
  end.


(** Automation friendly version of the variable constructor *)
Lemma typeVar' n (Gamma : ctx n) A i: Gamma i = A -> Gamma ⊩ var_value i : A.
Proof. intros <-; constructor. Qed.

Hint Resolve typeVar'.


(** ** Type Preservation under Substitution *)

(** Type preservation under renaming  *)
Fixpoint value_typepres_renaming n Gamma v A (H: Gamma ⊩ v : A)  m (delta: fin n -> fin m) Delta {struct H}:
  (forall i, Gamma i = Delta (delta i)) -> Delta ⊩ ren_value delta v : A
with comp_typepres_renaming n Gamma c B (H: Gamma ⊢ c : B) m (delta: fin n -> fin m) Delta {struct H}:
  (forall i, Gamma i = Delta (delta i)) -> Delta ⊢ ren_comp delta c : B.
Proof.
  all: destruct H; cbn; intros; eauto; econstructor; eauto;
    eapply comp_typepres_renaming; eauto.
  all: auto_case.
Qed.


(** Type preservation under substitution  *)
Fixpoint value_typepres_substitution n (Gamma: ctx n) v A (H: Gamma ⊩ v : A)  m (sigma: fin n -> value m) Delta {struct H}:
  (forall i, Delta ⊩ sigma i : Gamma i) -> Delta ⊩ subst_value sigma v : A
with comp_typepres_substitution n (Gamma: ctx n) c B (H: Gamma ⊢ c : B) m (sigma: fin n -> value m) Delta {struct H}:
  (forall i, Delta ⊩ sigma i : Gamma i) -> Delta ⊢ subst_comp sigma c : B.
Proof.
    all: destruct H; cbn; intros; eauto; econstructor; eauto.
    all: eapply comp_typepres_substitution; eauto.
    all: auto_case; repeat (eapply value_typepres_renaming); eauto.
Qed.


(** ** Preservation *)
(** Type preservation under beta reduction  *)
Lemma typepres_beta {n: nat} (Gamma: fin n -> valtype) c v A B:
  A .: Gamma ⊢ c : B -> Gamma ⊩ v : A -> Gamma ⊢ subst_comp (v..) c : B.
Proof.
  intros H1 H2; eapply (comp_typepres_substitution H1); intros []; cbn; asimpl; eauto.
Qed.


(** Type preservation under primitive reduction  *)
Lemma primitive_preservation {n} (c c': comp n) Gamma A:
  c ≽ c' -> Gamma ⊢ c : A -> inhab (Gamma ⊢ c' : A).
Proof.
  destruct 1; intros H1; repeat invt; try destruct b; constructor; eauto using typepres_beta.
  eapply comp_typepres_substitution; [eassumption |]; auto_case.
Qed.


(** Type preservation under reduction  *)
Lemma preservation {n: nat} Gamma (c c': comp n) A:
  c > c' -> Gamma ⊢ c : A -> inhab (Gamma ⊢ c' : A).
Proof.
  induction 1 in Gamma, A |-*; [ now apply primitive_preservation | idtac.. ];
    intros; invt; destruct (IHstep _ _ X0); constructor; eauto.
Qed.

Lemma preservation_steps n (Gamma: ctx n)(c c': comp n) A:
    Gamma ⊢ c : A -> c >* c' -> inhab (Gamma ⊢ c' : A).
Proof.
  induction 2; eauto using preservation.
  specialize (preservation H X) as [H1]; eauto.
Qed.

(** ** Progress *)
Lemma progress (e: comp 0) (B: comptype) :
  null ⊢ e : B -> (exists e', e > e') \/ nf e.
Proof with (left; eexists; eauto).
  enough (
      forall n Gamma e B, Gamma ⊢ e : B ->
      (match n return ctx n -> Prop with 0 => fun Gamma => Gamma = null | _ => fun  _ => False end) Gamma ->
      (exists e', e > e') \/ nf e
    ) by eauto.
  induction 1; destruct m; intuition; subst Gamma.
  1, 3, 5: destruct H1...
  1 - 3: inv H1; invt...
  all: inv v0; try (destruct i)...
Qed.
