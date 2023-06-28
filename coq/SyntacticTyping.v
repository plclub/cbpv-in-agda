(**
  This file contains the syntactic typing judegment,
  as well as type preservation under substitution and
  progress and preservation proofs
*)
Set Implicit Arguments.
Require Import Psatz  Logic List Classes.Morphisms.
Import List Notations.

Require Export CBPV.Terms CBPV.Base.
Import CommaNotation.

(** * Syntactic Typing Judement  *)
Reserved Notation "Gamma ⊢ c : A # phi" (at level 80, c at level 99).
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
| typeThunk c A (phi : effect) : 
    Gamma ⊢ c : A # phi -> Gamma ⊩ thunk c : (U phi A ) 

where "Gamma ⊩ v : A" := (value_typing Gamma v A)

(** ** Computation Typing Judgement *)
with computation_typing {m: nat} (Gamma: ctx m) : comp m -> comptype -> effect -> Type :=
| typeCone phi: Gamma ⊢ cu : cone # phi

| typeLambda (c: comp (S m)) A B phi:
    A .: Gamma ⊢ c : B # phi -> (Gamma ⊢ lambda c : A → B # phi)

| typeLetin c1 c2 A B phi1 phi2 phi:
    Gamma ⊢ c1 : F A # phi1 -> A .: Gamma ⊢ c2 : B # phi2 
    -> subeff (add phi1 phi2) phi
    -> Gamma ⊢ $ <- c1; c2 : B # phi
| typeRet v A phi:
    Gamma ⊩ v : A -> Gamma ⊢ ret v : F A # phi
| typeApp c v A B phi:
    Gamma ⊢ c : A → B # phi -> Gamma ⊩ v : A -> Gamma ⊢ c v : B # phi
| typeTuple c1 c2 B1 B2 phi :
    Gamma ⊢ c1 : B1 # phi -> Gamma ⊢ c2 : B2 # phi -> Gamma ⊢ tuple c1 c2 : Pi B1 B2 # phi
| typeProj b c B1 B2 phi:
    Gamma ⊢ c : Pi B1 B2 # phi -> Gamma ⊢ proj b c : (if b then B1 else B2) # phi
| typeForce v A phi1 phi2:
    Gamma ⊩ v : U phi1 A 
   -> subeff phi1 phi2 -> Gamma ⊢ v! : A # phi2
| typeCaseZ v A phi : Gamma ⊩ v : zero -> Gamma ⊢ caseZ v : A # phi
| typeCaseS v c1 c2 A1 A2 C phi:
    Gamma ⊩ v : Sigma A1 A2 ->
    A1, Gamma ⊢ c1 : C # phi ->
    A2, Gamma ⊢ c2 : C # phi ->
    Gamma ⊢ caseS v c1 c2 : C # phi
| typeCaseP v c A B C phi:
    Gamma ⊩ v : A * B ->
    B, A, Gamma  ⊢ c : C # phi ->
    Gamma ⊢ caseP v c : C # phi 
| typeTock phi : 
    subeff tick phi ->
    Gamma ⊢ tock : F one # phi 
    
                
where "Gamma ⊢ c : A # phi" := (computation_typing Gamma c A phi).

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

#[export] Hint Constructors computation_typing value_typing : core.


(** Type judgement inversion *)
Ltac invt :=
  match goal with
  | [H: (_ ⊢ cu : _ # _) |- _] => inv H
  | [H: (_ ⊢ lambda _ : _ # _) |- _] => inv H
  | [H: (_ ⊢ _ ! : _ # _) |- _] => inv H
  | [H: (_ ⊢ $ <- _; _ : _ # _) |- _] => inv H
  | [H: (_ ⊢ ret _ : _ # _) |- _] => inv H
  | [H: (_ ⊢ app _ _ : _ # _ ) |- _] => inv H
  | [H: (_ ⊢ tuple _ _ : _ # _ ) |- _] => inv H
  | [H: (_ ⊢ proj _ _ : _ # _) |- _] => inv H
  | [H: (_ ⊢ caseZ _ : _ # _ ) |- _] => inv H
  | [H: (_ ⊢ caseS _ _ _ : _ # _) |- _] => inv H
  | [H: (_ ⊢ caseP _ _ : _ # _) |- _] => inv H
  | [H: (_ ⊢ tock : _ # _) |- _ ] => inv H
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

#[export] Hint Resolve typeVar' : core.




(** ** Type Preservation under Substitution *)

(** Type preservation under renaming  *)
Fixpoint value_typepres_renaming n Gamma v A (H: Gamma ⊩ v : A)  m (delta: fin n -> fin m) Delta {struct H}:
  (forall i, Gamma i = Delta (delta i)) -> Delta ⊩ ren_value delta v : A
with comp_typepres_renaming n Gamma c B phi (H: Gamma ⊢ c : B # phi) m (delta: fin n -> fin m) Delta {struct H}:
  (forall i, Gamma i = Delta (delta i)) -> Delta ⊢ ren_comp delta c : B # phi.
Proof.
  all: destruct H; cbn; intros; eauto; econstructor; eauto;
    eapply comp_typepres_renaming; eauto.
  all: auto_case.
Qed.


(** Type preservation under substitution  *)
Fixpoint value_typepres_substitution n (Gamma: ctx n) v A (H: Gamma ⊩ v : A)  m (sigma: fin n -> value m) Delta {struct H}:
  (forall i, Delta ⊩ sigma i : Gamma i) -> Delta ⊩ subst_value sigma v : A
with comp_typepres_substitution n (Gamma: ctx n) c B phi (H: Gamma ⊢ c : B # phi) m (sigma: fin n -> value m) Delta {struct H}:
  (forall i, Delta ⊩ sigma i : Gamma i) -> Delta ⊢ subst_comp sigma c : B # phi.
Proof.
    all: destruct H; cbn; intros; eauto; econstructor; eauto.
    all: eapply comp_typepres_substitution; eauto.
    all: auto_case; repeat (eapply value_typepres_renaming); eauto.
Qed.


#[export] Hint Resolve comp_typepres_substitution.

(** ** Preservation *)
(** Type preservation under beta reduction  *)
Lemma typepres_beta {n: nat} (Gamma: fin n -> valtype) c v A B phi:
  A .: Gamma ⊢ c : B # phi -> Gamma ⊩ v : A -> Gamma ⊢ subst_comp (v..) c : B # phi.
Proof.
  intros H1 H2; eapply (comp_typepres_substitution H1); intros []; cbn; asimpl; eauto.
Qed.

Lemma type_subeff {n: nat} (Gamma: fin n -> valtype) c B phi:
  Gamma ⊢ c : B # phi -> forall psi, subeff phi psi -> Gamma ⊢ c : B # psi.
Proof.
  induction 1; intros; eauto.
Qed.

#[export] Hint Resolve type_subeff : core.
