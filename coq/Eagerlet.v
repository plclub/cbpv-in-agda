Require Export Syntax Types SyntacticTyping.
Require Export AbstractReductionSystems Base.
Require Import Morphisms.

Lemma ctx_plus n m (x y : comp n) C (R : forall n, comp n -> comp n -> Prop) :
  plus (R n) x y ->
  (Proper (plus (@R n) ==> plus (@R m)) C) ->
  plus (R m) (C x) (C y).
Proof.
  intros. hnf in H0. now eapply H0.
Qed.

Ltac trewrite H :=
  match type of H with
  | plus ?R ?y _ =>
    match R with ?R ?a =>
    match goal with
    | [ |- plus (R ?n) ?x' ?z ] =>
      match x' with
        context C' [y] =>
        let G := constr:(fun v => ltac:(let r := context C'[v] in exact r)) in
        change (plus (@R n) (G y) z);
        eapply plus_star_step;
        [ eapply ctx_plus with (x := y) (C := G) (1 := H) ; (try (typeclasses eauto)); try now (hnf; induction 1; eauto)  | ]
      end
    end end
  end.


(** * Eager let *)

(** ** Definition of eager let *)

Definition eagerlet {n} (M : comp n) (N : comp (S n)) :=
  match M with
  | ret V => subst_comp (V..) N
  | M => letin M N
  end.

Notation "$$ <- A ; B" := (eagerlet A B) (at level 55).

(** ** Inversion for eager let *)

Lemma eagerlet_inv {n} (M : comp n) N :
  ((eagerlet M N = letin M N) * ~ exists V, M = ret V) + ({V & prod (M = ret V) (eagerlet M N = subst_comp (V..) N)}).
Proof.
  destruct M. all: try (left; firstorder congruence).
  right; cbn; eauto.
Qed.

Ltac eagerlet_inv H :=
  match type of H with
  | context[ eagerlet ?M ?N ] => destruct (eagerlet_inv M N) as [(? & ?) | (? & ? & ?)]
  end.

(** ** Typing for eager let *)

Lemma eagerlet_ty {n : nat} (Gamma : ctx n) (M : comp n) (N : comp (S n)) A B phi1 phi2 phi :
  Gamma ⊢ M : F A # phi1 -> A .: Gamma ⊢ N : B # phi2 ->
  subeff (add phi1 phi2) phi -> Gamma ⊢ $$ <- M; N : B # phi.
Proof.
  unfold eagerlet. intros. destruct M; eauto. inv X.
  eapply comp_typepres_substitution; eauto.
  intros. destruct i; cbn; asimpl; eauto.
Qed.

(** ** Eager let and substitutions *)

Lemma eagerlet_rencomp {m n : nat} (sigma  : fin n -> fin m) (M : comp n) (N : comp (S n)) :
  ren_comp sigma (eagerlet M N) = eagerlet (ren_comp sigma M) (ren_comp (upRen_value_value sigma) N).
Proof.
  destruct M; cbn; try reflexivity. now asimpl.
Qed.

Lemma eagerlet_substcomp {m n : nat} (sigma  : fin n -> value m) (M : comp n) (N : comp (S n)) :
   subst_comp sigma (eagerlet M N) = eagerlet (subst_comp sigma M) (subst_comp (up_value_value sigma) N).
Proof.
  destruct M; cbn; try reflexivity. now asimpl.
Qed.
