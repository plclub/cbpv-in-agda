Require Export CBN.
Require Export Syntax.
Require Export StrongReduction.
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

Lemma eagerlet_ty {n : nat} (Gamma : ctx n) (M : comp n) (N : comp (S n)) A B phi :
  Gamma ⊢ M : F A # phi -> A .: Gamma ⊢ N : B # phi -> Gamma ⊢ $$ <- M; N : B # phi.
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

(** ** Eager let and reduction *)

Lemma let_to_eagerlet {n} (M : comp n) N phi :
  letin M N >* eagerlet M N # phi.
Proof.
  destruct M; eauto.
Admitted.

(** ** Eager let is a congruence *)

(** *** Weak reduction *)

Instance proper_eagerlet_star_step_L : forall n phi,
    Proper (star (fun x y => step x y phi) ==> eq ==> star (fun x y => @step n x y phi)) eagerlet.
Proof.
Admitted.
(*
  intros n c1 c1' H ? c2 ->.
  destruct c1, c1'; cbn. all: try rewrite H; eauto.
  all: inv H. all: try inv H0. all:try inv H. reflexivity.
Qed.
*)

Instance proper_eagerlet_plus_step_L n phi : Proper (plus (fun x y => step x y phi) ==> eq ==> plus (fun x y => step x y phi)) (@eagerlet n).
Proof.
Admitted.
(*
  repeat (hnf; intros). subst. unfold eagerlet at 1. inv H. inv H0. inv H.
  all: try now (eapply step_star_plus; eauto using let_to_eagerlet).
  destruct x.
  all : try (eapply plusSingle in H0; trewrite H0).
  all: try now rewrite H1, let_to_eagerlet.
  inv H0. inv H.
Qed.
*)

(** *** Strong reduction *)

Instance proper_eagerlet_sstep_R : forall n, Proper (eq ==> sstep ==> plus (@sstep n)) eagerlet.
Proof.
  repeat (hnf; intros); subst.
  destruct (eagerlet_inv y x0) as [ [-> ] | (? & -> & ?)].
  - eapply step_star_plus; try rewrite <- let_to_eagerlet; try reflexivity; eauto.
Admitted.
(*
  - rewrite e. cbn. eapply plus_sstep_preserves. eauto.
Qed.
*)

Instance proper_eagerlet_star_ssstep_R n :
  Proper (eq ==> star sstep ==> star (@sstep n)) eagerlet.
Proof.
  repeat (hnf; intros). subst. induction H0.
  - reflexivity.
  - now rewrite <- IHstar, H.
Qed.

Instance proper_eagerlet_plus_sstep_R n :
  Proper (eq ==> plus sstep ==> plus (@sstep n)) eagerlet.
Proof.
  repeat (hnf; intros). subst. induction H0.
  - destruct y; cbn; eauto.  eapply plus_sstep_preserves. eauto.
  - rewrite <- IHplus. destruct y; cbn; eauto.  eapply plus_sstep_preserves. eauto.
Qed.


Instance proper_eagerlet_sstep_L_star n :
  Proper (sstep ==> eq ==> star (@sstep n)) (eagerlet).
Proof.
  repeat (hnf; intros). subst.
  destruct x; cbn.
  all: try now rewrite <- let_to_eagerlet, H.
  inv H; try inv H0. cbn.
Admitted.
(*eapply proper_subst_comp.
  intros []; cbn; eauto.
Qed.
*)

Instance proper_eagerlet_star_sstep_L n  :
  Proper (star sstep ==> eq ==> star (@sstep n)) (eagerlet).
Proof.
  repeat (hnf; intros). subst. induction H; eauto.
  now rewrite H, IHstar.
Qed.

Lemma proper_eagerlet_star_sstep n  :
  Proper (star sstep ==> star sstep ==> star (@sstep n)) (eagerlet).
Proof.
  repeat (hnf; intros). now rewrite H, H0.
Qed.


Lemma proper_eagerlet_sstep_L n (M M' : comp n) N :
  sstep M M' -> (forall V V', sstep_value V V' -> plus sstep (subst_comp (V..) N) (subst_comp (V'..) N)) -> plus sstep (eagerlet M N) (eagerlet M' N).
Proof.
  intros. inv H; cbn; eauto.
  inv H1; cbn; eauto; eapply step_star_plus; try rewrite <- let_to_eagerlet; try reflexivity; eauto.
Admitted.

Lemma proper_eagerlet_plus_sstep_L n (M M' : comp n) N :
  plus sstep M M' -> (forall V V', sstep_value V V' -> plus sstep (subst_comp (V..) N) (subst_comp (V'..) N)) -> plus sstep (eagerlet M N) (eagerlet M' N).
Proof.
  intros. induction H.
  - eapply proper_eagerlet_sstep_L; eauto.
  - rewrite <- IHplus. eapply proper_eagerlet_sstep_L; eauto.
Qed.
