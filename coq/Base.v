(** This file contains basic tactics and useful lemmas/types *)
Set Implicit Arguments.
Require Export Morphisms.

(** Usable version of iter: *)
(** Taken from: http://www.ps.uni-saarland.de/courses/sem-ws17/confluence.v *)

Section Iter.
  Variables (X: Type) (f: X -> X).

  Fixpoint it n x : X :=
    match n with
    | 0 => x
    | S n'=> f (it n' x)
    end.

  Fact it_shift n x :
    f (it n x) = it n (f x).
  Proof.
    induction n; cbn; congruence.
  Qed.

End Iter.

Notation "{ x & P }" := (sigT (fun x => P)) : type_scope.


(** _Type inhabitace_ – Conversion from Type to Prop due to restriction
    on elimination in Prop. Having typing judgements in Type we sometimes 
    need to return a wrapped version of them to match on propositions. 
    See progress. *)

Inductive inhab (X: Type) :Prop :=
  | inhabited: X -> inhab X.


(** Pretty version of inversion *)
Ltac inv H := inversion H; subst; clear H.


Ltac invp R :=
  match goal with
  | [ H: R _ |- _] => inv H
  | [ H: R _ _ |- _] => inv H
  | [ H: R _ _ _ |- _] => inv H
  | [ H: R _ _ _ _ |- _] => inv H
  | [ H: R _ _ _ _ _ |- _] => inv H
  | [ H: R _ _ _ _ _ _ |- _] => inv H
  | [ H: R _ _ _ _ _ _ _ |- _] => inv H
  | [ H: R _ _ _ _ _ _ _ _ |- _] => inv H
  | [ H: R _ _ _ _ _ _ _ _ _ |- _] => inv H
  | [ H: R _ _ _ _ _ _ _ _ _  _|- _] => inv H
  end.

Ltac inject :=
  repeat match goal with
  | [H: ?C _ = ?C _ |- _] => injection H as ->
  | [H: ?C _ _ = ?C _ _ |- _] => injection H as -> ->
  | [H: ?C _ _ _ = ?C _ _ _ |- _] => injection H as -> -> ->
  | [H: ?C _ _ _ _ = ?C _ _ _ _ |- _] => injection H as -> -> -> ->
  | [H: ?C _ _ _ _ _ = ?C _ _ _ _ _ |- _] => injection H as -> -> -> -> ->
  end.



(** Automatically destruct existential quantifier *)
Ltac exdestruct :=
    match goal with
    | [ H: ex ?P     |- _] => destruct H
    | [ H: ex2 ?P ?Q |- _] => destruct H
    | [ H: sig ?P    |- _] => destruct H
    | [ H: sigT ?P   |- _] => destruct H
    end.

Ltac exintuition := intuition; repeat exdestruct; intuition.


(** Reduction tactic for beta reduction step *)
Ltac reduce := econstructor 2; [ solve [eauto] | cbn ].

(** _Modus Ponens_ - applies to implications,
    will generate a subgoal for the premise of H and then specialize H with the result *)
Ltac mp H :=
let x := fresh "H" in
    match type of H with
    | ?Q -> ?P => assert P as x; [apply H | clear H; assert P as H by exact x; clear x]
    end.
