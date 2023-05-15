(** This file contains the definitions of types + notations for terms *)

Set Implicit Arguments.
Require Import Psatz Logic List Classes.Morphisms.
Import List Notations.

Require Export Syntax Base AbstractReductionSystems.

(** Extension to the Syntax file *)
(** Mututal Inductive Scheme for values and computations *)
Scheme value_ind_2 := Induction for value Sort Prop
  with comp_ind_2  := Induction for comp Sort Prop.

Combined Scheme mutind_val_comp from value_ind_2, comp_ind_2.

(** * CBPV Types *)
(**
  Types of CBPV terms.
  Values in valtype are types of values
  and values in comptype are types of computations
*)
(*
(** ** Value Types*)
Inductive valtype : Type :=
| zero: valtype
| one: valtype
| U: comptype -> valtype
| Sigma: valtype -> valtype -> valtype
| cross: valtype -> valtype -> valtype

(** ** Computation Types*)
with comptype : Type :=
| cone: comptype
| F: valtype -> comptype
| Pi: comptype -> comptype -> comptype
| arrow: valtype -> comptype -> comptype.
*)

(** Combined induction schemes for types *)
Scheme valtype_ind_2 := Induction for valtype Sort Prop
  with comptype_ind_2  := Induction for comptype Sort Prop.

Combined Scheme mutind_valtype_comptype from valtype_ind_2, comptype_ind_2.



(** ** Ground Types*)
(** Ground Types, they only contain One, Sums and Pairs *)
Inductive groundtype : Type :=
| gone : groundtype
| gsum : groundtype -> groundtype -> groundtype
| gcross : groundtype -> groundtype -> groundtype.

(** We use the follwing obvious mapping from ground types to valtypes as a coercion,
    which hepls the notion on paper that every ground type is a valtype *)
Fixpoint to_valtype (G: groundtype) :=
  match G with
  | gone => one
  | gsum G1 G2 => Sigma (to_valtype  G1) (to_valtype  G2)
  | gcross G1 G2 => cross (to_valtype  G1) (to_valtype  G2)
  end.

Coercion to_valtype: groundtype >-> valtype.

Fixpoint nat_to_fin {m: nat} (n: nat)  : fin (S (it S n m)) :=
  match n with
  | O => var_zero
  | S n => Some (nat_to_fin n)
  end.

Definition var {m: nat} (n: nat) : value (S (it S n m)) :=
  var_value (nat_to_fin n).

(** We use the following notations for terms  *)
Notation "<{ c }>" := (thunk c).
Notation "c !" := (force c) (at level 50).
Notation "$ <- A ; B" := (letin A B) (at level 55).
(* Notation "⟨ A ; B ⟩" := (pair A B) (at level 52). *)
Notation "A → B" := (arrow A B) (at level 53).
Notation "A * B" := (cross A B).
Coercion app : comp >-> Funclass.
