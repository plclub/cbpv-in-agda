
Set Implicit Arguments.
Require Import Psatz Logic List Classes.Morphisms.
Import List Notations.

Require Export Base.

Parameter effect : Type.

Parameter pure : effect.
Parameter tick : effect.
Parameter add : effect -> effect -> effect.

(* Monoid laws *)

Parameter eff_idL : forall {phi}, add pure phi = phi.
Parameter eff_idR : forall {phi}, add phi pure = phi.
Parameter eff_assoc : forall {phi1 phi2 phi3}, add (add phi1 phi2) phi3 = add phi1 (add phi2 phi3).

#[export] Hint Resolve eff_idL eff_idR eff_assoc : core.
#[export] Hint Rewrite @eff_idL @eff_idR @eff_assoc : core.

(* Preordered monoid: preorder compatible with add *)

Inductive subeff : effect -> effect -> Prop :=
  | subeff_refl phi : subeff phi phi
  | subeff_trans phi1 phi2 phi3 :
    subeff phi1 phi2 -> subeff phi2 phi3 -> subeff phi1 phi3
  | subeff_add_right_compatible phi1 phi2 phi :
    subeff phi1 phi2 -> subeff (add phi1 phi) (add phi2 phi)
  | subeff_add_left_compatible phi1 phi2 phi :
    subeff phi1 phi2 -> subeff (add phi phi1) (add phi phi2).

#[export] Hint Constructors subeff : core.

Parameter subeff_pure : forall {phi}, subeff pure phi.

Theorem subeff_addright : forall {phi1 phi2}, subeff phi1 (add phi1 phi2).
Proof.
  intros. rewrite <- eff_idR at 1. apply subeff_add_left_compatible. apply subeff_pure.
Qed.

Theorem subeff_addleft : forall {phi1 phi2}, subeff phi1 (add phi2 phi1).
Proof.
  intros. rewrite <- eff_idL at 1. apply subeff_add_right_compatible. apply subeff_pure.
Qed.

#[export] Hint Resolve subeff_addright subeff_addleft.
