(*
Parts of this file are copied and modified from the Coq Demos of the lecture Semantics at UdS:
http://www.ps.uni-saarland.de/courses/sem-ws17/confluence.v
 *)

Set Implicit Arguments.
Require Import Morphisms.
Require Export CBPV.Base CBPV.AbstractReductionSystems Setoid.

Section Takahashi.
  Variables (X: Type)  (R: X -> X -> Prop).
  Implicit Types (x y z : X).
  Notation "x > y" := (R x y) (at level 70).
  Notation "x >* y" := (star R x y) (at level 60).

  Definition tak_fun rho := forall x y, x > y -> y > rho x.

  Variables (rho: X -> X) (tak: tak_fun rho).

  Fact tak_diamond :
    diamond R.
  Proof.
    intros x y z H1 % tak H2 % tak. exists (rho x); auto.
  Qed.

  Fact tak_sound x :
    Reflexive R -> x > rho x.
  Proof.
    intros H. apply tak, H.
  Qed.

  Fact tak_mono x y :
    x > y -> rho x > rho y.
  Proof.
    intros H % tak % tak. exact H.
  Qed.

  Fact tak_mono_n x y n :
    x > y -> it rho n x > it rho n y.
  Proof.
    intros H.
    induction n as [|n IH]; cbn.
    - exact H.
    - apply tak_mono, IH.
  Qed.

  Fact tak_cofinal x y :
    x >* y -> exists n, y >* it rho n x.
  Proof.
    induction 1 as [x |x x' y H _ (n&IH)].
    - exists 0. cbn. constructor.
    - exists (S n). rewrite IH. cbn.
      apply star_exp. apply tak, tak_mono_n, H.
  Qed.

End Takahashi.

Section TMT.
  Variables (X: Type) (R S: X -> X -> Prop)
            (H1: R <<= S) (H2: S <<= star R).

  Fact sandwich_equiv :
    star R === star S.
  Proof.
    split.
    - apply star_mono, H1.
    - intros x y H3. apply star_idem. revert x y H3.
      apply star_mono, H2.                            
  Qed.

  Fact sandwich_confluent :
    diamond S -> confluent R.
  Proof.
    intros H3 % diamond_confluent.
    revert H3. apply diamond_ext, sandwich_equiv; auto.
  Qed.

  Theorem TMT rho :
    Reflexive S -> tak_fun S rho -> confluent R.
  Proof.
    intros H3 H4. 
    eapply sandwich_confluent, tak_diamond, H4.
  Qed.
   
End TMT.
