Set Implicit Arguments.

Require Export StrongReduction ObservationalEquivalence Confluence SemanticTyping.


Lemma ssteps_congruence m n (K: cctx false m n) M N:
  M ↪* N -> fillc K M ↪* fillc K N.
Proof.
  induction 1; eauto using sstep_congruence.
Qed.

Lemma ground_normal n (V: value n) (Gamma: ctx n) (G: groundtype):
  Gamma ⊩ V : G -> Normal sstep_value V.
Proof.
  induction G in V |-*; intros H; inv H.
  all: intros t H; inv H.
  - destruct b. 
    + eapply IHG1; eauto.
    + eapply IHG2; eauto.
  - eapply IHG1; eauto.
  - eapply IHG2; eauto.
Qed.


Lemma ground_ret_normal n (V: value n) (Gamma: ctx n) (G: groundtype):
  Gamma ⊢ ret V : F G -> Normal sstep (ret V).
Proof.
  intros H; inv H.
  intros t H; inv H.
  - eapply ground_normal; eauto.
  - inv H0.
Qed.




Lemma soundness' n (Gamma: ctx n) A (M N: CBPVc Gamma A):
  M ↪* N -> M ≃ N.
Proof.
  intros H ? K H1 v. split; intros H2. 
  - assert (fillc K M ↪* fillc K N) by now apply ssteps_congruence.
    assert (fillc K M ↪* ret v) by now rewrite H2.
    assert (null ⊢ fillc K M : F G) by (eapply cctx_comp_typing_soundness; eauto).
    assert (null ⊢ fillc K N : F G) by (eapply cctx_comp_typing_soundness; eauto).
    assert (Normal sstep (ret v)).
    { specialize (ssteps_preservation H3 (inhabited X)) as [].
      eapply ground_ret_normal; eauto. }

    assert (fillc K N ↪* ret v).
    + destruct (sstep_confluent H0 H3) as [w ?].
      rewrite H5. enough (ret v = w) as -> by eauto.
      inv H6; eauto. exfalso; eapply H4; eauto. 
    + destruct (ClosedSemanticSoundness) as [_ sem].
      destruct (sem _ _ X0). intuition.
      destruct H8 as [w]; intuition; subst.
      eapply bigstep_soundness.
      enough (ret v = ret w) by congruence.
      eapply confluence_unique_normal_forms; eauto.
      { specialize (preservation_steps X0 (bigstep_soundness H7)) as [].
      eapply ground_ret_normal; eauto. }
      eapply bigstep_soundness in H7. rewrite H7. reflexivity. 
  - assert (fillc K M ↪* ret v).
    + rewrite <-H2. now apply ssteps_congruence.
    + assert (null ⊢ fillc K M : F G) by (eapply cctx_comp_typing_soundness; eauto).
      assert (null ⊢ fillc K N : F G) by (eapply cctx_comp_typing_soundness; eauto).
      destruct (ClosedSemanticSoundness) as [_ sem].
      destruct (sem _ _ X). intuition.
      destruct H5 as [w]; intuition; subst.
      eapply bigstep_soundness.
      enough (ret v = ret w) by congruence.
      eapply confluence_unique_normal_forms; eauto.
      * specialize (preservation_steps X0 H2) as [].
        eapply ground_ret_normal; eauto.
      * specialize (preservation_steps X (bigstep_soundness H4)) as [].
        eapply ground_ret_normal; eauto.
      * eapply bigstep_soundness in H4. rewrite H4. reflexivity.
Qed.

