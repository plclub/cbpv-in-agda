Require Export fintype.

Inductive type  : Type :=
  | Unit : type 
  | Arr : type  -> type  -> type 
  | Cross : type  -> type  -> type 
  | Plus : type  -> type  -> type .

Lemma congr_Unit  : Unit  = Unit  .
Proof. congruence. Qed.

Lemma congr_Arr  { s0 : type  } { s1 : type  } { t0 : type  } { t1 : type  } : s0 = t0 -> s1 = t1 -> Arr s0 s1 = Arr t0 t1 .
Proof. congruence. Qed.

Lemma congr_Cross  { s0 : type  } { s1 : type  } { t0 : type  } { t1 : type  } : s0 = t0 -> s1 = t1 -> Cross s0 s1 = Cross t0 t1 .
Proof. congruence. Qed.

Lemma congr_Plus  { s0 : type  } { s1 : type  } { t0 : type  } { t1 : type  } : s0 = t0 -> s1 = t1 -> Plus s0 s1 = Plus t0 t1 .
Proof. congruence. Qed.

Inductive exp (nexp : nat) : Type :=
  | var_exp : fin (nexp) -> exp (nexp)
  | One : exp (nexp)
  | Lam : exp (S nexp) -> exp (nexp)
  | App : exp (nexp) -> exp (nexp) -> exp (nexp)
  | Pair : exp (nexp) -> exp (nexp) -> exp (nexp)
  | Proj : bool  -> exp (nexp) -> exp (nexp)
  | Inj : bool  -> exp (nexp) -> exp (nexp)
  | CaseS : exp (nexp) -> exp (S nexp) -> exp (S nexp) -> exp (nexp).

Lemma congr_One { mexp : nat } : One (mexp) = One (mexp) .
Proof. congruence. Qed.

Lemma congr_Lam { mexp : nat } { s0 : exp (S mexp) } { t0 : exp (S mexp) } : s0 = t0 -> Lam (mexp) s0 = Lam (mexp) t0 .
Proof. congruence. Qed.

Lemma congr_App { mexp : nat } { s0 : exp (mexp) } { s1 : exp (mexp) } { t0 : exp (mexp) } { t1 : exp (mexp) } : s0 = t0 -> s1 = t1 -> App (mexp) s0 s1 = App (mexp) t0 t1 .
Proof. congruence. Qed.

Lemma congr_Pair { mexp : nat } { s0 : exp (mexp) } { s1 : exp (mexp) } { t0 : exp (mexp) } { t1 : exp (mexp) } : s0 = t0 -> s1 = t1 -> Pair (mexp) s0 s1 = Pair (mexp) t0 t1 .
Proof. congruence. Qed.

Lemma congr_Proj { mexp : nat } { s0 : bool  } { s1 : exp (mexp) } { t0 : bool  } { t1 : exp (mexp) } : s0 = t0 -> s1 = t1 -> Proj (mexp) s0 s1 = Proj (mexp) t0 t1 .
Proof. congruence. Qed.

Lemma congr_Inj { mexp : nat } { s0 : bool  } { s1 : exp (mexp) } { t0 : bool  } { t1 : exp (mexp) } : s0 = t0 -> s1 = t1 -> Inj (mexp) s0 s1 = Inj (mexp) t0 t1 .
Proof. congruence. Qed.

Lemma congr_CaseS { mexp : nat } { s0 : exp (mexp) } { s1 : exp (S mexp) } { s2 : exp (S mexp) } { t0 : exp (mexp) } { t1 : exp (S mexp) } { t2 : exp (S mexp) } : s0 = t0 -> s1 = t1 -> s2 = t2 -> CaseS (mexp) s0 s1 s2 = CaseS (mexp) t0 t1 t2 .
Proof. congruence. Qed.

Definition upRen_exp_exp { m : nat } { n : nat } (xi : fin (m) -> fin (n)) : _ :=
  up_ren xi.

Fixpoint ren_exp { mexp : nat } { nexp : nat } (xiexp : fin (mexp) -> fin (nexp)) (s : exp (mexp)) : _ :=
    match s with
    | var_exp (_) s => (var_exp (nexp)) (xiexp s)
    | One (_)  => One (nexp)
    | Lam (_) s0 => Lam (nexp) (ren_exp (upRen_exp_exp xiexp) s0)
    | App (_) s0 s1 => App (nexp) (ren_exp xiexp s0) (ren_exp xiexp s1)
    | Pair (_) s0 s1 => Pair (nexp) (ren_exp xiexp s0) (ren_exp xiexp s1)
    | Proj (_) s0 s1 => Proj (nexp) s0 (ren_exp xiexp s1)
    | Inj (_) s0 s1 => Inj (nexp) s0 (ren_exp xiexp s1)
    | CaseS (_) s0 s1 s2 => CaseS (nexp) (ren_exp xiexp s0) (ren_exp (upRen_exp_exp xiexp) s1) (ren_exp (upRen_exp_exp xiexp) s2)
    end.

Definition up_exp_exp { m : nat } { nexp : nat } (sigma : fin (m) -> exp (nexp)) : _ :=
  scons ((var_exp (S nexp)) var_zero) (funcomp (ren_exp shift) sigma).

Fixpoint subst_exp { mexp : nat } { nexp : nat } (sigmaexp : fin (mexp) -> exp (nexp)) (s : exp (mexp)) : _ :=
    match s with
    | var_exp (_) s => sigmaexp s
    | One (_)  => One (nexp)
    | Lam (_) s0 => Lam (nexp) (subst_exp (up_exp_exp sigmaexp) s0)
    | App (_) s0 s1 => App (nexp) (subst_exp sigmaexp s0) (subst_exp sigmaexp s1)
    | Pair (_) s0 s1 => Pair (nexp) (subst_exp sigmaexp s0) (subst_exp sigmaexp s1)
    | Proj (_) s0 s1 => Proj (nexp) s0 (subst_exp sigmaexp s1)
    | Inj (_) s0 s1 => Inj (nexp) s0 (subst_exp sigmaexp s1)
    | CaseS (_) s0 s1 s2 => CaseS (nexp) (subst_exp sigmaexp s0) (subst_exp (up_exp_exp sigmaexp) s1) (subst_exp (up_exp_exp sigmaexp) s2)
    end.

Definition upId_exp_exp { mexp : nat } (sigma : fin (mexp) -> exp (mexp)) (Eq : forall x, sigma x = (var_exp (mexp)) x) : forall x, (up_exp_exp sigma) x = (var_exp (S mexp)) x :=
  fun n => match n with
  | Some n => ap (ren_exp shift) (Eq n)
  | None => eq_refl
  end.

Fixpoint idSubst_exp { mexp : nat } (sigmaexp : fin (mexp) -> exp (mexp)) (Eqexp : forall x, sigmaexp x = (var_exp (mexp)) x) (s : exp (mexp)) : subst_exp sigmaexp s = s :=
    match s with
    | var_exp (_) s => Eqexp s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam (idSubst_exp (up_exp_exp sigmaexp) (upId_exp_exp (_) Eqexp) s0)
    | App (_) s0 s1 => congr_App (idSubst_exp sigmaexp Eqexp s0) (idSubst_exp sigmaexp Eqexp s1)
    | Pair (_) s0 s1 => congr_Pair (idSubst_exp sigmaexp Eqexp s0) (idSubst_exp sigmaexp Eqexp s1)
    | Proj (_) s0 s1 => congr_Proj (eq_refl s0) (idSubst_exp sigmaexp Eqexp s1)
    | Inj (_) s0 s1 => congr_Inj (eq_refl s0) (idSubst_exp sigmaexp Eqexp s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS (idSubst_exp sigmaexp Eqexp s0) (idSubst_exp (up_exp_exp sigmaexp) (upId_exp_exp (_) Eqexp) s1) (idSubst_exp (up_exp_exp sigmaexp) (upId_exp_exp (_) Eqexp) s2)
    end.

Definition upExtRen_exp_exp { m : nat } { n : nat } (xi : fin (m) -> fin (n)) (zeta : fin (m) -> fin (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_exp_exp xi) x = (upRen_exp_exp zeta) x :=
  fun n => match n with
  | Some n => ap shift (Eq n)
  | None => eq_refl
  end.

Fixpoint extRen_exp { mexp : nat } { nexp : nat } (xiexp : fin (mexp) -> fin (nexp)) (zetaexp : fin (mexp) -> fin (nexp)) (Eqexp : forall x, xiexp x = zetaexp x) (s : exp (mexp)) : ren_exp xiexp s = ren_exp zetaexp s :=
    match s with
    | var_exp (_) s => ap (var_exp (nexp)) (Eqexp s)
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam (extRen_exp (upRen_exp_exp xiexp) (upRen_exp_exp zetaexp) (upExtRen_exp_exp (_) (_) Eqexp) s0)
    | App (_) s0 s1 => congr_App (extRen_exp xiexp zetaexp Eqexp s0) (extRen_exp xiexp zetaexp Eqexp s1)
    | Pair (_) s0 s1 => congr_Pair (extRen_exp xiexp zetaexp Eqexp s0) (extRen_exp xiexp zetaexp Eqexp s1)
    | Proj (_) s0 s1 => congr_Proj (eq_refl s0) (extRen_exp xiexp zetaexp Eqexp s1)
    | Inj (_) s0 s1 => congr_Inj (eq_refl s0) (extRen_exp xiexp zetaexp Eqexp s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS (extRen_exp xiexp zetaexp Eqexp s0) (extRen_exp (upRen_exp_exp xiexp) (upRen_exp_exp zetaexp) (upExtRen_exp_exp (_) (_) Eqexp) s1) (extRen_exp (upRen_exp_exp xiexp) (upRen_exp_exp zetaexp) (upExtRen_exp_exp (_) (_) Eqexp) s2)
    end.

Definition upExt_exp_exp { m : nat } { nexp : nat } (sigma : fin (m) -> exp (nexp)) (tau : fin (m) -> exp (nexp)) (Eq : forall x, sigma x = tau x) : forall x, (up_exp_exp sigma) x = (up_exp_exp tau) x :=
  fun n => match n with
  | Some n => ap (ren_exp shift) (Eq n)
  | None => eq_refl
  end.

Fixpoint ext_exp { mexp : nat } { nexp : nat } (sigmaexp : fin (mexp) -> exp (nexp)) (tauexp : fin (mexp) -> exp (nexp)) (Eqexp : forall x, sigmaexp x = tauexp x) (s : exp (mexp)) : subst_exp sigmaexp s = subst_exp tauexp s :=
    match s with
    | var_exp (_) s => Eqexp s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam (ext_exp (up_exp_exp sigmaexp) (up_exp_exp tauexp) (upExt_exp_exp (_) (_) Eqexp) s0)
    | App (_) s0 s1 => congr_App (ext_exp sigmaexp tauexp Eqexp s0) (ext_exp sigmaexp tauexp Eqexp s1)
    | Pair (_) s0 s1 => congr_Pair (ext_exp sigmaexp tauexp Eqexp s0) (ext_exp sigmaexp tauexp Eqexp s1)
    | Proj (_) s0 s1 => congr_Proj (eq_refl s0) (ext_exp sigmaexp tauexp Eqexp s1)
    | Inj (_) s0 s1 => congr_Inj (eq_refl s0) (ext_exp sigmaexp tauexp Eqexp s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS (ext_exp sigmaexp tauexp Eqexp s0) (ext_exp (up_exp_exp sigmaexp) (up_exp_exp tauexp) (upExt_exp_exp (_) (_) Eqexp) s1) (ext_exp (up_exp_exp sigmaexp) (up_exp_exp tauexp) (upExt_exp_exp (_) (_) Eqexp) s2)
    end.

Fixpoint compRenRen_exp { kexp : nat } { lexp : nat } { mexp : nat } (xiexp : fin (mexp) -> fin (kexp)) (zetaexp : fin (kexp) -> fin (lexp)) (rhoexp : fin (mexp) -> fin (lexp)) (Eqexp : forall x, (funcomp zetaexp xiexp) x = rhoexp x) (s : exp (mexp)) : ren_exp zetaexp (ren_exp xiexp s) = ren_exp rhoexp s :=
    match s with
    | var_exp (_) s => ap (var_exp (lexp)) (Eqexp s)
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam (compRenRen_exp (upRen_exp_exp xiexp) (upRen_exp_exp zetaexp) (upRen_exp_exp rhoexp) (up_ren_ren (_) (_) (_) Eqexp) s0)
    | App (_) s0 s1 => congr_App (compRenRen_exp xiexp zetaexp rhoexp Eqexp s0) (compRenRen_exp xiexp zetaexp rhoexp Eqexp s1)
    | Pair (_) s0 s1 => congr_Pair (compRenRen_exp xiexp zetaexp rhoexp Eqexp s0) (compRenRen_exp xiexp zetaexp rhoexp Eqexp s1)
    | Proj (_) s0 s1 => congr_Proj (eq_refl s0) (compRenRen_exp xiexp zetaexp rhoexp Eqexp s1)
    | Inj (_) s0 s1 => congr_Inj (eq_refl s0) (compRenRen_exp xiexp zetaexp rhoexp Eqexp s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS (compRenRen_exp xiexp zetaexp rhoexp Eqexp s0) (compRenRen_exp (upRen_exp_exp xiexp) (upRen_exp_exp zetaexp) (upRen_exp_exp rhoexp) (up_ren_ren (_) (_) (_) Eqexp) s1) (compRenRen_exp (upRen_exp_exp xiexp) (upRen_exp_exp zetaexp) (upRen_exp_exp rhoexp) (up_ren_ren (_) (_) (_) Eqexp) s2)
    end.

Definition up_ren_subst_exp_exp { k : nat } { l : nat } { mexp : nat } (xi : fin (k) -> fin (l)) (tau : fin (l) -> exp (mexp)) (theta : fin (k) -> exp (mexp)) (Eq : forall x, (funcomp tau xi) x = theta x) : forall x, (funcomp (up_exp_exp tau) (upRen_exp_exp xi)) x = (up_exp_exp theta) x :=
  fun n => match n with
  | Some n => ap (ren_exp shift) (Eq n)
  | None => eq_refl
  end.

Fixpoint compRenSubst_exp { kexp : nat } { lexp : nat } { mexp : nat } (xiexp : fin (mexp) -> fin (kexp)) (tauexp : fin (kexp) -> exp (lexp)) (thetaexp : fin (mexp) -> exp (lexp)) (Eqexp : forall x, (funcomp tauexp xiexp) x = thetaexp x) (s : exp (mexp)) : subst_exp tauexp (ren_exp xiexp s) = subst_exp thetaexp s :=
    match s with
    | var_exp (_) s => Eqexp s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam (compRenSubst_exp (upRen_exp_exp xiexp) (up_exp_exp tauexp) (up_exp_exp thetaexp) (up_ren_subst_exp_exp (_) (_) (_) Eqexp) s0)
    | App (_) s0 s1 => congr_App (compRenSubst_exp xiexp tauexp thetaexp Eqexp s0) (compRenSubst_exp xiexp tauexp thetaexp Eqexp s1)
    | Pair (_) s0 s1 => congr_Pair (compRenSubst_exp xiexp tauexp thetaexp Eqexp s0) (compRenSubst_exp xiexp tauexp thetaexp Eqexp s1)
    | Proj (_) s0 s1 => congr_Proj (eq_refl s0) (compRenSubst_exp xiexp tauexp thetaexp Eqexp s1)
    | Inj (_) s0 s1 => congr_Inj (eq_refl s0) (compRenSubst_exp xiexp tauexp thetaexp Eqexp s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS (compRenSubst_exp xiexp tauexp thetaexp Eqexp s0) (compRenSubst_exp (upRen_exp_exp xiexp) (up_exp_exp tauexp) (up_exp_exp thetaexp) (up_ren_subst_exp_exp (_) (_) (_) Eqexp) s1) (compRenSubst_exp (upRen_exp_exp xiexp) (up_exp_exp tauexp) (up_exp_exp thetaexp) (up_ren_subst_exp_exp (_) (_) (_) Eqexp) s2)
    end.

Definition up_subst_ren_exp_exp { k : nat } { lexp : nat } { mexp : nat } (sigma : fin (k) -> exp (lexp)) (zetaexp : fin (lexp) -> fin (mexp)) (theta : fin (k) -> exp (mexp)) (Eq : forall x, (funcomp (ren_exp zetaexp) sigma) x = theta x) : forall x, (funcomp (ren_exp (upRen_exp_exp zetaexp)) (up_exp_exp sigma)) x = (up_exp_exp theta) x :=
  fun n => match n with
  | Some n => eq_trans (compRenRen_exp shift (upRen_exp_exp zetaexp) (funcomp shift zetaexp) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compRenRen_exp zetaexp shift (funcomp shift zetaexp) (fun x => eq_refl) (sigma n))) (ap (ren_exp shift) (Eq n)))
  | None => eq_refl
  end.

Fixpoint compSubstRen__exp { kexp : nat } { lexp : nat } { mexp : nat } (sigmaexp : fin (mexp) -> exp (kexp)) (zetaexp : fin (kexp) -> fin (lexp)) (thetaexp : fin (mexp) -> exp (lexp)) (Eqexp : forall x, (funcomp (ren_exp zetaexp) sigmaexp) x = thetaexp x) (s : exp (mexp)) : ren_exp zetaexp (subst_exp sigmaexp s) = subst_exp thetaexp s :=
    match s with
    | var_exp (_) s => Eqexp s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam (compSubstRen__exp (up_exp_exp sigmaexp) (upRen_exp_exp zetaexp) (up_exp_exp thetaexp) (up_subst_ren_exp_exp (_) (_) (_) Eqexp) s0)
    | App (_) s0 s1 => congr_App (compSubstRen__exp sigmaexp zetaexp thetaexp Eqexp s0) (compSubstRen__exp sigmaexp zetaexp thetaexp Eqexp s1)
    | Pair (_) s0 s1 => congr_Pair (compSubstRen__exp sigmaexp zetaexp thetaexp Eqexp s0) (compSubstRen__exp sigmaexp zetaexp thetaexp Eqexp s1)
    | Proj (_) s0 s1 => congr_Proj (eq_refl s0) (compSubstRen__exp sigmaexp zetaexp thetaexp Eqexp s1)
    | Inj (_) s0 s1 => congr_Inj (eq_refl s0) (compSubstRen__exp sigmaexp zetaexp thetaexp Eqexp s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS (compSubstRen__exp sigmaexp zetaexp thetaexp Eqexp s0) (compSubstRen__exp (up_exp_exp sigmaexp) (upRen_exp_exp zetaexp) (up_exp_exp thetaexp) (up_subst_ren_exp_exp (_) (_) (_) Eqexp) s1) (compSubstRen__exp (up_exp_exp sigmaexp) (upRen_exp_exp zetaexp) (up_exp_exp thetaexp) (up_subst_ren_exp_exp (_) (_) (_) Eqexp) s2)
    end.

Definition up_subst_subst_exp_exp { k : nat } { lexp : nat } { mexp : nat } (sigma : fin (k) -> exp (lexp)) (tauexp : fin (lexp) -> exp (mexp)) (theta : fin (k) -> exp (mexp)) (Eq : forall x, (funcomp (subst_exp tauexp) sigma) x = theta x) : forall x, (funcomp (subst_exp (up_exp_exp tauexp)) (up_exp_exp sigma)) x = (up_exp_exp theta) x :=
  fun n => match n with
  | Some n => eq_trans (compRenSubst_exp shift (up_exp_exp tauexp) (funcomp (up_exp_exp tauexp) shift) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compSubstRen__exp tauexp shift (funcomp (ren_exp shift) tauexp) (fun x => eq_refl) (sigma n))) (ap (ren_exp shift) (Eq n)))
  | None => eq_refl
  end.

Fixpoint compSubstSubst_exp { kexp : nat } { lexp : nat } { mexp : nat } (sigmaexp : fin (mexp) -> exp (kexp)) (tauexp : fin (kexp) -> exp (lexp)) (thetaexp : fin (mexp) -> exp (lexp)) (Eqexp : forall x, (funcomp (subst_exp tauexp) sigmaexp) x = thetaexp x) (s : exp (mexp)) : subst_exp tauexp (subst_exp sigmaexp s) = subst_exp thetaexp s :=
    match s with
    | var_exp (_) s => Eqexp s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam (compSubstSubst_exp (up_exp_exp sigmaexp) (up_exp_exp tauexp) (up_exp_exp thetaexp) (up_subst_subst_exp_exp (_) (_) (_) Eqexp) s0)
    | App (_) s0 s1 => congr_App (compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp s0) (compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp s1)
    | Pair (_) s0 s1 => congr_Pair (compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp s0) (compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp s1)
    | Proj (_) s0 s1 => congr_Proj (eq_refl s0) (compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp s1)
    | Inj (_) s0 s1 => congr_Inj (eq_refl s0) (compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS (compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp s0) (compSubstSubst_exp (up_exp_exp sigmaexp) (up_exp_exp tauexp) (up_exp_exp thetaexp) (up_subst_subst_exp_exp (_) (_) (_) Eqexp) s1) (compSubstSubst_exp (up_exp_exp sigmaexp) (up_exp_exp tauexp) (up_exp_exp thetaexp) (up_subst_subst_exp_exp (_) (_) (_) Eqexp) s2)
    end.

Definition rinstInst_up_exp_exp { m : nat } { nexp : nat } (xi : fin (m) -> fin (nexp)) (sigma : fin (m) -> exp (nexp)) (Eq : forall x, (funcomp (var_exp (nexp)) xi) x = sigma x) : forall x, (funcomp (var_exp (S nexp)) (upRen_exp_exp xi)) x = (up_exp_exp sigma) x :=
  fun n => match n with
  | Some n => ap (ren_exp shift) (Eq n)
  | None => eq_refl
  end.

Fixpoint rinst_inst_exp { mexp : nat } { nexp : nat } (xiexp : fin (mexp) -> fin (nexp)) (sigmaexp : fin (mexp) -> exp (nexp)) (Eqexp : forall x, (funcomp (var_exp (nexp)) xiexp) x = sigmaexp x) (s : exp (mexp)) : ren_exp xiexp s = subst_exp sigmaexp s :=
    match s with
    | var_exp (_) s => Eqexp s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam (rinst_inst_exp (upRen_exp_exp xiexp) (up_exp_exp sigmaexp) (rinstInst_up_exp_exp (_) (_) Eqexp) s0)
    | App (_) s0 s1 => congr_App (rinst_inst_exp xiexp sigmaexp Eqexp s0) (rinst_inst_exp xiexp sigmaexp Eqexp s1)
    | Pair (_) s0 s1 => congr_Pair (rinst_inst_exp xiexp sigmaexp Eqexp s0) (rinst_inst_exp xiexp sigmaexp Eqexp s1)
    | Proj (_) s0 s1 => congr_Proj (eq_refl s0) (rinst_inst_exp xiexp sigmaexp Eqexp s1)
    | Inj (_) s0 s1 => congr_Inj (eq_refl s0) (rinst_inst_exp xiexp sigmaexp Eqexp s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS (rinst_inst_exp xiexp sigmaexp Eqexp s0) (rinst_inst_exp (upRen_exp_exp xiexp) (up_exp_exp sigmaexp) (rinstInst_up_exp_exp (_) (_) Eqexp) s1) (rinst_inst_exp (upRen_exp_exp xiexp) (up_exp_exp sigmaexp) (rinstInst_up_exp_exp (_) (_) Eqexp) s2)
    end.

Lemma instId_exp { mexp : nat } : subst_exp (var_exp (mexp)) = id .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => idSubst_exp (var_exp (mexp)) (fun n => eq_refl) (id x))). Qed.

Lemma varL_exp { mexp : nat } { nexp : nat } (sigmaexp : fin (mexp) -> exp (nexp)) : funcomp (subst_exp sigmaexp) (var_exp (mexp)) = sigmaexp .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => eq_refl)). Qed.

Lemma varLRen_exp { mexp : nat } { nexp : nat } (xiexp : fin (mexp) -> fin (nexp)) : funcomp (ren_exp xiexp) (var_exp (mexp)) = funcomp (var_exp (nexp)) xiexp .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => eq_refl)). Qed.

Lemma rinstInst_exp { mexp : nat } { nexp : nat } (xiexp : fin (mexp) -> fin (nexp)) : ren_exp xiexp = subst_exp (funcomp (var_exp (nexp)) xiexp) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => rinst_inst_exp xiexp (_) (fun n => eq_refl) x)). Qed.

Lemma compComp_exp { kexp : nat } { lexp : nat } { mexp : nat } (sigmaexp : fin (mexp) -> exp (kexp)) (tauexp : fin (kexp) -> exp (lexp)) (s : exp (mexp)) : subst_exp tauexp (subst_exp sigmaexp s) = subst_exp (funcomp (subst_exp tauexp) sigmaexp) s .
Proof. exact (compSubstSubst_exp sigmaexp tauexp (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_exp { kexp : nat } { lexp : nat } { mexp : nat } (sigmaexp : fin (mexp) -> exp (kexp)) (tauexp : fin (kexp) -> exp (lexp)) : funcomp (subst_exp tauexp) (subst_exp sigmaexp) = subst_exp (funcomp (subst_exp tauexp) sigmaexp) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => compComp_exp sigmaexp tauexp n)). Qed.

Lemma compRen_exp { kexp : nat } { lexp : nat } { mexp : nat } (sigmaexp : fin (mexp) -> exp (kexp)) (zetaexp : fin (kexp) -> fin (lexp)) (s : exp (mexp)) : ren_exp zetaexp (subst_exp sigmaexp s) = subst_exp (funcomp (ren_exp zetaexp) sigmaexp) s .
Proof. exact (compSubstRen__exp sigmaexp zetaexp (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_exp { kexp : nat } { lexp : nat } { mexp : nat } (sigmaexp : fin (mexp) -> exp (kexp)) (zetaexp : fin (kexp) -> fin (lexp)) : funcomp (ren_exp zetaexp) (subst_exp sigmaexp) = subst_exp (funcomp (ren_exp zetaexp) sigmaexp) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => compRen_exp sigmaexp zetaexp n)). Qed.

Lemma renComp_exp { kexp : nat } { lexp : nat } { mexp : nat } (xiexp : fin (mexp) -> fin (kexp)) (tauexp : fin (kexp) -> exp (lexp)) (s : exp (mexp)) : subst_exp tauexp (ren_exp xiexp s) = subst_exp (funcomp tauexp xiexp) s .
Proof. exact (compRenSubst_exp xiexp tauexp (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_exp { kexp : nat } { lexp : nat } { mexp : nat } (xiexp : fin (mexp) -> fin (kexp)) (tauexp : fin (kexp) -> exp (lexp)) : funcomp (subst_exp tauexp) (ren_exp xiexp) = subst_exp (funcomp tauexp xiexp) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => renComp_exp xiexp tauexp n)). Qed.

Lemma renRen_exp { kexp : nat } { lexp : nat } { mexp : nat } (xiexp : fin (mexp) -> fin (kexp)) (zetaexp : fin (kexp) -> fin (lexp)) (s : exp (mexp)) : ren_exp zetaexp (ren_exp xiexp s) = ren_exp (funcomp zetaexp xiexp) s .
Proof. exact (compRenRen_exp xiexp zetaexp (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_exp { kexp : nat } { lexp : nat } { mexp : nat } (xiexp : fin (mexp) -> fin (kexp)) (zetaexp : fin (kexp) -> fin (lexp)) : funcomp (ren_exp zetaexp) (ren_exp xiexp) = ren_exp (funcomp zetaexp xiexp) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => renRen_exp xiexp zetaexp n)). Qed.

Arguments var_exp {nexp}.

Arguments One {nexp}.

Arguments Lam {nexp}.

Arguments App {nexp}.

Arguments Pair {nexp}.

Arguments Proj {nexp}.

Arguments Inj {nexp}.

Arguments CaseS {nexp}.

Instance Subst_exp : Subst1 exp exp := @subst_exp .

Instance Ren_exp : Ren1 exp := @ren_exp .

Instance VarInstance_exp : Var exp := @var_exp .

Notation "x '__exp'" := (@ids exp VarInstance_exp (_) x) (at level 30, format "x __exp") : subst_scope.

Notation "⇑__exp" := (@up_exp_exp (_)) (only printing) : subst_scope.

Ltac auto_unfold := repeat unfold subst1,  ren1,  subst2,  ren2,  Subst1,  Ren1,  Subst2,  Ren2,  ids,  Subst_exp,  Ren_exp,  VarInstance_exp.

Ltac auto_fold := try fold VarInstance_exp;  try fold (@ids _ VarInstance_exp);  try fold Subst_exp;  try fold (@subst1 _ _ Subst_exp);  try fold Ren_exp;  try fold (@ren1 _ Ren_exp).

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  ren1,  subst2,  ren2,  Subst1,  Ren1,  Subst2,  Ren2,  ids,  Subst_exp,  Ren_exp,  VarInstance_exp in *.

Tactic Notation "auto_fold" "in" "*" := try fold VarInstance_exp in *;  try fold (@ids _ VarInstance_exp) in *;  try fold Subst_exp in *;  try fold (@subst1 _ _ Subst_exp) in *;  try fold Ren_exp in *;  try fold (@ren1 _ Ren_exp) in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_exp| progress rewrite ?compComp_exp| progress rewrite ?compComp'_exp| progress rewrite ?compRen_exp| progress rewrite ?compRen'_exp| progress rewrite ?renComp_exp| progress rewrite ?renComp'_exp| progress rewrite ?renRen_exp| progress rewrite ?renRen'_exp| progress rewrite ?varL_exp| progress rewrite ?varLRen_exp| progress (unfold up_ren, upRen_exp_exp, up_exp_exp)| progress (cbn [subst_exp ren_exp])| fsimpl].

Ltac asimpl := auto_unfold; asimpl'; auto_fold.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_exp in *| progress rewrite ?compComp_exp in *| progress rewrite ?compComp'_exp in *| progress rewrite ?compRen_exp in *| progress rewrite ?compRen'_exp in *| progress rewrite ?renComp_exp in *| progress rewrite ?renComp'_exp in *| progress rewrite ?renRen_exp in *| progress rewrite ?renRen'_exp in *| progress rewrite ?varL_exp in *| progress rewrite ?varLRen_exp in *| progress (unfold up_ren, upRen_exp_exp, up_exp_exp in *)| progress (cbn [subst_exp ren_exp] in *)| fsimpl in *]; auto_fold in *.

Ltac substify := auto_unfold; try repeat (erewrite rinst_inst_exp; [|now intros]); auto_fold.

Ltac renamify := auto_unfold; try repeat (erewrite <- rinst_inst_exp; [|intros; now asimpl]); auto_fold.
