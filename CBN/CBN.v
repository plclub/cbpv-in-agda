Require Export fintype.



Section type.
Inductive type  : Type :=
  | Unit : type 
  | Arr : type   -> type   -> type 
  | Cross : type   -> type   -> type 
  | Plus : type   -> type   -> type .

Lemma congr_Unit  : Unit  = Unit  .
Proof. congruence. Qed.

Lemma congr_Arr  { s0 : type   } { s1 : type   } { t0 : type   } { t1 : type   } (H1 : s0 = t0) (H2 : s1 = t1) : Arr s0 s1 = Arr t0 t1 .
Proof. congruence. Qed.

Lemma congr_Cross  { s0 : type   } { s1 : type   } { t0 : type   } { t1 : type   } (H1 : s0 = t0) (H2 : s1 = t1) : Cross s0 s1 = Cross t0 t1 .
Proof. congruence. Qed.

Lemma congr_Plus  { s0 : type   } { s1 : type   } { t0 : type   } { t1 : type   } (H1 : s0 = t0) (H2 : s1 = t1) : Plus s0 s1 = Plus t0 t1 .
Proof. congruence. Qed.

End type.


Section exp.
Inductive exp (nexp : nat) : Type :=
  | var_exp : (fin) (nexp) -> exp (nexp)
  | One : exp (nexp)
  | Lam : exp  ((S) nexp) -> exp (nexp)
  | App : exp  (nexp) -> exp  (nexp) -> exp (nexp)
  | Pair : exp  (nexp) -> exp  (nexp) -> exp (nexp)
  | Proj : bool   -> exp  (nexp) -> exp (nexp)
  | Inj : bool   -> exp  (nexp) -> exp (nexp)
  | CaseS : exp  (nexp) -> exp  ((S) nexp) -> exp  ((S) nexp) -> exp (nexp).

Lemma congr_One { mexp : nat } : One (mexp) = One (mexp) .
Proof. congruence. Qed.

Lemma congr_Lam { mexp : nat } { s0 : exp  ((S) mexp) } { t0 : exp  ((S) mexp) } (H1 : s0 = t0) : Lam (mexp) s0 = Lam (mexp) t0 .
Proof. congruence. Qed.

Lemma congr_App { mexp : nat } { s0 : exp  (mexp) } { s1 : exp  (mexp) } { t0 : exp  (mexp) } { t1 : exp  (mexp) } (H1 : s0 = t0) (H2 : s1 = t1) : App (mexp) s0 s1 = App (mexp) t0 t1 .
Proof. congruence. Qed.

Lemma congr_Pair { mexp : nat } { s0 : exp  (mexp) } { s1 : exp  (mexp) } { t0 : exp  (mexp) } { t1 : exp  (mexp) } (H1 : s0 = t0) (H2 : s1 = t1) : Pair (mexp) s0 s1 = Pair (mexp) t0 t1 .
Proof. congruence. Qed.

Lemma congr_Proj { mexp : nat } { s0 : bool   } { s1 : exp  (mexp) } { t0 : bool   } { t1 : exp  (mexp) } (H1 : s0 = t0) (H2 : s1 = t1) : Proj (mexp) s0 s1 = Proj (mexp) t0 t1 .
Proof. congruence. Qed.

Lemma congr_Inj { mexp : nat } { s0 : bool   } { s1 : exp  (mexp) } { t0 : bool   } { t1 : exp  (mexp) } (H1 : s0 = t0) (H2 : s1 = t1) : Inj (mexp) s0 s1 = Inj (mexp) t0 t1 .
Proof. congruence. Qed.

Lemma congr_CaseS { mexp : nat } { s0 : exp  (mexp) } { s1 : exp  ((S) mexp) } { s2 : exp  ((S) mexp) } { t0 : exp  (mexp) } { t1 : exp  ((S) mexp) } { t2 : exp  ((S) mexp) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : CaseS (mexp) s0 s1 s2 = CaseS (mexp) t0 t1 t2 .
Proof. congruence. Qed.

Definition upRen_exp_exp { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Fixpoint ren_exp { mexp : nat } { nexp : nat } (xiexp : (fin) (mexp) -> (fin) (nexp)) (s : exp (mexp)) : exp (nexp) :=
    match s return exp (nexp) with
    | var_exp (_) s => (var_exp (nexp)) (xiexp s)
    | One (_)  => One (nexp)
    | Lam (_) s0 => Lam (nexp) ((ren_exp (upRen_exp_exp xiexp)) s0)
    | App (_) s0 s1 => App (nexp) ((ren_exp xiexp) s0) ((ren_exp xiexp) s1)
    | Pair (_) s0 s1 => Pair (nexp) ((ren_exp xiexp) s0) ((ren_exp xiexp) s1)
    | Proj (_) s0 s1 => Proj (nexp) ((fun x => x) s0) ((ren_exp xiexp) s1)
    | Inj (_) s0 s1 => Inj (nexp) ((fun x => x) s0) ((ren_exp xiexp) s1)
    | CaseS (_) s0 s1 s2 => CaseS (nexp) ((ren_exp xiexp) s0) ((ren_exp (upRen_exp_exp xiexp)) s1) ((ren_exp (upRen_exp_exp xiexp)) s2)
    end.

Definition up_exp_exp { m : nat } { nexp : nat } (sigma : (fin) (m) -> exp (nexp)) : (fin) ((S) (m)) -> exp ((S) nexp) :=
  (scons) ((var_exp ((S) nexp)) (var_zero)) ((funcomp) (ren_exp (shift)) sigma).

Fixpoint subst_exp { mexp : nat } { nexp : nat } (sigmaexp : (fin) (mexp) -> exp (nexp)) (s : exp (mexp)) : exp (nexp) :=
    match s return exp (nexp) with
    | var_exp (_) s => sigmaexp s
    | One (_)  => One (nexp)
    | Lam (_) s0 => Lam (nexp) ((subst_exp (up_exp_exp sigmaexp)) s0)
    | App (_) s0 s1 => App (nexp) ((subst_exp sigmaexp) s0) ((subst_exp sigmaexp) s1)
    | Pair (_) s0 s1 => Pair (nexp) ((subst_exp sigmaexp) s0) ((subst_exp sigmaexp) s1)
    | Proj (_) s0 s1 => Proj (nexp) ((fun x => x) s0) ((subst_exp sigmaexp) s1)
    | Inj (_) s0 s1 => Inj (nexp) ((fun x => x) s0) ((subst_exp sigmaexp) s1)
    | CaseS (_) s0 s1 s2 => CaseS (nexp) ((subst_exp sigmaexp) s0) ((subst_exp (up_exp_exp sigmaexp)) s1) ((subst_exp (up_exp_exp sigmaexp)) s2)
    end.

Definition upId_exp_exp { mexp : nat } (sigma : (fin) (mexp) -> exp (mexp)) (Eq : forall x, sigma x = (var_exp (mexp)) x) : forall x, (up_exp_exp sigma) x = (var_exp ((S) mexp)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_exp (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint idSubst_exp { mexp : nat } (sigmaexp : (fin) (mexp) -> exp (mexp)) (Eqexp : forall x, sigmaexp x = (var_exp (mexp)) x) (s : exp (mexp)) : subst_exp sigmaexp s = s :=
    match s return subst_exp sigmaexp s = s with
    | var_exp (_) s => Eqexp s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam ((idSubst_exp (up_exp_exp sigmaexp) (upId_exp_exp (_) Eqexp)) s0)
    | App (_) s0 s1 => congr_App ((idSubst_exp sigmaexp Eqexp) s0) ((idSubst_exp sigmaexp Eqexp) s1)
    | Pair (_) s0 s1 => congr_Pair ((idSubst_exp sigmaexp Eqexp) s0) ((idSubst_exp sigmaexp Eqexp) s1)
    | Proj (_) s0 s1 => congr_Proj ((fun x => (eq_refl) x) s0) ((idSubst_exp sigmaexp Eqexp) s1)
    | Inj (_) s0 s1 => congr_Inj ((fun x => (eq_refl) x) s0) ((idSubst_exp sigmaexp Eqexp) s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS ((idSubst_exp sigmaexp Eqexp) s0) ((idSubst_exp (up_exp_exp sigmaexp) (upId_exp_exp (_) Eqexp)) s1) ((idSubst_exp (up_exp_exp sigmaexp) (upId_exp_exp (_) Eqexp)) s2)
    end.

Definition upExtRen_exp_exp { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_exp_exp xi) x = (upRen_exp_exp zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint extRen_exp { mexp : nat } { nexp : nat } (xiexp : (fin) (mexp) -> (fin) (nexp)) (zetaexp : (fin) (mexp) -> (fin) (nexp)) (Eqexp : forall x, xiexp x = zetaexp x) (s : exp (mexp)) : ren_exp xiexp s = ren_exp zetaexp s :=
    match s return ren_exp xiexp s = ren_exp zetaexp s with
    | var_exp (_) s => (ap) (var_exp (nexp)) (Eqexp s)
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam ((extRen_exp (upRen_exp_exp xiexp) (upRen_exp_exp zetaexp) (upExtRen_exp_exp (_) (_) Eqexp)) s0)
    | App (_) s0 s1 => congr_App ((extRen_exp xiexp zetaexp Eqexp) s0) ((extRen_exp xiexp zetaexp Eqexp) s1)
    | Pair (_) s0 s1 => congr_Pair ((extRen_exp xiexp zetaexp Eqexp) s0) ((extRen_exp xiexp zetaexp Eqexp) s1)
    | Proj (_) s0 s1 => congr_Proj ((fun x => (eq_refl) x) s0) ((extRen_exp xiexp zetaexp Eqexp) s1)
    | Inj (_) s0 s1 => congr_Inj ((fun x => (eq_refl) x) s0) ((extRen_exp xiexp zetaexp Eqexp) s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS ((extRen_exp xiexp zetaexp Eqexp) s0) ((extRen_exp (upRen_exp_exp xiexp) (upRen_exp_exp zetaexp) (upExtRen_exp_exp (_) (_) Eqexp)) s1) ((extRen_exp (upRen_exp_exp xiexp) (upRen_exp_exp zetaexp) (upExtRen_exp_exp (_) (_) Eqexp)) s2)
    end.

Definition upExt_exp_exp { m : nat } { nexp : nat } (sigma : (fin) (m) -> exp (nexp)) (tau : (fin) (m) -> exp (nexp)) (Eq : forall x, sigma x = tau x) : forall x, (up_exp_exp sigma) x = (up_exp_exp tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_exp (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint ext_exp { mexp : nat } { nexp : nat } (sigmaexp : (fin) (mexp) -> exp (nexp)) (tauexp : (fin) (mexp) -> exp (nexp)) (Eqexp : forall x, sigmaexp x = tauexp x) (s : exp (mexp)) : subst_exp sigmaexp s = subst_exp tauexp s :=
    match s return subst_exp sigmaexp s = subst_exp tauexp s with
    | var_exp (_) s => Eqexp s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam ((ext_exp (up_exp_exp sigmaexp) (up_exp_exp tauexp) (upExt_exp_exp (_) (_) Eqexp)) s0)
    | App (_) s0 s1 => congr_App ((ext_exp sigmaexp tauexp Eqexp) s0) ((ext_exp sigmaexp tauexp Eqexp) s1)
    | Pair (_) s0 s1 => congr_Pair ((ext_exp sigmaexp tauexp Eqexp) s0) ((ext_exp sigmaexp tauexp Eqexp) s1)
    | Proj (_) s0 s1 => congr_Proj ((fun x => (eq_refl) x) s0) ((ext_exp sigmaexp tauexp Eqexp) s1)
    | Inj (_) s0 s1 => congr_Inj ((fun x => (eq_refl) x) s0) ((ext_exp sigmaexp tauexp Eqexp) s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS ((ext_exp sigmaexp tauexp Eqexp) s0) ((ext_exp (up_exp_exp sigmaexp) (up_exp_exp tauexp) (upExt_exp_exp (_) (_) Eqexp)) s1) ((ext_exp (up_exp_exp sigmaexp) (up_exp_exp tauexp) (upExt_exp_exp (_) (_) Eqexp)) s2)
    end.

Definition up_ren_ren_exp_exp { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_exp_exp tau) (upRen_exp_exp xi)) x = (upRen_exp_exp theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_exp { kexp : nat } { lexp : nat } { mexp : nat } (xiexp : (fin) (mexp) -> (fin) (kexp)) (zetaexp : (fin) (kexp) -> (fin) (lexp)) (rhoexp : (fin) (mexp) -> (fin) (lexp)) (Eqexp : forall x, ((funcomp) zetaexp xiexp) x = rhoexp x) (s : exp (mexp)) : ren_exp zetaexp (ren_exp xiexp s) = ren_exp rhoexp s :=
    match s return ren_exp zetaexp (ren_exp xiexp s) = ren_exp rhoexp s with
    | var_exp (_) s => (ap) (var_exp (lexp)) (Eqexp s)
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam ((compRenRen_exp (upRen_exp_exp xiexp) (upRen_exp_exp zetaexp) (upRen_exp_exp rhoexp) (up_ren_ren (_) (_) (_) Eqexp)) s0)
    | App (_) s0 s1 => congr_App ((compRenRen_exp xiexp zetaexp rhoexp Eqexp) s0) ((compRenRen_exp xiexp zetaexp rhoexp Eqexp) s1)
    | Pair (_) s0 s1 => congr_Pair ((compRenRen_exp xiexp zetaexp rhoexp Eqexp) s0) ((compRenRen_exp xiexp zetaexp rhoexp Eqexp) s1)
    | Proj (_) s0 s1 => congr_Proj ((fun x => (eq_refl) x) s0) ((compRenRen_exp xiexp zetaexp rhoexp Eqexp) s1)
    | Inj (_) s0 s1 => congr_Inj ((fun x => (eq_refl) x) s0) ((compRenRen_exp xiexp zetaexp rhoexp Eqexp) s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS ((compRenRen_exp xiexp zetaexp rhoexp Eqexp) s0) ((compRenRen_exp (upRen_exp_exp xiexp) (upRen_exp_exp zetaexp) (upRen_exp_exp rhoexp) (up_ren_ren (_) (_) (_) Eqexp)) s1) ((compRenRen_exp (upRen_exp_exp xiexp) (upRen_exp_exp zetaexp) (upRen_exp_exp rhoexp) (up_ren_ren (_) (_) (_) Eqexp)) s2)
    end.

Definition up_ren_subst_exp_exp { k : nat } { l : nat } { mexp : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> exp (mexp)) (theta : (fin) (k) -> exp (mexp)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_exp_exp tau) (upRen_exp_exp xi)) x = (up_exp_exp theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_exp (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint compRenSubst_exp { kexp : nat } { lexp : nat } { mexp : nat } (xiexp : (fin) (mexp) -> (fin) (kexp)) (tauexp : (fin) (kexp) -> exp (lexp)) (thetaexp : (fin) (mexp) -> exp (lexp)) (Eqexp : forall x, ((funcomp) tauexp xiexp) x = thetaexp x) (s : exp (mexp)) : subst_exp tauexp (ren_exp xiexp s) = subst_exp thetaexp s :=
    match s return subst_exp tauexp (ren_exp xiexp s) = subst_exp thetaexp s with
    | var_exp (_) s => Eqexp s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam ((compRenSubst_exp (upRen_exp_exp xiexp) (up_exp_exp tauexp) (up_exp_exp thetaexp) (up_ren_subst_exp_exp (_) (_) (_) Eqexp)) s0)
    | App (_) s0 s1 => congr_App ((compRenSubst_exp xiexp tauexp thetaexp Eqexp) s0) ((compRenSubst_exp xiexp tauexp thetaexp Eqexp) s1)
    | Pair (_) s0 s1 => congr_Pair ((compRenSubst_exp xiexp tauexp thetaexp Eqexp) s0) ((compRenSubst_exp xiexp tauexp thetaexp Eqexp) s1)
    | Proj (_) s0 s1 => congr_Proj ((fun x => (eq_refl) x) s0) ((compRenSubst_exp xiexp tauexp thetaexp Eqexp) s1)
    | Inj (_) s0 s1 => congr_Inj ((fun x => (eq_refl) x) s0) ((compRenSubst_exp xiexp tauexp thetaexp Eqexp) s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS ((compRenSubst_exp xiexp tauexp thetaexp Eqexp) s0) ((compRenSubst_exp (upRen_exp_exp xiexp) (up_exp_exp tauexp) (up_exp_exp thetaexp) (up_ren_subst_exp_exp (_) (_) (_) Eqexp)) s1) ((compRenSubst_exp (upRen_exp_exp xiexp) (up_exp_exp tauexp) (up_exp_exp thetaexp) (up_ren_subst_exp_exp (_) (_) (_) Eqexp)) s2)
    end.

Definition up_subst_ren_exp_exp { k : nat } { lexp : nat } { mexp : nat } (sigma : (fin) (k) -> exp (lexp)) (zetaexp : (fin) (lexp) -> (fin) (mexp)) (theta : (fin) (k) -> exp (mexp)) (Eq : forall x, ((funcomp) (ren_exp zetaexp) sigma) x = theta x) : forall x, ((funcomp) (ren_exp (upRen_exp_exp zetaexp)) (up_exp_exp sigma)) x = (up_exp_exp theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_exp (shift) (upRen_exp_exp zetaexp) ((funcomp) (shift) zetaexp) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_exp zetaexp (shift) ((funcomp) (shift) zetaexp) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_exp (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstRen_exp { kexp : nat } { lexp : nat } { mexp : nat } (sigmaexp : (fin) (mexp) -> exp (kexp)) (zetaexp : (fin) (kexp) -> (fin) (lexp)) (thetaexp : (fin) (mexp) -> exp (lexp)) (Eqexp : forall x, ((funcomp) (ren_exp zetaexp) sigmaexp) x = thetaexp x) (s : exp (mexp)) : ren_exp zetaexp (subst_exp sigmaexp s) = subst_exp thetaexp s :=
    match s return ren_exp zetaexp (subst_exp sigmaexp s) = subst_exp thetaexp s with
    | var_exp (_) s => Eqexp s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam ((compSubstRen_exp (up_exp_exp sigmaexp) (upRen_exp_exp zetaexp) (up_exp_exp thetaexp) (up_subst_ren_exp_exp (_) (_) (_) Eqexp)) s0)
    | App (_) s0 s1 => congr_App ((compSubstRen_exp sigmaexp zetaexp thetaexp Eqexp) s0) ((compSubstRen_exp sigmaexp zetaexp thetaexp Eqexp) s1)
    | Pair (_) s0 s1 => congr_Pair ((compSubstRen_exp sigmaexp zetaexp thetaexp Eqexp) s0) ((compSubstRen_exp sigmaexp zetaexp thetaexp Eqexp) s1)
    | Proj (_) s0 s1 => congr_Proj ((fun x => (eq_refl) x) s0) ((compSubstRen_exp sigmaexp zetaexp thetaexp Eqexp) s1)
    | Inj (_) s0 s1 => congr_Inj ((fun x => (eq_refl) x) s0) ((compSubstRen_exp sigmaexp zetaexp thetaexp Eqexp) s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS ((compSubstRen_exp sigmaexp zetaexp thetaexp Eqexp) s0) ((compSubstRen_exp (up_exp_exp sigmaexp) (upRen_exp_exp zetaexp) (up_exp_exp thetaexp) (up_subst_ren_exp_exp (_) (_) (_) Eqexp)) s1) ((compSubstRen_exp (up_exp_exp sigmaexp) (upRen_exp_exp zetaexp) (up_exp_exp thetaexp) (up_subst_ren_exp_exp (_) (_) (_) Eqexp)) s2)
    end.

Definition up_subst_subst_exp_exp { k : nat } { lexp : nat } { mexp : nat } (sigma : (fin) (k) -> exp (lexp)) (tauexp : (fin) (lexp) -> exp (mexp)) (theta : (fin) (k) -> exp (mexp)) (Eq : forall x, ((funcomp) (subst_exp tauexp) sigma) x = theta x) : forall x, ((funcomp) (subst_exp (up_exp_exp tauexp)) (up_exp_exp sigma)) x = (up_exp_exp theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_exp (shift) (up_exp_exp tauexp) ((funcomp) (up_exp_exp tauexp) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_exp tauexp (shift) ((funcomp) (ren_exp (shift)) tauexp) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_exp (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstSubst_exp { kexp : nat } { lexp : nat } { mexp : nat } (sigmaexp : (fin) (mexp) -> exp (kexp)) (tauexp : (fin) (kexp) -> exp (lexp)) (thetaexp : (fin) (mexp) -> exp (lexp)) (Eqexp : forall x, ((funcomp) (subst_exp tauexp) sigmaexp) x = thetaexp x) (s : exp (mexp)) : subst_exp tauexp (subst_exp sigmaexp s) = subst_exp thetaexp s :=
    match s return subst_exp tauexp (subst_exp sigmaexp s) = subst_exp thetaexp s with
    | var_exp (_) s => Eqexp s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam ((compSubstSubst_exp (up_exp_exp sigmaexp) (up_exp_exp tauexp) (up_exp_exp thetaexp) (up_subst_subst_exp_exp (_) (_) (_) Eqexp)) s0)
    | App (_) s0 s1 => congr_App ((compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp) s0) ((compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp) s1)
    | Pair (_) s0 s1 => congr_Pair ((compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp) s0) ((compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp) s1)
    | Proj (_) s0 s1 => congr_Proj ((fun x => (eq_refl) x) s0) ((compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp) s1)
    | Inj (_) s0 s1 => congr_Inj ((fun x => (eq_refl) x) s0) ((compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp) s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS ((compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp) s0) ((compSubstSubst_exp (up_exp_exp sigmaexp) (up_exp_exp tauexp) (up_exp_exp thetaexp) (up_subst_subst_exp_exp (_) (_) (_) Eqexp)) s1) ((compSubstSubst_exp (up_exp_exp sigmaexp) (up_exp_exp tauexp) (up_exp_exp thetaexp) (up_subst_subst_exp_exp (_) (_) (_) Eqexp)) s2)
    end.

Definition rinstInst_up_exp_exp { m : nat } { nexp : nat } (xi : (fin) (m) -> (fin) (nexp)) (sigma : (fin) (m) -> exp (nexp)) (Eq : forall x, ((funcomp) (var_exp (nexp)) xi) x = sigma x) : forall x, ((funcomp) (var_exp ((S) nexp)) (upRen_exp_exp xi)) x = (up_exp_exp sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_exp (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint rinst_inst_exp { mexp : nat } { nexp : nat } (xiexp : (fin) (mexp) -> (fin) (nexp)) (sigmaexp : (fin) (mexp) -> exp (nexp)) (Eqexp : forall x, ((funcomp) (var_exp (nexp)) xiexp) x = sigmaexp x) (s : exp (mexp)) : ren_exp xiexp s = subst_exp sigmaexp s :=
    match s return ren_exp xiexp s = subst_exp sigmaexp s with
    | var_exp (_) s => Eqexp s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam ((rinst_inst_exp (upRen_exp_exp xiexp) (up_exp_exp sigmaexp) (rinstInst_up_exp_exp (_) (_) Eqexp)) s0)
    | App (_) s0 s1 => congr_App ((rinst_inst_exp xiexp sigmaexp Eqexp) s0) ((rinst_inst_exp xiexp sigmaexp Eqexp) s1)
    | Pair (_) s0 s1 => congr_Pair ((rinst_inst_exp xiexp sigmaexp Eqexp) s0) ((rinst_inst_exp xiexp sigmaexp Eqexp) s1)
    | Proj (_) s0 s1 => congr_Proj ((fun x => (eq_refl) x) s0) ((rinst_inst_exp xiexp sigmaexp Eqexp) s1)
    | Inj (_) s0 s1 => congr_Inj ((fun x => (eq_refl) x) s0) ((rinst_inst_exp xiexp sigmaexp Eqexp) s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS ((rinst_inst_exp xiexp sigmaexp Eqexp) s0) ((rinst_inst_exp (upRen_exp_exp xiexp) (up_exp_exp sigmaexp) (rinstInst_up_exp_exp (_) (_) Eqexp)) s1) ((rinst_inst_exp (upRen_exp_exp xiexp) (up_exp_exp sigmaexp) (rinstInst_up_exp_exp (_) (_) Eqexp)) s2)
    end.

Lemma rinstInst_exp { mexp : nat } { nexp : nat } (xiexp : (fin) (mexp) -> (fin) (nexp)) : ren_exp xiexp = subst_exp ((funcomp) (var_exp (nexp)) xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_exp xiexp (_) (fun n => eq_refl) x)). Qed.

Lemma instId_exp { mexp : nat } : subst_exp (var_exp (mexp)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_exp (var_exp (mexp)) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_exp { mexp : nat } : @ren_exp (mexp) (mexp) (id) = id .
Proof. exact ((eq_trans) (rinstInst_exp ((id) (_))) instId_exp). Qed.

Lemma varL_exp { mexp : nat } { nexp : nat } (sigmaexp : (fin) (mexp) -> exp (nexp)) : (funcomp) (subst_exp sigmaexp) (var_exp (mexp)) = sigmaexp .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_exp { mexp : nat } { nexp : nat } (xiexp : (fin) (mexp) -> (fin) (nexp)) : (funcomp) (ren_exp xiexp) (var_exp (mexp)) = (funcomp) (var_exp (nexp)) xiexp .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_exp { kexp : nat } { lexp : nat } { mexp : nat } (sigmaexp : (fin) (mexp) -> exp (kexp)) (tauexp : (fin) (kexp) -> exp (lexp)) (s : exp (mexp)) : subst_exp tauexp (subst_exp sigmaexp s) = subst_exp ((funcomp) (subst_exp tauexp) sigmaexp) s .
Proof. exact (compSubstSubst_exp sigmaexp tauexp (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_exp { kexp : nat } { lexp : nat } { mexp : nat } (sigmaexp : (fin) (mexp) -> exp (kexp)) (tauexp : (fin) (kexp) -> exp (lexp)) : (funcomp) (subst_exp tauexp) (subst_exp sigmaexp) = subst_exp ((funcomp) (subst_exp tauexp) sigmaexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_exp sigmaexp tauexp n)). Qed.

Lemma compRen_exp { kexp : nat } { lexp : nat } { mexp : nat } (sigmaexp : (fin) (mexp) -> exp (kexp)) (zetaexp : (fin) (kexp) -> (fin) (lexp)) (s : exp (mexp)) : ren_exp zetaexp (subst_exp sigmaexp s) = subst_exp ((funcomp) (ren_exp zetaexp) sigmaexp) s .
Proof. exact (compSubstRen_exp sigmaexp zetaexp (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_exp { kexp : nat } { lexp : nat } { mexp : nat } (sigmaexp : (fin) (mexp) -> exp (kexp)) (zetaexp : (fin) (kexp) -> (fin) (lexp)) : (funcomp) (ren_exp zetaexp) (subst_exp sigmaexp) = subst_exp ((funcomp) (ren_exp zetaexp) sigmaexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_exp sigmaexp zetaexp n)). Qed.

Lemma renComp_exp { kexp : nat } { lexp : nat } { mexp : nat } (xiexp : (fin) (mexp) -> (fin) (kexp)) (tauexp : (fin) (kexp) -> exp (lexp)) (s : exp (mexp)) : subst_exp tauexp (ren_exp xiexp s) = subst_exp ((funcomp) tauexp xiexp) s .
Proof. exact (compRenSubst_exp xiexp tauexp (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_exp { kexp : nat } { lexp : nat } { mexp : nat } (xiexp : (fin) (mexp) -> (fin) (kexp)) (tauexp : (fin) (kexp) -> exp (lexp)) : (funcomp) (subst_exp tauexp) (ren_exp xiexp) = subst_exp ((funcomp) tauexp xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_exp xiexp tauexp n)). Qed.

Lemma renRen_exp { kexp : nat } { lexp : nat } { mexp : nat } (xiexp : (fin) (mexp) -> (fin) (kexp)) (zetaexp : (fin) (kexp) -> (fin) (lexp)) (s : exp (mexp)) : ren_exp zetaexp (ren_exp xiexp s) = ren_exp ((funcomp) zetaexp xiexp) s .
Proof. exact (compRenRen_exp xiexp zetaexp (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_exp { kexp : nat } { lexp : nat } { mexp : nat } (xiexp : (fin) (mexp) -> (fin) (kexp)) (zetaexp : (fin) (kexp) -> (fin) (lexp)) : (funcomp) (ren_exp zetaexp) (ren_exp xiexp) = ren_exp ((funcomp) zetaexp xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_exp xiexp zetaexp n)). Qed.

End exp.

Arguments var_exp {nexp}.

Arguments One {nexp}.

Arguments Lam {nexp}.

Arguments App {nexp}.

Arguments Pair {nexp}.

Arguments Proj {nexp}.

Arguments Inj {nexp}.

Arguments CaseS {nexp}.

Global Instance Subst_exp { mexp : nat } { nexp : nat } : Subst1 ((fin) (mexp) -> exp (nexp)) (exp (mexp)) (exp (nexp)) := @subst_exp (mexp) (nexp) .

Global Instance Ren_exp { mexp : nat } { nexp : nat } : Ren1 ((fin) (mexp) -> (fin) (nexp)) (exp (mexp)) (exp (nexp)) := @ren_exp (mexp) (nexp) .

Global Instance VarInstance_exp { mexp : nat } : Var ((fin) (mexp)) (exp (mexp)) := @var_exp (mexp) .

Notation "x '__exp'" := (var_exp x) (at level 5, format "x __exp") : subst_scope.

Notation "x '__exp'" := (@ids (_) (_) VarInstance_exp x) (at level 5, only printing, format "x __exp") : subst_scope.

Notation "'var'" := (var_exp) (only printing, at level 1) : subst_scope.

Class Up_exp X Y := up_exp : X -> Y.

Notation "↑__exp" := (up_exp) (only printing) : subst_scope.

Notation "↑__exp" := (up_exp_exp) (only printing) : subst_scope.

Global Instance Up_exp_exp { m : nat } { nexp : nat } : Up_exp (_) (_) := @up_exp_exp (m) (nexp) .

Notation "s [ sigmaexp ]" := (subst_exp sigmaexp s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaexp ]" := (subst_exp sigmaexp) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiexp ⟩" := (ren_exp xiexp s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiexp ⟩" := (ren_exp xiexp) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_exp,  Ren_exp,  VarInstance_exp.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_exp,  Ren_exp,  VarInstance_exp in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_exp| progress rewrite ?compComp_exp| progress rewrite ?compComp'_exp| progress rewrite ?rinstId_exp| progress rewrite ?compRen_exp| progress rewrite ?compRen'_exp| progress rewrite ?renComp_exp| progress rewrite ?renComp'_exp| progress rewrite ?renRen_exp| progress rewrite ?renRen'_exp| progress rewrite ?varL_exp| progress rewrite ?varLRen_exp| progress (unfold up_ren, upRen_exp_exp, up_exp_exp)| progress (cbn [subst_exp ren_exp])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_exp in *| progress rewrite ?compComp_exp in *| progress rewrite ?compComp'_exp in *| progress rewrite ?rinstId_exp in *| progress rewrite ?compRen_exp in *| progress rewrite ?compRen'_exp in *| progress rewrite ?renComp_exp in *| progress rewrite ?renComp'_exp in *| progress rewrite ?renRen_exp in *| progress rewrite ?renRen'_exp in *| progress rewrite ?varL_exp in *| progress rewrite ?varLRen_exp in *| progress (unfold up_ren, upRen_exp_exp, up_exp_exp in *)| progress (cbn [subst_exp ren_exp] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_exp).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_exp).

