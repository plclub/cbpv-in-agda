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

Inductive Value (nValue : nat) : Type :=
  | var_Value : fin (nValue) -> Value (nValue)
  | One : Value (nValue)
  | Lam : Exp (S nValue) -> Value (nValue)
  | Pair : Value (nValue) -> Value (nValue) -> Value (nValue)
  | Inj : bool  -> Value (nValue) -> Value (nValue)
 with Exp (nValue : nat) : Type :=
  | Val : Value (nValue) -> Exp (nValue)
  | App : Exp (nValue) -> Exp (nValue) -> Exp (nValue)
  | CaseS : Exp (nValue) -> Exp (S nValue) -> Exp (S nValue) -> Exp (nValue)
  | CaseP : Exp (nValue) -> Exp (S (S nValue)) -> Exp (nValue).

Lemma congr_One { mValue : nat } : One (mValue) = One (mValue) .
Proof. congruence. Qed.

Lemma congr_Lam { mValue : nat } { s0 : Exp (S mValue) } { t0 : Exp (S mValue) } : s0 = t0 -> Lam (mValue) s0 = Lam (mValue) t0 .
Proof. congruence. Qed.

Lemma congr_Pair { mValue : nat } { s0 : Value (mValue) } { s1 : Value (mValue) } { t0 : Value (mValue) } { t1 : Value (mValue) } : s0 = t0 -> s1 = t1 -> Pair (mValue) s0 s1 = Pair (mValue) t0 t1 .
Proof. congruence. Qed.

Lemma congr_Inj { mValue : nat } { s0 : bool  } { s1 : Value (mValue) } { t0 : bool  } { t1 : Value (mValue) } : s0 = t0 -> s1 = t1 -> Inj (mValue) s0 s1 = Inj (mValue) t0 t1 .
Proof. congruence. Qed.

Lemma congr_Val { mValue : nat } { s0 : Value (mValue) } { t0 : Value (mValue) } : s0 = t0 -> Val (mValue) s0 = Val (mValue) t0 .
Proof. congruence. Qed.

Lemma congr_App { mValue : nat } { s0 : Exp (mValue) } { s1 : Exp (mValue) } { t0 : Exp (mValue) } { t1 : Exp (mValue) } : s0 = t0 -> s1 = t1 -> App (mValue) s0 s1 = App (mValue) t0 t1 .
Proof. congruence. Qed.

Lemma congr_CaseS { mValue : nat } { s0 : Exp (mValue) } { s1 : Exp (S mValue) } { s2 : Exp (S mValue) } { t0 : Exp (mValue) } { t1 : Exp (S mValue) } { t2 : Exp (S mValue) } : s0 = t0 -> s1 = t1 -> s2 = t2 -> CaseS (mValue) s0 s1 s2 = CaseS (mValue) t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_CaseP { mValue : nat } { s0 : Exp (mValue) } { s1 : Exp (S (S mValue)) } { t0 : Exp (mValue) } { t1 : Exp (S (S mValue)) } : s0 = t0 -> s1 = t1 -> CaseP (mValue) s0 s1 = CaseP (mValue) t0 t1 .
Proof. congruence. Qed.

Definition upRen_Value_Value { m : nat } { n : nat } (xi : fin (m) -> fin (n)) : _ :=
  up_ren xi.

Fixpoint ren_Value { mValue : nat } { nValue : nat } (xiValue : fin (mValue) -> fin (nValue)) (s : Value (mValue)) : _ :=
    match s with
    | var_Value (_) s => (var_Value (nValue)) (xiValue s)
    | One (_)  => One (nValue)
    | Lam (_) s0 => Lam (nValue) (ren_Exp (upRen_Value_Value xiValue) s0)
    | Pair (_) s0 s1 => Pair (nValue) (ren_Value xiValue s0) (ren_Value xiValue s1)
    | Inj (_) s0 s1 => Inj (nValue) s0 (ren_Value xiValue s1)
    end
 with ren_Exp { mValue : nat } { nValue : nat } (xiValue : fin (mValue) -> fin (nValue)) (s : Exp (mValue)) : _ :=
    match s with
    | Val (_) s0 => Val (nValue) (ren_Value xiValue s0)
    | App (_) s0 s1 => App (nValue) (ren_Exp xiValue s0) (ren_Exp xiValue s1)
    | CaseS (_) s0 s1 s2 => CaseS (nValue) (ren_Exp xiValue s0) (ren_Exp (upRen_Value_Value xiValue) s1) (ren_Exp (upRen_Value_Value xiValue) s2)
    | CaseP (_) s0 s1 => CaseP (nValue) (ren_Exp xiValue s0) (ren_Exp (upRen_Value_Value (upRen_Value_Value xiValue)) s1)
    end.

Definition up_Value_Value { m : nat } { nValue : nat } (sigma : fin (m) -> Value (nValue)) : _ :=
  scons ((var_Value (S nValue)) var_zero) (funcomp (ren_Value shift) sigma).

Fixpoint subst_Value { mValue : nat } { nValue : nat } (sigmaValue : fin (mValue) -> Value (nValue)) (s : Value (mValue)) : _ :=
    match s with
    | var_Value (_) s => sigmaValue s
    | One (_)  => One (nValue)
    | Lam (_) s0 => Lam (nValue) (subst_Exp (up_Value_Value sigmaValue) s0)
    | Pair (_) s0 s1 => Pair (nValue) (subst_Value sigmaValue s0) (subst_Value sigmaValue s1)
    | Inj (_) s0 s1 => Inj (nValue) s0 (subst_Value sigmaValue s1)
    end
 with subst_Exp { mValue : nat } { nValue : nat } (sigmaValue : fin (mValue) -> Value (nValue)) (s : Exp (mValue)) : _ :=
    match s with
    | Val (_) s0 => Val (nValue) (subst_Value sigmaValue s0)
    | App (_) s0 s1 => App (nValue) (subst_Exp sigmaValue s0) (subst_Exp sigmaValue s1)
    | CaseS (_) s0 s1 s2 => CaseS (nValue) (subst_Exp sigmaValue s0) (subst_Exp (up_Value_Value sigmaValue) s1) (subst_Exp (up_Value_Value sigmaValue) s2)
    | CaseP (_) s0 s1 => CaseP (nValue) (subst_Exp sigmaValue s0) (subst_Exp (up_Value_Value (up_Value_Value sigmaValue)) s1)
    end.

Definition upId_Value_Value { mValue : nat } (sigma : fin (mValue) -> Value (mValue)) (Eq : forall x, sigma x = (var_Value (mValue)) x) : forall x, (up_Value_Value sigma) x = (var_Value (S mValue)) x :=
  fun n => match n with
  | Some n => ap (ren_Value shift) (Eq n)
  | None => eq_refl
  end.

Fixpoint idSubst_Value { mValue : nat } (sigmaValue : fin (mValue) -> Value (mValue)) (EqValue : forall x, sigmaValue x = (var_Value (mValue)) x) (s : Value (mValue)) : subst_Value sigmaValue s = s :=
    match s with
    | var_Value (_) s => EqValue s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam (idSubst_Exp (up_Value_Value sigmaValue) (upId_Value_Value (_) EqValue) s0)
    | Pair (_) s0 s1 => congr_Pair (idSubst_Value sigmaValue EqValue s0) (idSubst_Value sigmaValue EqValue s1)
    | Inj (_) s0 s1 => congr_Inj (eq_refl s0) (idSubst_Value sigmaValue EqValue s1)
    end
 with idSubst_Exp { mValue : nat } (sigmaValue : fin (mValue) -> Value (mValue)) (EqValue : forall x, sigmaValue x = (var_Value (mValue)) x) (s : Exp (mValue)) : subst_Exp sigmaValue s = s :=
    match s with
    | Val (_) s0 => congr_Val (idSubst_Value sigmaValue EqValue s0)
    | App (_) s0 s1 => congr_App (idSubst_Exp sigmaValue EqValue s0) (idSubst_Exp sigmaValue EqValue s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS (idSubst_Exp sigmaValue EqValue s0) (idSubst_Exp (up_Value_Value sigmaValue) (upId_Value_Value (_) EqValue) s1) (idSubst_Exp (up_Value_Value sigmaValue) (upId_Value_Value (_) EqValue) s2)
    | CaseP (_) s0 s1 => congr_CaseP (idSubst_Exp sigmaValue EqValue s0) (idSubst_Exp (up_Value_Value (up_Value_Value sigmaValue)) (upId_Value_Value (_) (upId_Value_Value (_) EqValue)) s1)
    end.

Definition upExtRen_Value_Value { m : nat } { n : nat } (xi : fin (m) -> fin (n)) (zeta : fin (m) -> fin (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_Value_Value xi) x = (upRen_Value_Value zeta) x :=
  fun n => match n with
  | Some n => ap shift (Eq n)
  | None => eq_refl
  end.

Fixpoint extRen_Value { mValue : nat } { nValue : nat } (xiValue : fin (mValue) -> fin (nValue)) (zetaValue : fin (mValue) -> fin (nValue)) (EqValue : forall x, xiValue x = zetaValue x) (s : Value (mValue)) : ren_Value xiValue s = ren_Value zetaValue s :=
    match s with
    | var_Value (_) s => ap (var_Value (nValue)) (EqValue s)
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam (extRen_Exp (upRen_Value_Value xiValue) (upRen_Value_Value zetaValue) (upExtRen_Value_Value (_) (_) EqValue) s0)
    | Pair (_) s0 s1 => congr_Pair (extRen_Value xiValue zetaValue EqValue s0) (extRen_Value xiValue zetaValue EqValue s1)
    | Inj (_) s0 s1 => congr_Inj (eq_refl s0) (extRen_Value xiValue zetaValue EqValue s1)
    end
 with extRen_Exp { mValue : nat } { nValue : nat } (xiValue : fin (mValue) -> fin (nValue)) (zetaValue : fin (mValue) -> fin (nValue)) (EqValue : forall x, xiValue x = zetaValue x) (s : Exp (mValue)) : ren_Exp xiValue s = ren_Exp zetaValue s :=
    match s with
    | Val (_) s0 => congr_Val (extRen_Value xiValue zetaValue EqValue s0)
    | App (_) s0 s1 => congr_App (extRen_Exp xiValue zetaValue EqValue s0) (extRen_Exp xiValue zetaValue EqValue s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS (extRen_Exp xiValue zetaValue EqValue s0) (extRen_Exp (upRen_Value_Value xiValue) (upRen_Value_Value zetaValue) (upExtRen_Value_Value (_) (_) EqValue) s1) (extRen_Exp (upRen_Value_Value xiValue) (upRen_Value_Value zetaValue) (upExtRen_Value_Value (_) (_) EqValue) s2)
    | CaseP (_) s0 s1 => congr_CaseP (extRen_Exp xiValue zetaValue EqValue s0) (extRen_Exp (upRen_Value_Value (upRen_Value_Value xiValue)) (upRen_Value_Value (upRen_Value_Value zetaValue)) (upExtRen_Value_Value (_) (_) (upExtRen_Value_Value (_) (_) EqValue)) s1)
    end.

Definition upExt_Value_Value { m : nat } { nValue : nat } (sigma : fin (m) -> Value (nValue)) (tau : fin (m) -> Value (nValue)) (Eq : forall x, sigma x = tau x) : forall x, (up_Value_Value sigma) x = (up_Value_Value tau) x :=
  fun n => match n with
  | Some n => ap (ren_Value shift) (Eq n)
  | None => eq_refl
  end.

Fixpoint ext_Value { mValue : nat } { nValue : nat } (sigmaValue : fin (mValue) -> Value (nValue)) (tauValue : fin (mValue) -> Value (nValue)) (EqValue : forall x, sigmaValue x = tauValue x) (s : Value (mValue)) : subst_Value sigmaValue s = subst_Value tauValue s :=
    match s with
    | var_Value (_) s => EqValue s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam (ext_Exp (up_Value_Value sigmaValue) (up_Value_Value tauValue) (upExt_Value_Value (_) (_) EqValue) s0)
    | Pair (_) s0 s1 => congr_Pair (ext_Value sigmaValue tauValue EqValue s0) (ext_Value sigmaValue tauValue EqValue s1)
    | Inj (_) s0 s1 => congr_Inj (eq_refl s0) (ext_Value sigmaValue tauValue EqValue s1)
    end
 with ext_Exp { mValue : nat } { nValue : nat } (sigmaValue : fin (mValue) -> Value (nValue)) (tauValue : fin (mValue) -> Value (nValue)) (EqValue : forall x, sigmaValue x = tauValue x) (s : Exp (mValue)) : subst_Exp sigmaValue s = subst_Exp tauValue s :=
    match s with
    | Val (_) s0 => congr_Val (ext_Value sigmaValue tauValue EqValue s0)
    | App (_) s0 s1 => congr_App (ext_Exp sigmaValue tauValue EqValue s0) (ext_Exp sigmaValue tauValue EqValue s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS (ext_Exp sigmaValue tauValue EqValue s0) (ext_Exp (up_Value_Value sigmaValue) (up_Value_Value tauValue) (upExt_Value_Value (_) (_) EqValue) s1) (ext_Exp (up_Value_Value sigmaValue) (up_Value_Value tauValue) (upExt_Value_Value (_) (_) EqValue) s2)
    | CaseP (_) s0 s1 => congr_CaseP (ext_Exp sigmaValue tauValue EqValue s0) (ext_Exp (up_Value_Value (up_Value_Value sigmaValue)) (up_Value_Value (up_Value_Value tauValue)) (upExt_Value_Value (_) (_) (upExt_Value_Value (_) (_) EqValue)) s1)
    end.

Fixpoint compRenRen_Value { kValue : nat } { lValue : nat } { mValue : nat } (xiValue : fin (mValue) -> fin (kValue)) (zetaValue : fin (kValue) -> fin (lValue)) (rhoValue : fin (mValue) -> fin (lValue)) (EqValue : forall x, (funcomp zetaValue xiValue) x = rhoValue x) (s : Value (mValue)) : ren_Value zetaValue (ren_Value xiValue s) = ren_Value rhoValue s :=
    match s with
    | var_Value (_) s => ap (var_Value (lValue)) (EqValue s)
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam (compRenRen_Exp (upRen_Value_Value xiValue) (upRen_Value_Value zetaValue) (upRen_Value_Value rhoValue) (up_ren_ren (_) (_) (_) EqValue) s0)
    | Pair (_) s0 s1 => congr_Pair (compRenRen_Value xiValue zetaValue rhoValue EqValue s0) (compRenRen_Value xiValue zetaValue rhoValue EqValue s1)
    | Inj (_) s0 s1 => congr_Inj (eq_refl s0) (compRenRen_Value xiValue zetaValue rhoValue EqValue s1)
    end
 with compRenRen_Exp { kValue : nat } { lValue : nat } { mValue : nat } (xiValue : fin (mValue) -> fin (kValue)) (zetaValue : fin (kValue) -> fin (lValue)) (rhoValue : fin (mValue) -> fin (lValue)) (EqValue : forall x, (funcomp zetaValue xiValue) x = rhoValue x) (s : Exp (mValue)) : ren_Exp zetaValue (ren_Exp xiValue s) = ren_Exp rhoValue s :=
    match s with
    | Val (_) s0 => congr_Val (compRenRen_Value xiValue zetaValue rhoValue EqValue s0)
    | App (_) s0 s1 => congr_App (compRenRen_Exp xiValue zetaValue rhoValue EqValue s0) (compRenRen_Exp xiValue zetaValue rhoValue EqValue s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS (compRenRen_Exp xiValue zetaValue rhoValue EqValue s0) (compRenRen_Exp (upRen_Value_Value xiValue) (upRen_Value_Value zetaValue) (upRen_Value_Value rhoValue) (up_ren_ren (_) (_) (_) EqValue) s1) (compRenRen_Exp (upRen_Value_Value xiValue) (upRen_Value_Value zetaValue) (upRen_Value_Value rhoValue) (up_ren_ren (_) (_) (_) EqValue) s2)
    | CaseP (_) s0 s1 => congr_CaseP (compRenRen_Exp xiValue zetaValue rhoValue EqValue s0) (compRenRen_Exp (upRen_Value_Value (upRen_Value_Value xiValue)) (upRen_Value_Value (upRen_Value_Value zetaValue)) (upRen_Value_Value (upRen_Value_Value rhoValue)) (up_ren_ren (_) (_) (_) (up_ren_ren (_) (_) (_) EqValue)) s1)
    end.

Definition up_ren_subst_Value_Value { k : nat } { l : nat } { mValue : nat } (xi : fin (k) -> fin (l)) (tau : fin (l) -> Value (mValue)) (theta : fin (k) -> Value (mValue)) (Eq : forall x, (funcomp tau xi) x = theta x) : forall x, (funcomp (up_Value_Value tau) (upRen_Value_Value xi)) x = (up_Value_Value theta) x :=
  fun n => match n with
  | Some n => ap (ren_Value shift) (Eq n)
  | None => eq_refl
  end.

Fixpoint compRenSubst_Value { kValue : nat } { lValue : nat } { mValue : nat } (xiValue : fin (mValue) -> fin (kValue)) (tauValue : fin (kValue) -> Value (lValue)) (thetaValue : fin (mValue) -> Value (lValue)) (EqValue : forall x, (funcomp tauValue xiValue) x = thetaValue x) (s : Value (mValue)) : subst_Value tauValue (ren_Value xiValue s) = subst_Value thetaValue s :=
    match s with
    | var_Value (_) s => EqValue s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam (compRenSubst_Exp (upRen_Value_Value xiValue) (up_Value_Value tauValue) (up_Value_Value thetaValue) (up_ren_subst_Value_Value (_) (_) (_) EqValue) s0)
    | Pair (_) s0 s1 => congr_Pair (compRenSubst_Value xiValue tauValue thetaValue EqValue s0) (compRenSubst_Value xiValue tauValue thetaValue EqValue s1)
    | Inj (_) s0 s1 => congr_Inj (eq_refl s0) (compRenSubst_Value xiValue tauValue thetaValue EqValue s1)
    end
 with compRenSubst_Exp { kValue : nat } { lValue : nat } { mValue : nat } (xiValue : fin (mValue) -> fin (kValue)) (tauValue : fin (kValue) -> Value (lValue)) (thetaValue : fin (mValue) -> Value (lValue)) (EqValue : forall x, (funcomp tauValue xiValue) x = thetaValue x) (s : Exp (mValue)) : subst_Exp tauValue (ren_Exp xiValue s) = subst_Exp thetaValue s :=
    match s with
    | Val (_) s0 => congr_Val (compRenSubst_Value xiValue tauValue thetaValue EqValue s0)
    | App (_) s0 s1 => congr_App (compRenSubst_Exp xiValue tauValue thetaValue EqValue s0) (compRenSubst_Exp xiValue tauValue thetaValue EqValue s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS (compRenSubst_Exp xiValue tauValue thetaValue EqValue s0) (compRenSubst_Exp (upRen_Value_Value xiValue) (up_Value_Value tauValue) (up_Value_Value thetaValue) (up_ren_subst_Value_Value (_) (_) (_) EqValue) s1) (compRenSubst_Exp (upRen_Value_Value xiValue) (up_Value_Value tauValue) (up_Value_Value thetaValue) (up_ren_subst_Value_Value (_) (_) (_) EqValue) s2)
    | CaseP (_) s0 s1 => congr_CaseP (compRenSubst_Exp xiValue tauValue thetaValue EqValue s0) (compRenSubst_Exp (upRen_Value_Value (upRen_Value_Value xiValue)) (up_Value_Value (up_Value_Value tauValue)) (up_Value_Value (up_Value_Value thetaValue)) (up_ren_subst_Value_Value (_) (_) (_) (up_ren_subst_Value_Value (_) (_) (_) EqValue)) s1)
    end.

Definition up_subst_ren_Value_Value { k : nat } { lValue : nat } { mValue : nat } (sigma : fin (k) -> Value (lValue)) (zetaValue : fin (lValue) -> fin (mValue)) (theta : fin (k) -> Value (mValue)) (Eq : forall x, (funcomp (ren_Value zetaValue) sigma) x = theta x) : forall x, (funcomp (ren_Value (upRen_Value_Value zetaValue)) (up_Value_Value sigma)) x = (up_Value_Value theta) x :=
  fun n => match n with
  | Some n => eq_trans (compRenRen_Value shift (upRen_Value_Value zetaValue) (funcomp shift zetaValue) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compRenRen_Value zetaValue shift (funcomp shift zetaValue) (fun x => eq_refl) (sigma n))) (ap (ren_Value shift) (Eq n)))
  | None => eq_refl
  end.

Fixpoint compSubstRen__Value { kValue : nat } { lValue : nat } { mValue : nat } (sigmaValue : fin (mValue) -> Value (kValue)) (zetaValue : fin (kValue) -> fin (lValue)) (thetaValue : fin (mValue) -> Value (lValue)) (EqValue : forall x, (funcomp (ren_Value zetaValue) sigmaValue) x = thetaValue x) (s : Value (mValue)) : ren_Value zetaValue (subst_Value sigmaValue s) = subst_Value thetaValue s :=
    match s with
    | var_Value (_) s => EqValue s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam (compSubstRen__Exp (up_Value_Value sigmaValue) (upRen_Value_Value zetaValue) (up_Value_Value thetaValue) (up_subst_ren_Value_Value (_) (_) (_) EqValue) s0)
    | Pair (_) s0 s1 => congr_Pair (compSubstRen__Value sigmaValue zetaValue thetaValue EqValue s0) (compSubstRen__Value sigmaValue zetaValue thetaValue EqValue s1)
    | Inj (_) s0 s1 => congr_Inj (eq_refl s0) (compSubstRen__Value sigmaValue zetaValue thetaValue EqValue s1)
    end
 with compSubstRen__Exp { kValue : nat } { lValue : nat } { mValue : nat } (sigmaValue : fin (mValue) -> Value (kValue)) (zetaValue : fin (kValue) -> fin (lValue)) (thetaValue : fin (mValue) -> Value (lValue)) (EqValue : forall x, (funcomp (ren_Value zetaValue) sigmaValue) x = thetaValue x) (s : Exp (mValue)) : ren_Exp zetaValue (subst_Exp sigmaValue s) = subst_Exp thetaValue s :=
    match s with
    | Val (_) s0 => congr_Val (compSubstRen__Value sigmaValue zetaValue thetaValue EqValue s0)
    | App (_) s0 s1 => congr_App (compSubstRen__Exp sigmaValue zetaValue thetaValue EqValue s0) (compSubstRen__Exp sigmaValue zetaValue thetaValue EqValue s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS (compSubstRen__Exp sigmaValue zetaValue thetaValue EqValue s0) (compSubstRen__Exp (up_Value_Value sigmaValue) (upRen_Value_Value zetaValue) (up_Value_Value thetaValue) (up_subst_ren_Value_Value (_) (_) (_) EqValue) s1) (compSubstRen__Exp (up_Value_Value sigmaValue) (upRen_Value_Value zetaValue) (up_Value_Value thetaValue) (up_subst_ren_Value_Value (_) (_) (_) EqValue) s2)
    | CaseP (_) s0 s1 => congr_CaseP (compSubstRen__Exp sigmaValue zetaValue thetaValue EqValue s0) (compSubstRen__Exp (up_Value_Value (up_Value_Value sigmaValue)) (upRen_Value_Value (upRen_Value_Value zetaValue)) (up_Value_Value (up_Value_Value thetaValue)) (up_subst_ren_Value_Value (_) (_) (_) (up_subst_ren_Value_Value (_) (_) (_) EqValue)) s1)
    end.

Definition up_subst_subst_Value_Value { k : nat } { lValue : nat } { mValue : nat } (sigma : fin (k) -> Value (lValue)) (tauValue : fin (lValue) -> Value (mValue)) (theta : fin (k) -> Value (mValue)) (Eq : forall x, (funcomp (subst_Value tauValue) sigma) x = theta x) : forall x, (funcomp (subst_Value (up_Value_Value tauValue)) (up_Value_Value sigma)) x = (up_Value_Value theta) x :=
  fun n => match n with
  | Some n => eq_trans (compRenSubst_Value shift (up_Value_Value tauValue) (funcomp (up_Value_Value tauValue) shift) (fun x => eq_refl) (sigma n)) (eq_trans (eq_sym (compSubstRen__Value tauValue shift (funcomp (ren_Value shift) tauValue) (fun x => eq_refl) (sigma n))) (ap (ren_Value shift) (Eq n)))
  | None => eq_refl
  end.

Fixpoint compSubstSubst_Value { kValue : nat } { lValue : nat } { mValue : nat } (sigmaValue : fin (mValue) -> Value (kValue)) (tauValue : fin (kValue) -> Value (lValue)) (thetaValue : fin (mValue) -> Value (lValue)) (EqValue : forall x, (funcomp (subst_Value tauValue) sigmaValue) x = thetaValue x) (s : Value (mValue)) : subst_Value tauValue (subst_Value sigmaValue s) = subst_Value thetaValue s :=
    match s with
    | var_Value (_) s => EqValue s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam (compSubstSubst_Exp (up_Value_Value sigmaValue) (up_Value_Value tauValue) (up_Value_Value thetaValue) (up_subst_subst_Value_Value (_) (_) (_) EqValue) s0)
    | Pair (_) s0 s1 => congr_Pair (compSubstSubst_Value sigmaValue tauValue thetaValue EqValue s0) (compSubstSubst_Value sigmaValue tauValue thetaValue EqValue s1)
    | Inj (_) s0 s1 => congr_Inj (eq_refl s0) (compSubstSubst_Value sigmaValue tauValue thetaValue EqValue s1)
    end
 with compSubstSubst_Exp { kValue : nat } { lValue : nat } { mValue : nat } (sigmaValue : fin (mValue) -> Value (kValue)) (tauValue : fin (kValue) -> Value (lValue)) (thetaValue : fin (mValue) -> Value (lValue)) (EqValue : forall x, (funcomp (subst_Value tauValue) sigmaValue) x = thetaValue x) (s : Exp (mValue)) : subst_Exp tauValue (subst_Exp sigmaValue s) = subst_Exp thetaValue s :=
    match s with
    | Val (_) s0 => congr_Val (compSubstSubst_Value sigmaValue tauValue thetaValue EqValue s0)
    | App (_) s0 s1 => congr_App (compSubstSubst_Exp sigmaValue tauValue thetaValue EqValue s0) (compSubstSubst_Exp sigmaValue tauValue thetaValue EqValue s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS (compSubstSubst_Exp sigmaValue tauValue thetaValue EqValue s0) (compSubstSubst_Exp (up_Value_Value sigmaValue) (up_Value_Value tauValue) (up_Value_Value thetaValue) (up_subst_subst_Value_Value (_) (_) (_) EqValue) s1) (compSubstSubst_Exp (up_Value_Value sigmaValue) (up_Value_Value tauValue) (up_Value_Value thetaValue) (up_subst_subst_Value_Value (_) (_) (_) EqValue) s2)
    | CaseP (_) s0 s1 => congr_CaseP (compSubstSubst_Exp sigmaValue tauValue thetaValue EqValue s0) (compSubstSubst_Exp (up_Value_Value (up_Value_Value sigmaValue)) (up_Value_Value (up_Value_Value tauValue)) (up_Value_Value (up_Value_Value thetaValue)) (up_subst_subst_Value_Value (_) (_) (_) (up_subst_subst_Value_Value (_) (_) (_) EqValue)) s1)
    end.

Definition rinstInst_up_Value_Value { m : nat } { nValue : nat } (xi : fin (m) -> fin (nValue)) (sigma : fin (m) -> Value (nValue)) (Eq : forall x, (funcomp (var_Value (nValue)) xi) x = sigma x) : forall x, (funcomp (var_Value (S nValue)) (upRen_Value_Value xi)) x = (up_Value_Value sigma) x :=
  fun n => match n with
  | Some n => ap (ren_Value shift) (Eq n)
  | None => eq_refl
  end.

Fixpoint rinst_inst_Value { mValue : nat } { nValue : nat } (xiValue : fin (mValue) -> fin (nValue)) (sigmaValue : fin (mValue) -> Value (nValue)) (EqValue : forall x, (funcomp (var_Value (nValue)) xiValue) x = sigmaValue x) (s : Value (mValue)) : ren_Value xiValue s = subst_Value sigmaValue s :=
    match s with
    | var_Value (_) s => EqValue s
    | One (_)  => congr_One 
    | Lam (_) s0 => congr_Lam (rinst_inst_Exp (upRen_Value_Value xiValue) (up_Value_Value sigmaValue) (rinstInst_up_Value_Value (_) (_) EqValue) s0)
    | Pair (_) s0 s1 => congr_Pair (rinst_inst_Value xiValue sigmaValue EqValue s0) (rinst_inst_Value xiValue sigmaValue EqValue s1)
    | Inj (_) s0 s1 => congr_Inj (eq_refl s0) (rinst_inst_Value xiValue sigmaValue EqValue s1)
    end
 with rinst_inst_Exp { mValue : nat } { nValue : nat } (xiValue : fin (mValue) -> fin (nValue)) (sigmaValue : fin (mValue) -> Value (nValue)) (EqValue : forall x, (funcomp (var_Value (nValue)) xiValue) x = sigmaValue x) (s : Exp (mValue)) : ren_Exp xiValue s = subst_Exp sigmaValue s :=
    match s with
    | Val (_) s0 => congr_Val (rinst_inst_Value xiValue sigmaValue EqValue s0)
    | App (_) s0 s1 => congr_App (rinst_inst_Exp xiValue sigmaValue EqValue s0) (rinst_inst_Exp xiValue sigmaValue EqValue s1)
    | CaseS (_) s0 s1 s2 => congr_CaseS (rinst_inst_Exp xiValue sigmaValue EqValue s0) (rinst_inst_Exp (upRen_Value_Value xiValue) (up_Value_Value sigmaValue) (rinstInst_up_Value_Value (_) (_) EqValue) s1) (rinst_inst_Exp (upRen_Value_Value xiValue) (up_Value_Value sigmaValue) (rinstInst_up_Value_Value (_) (_) EqValue) s2)
    | CaseP (_) s0 s1 => congr_CaseP (rinst_inst_Exp xiValue sigmaValue EqValue s0) (rinst_inst_Exp (upRen_Value_Value (upRen_Value_Value xiValue)) (up_Value_Value (up_Value_Value sigmaValue)) (rinstInst_up_Value_Value (_) (_) (rinstInst_up_Value_Value (_) (_) EqValue)) s1)
    end.

Lemma instId_Value { mValue : nat } : subst_Value (var_Value (mValue)) = id .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => idSubst_Value (var_Value (mValue)) (fun n => eq_refl) (id x))). Qed.

Lemma instId_Exp { mValue : nat } : subst_Exp (var_Value (mValue)) = id .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => idSubst_Exp (var_Value (mValue)) (fun n => eq_refl) (id x))). Qed.

Lemma varL_Value { mValue : nat } { nValue : nat } (sigmaValue : fin (mValue) -> Value (nValue)) : funcomp (subst_Value sigmaValue) (var_Value (mValue)) = sigmaValue .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => eq_refl)). Qed.

Lemma varLRen_Value { mValue : nat } { nValue : nat } (xiValue : fin (mValue) -> fin (nValue)) : funcomp (ren_Value xiValue) (var_Value (mValue)) = funcomp (var_Value (nValue)) xiValue .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => eq_refl)). Qed.

Lemma rinstInst_Value { mValue : nat } { nValue : nat } (xiValue : fin (mValue) -> fin (nValue)) : ren_Value xiValue = subst_Value (funcomp (var_Value (nValue)) xiValue) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => rinst_inst_Value xiValue (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_Exp { mValue : nat } { nValue : nat } (xiValue : fin (mValue) -> fin (nValue)) : ren_Exp xiValue = subst_Exp (funcomp (var_Value (nValue)) xiValue) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun x => rinst_inst_Exp xiValue (_) (fun n => eq_refl) x)). Qed.

Lemma compComp_Value { kValue : nat } { lValue : nat } { mValue : nat } (sigmaValue : fin (mValue) -> Value (kValue)) (tauValue : fin (kValue) -> Value (lValue)) (s : Value (mValue)) : subst_Value tauValue (subst_Value sigmaValue s) = subst_Value (funcomp (subst_Value tauValue) sigmaValue) s .
Proof. exact (compSubstSubst_Value sigmaValue tauValue (_) (fun n => eq_refl) s). Qed.

Lemma compComp_Exp { kValue : nat } { lValue : nat } { mValue : nat } (sigmaValue : fin (mValue) -> Value (kValue)) (tauValue : fin (kValue) -> Value (lValue)) (s : Exp (mValue)) : subst_Exp tauValue (subst_Exp sigmaValue s) = subst_Exp (funcomp (subst_Value tauValue) sigmaValue) s .
Proof. exact (compSubstSubst_Exp sigmaValue tauValue (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_Value { kValue : nat } { lValue : nat } { mValue : nat } (sigmaValue : fin (mValue) -> Value (kValue)) (tauValue : fin (kValue) -> Value (lValue)) : funcomp (subst_Value tauValue) (subst_Value sigmaValue) = subst_Value (funcomp (subst_Value tauValue) sigmaValue) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => compComp_Value sigmaValue tauValue n)). Qed.

Lemma compComp'_Exp { kValue : nat } { lValue : nat } { mValue : nat } (sigmaValue : fin (mValue) -> Value (kValue)) (tauValue : fin (kValue) -> Value (lValue)) : funcomp (subst_Exp tauValue) (subst_Exp sigmaValue) = subst_Exp (funcomp (subst_Value tauValue) sigmaValue) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => compComp_Exp sigmaValue tauValue n)). Qed.

Lemma compRen_Value { kValue : nat } { lValue : nat } { mValue : nat } (sigmaValue : fin (mValue) -> Value (kValue)) (zetaValue : fin (kValue) -> fin (lValue)) (s : Value (mValue)) : ren_Value zetaValue (subst_Value sigmaValue s) = subst_Value (funcomp (ren_Value zetaValue) sigmaValue) s .
Proof. exact (compSubstRen__Value sigmaValue zetaValue (_) (fun n => eq_refl) s). Qed.

Lemma compRen_Exp { kValue : nat } { lValue : nat } { mValue : nat } (sigmaValue : fin (mValue) -> Value (kValue)) (zetaValue : fin (kValue) -> fin (lValue)) (s : Exp (mValue)) : ren_Exp zetaValue (subst_Exp sigmaValue s) = subst_Exp (funcomp (ren_Value zetaValue) sigmaValue) s .
Proof. exact (compSubstRen__Exp sigmaValue zetaValue (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_Value { kValue : nat } { lValue : nat } { mValue : nat } (sigmaValue : fin (mValue) -> Value (kValue)) (zetaValue : fin (kValue) -> fin (lValue)) : funcomp (ren_Value zetaValue) (subst_Value sigmaValue) = subst_Value (funcomp (ren_Value zetaValue) sigmaValue) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => compRen_Value sigmaValue zetaValue n)). Qed.

Lemma compRen'_Exp { kValue : nat } { lValue : nat } { mValue : nat } (sigmaValue : fin (mValue) -> Value (kValue)) (zetaValue : fin (kValue) -> fin (lValue)) : funcomp (ren_Exp zetaValue) (subst_Exp sigmaValue) = subst_Exp (funcomp (ren_Value zetaValue) sigmaValue) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => compRen_Exp sigmaValue zetaValue n)). Qed.

Lemma renComp_Value { kValue : nat } { lValue : nat } { mValue : nat } (xiValue : fin (mValue) -> fin (kValue)) (tauValue : fin (kValue) -> Value (lValue)) (s : Value (mValue)) : subst_Value tauValue (ren_Value xiValue s) = subst_Value (funcomp tauValue xiValue) s .
Proof. exact (compRenSubst_Value xiValue tauValue (_) (fun n => eq_refl) s). Qed.

Lemma renComp_Exp { kValue : nat } { lValue : nat } { mValue : nat } (xiValue : fin (mValue) -> fin (kValue)) (tauValue : fin (kValue) -> Value (lValue)) (s : Exp (mValue)) : subst_Exp tauValue (ren_Exp xiValue s) = subst_Exp (funcomp tauValue xiValue) s .
Proof. exact (compRenSubst_Exp xiValue tauValue (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_Value { kValue : nat } { lValue : nat } { mValue : nat } (xiValue : fin (mValue) -> fin (kValue)) (tauValue : fin (kValue) -> Value (lValue)) : funcomp (subst_Value tauValue) (ren_Value xiValue) = subst_Value (funcomp tauValue xiValue) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => renComp_Value xiValue tauValue n)). Qed.

Lemma renComp'_Exp { kValue : nat } { lValue : nat } { mValue : nat } (xiValue : fin (mValue) -> fin (kValue)) (tauValue : fin (kValue) -> Value (lValue)) : funcomp (subst_Exp tauValue) (ren_Exp xiValue) = subst_Exp (funcomp tauValue xiValue) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => renComp_Exp xiValue tauValue n)). Qed.

Lemma renRen_Value { kValue : nat } { lValue : nat } { mValue : nat } (xiValue : fin (mValue) -> fin (kValue)) (zetaValue : fin (kValue) -> fin (lValue)) (s : Value (mValue)) : ren_Value zetaValue (ren_Value xiValue s) = ren_Value (funcomp zetaValue xiValue) s .
Proof. exact (compRenRen_Value xiValue zetaValue (_) (fun n => eq_refl) s). Qed.

Lemma renRen_Exp { kValue : nat } { lValue : nat } { mValue : nat } (xiValue : fin (mValue) -> fin (kValue)) (zetaValue : fin (kValue) -> fin (lValue)) (s : Exp (mValue)) : ren_Exp zetaValue (ren_Exp xiValue s) = ren_Exp (funcomp zetaValue xiValue) s .
Proof. exact (compRenRen_Exp xiValue zetaValue (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_Value { kValue : nat } { lValue : nat } { mValue : nat } (xiValue : fin (mValue) -> fin (kValue)) (zetaValue : fin (kValue) -> fin (lValue)) : funcomp (ren_Value zetaValue) (ren_Value xiValue) = ren_Value (funcomp zetaValue xiValue) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => renRen_Value xiValue zetaValue n)). Qed.

Lemma renRen'_Exp { kValue : nat } { lValue : nat } { mValue : nat } (xiValue : fin (mValue) -> fin (kValue)) (zetaValue : fin (kValue) -> fin (lValue)) : funcomp (ren_Exp zetaValue) (ren_Exp xiValue) = ren_Exp (funcomp zetaValue xiValue) .
Proof. exact (FunctionalExtensionality.functional_extensionality _ _ (fun n => renRen_Exp xiValue zetaValue n)). Qed.

Arguments var_Value {nValue}.

Arguments One {nValue}.

Arguments Lam {nValue}.

Arguments Pair {nValue}.

Arguments Inj {nValue}.

Arguments Val {nValue}.

Arguments App {nValue}.

Arguments CaseS {nValue}.

Arguments CaseP {nValue}.

Instance Subst_Value : Subst1 Value Value := @subst_Value .

Instance Subst_Exp : Subst1 Value Exp := @subst_Exp .

Instance Ren_Value : Ren1 Value := @ren_Value .

Instance Ren_Exp : Ren1 Exp := @ren_Exp .

Instance VarInstance_Value : Var Value := @var_Value .

Notation "x '__Value'" := (@ids Value VarInstance_Value (_) x) (at level 30, format "x __Value") : subst_scope.

Notation "⇑__Value" := (@up_Value_Value (_)) (only printing) : subst_scope.

Ltac auto_unfold := repeat unfold subst1,  ren1,  subst2,  ren2,  Subst1,  Ren1,  Subst2,  Ren2,  ids,  Subst_Value,  Subst_Exp,  Ren_Value,  Ren_Exp,  VarInstance_Value.

Ltac auto_fold := try fold VarInstance_Value;  try fold (@ids _ VarInstance_Value);  try fold Subst_Value;  try fold Subst_Exp;  try fold (@subst1 _ _ Subst_Value);  try fold (@subst1 _ _ Subst_Exp);  try fold Ren_Value;  try fold Ren_Exp;  try fold (@ren1 _ Ren_Value);  try fold (@ren1 _ Ren_Exp).

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  ren1,  subst2,  ren2,  Subst1,  Ren1,  Subst2,  Ren2,  ids,  Subst_Value,  Subst_Exp,  Ren_Value,  Ren_Exp,  VarInstance_Value in *.

Tactic Notation "auto_fold" "in" "*" := try fold VarInstance_Value in *;  try fold (@ids _ VarInstance_Value) in *;  try fold Subst_Value in *;  try fold Subst_Exp in *;  try fold (@subst1 _ _ Subst_Value) in *;  try fold (@subst1 _ _ Subst_Exp) in *;  try fold Ren_Value in *;  try fold Ren_Exp in *;  try fold (@ren1 _ Ren_Value) in *;  try fold (@ren1 _ Ren_Exp) in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_Value| progress rewrite ?compComp_Value| progress rewrite ?compComp'_Value| progress rewrite ?compRen_Value| progress rewrite ?compRen'_Value| progress rewrite ?renComp_Value| progress rewrite ?renComp'_Value| progress rewrite ?renRen_Value| progress rewrite ?renRen'_Value| progress rewrite ?instId_Exp| progress rewrite ?compComp_Exp| progress rewrite ?compComp'_Exp| progress rewrite ?compRen_Exp| progress rewrite ?compRen'_Exp| progress rewrite ?renComp_Exp| progress rewrite ?renComp'_Exp| progress rewrite ?renRen_Exp| progress rewrite ?renRen'_Exp| progress rewrite ?varL_Value| progress rewrite ?varLRen_Value| progress (unfold up_ren, upRen_Value_Value, up_Value_Value)| progress (cbn [subst_Value subst_Exp ren_Value ren_Exp])| fsimpl].

Ltac asimpl := auto_unfold; asimpl'; auto_fold.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_Value in *| progress rewrite ?compComp_Value in *| progress rewrite ?compComp'_Value in *| progress rewrite ?compRen_Value in *| progress rewrite ?compRen'_Value in *| progress rewrite ?renComp_Value in *| progress rewrite ?renComp'_Value in *| progress rewrite ?renRen_Value in *| progress rewrite ?renRen'_Value in *| progress rewrite ?instId_Exp in *| progress rewrite ?compComp_Exp in *| progress rewrite ?compComp'_Exp in *| progress rewrite ?compRen_Exp in *| progress rewrite ?compRen'_Exp in *| progress rewrite ?renComp_Exp in *| progress rewrite ?renComp'_Exp in *| progress rewrite ?renRen_Exp in *| progress rewrite ?renRen'_Exp in *| progress rewrite ?varL_Value in *| progress rewrite ?varLRen_Value in *| progress (unfold up_ren, upRen_Value_Value, up_Value_Value in *)| progress (cbn [subst_Value subst_Exp ren_Value ren_Exp] in *)| fsimpl in *]; auto_fold in *.

Ltac substify := auto_unfold; try repeat (erewrite rinst_inst_Value; [|now intros]); try repeat (erewrite rinst_inst_Exp; [|now intros]); auto_fold.

Ltac renamify := auto_unfold; try repeat (erewrite <- rinst_inst_Value; [|intros; now asimpl]); try repeat (erewrite <- rinst_inst_Exp; [|intros; now asimpl]); auto_fold.
