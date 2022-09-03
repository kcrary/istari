
Require Import Tactics.
Require Import Axioms.
Require Import Sigma.
Require Import Equality.
Require Import Ordinal.
Require Import Relation.
Require Import Ofe.
Require Import Syntax.
Require Import SimpSub.
Require Import Hygiene.
Require Import Uniform.
Require Import Urelsp.
Require Import Intensional.
Require Import Dynamic.
Require Import Equivalence.
Require Import Equivalences.
Require Import Candidate.
Require Import Model.
Require Import Ceiling.
Require Import Truncate.
Require Import Standard.
Require Import MapTerm.
Require Import Extend.
Require Import System.
Require Import Page.
Require Import PageCode.
Require Import Defined.


Definition kext (w : ordinal) (K : qkind) : wterm w
  :=
  match lt_ord_dec (level K) w with
  | left h =>
      ext (objin (objsome (expair K (space_inhabitant _)) h))

  | right _ =>
      arb
  end.


Definition uext (w : ordinal) {l} (A : wurel l) : wterm w
  :=
  match lt_ord_dec l w with
  | left h =>
      ext (objin (objsome (expair (qtype l) (iubase A)) h))

  | right _ => arb
  end.


Fixpoint tosp (w : ordinal) (pg : page) (K : qkind) {struct K} : wterm w :=
  match K with
  | qone => 
      lam cunit

  | qtype l =>
      lam (cty (var 0))

  | qarrow K1 K2 =>
      lam (clam (kext w K1)
             (app (tosp w pg K2)
                (app (var 1) (app (fromsp w pg K1) (var 0)))))

  | qtarrow l A K2 =>
      lam (ctlam (uext w A)
             (app (tosp w pg K2) (app (var 1) (var 0)))
             (kext w K2))

  | qprod K1 K2 =>
      lam (cpair (app (tosp w pg K1) (ppi1 (var 0))) (app (tosp w pg K2) (ppi2 (var 0))))

  | qfut K1 =>
      lam (cnext (app (tosp w pg K1) (prev (var 0))))
  end


with fromsp (w : ordinal) (pg : page) (K : qkind) {struct K} : wterm w :=
  match K with
  | qone => 
      lam triv

  | qtype l =>
      (* Should have cin pg = l, don't need to check it. *)
      lam (con (pagelit pg) (var 0))

  | qarrow K1 K2 =>
      lam (lam (app (fromsp w pg K2) 
                  (capp (var 1) (app (tosp w pg K1) (var 0)))))

  | qtarrow l A K2 =>
      lam (lam (app (fromsp w pg K2)
                  (ctapp (var 1) (var 0))))

  | qprod K1 K2 =>
      lam (ppair (app (fromsp w pg K1) (cpi1 (var 0))) (app (fromsp w pg K2) (cpi2 (var 0))))

  | qfut K1 =>
      lam (next (app (fromsp w pg K1) (cprev (var 0))))
  end.


Lemma kext_hygiene :
  forall w K,
    hygiene clo (kext w K).
Proof.
intros w K.
unfold kext.
set (X := lt_ord_dec (level K) w).
destruct X; apply hygiene_auto; cbn; auto.
Qed.


Lemma uext_hygiene :
  forall w l A,
    hygiene clo (@uext w l A).
Proof.
intros w l A.
unfold uext.
set (X := lt_ord_dec l w).
destruct X; apply hygiene_auto; cbn; auto.
Qed.


Local Ltac prove_hygiene :=
  repeat (first [ apply hygiene_shift_permit
                | apply hygiene_sumbool
                | apply hygiene_auto; cbn [row_rect nat_rect]; repeat2 split; auto
                ]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1, kext_hygiene, uext_hygiene, pagelit_closed;
  try (apply hygiene_var; cbn; auto; done).


Lemma tosp_fromsp_hygiene :
  forall w pg K,
    hygiene clo (tosp w pg K)
    /\ hygiene clo (fromsp w pg K).
Proof.
intros w pg K.
induct K; intros; destruct_everywhere; cbn; split;
prove_hygiene.
Qed.


Lemma tosp_hygiene :
  forall w pg K, hygiene clo (tosp w pg K).
Proof.
intros w pg K.
exact (tosp_fromsp_hygiene w pg K andel).
Qed.


Lemma fromsp_hygiene :
  forall w pg K, hygiene clo (fromsp w pg K).
Proof.
intros w pg K.
exact (tosp_fromsp_hygiene w pg K ander).
Qed.


Lemma subst_kext :
  forall w s K, subst s (kext w K) = kext w K.
Proof.
intros.
unfold kext.
set (X := lt_ord_dec (level K) w).
destruct X; auto.
Qed.


Lemma subst_uext :
  forall w s l A, subst s (@uext w l A) = uext w A.
Proof.
intros.
unfold uext.
set (X := lt_ord_dec l w).
destruct X; auto.
Qed.  


Lemma subst_tosp :
  forall w s pg K, subst s (tosp w pg K) = tosp w pg K.
Proof.
intros w s pg K.
apply subst_into_closed.
apply tosp_hygiene.
Qed.


Lemma subst_fromsp :
  forall w s pg K, subst s (fromsp w pg K) = fromsp w pg K.
Proof.
intros w s pg K.
apply subst_into_closed.
apply fromsp_hygiene.
Qed.


Hint Rewrite subst_kext subst_uext subst_tosp subst_fromsp : subst.




Lemma extend_kext :
  forall v w K,
    level K << v
    -> level K << w
    -> map_term (extend v w) (kext v K) = kext w K.
Proof.
intros v w K h h'.
unfold kext.
rewrite -> (lt_ord_dec_is _ _ h).
rewrite -> (lt_ord_dec_is _ _ h').
simpmap.
rewrite -> (extend_some v w (expair K (space_inhabitant K)) h h').
reflexivity.
Qed.


Lemma extend_uext :
  forall v w u (A : wurel u),
    u << v
    -> u << w
    -> map_term (extend v w) (uext v A) = uext w A.
Proof.
intros v w u A h h'.
unfold uext.
rewrite -> (lt_ord_dec_is _ _ h).
rewrite -> (lt_ord_dec_is _ _ h').
simpmap.
rewrite -> (extend_some v w (expair (qtype u) (iubase A)) h h').
reflexivity.
Qed.


Lemma extend_tosp_fromsp :
  forall v w pg K,
    (level K << v -> level K << w -> map_term (extend v w) (tosp v pg K) = tosp w pg K)
    /\ (level K << v -> level K << w -> map_term (extend v w) (fromsp v pg K) = fromsp w pg K).
Proof.
intros v w pg K.
induct K; split; cbn [fromsp tosp]; destruct_everywhere; try (simpmap; reflexivity); revert_all.

(* arrow tosp *)
{
intros v w pg K _ IH1 L IH2 _ Hlevv Hlevw.
cbn in Hlevv, Hlevw.
so (max_ord_lub_strict_l _#3 Hlevv) as HlevKv.
so (max_ord_lub_strict_r _#3 Hlevv) as HlevLv.
so (max_ord_lub_strict_l _#3 Hlevw) as HlevKw.
so (max_ord_lub_strict_r _#3 Hlevw) as HlevLw.
simpmap.
f_equal.
f_equal.
  {
  apply extend_kext; auto.
  }
f_equal; auto.
f_equal.
f_equal; auto.
}

(* arrow fromsp *)
{
intros v w pg K IH1 _ L _ IH2 Hlevv Hlevw.
cbn in Hlevv, Hlevw.
so (max_ord_lub_strict_l _#3 Hlevv) as HlevKv.
so (max_ord_lub_strict_r _#3 Hlevv) as HlevLv.
so (max_ord_lub_strict_l _#3 Hlevw) as HlevKw.
so (max_ord_lub_strict_r _#3 Hlevw) as HlevLw.
simpmap.
f_equal.
f_equal.
f_equal; auto.
f_equal.
f_equal; auto.
}

(* tarrow tosp *)
{
intros v w pg u A K IH1 IH2 Hlevv Hlevw.
cbn in Hlevv, Hlevw.
so (max_ord_lub_strict_l _#3 Hlevv) as Huv.
so (max_ord_lub_strict_r _#3 Hlevv) as HlevKv.
so (max_ord_lub_strict_l _#3 Hlevw) as Huw.
so (max_ord_lub_strict_r _#3 Hlevw) as HlevKw.
simpmap.
f_equal.
f_equal; auto using extend_uext, extend_kext.
f_equal; auto.
}

(* tarrow fromsp *)
{
intros v w pg u A K IH1 IH2 Hlevv Hlevw.
cbn in Hlevv, Hlevw.
so (max_ord_lub_strict_l _#3 Hlevv) as Huv.
so (max_ord_lub_strict_r _#3 Hlevv) as HlevKv.
so (max_ord_lub_strict_l _#3 Hlevw) as Huw.
so (max_ord_lub_strict_r _#3 Hlevw) as HlevKw.
simpmap.
f_equal.
f_equal.
f_equal; auto.
}

(* prod tosp *)
{
intros v w pg K IH1 _ L IH2 _ Hlevv Hlevw.
cbn in Hlevv, Hlevw.
so (max_ord_lub_strict_l _#3 Hlevv) as HlevKv.
so (max_ord_lub_strict_r _#3 Hlevv) as HlevLv.
so (max_ord_lub_strict_l _#3 Hlevw) as HlevKw.
so (max_ord_lub_strict_r _#3 Hlevw) as HlevLw.
simpmap.
f_equal.
rewrite -> IH1; auto.
rewrite -> IH2; auto.
}

(* prod fromsp *)
{
intros v w pg K _ IH1 L _ IH2 Hlevv Hlevw.
cbn in Hlevv, Hlevw.
so (max_ord_lub_strict_l _#3 Hlevv) as HlevKv.
so (max_ord_lub_strict_r _#3 Hlevv) as HlevLv.
so (max_ord_lub_strict_l _#3 Hlevw) as HlevKw.
so (max_ord_lub_strict_r _#3 Hlevw) as HlevLw.
simpmap.
f_equal.
rewrite -> IH1; auto.
rewrite -> IH2; auto.
}

(* fut tosp *)
{
intros v w pg K IH1 IH2 Hlevv Hlevw.
cbn in Hlevv, Hlevw.
simpmap.
f_equal.
f_equal.
f_equal; auto.
}

(* fut fromsp *)
{
intros v w pg K IH1 IH2 Hlevv Hlevw.
cbn in Hlevv, Hlevw.
simpmap.
f_equal.
f_equal.
f_equal; auto.
}
Qed.


Lemma extend_tosp :
  forall v w pg K,
    level K << v
    -> level K << w
    -> map_term (extend v w) (tosp v pg K) = tosp w pg K.
Proof.
intros v w pg K Hv Hw.
exact (extend_tosp_fromsp v w pg K andel Hv Hw).
Qed.


Lemma extend_fromsp :
  forall v w pg K,
    level K << v
    -> level K << w
    -> map_term (extend v w) (fromsp v pg K) = fromsp w pg K.
Proof.
intros v w pg K Hv Hw.
exact (extend_tosp_fromsp v w pg K ander Hv Hw).
Qed.
