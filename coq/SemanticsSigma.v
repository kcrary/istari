
Require Import Axioms.
Require Import Tactics.
Require Import Sigma.
Require Import Equality.
Require Import Relation.
Require Import Syntax.
Require Import Ofe.
Require Import Uniform.
Require Import Spaces.
Require Import Dynamic.
Require Import Hygiene.
Require Import Equivalence.
Require Import Urelsp.
Require Import Intensional.
Require Import Ordinal.
Require Import Candidate.
Require Import Ceiling.
Require Import Truncate.
Require Import MapTerm.
Require Import Extend.
Require Import Standard.
Require Import Equivalences.
Require Import ExtendTruncate.

Require Import SemanticsPi.


Definition prod_action
  (w : ordinal) (A B : wurel w)
  : nat -> relation (wterm w)
  :=
  fun i m m' =>
    exists n n' p p', 
      hygiene clo m
      /\ hygiene clo m'
      /\ star step m (ppair n p)
      /\ star step m' (ppair n' p')
      /\ rel A i n n'
      /\ rel B i p p'.


Lemma prod_uniform :
  forall w A B, uniform _ (prod_action w A B).
Proof.
intros w A B.
do2 3 split.

(* closed *)
{
intros i m n H.
decompose H; auto.
}

(* equiv *)
{
intros i m m' n n' Hclm' Hcln' Hequivm Hequivn H.
decompose H.
intros p q r t _ _ Hstepsm Hstepsn Hpq Hrt.
so (equiv_eval _#4 Hequivm (conj Hstepsm value_ppair)) as (m'' & (Hstepsm' & _) & Hmc).
invertc_mc Hmc.
intros p' Hequivp r' Hequivr <-.
fold (ppair p' r') in *.
so (equiv_eval _#4 Hequivn (conj Hstepsn value_ppair)) as (n'' & (Hstepsn' & _) & Hmc).
invertc_mc Hmc.
intros q' Hequivq t' Hequivt <-.
fold (ppair q' t') in *.
exists p', q', r', t'.
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsm' Hclm')) as H; cbn in H.
destruct H as (Hclp' & Hclr' & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsn' Hcln')) as H; cbn in H.
destruct H as (Hclq' & Hclt' & _).
do2 5 split; auto; eapply urel_equiv; eauto.
}

(* zigzag *)
{
intros i m n p q Hmn Hpn Hpq.
decompose Hmn.
intros m1 n1 m2 n2 Hclm _ Hstepsm Hstepsn Hmn1 Hmn2.
decompose Hpn.
intros p1 n1' p2 n2' _ _ Hstepsp Hstepsn' Hpn1 Hpn2.
decompose Hpq.
intros p1' q1 p2' q2 _ Hclq Hstepsp' Hstepsq Hpq1 Hpq2.
injection (determinism_eval _#4 (conj Hstepsn value_ppair) (conj Hstepsn' value_ppair)).
intros <- <-.
injection (determinism_eval _#4 (conj Hstepsp value_ppair) (conj Hstepsp' value_ppair)).
intros <- <-.
exists m1, q1, m2, q2.
do2 5 split; eauto using urel_zigzag.
}

(* downward *)
{
intros i m n H.
decompose H.
intros p q r t Hclm Hcln Hstepsm Hstepsn Hpq Hrt.
exists p, q, r, t.
do2 5 split; auto using urel_downward.
}
Qed.


Definition prod_urel w A B : wurel w
  :=
  mk_urel (prod_action w A B) (prod_uniform _ _ _).


Lemma ceiling_prod :
  forall n w A B,
    ceiling (S n) (prod_urel w A B)
    =
    prod_urel w
      (ceiling (S n) A)
      (ceiling (S n) B).
Proof.
intros n w A B.
apply urel_extensionality.
fextensionality 3.
intros i m p.
cbn.
pextensionality.
  {
  intros (Hi & Hact).
  decompose Hact.
  intros m1 p1 m2 p2 Hclm Hclp Hstepsm Hstepsp Hmp1 Hmp2.
  exists m1, p1, m2, p2.
  do2 5 split; auto; split; auto.
  }

  {
  intros Hact.
  decompose Hact.
  intros m1 p1 m2 p2 Hclm Hclp Hstepsm Hstepsp Hmp1 Hmp2.
  destruct Hmp1 as (Hi & Hmp1).
  destruct Hmp2 as (_ & Hmp2).
  split; auto.
  exists m1, p1, m2, p2.
  do2 5 split; auto.
  }
Qed.


Lemma extend_prod :
  forall v w (h : v <<= w) A B,
    extend_urel v w (prod_urel v A B)
    =
    prod_urel w (extend_urel v w A) (extend_urel v w B).
Proof.
intros v w h A B.
apply urel_extensionality.
fextensionality 3.
intros i m p.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros m1 p1 m2 p2 Hclm Hclp Hstepsm Hstepsp Hmp1 Hmp2.
  so (map_steps_form _#5 Hstepsm) as (m' & Heq & Hstepsm').
  so (map_eq_ppair_invert _#6 (eqsymm Heq)) as (m1' & m2' & -> & <- & <-); clear Heq.
  so (map_steps_form _#5 Hstepsp) as (p' & Heq & Hstepsp').
  so (map_eq_ppair_invert _#6 (eqsymm Heq)) as (p1' & p2' & -> & <- & <-); clear Heq.
  exists m1', p1', m2', p2'.
  do2 4 split; eauto using map_hygiene_conv.
  }

  {
  intro H.
  decompose H.
  intros m1 p1 m2 p2 Hclm Hclp Hstepsm Hstepsp Hmp1 Hmp2.
  cbn in Hmp1, Hmp2.
  exists (map_term (extend w v) m1), (map_term (extend w v) p1), (map_term (extend w v) m2), (map_term (extend w v) p2).
  do2 4 split; auto using map_hygiene.
    {
    so (map_steps _ _ (extend w v) _ _ Hstepsm) as H.
    simpmapin H.
    exact H.
    }

    {
    so (map_steps _ _ (extend w v) _ _ Hstepsp) as H.
    simpmapin H.
    exact H.
    }
  }
Qed.


Definition iuprod (w : ordinal) (A B : wiurel w) : wiurel w
  :=
  (prod_urel w (den A) (den B),
   meta_pair (meta_iurel A) 
     (meta_fn (den A) 
      (nearrow_compose meta_iurel_ne 
         (semiconst_ne (den A) B)))).


Lemma iuprod_inj :
  forall w A A' B B',
    iuprod w A B = iuprod w A' B'
    -> A = A'
       /\ (forall j m p, rel (den A) j m p -> iutruncate (S j) B = iutruncate (S j) B').
Proof.
intros w A A' B B' Heq.
unfold iupi in Heq.
so (f_equal (fun z => snd z) Heq) as Heq'.
cbn in Heq'.
so (meta_pair_inj _#5 Heq') as (H3 & H4).
so (meta_iurel_inj _#3 H3); subst A'.
split; auto.
intros i m p Hmp.
so (meta_fn_inj _#5 H4) as H5.
so (eq_dep_impl_eq_snd _#5 H5) as H6.
so (f_equal (fun f => pi1 f (urelspinj (den A) i m p Hmp)) H6) as H7.
cbn in H7.
so (meta_iurel_inj _#3 H7) as H8.
unfold semiconst in H8.
rewrite -> !urelsp_index_inj in H8.
exact H8.
Qed.


Lemma iutruncate_iuprod :
  forall n w A B,
    iutruncate (S n) (iuprod w A B)
    =
    iuprod w 
      (iutruncate (S n) A)
      (iutruncate (S n) B).
Proof.
intros n w A B.
unfold iuprod.
unfold iutruncate.
cbn [fst snd].
f_equal.
  {
  apply ceiling_prod.
  }

  {
  fold (iutruncate (S n) B).
  rewrite -> !meta_truncate_pair; try omega.
  f_equal.
    {
    apply meta_truncate_iurel; try omega.
    }
  rewrite -> meta_truncate_fn; try omega.
  f_equal.
  apply nearrow_extensionality.
  intro C.
  cbn -[meta_truncate].
  rewrite -> meta_truncate_iurel; try omega.
  f_equal.
  unfold semiconst.
  rewrite <- urelsp_index_embed_ceiling.
  rewrite -> !iutruncate_combine.
  rewrite -> Nat.min_comm.
  reflexivity.
  }
Qed.


Lemma extend_iuprod :
  forall v w (h : v <<= w) A B,
    extend_iurel h (iuprod v A B)
    =
    iuprod w (extend_iurel h A) (extend_iurel h B).
Proof.
intros v w h A B.
unfold iuprod, extend_iurel.
cbn.
f_equal.
  {
  apply (extend_prod v w h).
  }

  {
  unfold meta_iurel.
  cbn.
  rewrite -> !extend_meta_pair.
  rewrite -> extend_meta_urel.
  rewrite -> extend_meta_fn.
  f_equal.
  f_equal.
  f_equal.
  apply exT_extensionality_prop.
  cbn.
  fextensionality 1.
  intro x.
  rewrite -> extend_meta_iurel.
  f_equal.
  unfold semiconst.
  rewrite <- iutruncate_extend_iurel.
  rewrite -> urelsp_index_deextend.
  reflexivity.
  }
Qed.


Definition sigma_action
  (w : ordinal) (A : wurel w) (B : urelsp_car A -> wurel w)
  : nat -> relation (wterm w)
  :=
  fun i m m' =>
    exists n n' p p' (Hn : rel A i n n'),
      hygiene clo m
      /\ hygiene clo m'
      /\ star step m (ppair n p)
      /\ star step m' (ppair n' p')
      /\ rel (B (urelspinj A i n n' Hn)) i p p'.


Lemma sigma_uniform :
  forall w A (B : urelsp A -n> wurel_ofe w), uniform _ (sigma_action w A (pi1 B)).
Proof.
intros w A B.
do2 3 split.

(* closed *)
{
intros i m n H.
decompose H; auto.
}

(* equiv *)
{
intros i m m' n n' Hclm' Hcln' Hequivm Hequivn H.
decompose H.
intros p q r t Hpq _ _ Hstepsm Hstepsn Hrt.
so (equiv_eval _#4 Hequivm (conj Hstepsm value_ppair)) as (m'' & (Hstepsm' & _) & Hmc).
invertc_mc Hmc.
intros p' Hequivp r' Hequivr <-.
fold (ppair p' r') in *.
so (equiv_eval _#4 Hequivn (conj Hstepsn value_ppair)) as (n'' & (Hstepsn' & _) & Hmc).
invertc_mc Hmc.
intros q' Hequivq t' Hequivt <-.
fold (ppair q' t') in *.
exists p', q', r', t'.
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsm' Hclm')) as H; cbn in H.
destruct H as (Hclp' & Hclr' & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsn' Hcln')) as H; cbn in H.
destruct H as (Hclq' & Hclt' & _).
assert (rel A i p' q') as Hpq'.
  {
  eapply urel_equiv; eauto.
  }
exists Hpq'.
do2 4 split; auto.
replace (pi1 B (urelspinj A i p' q' Hpq')) with (pi1 B (urelspinj A i p q Hpq)).
2:{
  f_equal.
  apply urelspinj_equal.
  eapply urel_equiv_2; eauto.
  }
eapply urel_equiv; eauto.
}

(* zigzag *)
{
intros i m n p q Hmn Hpn Hpq.
decompose Hmn.
intros m1 n1 m2 n2 Hmn1 Hclm _ Hstepsm Hstepsn Hmn2.
decompose Hpn.
intros p1 n1' p2 n2' Hpn1 _ _ Hstepsp Hstepsn' Hpn2.
decompose Hpq.
intros p1' q1 p2' q2 Hpq1 _ Hclq Hstepsp' Hstepsq Hpq2.
injection (determinism_eval _#4 (conj Hstepsn value_ppair) (conj Hstepsn' value_ppair)).
intros <- <-.
injection (determinism_eval _#4 (conj Hstepsp value_ppair) (conj Hstepsp' value_ppair)).
intros <- <-.
so (urel_zigzag _#7 Hmn1 Hpn1 Hpq1) as Hmq1.
exists m1, q1, m2, q2, Hmq1.
do2 4 split; auto.
apply (urel_zigzag _#4 n2 p2); auto.
  {
  force_exact Hmn2.
  f_equal; f_equal.
  apply urelspinj_equal; auto.
  }

  {
  force_exact Hpn2.
  f_equal; f_equal.
  apply urelspinj_equal; auto.
  }

  {
  force_exact Hpq2.
  f_equal; f_equal.
  apply urelspinj_equal; auto.
  }
}

(* downward *)
{
intros i m n H.
decompose H.
intros p q r t Hpq Hclm Hcln Hstepsm Hstepsn Hrt.
so (urel_downward _#5 Hpq) as Hpq'.
exists p, q, r, t, Hpq'.
do2 4 split; auto.
refine (rel_from_dist _#6 _ (urel_downward _#5 Hrt)).
apply (pi2 B).
apply urelspinj_dist_diff; auto.
}
Qed.


Definition sigma_urel w A B :=
  mk_urel (sigma_action w A (pi1 B)) (sigma_uniform _ _ _).


Lemma prod_urel_eq_sigma_urel :
  forall w A (B : wiurel w),
    prod_urel w A (den B)
    =
    sigma_urel w A (nearrow_compose den_ne (semiconst_ne A B)).
Proof.
intros w A B.
apply urel_extensionality.
fextensionality 3.
intros i' m p.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros m1 p1 m2 p2 Hclm Hclp Hstepsm Hstepsp Hmp1 Hmp2.
  exists m1, p1, m2, p2, Hmp1.
  do2 4 split; auto.
  rewrite -> urelsp_index_inj.
  split; [omega |].
  auto.
  }

  {
  intro H.
  decompose H.
  intros m1 p1 m2 p2 Hmp1 Hclm Hclp Hstepsm Hstepsp Hmp2.
  exists m1, p1, m2, p2.
  do2 5 split; auto.
  rewrite -> urelsp_index_inj in Hmp2.
  destruct Hmp2; auto.
  }
Qed.


Lemma ceiling_sigma :
  forall n w A B,
    ceiling (S n) (sigma_urel w A B)
    =
    sigma_urel w
      (ceiling (S n) A)
      (nearrow_compose2 (embed_ceiling_ne (S n) A) (ceiling_ne (S n)) B).
Proof.
intros n w A B.
apply urel_extensionality.
fextensionality 3.
intros i m p.
cbn.
pextensionality.
  {
  intros (Hi, Hact).
  decompose Hact.
  intros m1 p1 m2 p2 Hmp1 Hclm Hclp Hstepsm Hstepsp Hmp2.
  exists m1, p1, m2, p2, (conj Hi Hmp1).
  do2 4 split; auto.
  split; auto.
  rewrite -> embed_ceiling_urelspinj; auto.
  }

  {
  intro Hact.
  decompose Hact.
  intros m1 p1 m2 p2 Hmp1 Hclm Hclp Hstepsm Hstepsp Hmp2.
  destruct Hmp1 as (Hi & Hmp1).
  destruct Hmp2 as (_ & Hmp2).
  split; auto.
  exists m1, p1, m2, p2, Hmp1.
  do2 4 split; auto.
  rewrite -> embed_ceiling_urelspinj in Hmp2; auto.
  }
Qed.


Lemma extend_sigma :
  forall v w (h : v <<= w) A B,
    extend_urel v w (sigma_urel v A B)
    =
    sigma_urel w 
      (extend_urel v w A)
      (nearrow_compose2 (deextend_urelsp_ne h A) (extend_urel_ne v w) B).
Proof.
intros v w h A B.
apply urel_extensionality.
fextensionality 3.
intros i m p.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros m1 p1 m2 p2 Hmp1 Hclm Hclp Hstepsm Hstepsp Hmp2.
  so (map_steps_form _#5 Hstepsm) as (m' & Heq & Hstepsm').
  so (map_eq_ppair_invert _#6 (eqsymm Heq)) as (m1' & m2' & -> & <- & <-); clear Heq.
  so (map_steps_form _#5 Hstepsp) as (p' & Heq & Hstepsp').
  so (map_eq_ppair_invert _#6 (eqsymm Heq)) as (p1' & p2' & -> & <- & <-); clear Heq.
  exists m1', p1', m2', p2', Hmp1.
  do2 4 split; eauto using map_hygiene_conv.
  rewrite -> deextend_urelsp_urelspinj.
  cbn.
  exact Hmp2.
  }

  {
  intro H.
  decompose H.
  intros m1 p1 m2 p2 Hmp1 Hclm Hclp Hstepsm Hstepsp Hmp2.
  cbn in Hmp1.
  exists (map_term (extend w v) m1), (map_term (extend w v) p1), (map_term (extend w v) m2), (map_term (extend w v) p2), Hmp1.
  do2 4 split; auto using map_hygiene.
    {
    so (map_steps _ _ (extend w v) _ _ Hstepsm) as H.
    simpmapin H.
    exact H.
    }

    {
    so (map_steps _ _ (extend w v) _ _ Hstepsp) as H.
    simpmapin H.
    exact H.
    }

    {
    cbn in Hmp2.
    rewrite -> deextend_urelsp_urelspinj in Hmp2.
    exact Hmp2.
    }
  }
Qed.


Definition iusigma (w : ordinal) (A : wiurel w) (B : urelsp (den A) -n> wiurel_ofe w) : wiurel w
  :=
  (sigma_urel w (den A) (nearrow_compose den_ne B),
   meta_pair (meta_iurel A) 
     (meta_fn (den A) 
      (nearrow_compose meta_iurel_ne B))).


Lemma iuprod_eq_iusigma :
  forall w A B,
    iuprod w A B
    =
    iusigma w A (semiconst_ne (den A) B).
Proof.
intros w A B.
apply prod_extensionality; auto.
cbn.
apply prod_urel_eq_sigma_urel.
Qed.


Lemma iusigma_inj :
  forall w A A' B B',
    iusigma w A B = iusigma w A' B'
    -> eq_dep (wiurel w) (fun r => urelsp (den r) -n> wiurel_ofe w) A B A' B'.
Proof.
intros w A A' B B' Heq.
unfold iusigma in Heq.
so (f_equal (fun z => snd z) Heq) as Heq'.
cbn in Heq'.
so (meta_pair_inj _#5 Heq') as (H3 & H4).
so (meta_iurel_inj _#3 H3); subst A'.
so (meta_fn_inj _#5 H4) as H5.
apply eq_impl_eq_dep_snd.
clear Heq Heq' H3 H4.
so (eq_dep_impl_eq_snd _#5 H5) as Heq.
apply nearrow_extensionality.
intro x.
so (f_equal (fun z => pi1 z x) Heq) as Heq'.
cbn in Heq'.
eapply meta_iurel_inj; eauto.
Qed.


Lemma iutruncate_iusigma :
  forall n w A B,
    iutruncate (S n) (iusigma w A B)
    =
    iusigma w 
      (iutruncate (S n) A)
      (nearrow_compose
         (nearrow_compose (iutruncate_ne (S n)) B)
         (embed_ceiling_ne (S n) (den A))).
Proof.
intros n w A B.
assert (S n > 0) as Hpos by omega.
unfold iusigma.
unfold iutruncate.
unfold den.
cbn [fst snd].
f_equal.
  {
  rewrite -> ceiling_sigma.
  f_equal.
  apply nearrow_extensionality.
  auto.
  }

  {
  rewrite -> !meta_truncate_pair; auto.
  f_equal.
    {
    apply meta_truncate_iurel; auto.
    }
  rewrite -> meta_truncate_fn; auto.
  f_equal.
  apply nearrow_extensionality.
  intro C.
  cbn -[meta_truncate].
  apply meta_truncate_iurel; auto.
  }
Qed.


Lemma extend_iusigma :
  forall v w (h : v <<= w) A B,
    extend_iurel h (iusigma v A B)
    =
    iusigma w (extend_iurel h A)
      (nearrow_compose
         (nearrow_compose (extend_iurel_ne h) B)
         (deextend_urelsp_ne h (den A))).
Proof.
intros v w h A B.
unfold iusigma, extend_iurel.
cbn.
f_equal.
  {
  rewrite -> (extend_sigma _ _ h).
  f_equal.
  apply nearrow_extensionality; auto.
  }
unfold meta_iurel.
cbn.
rewrite -> !extend_meta_pair.
rewrite -> extend_meta_urel.
rewrite -> extend_meta_fn.
f_equal.
f_equal.
f_equal.
apply exT_extensionality_prop.
cbn.
fextensionality 1.
intro x.
rewrite -> extend_meta_iurel.
reflexivity.
Qed.


Lemma prod_action_ppair :
  forall w A B i m1 m2 n1 n2,
    rel A i m1 n1
    -> rel B i m2 n2
    -> prod_action w A B i (ppair m1 m2) (ppair n1 n2).
Proof.
intros w A B i m1 m2 n1 n2 H1 H2.
exists m1, n1, m2, n2.
so (urel_closed _#5 H1) as (Hclm1 & Hcln1).
so (urel_closed _#5 H2) as (Hclm2 & Hcln2).
do2 4 split; auto using star_refl; apply hygiene_auto; cbn; auto.
Qed.


Local Ltac prove_hygiene :=
  repeat (first [ apply hygiene_shift_permit
                | apply hygiene_sumbool
                | apply hygiene_auto; cbn [row_rect nat_rect]; repeat2 split; auto
                ]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1;
  try (apply hygiene_var; cbn; auto; done).


Lemma prod_action_ppi1 :
  forall w A B i m n,
    prod_action w A B i m n
    -> rel A i (ppi1 m) (ppi1 n).
Proof.
intros w A B i m n H.
decompose H.
intros m1 n1 m2 n2 Hclm Hcln Hsteps Hsteps' Hmn1 Hmn2.
refine (urel_equiv _#7 _ _ _ _ Hmn1); try prove_hygiene.
  {
  apply equiv_symm.
  eapply equiv_trans.
    {
    apply equiv_ppi1.
    eapply steps_equiv; eauto.
    }
  apply steps_equiv; apply star_one; apply step_ppi12.
  }

  {
  apply equiv_symm.
  eapply equiv_trans.
    {
    apply equiv_ppi1.
    eapply steps_equiv; eauto.
    }
  apply steps_equiv; apply star_one; apply step_ppi12.
  }
Qed.


Lemma prod_action_ppi2 :
  forall w A B i m n,
    prod_action w A B i m n
    -> rel B i (ppi2 m) (ppi2 n).
Proof.
intros w A B i m n H.
decompose H.
intros m1 n1 m2 n2 Hclm Hcln Hsteps Hsteps' Hmn1 Hmn2.
refine (urel_equiv _#7 _ _ _ _ Hmn2); try prove_hygiene.
  {
  apply equiv_symm.
  eapply equiv_trans.
    {
    apply equiv_ppi2.
    eapply steps_equiv; eauto.
    }
  apply steps_equiv; apply star_one; apply step_ppi22.
  }

  {
  apply equiv_symm.
  eapply equiv_trans.
    {
    apply equiv_ppi2.
    eapply steps_equiv; eauto.
    }
  apply steps_equiv; apply star_one; apply step_ppi22.
  }
Qed.


Lemma prod_action_ppair1 :
  forall w A B i m n r p,
    hygiene clo (ppair m n)
    -> prod_action w A B i r p
    -> rel A i m (ppi1 p)
    -> rel B i n (ppi2 p)
    -> prod_action w A B i (ppair m n) p.
Proof.
intros w A B i m n r p Hclmn Hrp H1 H2.
decompose Hrp.
intros _ p1 _ p2 _ Hclp _ Hstepsp _ _.
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsp Hclp)) as H; cbn in H.
destruct H as (Hclp1 & Hclp2 & _).
exists m, p1, n, p2.
do2 5 split; auto using star_refl.
  {
  eapply urel_equiv_2; eauto.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi1); auto using step_ppi11.
    exact Hstepsp.
    }
  apply star_one; apply step_ppi12.
  }

  {
  eapply urel_equiv_2; eauto.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi2); auto using step_ppi21.
    exact Hstepsp.
    }
  apply star_one; apply step_ppi22.
  }
Qed.


Lemma embed_ceiling_urelspinj_prod :
  forall i w A B j m n p q (Hj : j < S i) (Hmn : rel A j m n) (Hpq : rel B j p q),
    embed_ceiling (S i) (prod_urel w A B)
      (transport (eqsymm (ceiling_prod i w A B)) urelsp_car
         (urelspinj (prod_urel w (ceiling (S i) A) (ceiling (S i) B)) j
            (ppair m p) (ppair n q)
            (prod_action_ppair w (ceiling (S i) A) (ceiling (S i) B) j m p n q
              (conj Hj Hmn) (conj Hj Hpq))))
    =
    urelspinj (prod_urel w A B) j (ppair m p) (ppair n q)
      (prod_action_ppair w A B j m p n q Hmn Hpq).
Proof.
intros i w A B j m n p q Hj Hmn Hpq.
apply exT_extensionality_prop.
cbn.
rewrite -> (pi1_transport_dep_lift _ _ urelsp_car_rhs _ _ (eqsymm (ceiling_prod i w A B))).
cbn.
rewrite -> transport_const.
fextensionality 2.
intros k r.
pextensionality.
  {
  intros (Hk & Hact).
  split; auto.
  decompose Hact.
  intros r1 n' r2 q' Hclr Hclnq Hsteps Hsteps' H1 H2.
  exists r1, n', r2, q'.
  do2 5 split; auto.
    {
    destruct H1; auto.
    }

    {
    destruct H2; auto.
    }
  }

  {
  intros (Hk & Hact).
  split; auto.
  decompose Hact.
  intros r1 n' r2 q' Hclr Hclnq Hsteps Hsteps' H1 H2.
  exists r1, n', r2, q'.
  do2 5 split; auto.
    {
    split; auto; omega.
    }

    {
    split; auto; omega.
    }
  }
Qed.


Lemma deextend_urelsp_urelspinj_prod :
  forall v w (h : v <<= w) A B i m n p q (Hmn : rel (extend_urel v w A) i m n) (Hpq : rel (extend_urel v w B) i p q),
    deextend_urelsp h (prod_urel v A B)
      (transport (eqsymm (extend_prod v w h A B)) urelsp_car
         (urelspinj (prod_urel w (extend_urel v w A) (extend_urel v w B)) i
            (ppair m p) (ppair n q)
            (prod_action_ppair w (extend_urel v w A) (extend_urel v w B) i m p n q Hmn Hpq)))
    =
    urelspinj (prod_urel v A B) i (map_term (extend w v) (ppair m p)) (map_term (extend w v) (ppair n q)) 
      (prod_action_ppair v A B i (map_term (extend w v) m) (map_term (extend w v) p) (map_term (extend w v) n) (map_term (extend w v) q) Hmn Hpq).
Proof.
intros v w h A B i m n p q Hmn Hpq.
apply exT_extensionality_prop.
cbn.
fold (ppair (map_term (extend w v) n) (map_term (extend w v) q)).
rewrite -> (pi1_transport_dep_lift _ _ urelsp_car_rhs _ _ (eqsymm (extend_prod v w h A B))).
cbn.
rewrite -> transport_const.
fextensionality 2.
intros k r.
pextensionality.
  {
  intros (Hk & Hact).
  split; auto.
  decompose Hact.
  intros r1 n' r2 q' Hclr Hclnq Hsteps Hsteps' H1 H2.
  exists (map_term (extend w v) r1), (map_term (extend w v) n'), (map_term (extend w v) r2), (map_term (extend w v) q').
  do2 5 split; eauto using map_hygiene_conv.
    {
    so (map_hygiene _ _ (extend w v) _ _ Hclnq) as H.
    simpmapin H.
    exact H.
    }

    {
    so (map_steps _ _ (extend w v) _ _ Hsteps) as H.
    simpmapin H.
    rewrite -> extend_term_cancel in H; auto.
    }

    {
    so (map_steps _ _ (extend w v) _ _ Hsteps') as H.
    simpmapin H.
    auto.
    }
  }

  {
  intros (Hk & Hact).
  split; auto.
  decompose Hact.
  intros r1 n' r2 q' Hclr Hclnq Hsteps Hsteps' H1 H2.
  exploit (map_steps_form _ _ (extend w v) (ppair n q) (ppair n' q')) as H.
    {
    simpmap; auto.
    }
  destruct H as (x & Heq & Hsteps'').
  so (map_eq_ppair_invert _#6 (eqsymm Heq)) as (n'' & q'' & -> & <- & <-).
  exists (map_term (extend v w) r1), n'', (map_term (extend v w) r2), q''.
  do2 5 split; auto.
    {
    apply map_hygiene; auto.
    }

    {
    apply (map_hygiene_conv _ _ (extend w v)).
    simpmap; auto.
    }

    {
    so (map_steps _ _ (extend v w) _ _ Hsteps) as H.
    simpmapin H; auto.
    }

    {
    cbn.
    rewrite -> !extend_term_cancel; auto.
    }

    {
    cbn.
    rewrite -> !extend_term_cancel; auto.
    }
  }
Qed.

