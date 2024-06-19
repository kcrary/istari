
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


Definition arrow_action
  (w : ordinal) i (A B : wurel w)
  : nat -> relation (wterm w)
  :=
  fun i' m m' =>
    exists l l',
      i' <= i
      /\ hygiene clo m
      /\ hygiene clo m'
      /\ star step m (lam l)
      /\ star step m' (lam l')
      /\ forall j n n',
           j <= i'
           -> rel A j n n'
           -> rel B j (subst1 n l) (subst1 n' l').


Lemma arrow_uniform :
  forall w i A B, uniform _ (arrow_action w i A B).
Proof.
intros w i A B.
do2 3 split.

(* closed *)
{
intros i' m n H.
decompose H; auto.
}

(* equiv *)
{
intros i' m m' n n' Hclm' Hcln' Hm Hn H.
decompose H.
intros l p Hi _ _ Hstepsm Hstepsn Hact.
so (equiv_eval _ _ _ _ Hm (conj Hstepsm value_lam)) as (x & (Hstepsm' & _) & Hmc).
assert (exists l', x = lam l') as (l' & ->).
  {
  invertc_mc Hmc; [].
  intros l' _ <-.
  exists l'.
  reflexivity.
  }
so (equiv_eval _ _ _ _ Hn (conj Hstepsn value_lam)) as (x & (Hstepsn' & _) & Hmc').
assert (exists p', x = lam p') as (p' & ->).
  {
  invertc_mc Hmc'; [].
  intros p' _ <-.
  exists p'.
  reflexivity.
  }
exists l', p'.
do2 5 split; eauto using equiv_trans.
intros j q r Hleq' Hqr.
so (Hact j q r Hleq' Hqr) as Hrel.
so (urel_closed _#5 Hqr) as (Hclq & Hclr).
eapply urel_equiv; eauto.
  {
  apply hygiene_subst1; auto.
  so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsm' Hclm')) as H; cbn in H.
  destruct H; auto.
  }

  {
  apply hygiene_subst1; auto.
  so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsn' Hcln')) as H; cbn in H.
  destruct H; auto.
  }

  {
  apply equiv_subst1; [].
  invertc Hmc; [].
  intros H _.
  invertc H; [].
  auto.
  }

  {
  apply equiv_subst1; [].
  invertc Hmc'; [].
  intros H _.
  invertc H; [].
  auto.
  }
}

(* zigzag *)
{
intros i' m n p q Hmn Hpn Hpq.
destruct Hmn as (m' & n' & Hi & Hclm & Hcln & Hstepsm & Hstepsn & Hmn).
destruct Hpn as (p' & n'' & _ & Hclp & _ & Hstepsp & Hstepsn' & Hpn).
so (determinism_eval _#4 (conj Hstepsn value_lam) (conj Hstepsn' value_lam)) as H.
injection H; intros; subst n''.
clear Hstepsn' H.
destruct Hpq as (p'' & q' & _ & _ & Hclq' & Hstepsp' & Hstepsq & Hpq).
so (determinism_eval _#4 (conj Hstepsp value_lam) (conj Hstepsp' value_lam)) as H.
injection H; intros; subst p''.
clear Hstepsp' H.
exists m', q'.
repeat2 split; eauto; [].
intros j r s Hleqj Hrs.
so (Hmn _#3 Hleqj Hrs) as Hmn'.
so (Hpn _#3 Hleqj Hrs) as Hpn'.
so (Hpq _#3 Hleqj Hrs) as Hpq'.
eapply urel_zigzag; eauto.
}

(* downward *)
{
intros i' m n Hmn.
destruct Hmn as (m' & n' & Hi & Hclm & Hcln & Hstepsm & Hstepsn & Hmn).
exists m', n'.
repeat2 split; auto.
omega.
}
Qed.


Definition arrow_urel w i A B :=
  mk_urel (arrow_action w i A B) (arrow_uniform _ _ _ _).


Definition pi_action
  (w : ordinal) i (A : wurel w) (B : urelsp_car A -> wurel w)
  : nat -> relation (wterm w)
  :=
  fun i' m m' =>
    exists l l',
      i' <= i
      /\ hygiene clo m
      /\ hygiene clo m'
      /\ star step m (lam l)
      /\ star step m' (lam l')
      /\ forall j n n',
           j <= i'
           -> forall (Hn : rel A j n n'),
                rel (B (urelspinj A j n n' Hn)) j (subst1 n l) (subst1 n' l').


Lemma pi_uniform :
  forall w i A B, uniform _ (pi_action w i A B).
Proof.
intros w i A B.
do2 3 split.

(* closed *)
{
intros i' m n H.
decompose H; auto.
}

(* equiv *)
{
intros i' m m' n n' Hclm' Hcln' Hm Hn H.
decompose H.
intros l p Hi _ _ Hstepsm Hstepsn Hact.
so (equiv_eval _ _ _ _ Hm (conj Hstepsm value_lam)) as (x & (Hstepsm' & _) & Hmc).
assert (exists l', x = lam l') as (l' & ->).
  {
  invertc_mc Hmc; [].
  intros l' _ <-.
  exists l'.
  reflexivity.
  }
so (equiv_eval _ _ _ _ Hn (conj Hstepsn value_lam)) as (x & (Hstepsn' & _) & Hmc').
assert (exists p', x = lam p') as (p' & ->).
  {
  invertc_mc Hmc'; [].
  intros p' _ <-.
  exists p'.
  reflexivity.
  }
exists l', p'.
do2 5 split; eauto using equiv_trans.
intros j q r Hleq' Hqr.
so (Hact j q r Hleq' Hqr) as Hrel.
so (urel_closed _#5 Hqr) as (Hclq & Hclr).
eapply urel_equiv; eauto.
  {
  apply hygiene_subst1; auto.
  so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsm' Hclm')) as H; cbn in H.
  destruct H; auto.
  }

  {
  apply hygiene_subst1; auto.
  so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsn' Hcln')) as H; cbn in H.
  destruct H; auto.
  }

  {
  apply equiv_subst1; [].
  invertc Hmc; [].
  intros H _.
  invertc H; [].
  auto.
  }

  {
  apply equiv_subst1; [].
  invertc Hmc'; [].
  intros H _.
  invertc H; [].
  auto.
  }
}

(* zigzag *)
{
intros i' m n p q Hmn Hpn Hpq.
destruct Hmn as (m' & n' & Hi & Hclm & Hcln & Hstepsm & Hstepsn & Hmn).
destruct Hpn as (p' & n'' & _ & Hclp & _ & Hstepsp & Hstepsn' & Hpn).
so (determinism_eval _#4 (conj Hstepsn value_lam) (conj Hstepsn' value_lam)) as H.
injection H; intros; subst n''.
clear Hstepsn' H.
destruct Hpq as (p'' & q' & _ & _ & Hclq' & Hstepsp' & Hstepsq & Hpq).
so (determinism_eval _#4 (conj Hstepsp value_lam) (conj Hstepsp' value_lam)) as H.
injection H; intros; subst p''.
clear Hstepsp' H.
exists m', q'.
repeat2 split; eauto; [].
intros j r s Hleqj Hrs.
so (Hmn _#3 Hleqj Hrs) as Hmn'.
so (Hpn _#3 Hleqj Hrs) as Hpn'.
so (Hpq _#3 Hleqj Hrs) as Hpq'.
eapply urel_zigzag; eauto.
}

(* downward *)
{
intros i' m n Hmn.
destruct Hmn as (m' & n' & Hi & Hclm & Hcln & Hstepsm & Hstepsn & Hmn).
exists m', n'.
repeat2 split; auto.
omega.
}
Qed.


Definition pi_urel w i A B :=
  mk_urel (pi_action w i A B) (pi_uniform _ _ _ _).


Lemma arrow_urel_eq_pi_urel :
  forall w i A B,
    arrow_urel w i A B
    =
    pi_urel w i A (fun x => ceiling (S (urelsp_index _ x)) B).
Proof.
intros w i A B.
apply urel_extensionality.
fextensionality 3.
intros i' m p.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros l l' Hi Hclm Hclp Hsteps Hsteps' Hact.
  exists l, l'.
  do2 5 split; auto.
  intros j n q Hj Hnq.
  rewrite -> urelsp_index_inj.
  split; [omega |].
  apply Hact; auto.
  }

  {
  intro H.
  decompose H.
  intros l l' Hi Hclm Hclp Hsteps Hsteps' Hact.
  exists l, l'.
  do2 5 split; auto.
  intros j n q Hj Hnq.
  so (Hact _#3 Hj Hnq) as H.
  rewrite -> urelsp_index_inj in H.
  destruct H; auto.
  }
Qed.


Definition iupi (w : ordinal) i (A : wiurel w) (B : urelsp (den A) -n> wiurel_ofe w) : wiurel w
  :=
  (pi_urel w i (den A) (fun C => den (pi1 B C)),
   meta_pair (meta_iurel A) 
     (meta_fn (den A) 
      (nearrow_compose meta_iurel_ne B))).


Definition semiconst {cur} (A : wurel cur) (B : wiurel cur) : car (urelsp A) -> car (wiurel_ofe cur)
  :=
  fun x => iutruncate (S (urelsp_index _ x)) B.


Lemma semiconst_nonexpansive :
  forall cur (A : wurel cur) (B : wiurel cur),
    nonexpansive (semiconst A B).
Proof.
intros cur A B.
intros i x y Hxy.
so (urelsp_eta _ _ x) as (j & m & p & Hmp & ->).
so (urelsp_eta _ _ y) as (j' & n & q & Hnq & ->).
unfold semiconst.
rewrite -> !urelsp_index_inj.
so (urelspinj_dist_index' _#9 Hmp Hnq Hxy) as [(Heq & _) | (Hle & Hle')].
  {
  subst j'.
  apply dist_refl.
  }

  {
  eapply dist_trans.
    {
    apply (dist_downward_leq _ _ (S j)); auto.
    apply iutruncate_near.
    }
  eapply dist_trans.
  2:{
    apply dist_symm.
    apply (dist_downward_leq _ _ (S j')); auto.
    apply iutruncate_near.
    }
  apply dist_refl.
  }
Qed.


Definition semiconst_ne {cur} (A : wurel cur) (B : wiurel cur) : urelsp A -n> wiurel_ofe cur
  :=
  expair (semiconst A B) (semiconst_nonexpansive cur A B).


Definition iuarrow (w : ordinal) i (A B : wiurel w) : wiurel w
  :=
  (arrow_urel w i (den A) (den B),
   meta_pair (meta_iurel A) 
     (meta_fn (den A) 
      (nearrow_compose meta_iurel_ne 
         (semiconst_ne (den A) B)))).


Lemma den_iuarrow :
  forall w i A B,
    den (iuarrow w i A B) = arrow_urel w i (den A) (den B).
Proof.
reflexivity.
Qed.


Lemma iuarrow_eq_iupi :
  forall w i A B,
    iuarrow w i A B
    =
    iupi w i A (semiconst_ne (den A) B).
Proof.
intros w i A B.
apply prod_extensionality; auto.
cbn.
apply arrow_urel_eq_pi_urel.
Qed.


Lemma den_iupi_semiconst :
  forall w i A B,
    den (iupi w i A (nearrow_const (urelsp (den A)) (wiurel_ofe w) B))
    =
    den (iupi w i A (semiconst_ne (den A) B)).
Proof.
intros w i A B.
cbn.
apply urel_extensionality.
fextensionality 3.
intros i' m p.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros l l' Hi Hclm Hclp Hsteps Hsteps' Hact.
  exists l, l'.
  do2 5 split; auto.
  intros j n q Hj Hnq.
  cbn.
  split; auto.
  rewrite -> urelsp_index_inj.
  omega.
  }

  {
  intro H.
  decompose H.
  intros l l' Hi Hclm Hclp Hsteps Hsteps' Hact.
  exists l, l'.
  do2 5 split; auto.
  intros j n q Hj Hnq.
  so (Hact j n q Hj Hnq) as H.
  cbn in H.
  destruct H; auto.
  }
Qed.


Lemma iuarrow_inj :
  forall w i i' A A' B B',
    iuarrow w i A B = iuarrow w i' A' B'
    -> A = A'
       /\ (forall j m p, rel (den A) j m p -> iutruncate (S j) B = iutruncate (S j) B').
Proof.
intros w I I' A A' B B' Heq.
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


Lemma iupi_inj :
  forall w I I' A A' B B',
    iupi w I A B = iupi w I' A' B'
    -> eq_dep (wiurel w) (fun r => urelsp (den r) -n> wiurel_ofe w) A B A' B'.
Proof.
intros w I I' A A' B B' Heq.
unfold iupi in Heq.
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


Lemma ceiling_arrow :
  forall n w i A B,
    ceiling (S n) (arrow_urel w i A B)
    =
    arrow_urel w
      (min i n)
      (ceiling (S n) A)
      (ceiling (S n) B).
Proof.
intros i w I A B.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros (Hj, Hact).
  decompose Hact.
  intros r s HIj Hclm Hclp Hsteps Hsteps' Hact.
  exists r, s.
  do2 5 split; auto.
    {
    apply Nat.min_glb; omega.
    }
  intros j' a b Hj' Hab.
  cbn.
  split; [omega |].
  destruct Hab as (Hj'' & Hab).
  apply Hact; auto.
  }

  {
  intro Hact.
  decompose Hact.
  intros r s HIj Hclm Hclp Hsteps Hsteps' Hact.
  so (Nat.min_glb_r _#3 HIj) as Hji.
  split; [omega |].
  exists r, s.
  do2 5 split; auto.
    {
    eapply Nat.min_glb_l; eauto.
    }
  intros j' a b Hj' Hab.
  exploit (Hact j' a b Hj') as H.
    {
    split; auto.
    omega.
    }
  cbn in H.
  destruct H as (_ & H).
  exact H.
  }
Qed.


Lemma ceiling_pi :
  forall n w i A B,
    ceiling (S n) (pi_urel w i A B)
    =
    pi_urel w
      (min i n)
      (ceiling (S n) A)
      (fun C => ceiling (S n) (B (embed_ceiling (S n) A C))).
Proof.
intros i w I A B.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros (Hj, Hact).
  decompose Hact.
  intros r s HIj Hclm Hclp Hsteps Hsteps' Hact.
  exists r, s.
  do2 5 split; auto.
    {
    apply Nat.min_glb; omega.
    }
  intros j' a b Hj' Hab.
  cbn.
  split; [omega |].
  destruct Hab as (Hj'' & Hab).
  rewrite -> embed_ceiling_urelspinj.
  apply Hact; auto.
  }

  {
  intro Hact.
  decompose Hact.
  intros r s HIj Hclm Hclp Hsteps Hsteps' Hact.
  so (Nat.min_glb_r _#3 HIj) as Hji.
  split; [omega |].
  exists r, s.
  do2 5 split; auto.
    {
    eapply Nat.min_glb_l; eauto.
    }
  intros j' a b Hj' Hab.
  assert (j < S i) as Hji' by omega.
  so (Hact j' a b Hj' (conj (le_lt_trans _#3 Hj' Hji') Hab)) as H.
  cbn in H.
  destruct H as (_ & H).
  rewrite -> embed_ceiling_urelspinj in H.
  exact H.
  }
Qed.


Lemma iutruncate_iuarrow :
  forall n w i A B,
    iutruncate (S n) (iuarrow w i A B)
    =
    iuarrow w 
      (min i n)
      (iutruncate (S n) A)
      (iutruncate (S n) B).
Proof.
intros n w i A B.
unfold iuarrow.
unfold iutruncate.
cbn [fst snd].
f_equal.
  {
  apply ceiling_arrow.
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


Lemma iutruncate_iupi :
  forall n w i A B,
    iutruncate (S n) (iupi w i A B)
    =
    iupi w 
      (min i n)
      (iutruncate (S n) A)
      (nearrow_compose
         (nearrow_compose (iutruncate_ne (S n)) B)
         (embed_ceiling_ne (S n) (den A))).
Proof.
intros n w I A B.
assert (S n > 0) as Hpos by omega.
unfold iupi.
unfold iutruncate.
cbn [fst snd].
f_equal.
  {
  apply ceiling_pi.
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


Lemma extend_arrow :
  forall v w (h : v <<= w) I A B,
    extend_urel v w (arrow_urel v I A B)
    =
    arrow_urel w I (extend_urel v w A) (extend_urel v w B).
Proof.
intros v w h I A B.
apply urel_extensionality.
fextensionality 3.
intros i m m'.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros l l' Hi Hcl Hcl' Hstepsl Hstepsl' Hact.
  so (map_steps_form _#5 Hstepsl) as (m'' & Heq & Hstepsn).
  so (map_steps_form _#5 Hstepsl') as (m''' & Heq' & Hstepsn').
  so (map_eq_lam_invert _#5 (eqsymm Heq)) as (n & -> & <-).
  so (map_eq_lam_invert _#5 (eqsymm Heq')) as (n' & -> & <-).
  exists n, n'.
  do2 5 split; eauto using map_hygiene_conv.
  intros j p p' Hj Hp.
  cbn.
  cbn in Hp.
  rewrite -> !map_subst1.
  apply Hact; auto.
  }


  {
  intro H.
  decompose H.
  intros l l' Hi Hcl Hcl' Hstepsl Hstepsl' Hact.
  exists (map_term (extend w v) l), (map_term (extend w v) l').
  do2 5 split; eauto using map_hygiene.
    {
    so (map_steps _ _ (extend w v) _ _ Hstepsl) as H.
    simpmapin H.
    exact H.
    }

    {
    so (map_steps _ _ (extend w v) _ _ Hstepsl') as H.
    simpmapin H.
    exact H.
    }
  intros j p p' Hj Hp.
  assert (rel (extend_urel v w A) j (map_term (extend v w) p) (map_term (extend v w) p')) as Hp'.
    {
    cbn.
    rewrite -> !map_term_inv; auto using extend_inv.
    }
  force_exact (Hact _#3 Hj Hp').
  cbn.
  f_equal.
    {
    simpmap.
    f_equal.
    apply map_term_inv; auto using extend_inv.
    }

    {
    simpmap.
    f_equal.
    apply map_term_inv; auto using extend_inv.
    }
  }
Qed.


Lemma extend_pi :
  forall v w (h : v <<= w) I A B,
    extend_urel v w (pi_urel v I A B)
    =
    pi_urel w I 
      (extend_urel v w A)
      (fun C => extend_urel v w (B (deextend_urelsp h A C))).
Proof.
intros v w h I A B.
apply urel_extensionality.
fextensionality 3.
intros i m m'.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros l l' Hi Hcl Hcl' Hstepsl Hstepsl' Hact.
  so (map_steps_form _#5 Hstepsl) as (m'' & Heq & Hstepsn).
  so (map_steps_form _#5 Hstepsl') as (m''' & Heq' & Hstepsn').
  so (map_eq_lam_invert _#5 (eqsymm Heq)) as (n & -> & <-).
  so (map_eq_lam_invert _#5 (eqsymm Heq')) as (n' & -> & <-).
  exists n, n'.
  do2 5 split; eauto using map_hygiene_conv.
  intros j p p' Hj Hp.
  cbn.
  cbn in Hp.
  rewrite -> deextend_urelsp_urelspinj.
  rewrite -> !map_subst1.
  apply Hact; auto.
  }

  {
  intro H.
  decompose H.
  intros l l' Hi Hcl Hcl' Hstepsl Hstepsl' Hact.
  exists (map_term (extend w v) l), (map_term (extend w v) l').
  do2 5 split; eauto using map_hygiene.
    {
    so (map_steps _ _ (extend w v) _ _ Hstepsl) as H.
    simpmapin H.
    exact H.
    }

    {
    so (map_steps _ _ (extend w v) _ _ Hstepsl') as H.
    simpmapin H.
    exact H.
    }
  intros j p p' Hj Hp.
  assert (rel (extend_urel v w A) j (map_term (extend v w) p) (map_term (extend v w) p')) as Hp'.
    {
    cbn.
    rewrite -> !map_term_inv; auto using extend_inv.
    }
  force_exact (Hact _#3 Hj Hp').
  cbn.
  f_equal.
    {
    rewrite -> deextend_urelsp_urelspinj.
    f_equal.
    apply urelspinj_equal.
    rewrite -> map_term_inv; auto using extend_inv.
    }

    {
    simpmap.
    f_equal.
    apply map_term_inv; auto using extend_inv.
    }

    {
    simpmap.
    f_equal.
    apply map_term_inv; auto using extend_inv.
    }
  }
Qed.


Lemma extend_iuarrow :
  forall v w (h : v <<= w) I A B,
    extend_iurel h (iuarrow v I A B)
    =
    iuarrow w I (extend_iurel h A) (extend_iurel h B).
Proof.
intros v w h I A B.
unfold iuarrow, extend_iurel.
cbn.
f_equal.
  {
  apply (extend_arrow v w h).
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


Lemma extend_iupi :
  forall v w (h : v <<= w) I A B,
    extend_iurel h (iupi v I A B)
    =
    iupi w I (extend_iurel h A)
      (nearrow_compose
         (nearrow_compose (extend_iurel_ne h) B)
         (deextend_urelsp_ne h (den A))).
Proof.
intros v w h I A B.
unfold iupi, extend_iurel.
cbn.
f_equal.
  {
  apply (extend_pi v w h).
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


Lemma pi_action_app :
  forall w I A (B : urelsp_car A -> wurel w) i m n j p q (h : rel A j p q),
    j <= i
    -> pi_action w I A B i m n
    -> rel (B (urelspinj A j p q h)) j (app m p) (app n q).
Proof.
intros w I A B i m n j p q Hpq Hj Hmn.
decompose Hmn.
intros m1 n1 _ Hclm Hcln Hstepsm Hstepsn Hact.
so (urel_closed _#5 Hpq) as (Hclp & Hclq).
apply (urel_equiv _#3 (subst1 p m1) _ (subst1 q n1)).
  {
  apply hygiene_auto; cbn; auto.
  }

  {
  apply hygiene_auto; cbn; auto.
  }

  {
  apply equiv_symm.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
    }
  apply star_one.
  apply step_app2.
  }

  {
  apply equiv_symm.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
    }
  apply star_one.
  apply step_app2.
  }
apply Hact; auto.
Qed.


Lemma arrow_action_app :
  forall w I A B i m n p q,
    arrow_action w I A B i m n
    -> rel A i p q
    -> rel B i (app m p) (app n q).
Proof.
intros w I A B i m n p q Hmn Hpq.
decompose Hmn.
intros l l' _ Hclm Hcln Hsteps Hsteps' Hact.
so (urel_closed _#5 Hpq) as (Hclp & Hclq).
so (Hact i p q (le_refl _) Hpq) as H.
eapply urel_equiv; eauto; clear H.
  {
  apply hygiene_auto; cbn; auto.
  }

  {
  apply hygiene_auto; cbn; auto.
  }

  {
  apply equiv_symm.
  eapply equiv_trans.
    {
    apply equiv_app.
      {
      apply steps_equiv; eauto.
      }

      {
      apply equiv_refl.
      }
    }
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app2.
    }
  apply star_refl.
  }

  {
  apply equiv_symm.
  eapply equiv_trans.
    {
    apply equiv_app.
      {
      apply steps_equiv; eauto.
      }

      {
      apply equiv_refl.
      }
    }
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app2.
    }
  apply star_refl.
  }
Qed.


Lemma arrow_action_lam :
  forall w i A B i' m n,
    i' <= i
    -> hygiene clo (lam m)
    -> hygiene clo (lam n)
    -> (forall j p q,
          j <= i'
          -> rel A j p q
          -> rel B j (subst1 p m) (subst1 q n))
    -> arrow_action w i A B i' (lam m) (lam n).
Proof.
intros w I A B i m n Hi Hclm Hcln Hact.
exists m, n.
do2 5 split; auto using star_refl.
Qed.


Lemma arrow_action_lam' :
  forall w i A B i' m n l l',
    i' <= i
    -> hygiene clo m 
    -> hygiene clo n
    -> star step m (lam l)
    -> star step n (lam l')
    -> (forall j p q,
          j <= i'
          -> rel A j p q
          -> rel B j (app m p) (app n q))
    -> arrow_action w i A B i' m n.
Proof.
intros w i A B i' m n l l' Hi Hclm Hcln Hl Hl' Hact.
exists l, l'.
do2 5 split; auto using star_refl.
intros j p q Hj Hpq.
so (urel_closed _#5 Hpq) as (Hclp & Hclq).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hl Hclm)) as H; cbn in H.
destruct H as (Hcll & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hl' Hcln)) as H; cbn in H.
destruct H as (Hcll' & _).
refine (urel_equiv _#7 _ _ _ _ (Hact _#3 Hj Hpq)); eauto using hygiene_subst1.
  {
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ (fun z => app z _)); auto using step_app1.
    eauto.
    }
  apply star_one; apply step_app2.
  }

  {
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ (fun z => app z _)); auto using step_app1.
    eauto.
    }
  apply star_one; apply step_app2.
  }
Qed.


Lemma arrow_action_lam1 :
  forall w I A B i m r n,
    hygiene clo (lam m)
    -> arrow_action w I A B i r n
    -> (forall j p q,
          j <= i
          -> rel A j p q
          -> rel B j (subst1 p m) (app n q))
    -> arrow_action w I A B i (lam m) n.
Proof.
intros w I A B i m r n Hclm Hrn Hact.
decompose Hrn.
intros _ l Hi _ Hcln _ Hsteps _.
exists m, l.
do2 5 split; auto using star_refl.
intros j p q Hj Hpq.
so (urel_closed _#5 Hpq) as (_ & Hclq).
so (Hact _#3 Hj Hpq) as Hrel.
eapply urel_equiv_2; eauto.
  {
  apply hygiene_subst1; auto.
  so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hsteps Hcln)) as H; cbn in H.
  destruct H; auto.
  }

  {
  eapply equiv_trans.
    {
    apply equiv_app; [| apply equiv_refl].
    apply steps_equiv; eauto.
    }
  apply steps_equiv.
  apply star_one.
  apply step_app2.
  }
Qed.


Definition intersect_action
  (w : ordinal) i (A : wurel w) (B : urelsp_car A -> wurel w)
  : nat -> relation (wterm w)
  :=
  fun i' m m' =>
    i' <= i
    /\ hygiene clo m
    /\ hygiene clo m'
    /\ forall j n n',
         j <= i'
         -> forall (Hn : rel A j n n'),
              rel (B (urelspinj A j n n' Hn)) j m m'.


Lemma intersect_uniform :
  forall w i A B, uniform _ (intersect_action w i A B).
Proof.
intros w i A B.
do2 3 split.

(* closed *)
{
intros i' m p Hmp.
decompose Hmp; auto.
}

(* equiv *)
{
intros i' m m' p p' Hclm' Hclp' Hequivm Hequivp Hact.
decompose Hact.
intros Hi _ _ Hact.
do2 3 split; auto.
intros j n q Hj Hnq.
eapply urel_equiv; eauto.
}

(* zigzag *)
{
intros i' m p n q Hmp Hnp Hnq.
decompose Hmp.
intros Hi' Hclm _ Hmp.
decompose Hnp.
intros _ _ _ Hnp.
decompose Hnq.
intros _ _ Hclq Hnq.
do2 3 split; auto.
intros j r t Hj Hrt.
apply (urel_zigzag _#3 m p n q); auto.
}

(* downward *)
{
intros i' m p Hact.
decompose Hact.
intros Hi' Hclm Hclp Hact.
do2 3 split; auto.       
omega.
}
Qed.


Definition intersect_urel w i A B :=
  mk_urel (intersect_action w i A B) (intersect_uniform w i A B).


Lemma ceiling_intersect :
  forall n w i A B,
    ceiling (S n) (intersect_urel w i A B)
    =
    intersect_urel w
      (min i n)
      (ceiling (S n) A)
      (fun C => ceiling (S n) (B (embed_ceiling (S n) A C))).
Proof.
intros n w i A B.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros (Hjn & Hmp).
  decompose Hmp.
  intros Hj Hclm Hclp Hact.
  do2 3 split; auto.
    {
    apply Nat.min_glb; omega.
    }
  intros k r t Hk Hrt.
  split; [omega |].
  destruct Hrt as (Hkn & Hrt).
  rewrite -> embed_ceiling_urelspinj.
  apply Hact; auto.
  }

  {
  intros Hmp.
  decompose Hmp.
  intros Hj Hclm Hclp Hact.
  so (Nat.le_min_r i n) as Hminl.
  so (Nat.le_min_l i n) as Hminr.
  split; [omega |].
  do2 3 split; auto; try omega.
  intros k r t Hk Hrt.
  assert (k < S n) as Hkn by omega.
  so (Hact k r t Hk (conj Hkn Hrt)) as H.
  rewrite -> embed_ceiling_urelspinj in H.
  destruct H; auto.
  }
Qed.
    


Lemma extend_intersect :
  forall v w (h : v <<= w) i A B,
    extend_urel v w (intersect_urel v i A B)
    =
    intersect_urel w i 
      (extend_urel v w A)
      (fun C => extend_urel v w (B (deextend_urelsp h A C))).
Proof.
intros v w h i A B.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros Hj Hclm Hclp Hact.
  do2 3 split; eauto using map_hygiene_conv.
  intros k r t Hk Hrt.
  rewrite -> deextend_urelsp_urelspinj.
  cbn.
  apply Hact; auto.
  }

  {
  intro H.
  decompose H.
  intros Hj Hclm Hclp Hact.
  do2 3 split; auto using map_hygiene.
  intros k r t Hk Hrt.
  assert (rel (extend_urel v w A) k (map_term (extend v w) r) (map_term (extend v w) t)) as Hrt'.
    {
    cbn.
    rewrite -> !extend_term_cancel; auto.
    }
  force_exact (Hact _#3 Hk Hrt').
  cbn.
  f_equal.
  rewrite -> deextend_urelsp_urelspinj.
  f_equal.
  apply urelspinj_equal.
  rewrite -> extend_term_cancel; auto.
  }
Qed.


Definition iuintersect (w : ordinal) i (A : wiurel w) (B : urelsp (den A) -n> wiurel_ofe w) : wiurel w
  :=
  (intersect_urel w i (den A) (fun C => den (pi1 B C)),
   meta_pair (meta_iurel A) 
     (meta_fn (den A) 
      (nearrow_compose meta_iurel_ne B))).



Lemma iutruncate_iuintersect :
  forall n w i A B,
    iutruncate (S n) (iuintersect w i A B)
    =
    iuintersect w 
      (min i n)
      (iutruncate (S n) A)
      (nearrow_compose
         (nearrow_compose (iutruncate_ne (S n)) B)
         (embed_ceiling_ne (S n) (den A))).
Proof.
intros n w I A B.
assert (S n > 0) as Hpos by omega.
unfold iuintersect.
unfold iutruncate.
cbn [fst snd].
f_equal.
  {
  apply ceiling_intersect.
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


Lemma extend_iuintersect :
  forall v w (h : v <<= w) I A B,
    extend_iurel h (iuintersect v I A B)
    =
    iuintersect w I (extend_iurel h A)
      (nearrow_compose
         (nearrow_compose (extend_iurel_ne h) B)
         (deextend_urelsp_ne h (den A))).
Proof.
intros v w h I A B.
unfold iuintersect, extend_iurel.
cbn.
f_equal.
  {
  apply (extend_intersect v w h).
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


Lemma iuintersect_inj :
  forall w I I' A A' B B',
    iuintersect w I A B = iuintersect w I' A' B'
    -> eq_dep (wiurel w) (fun r => urelsp (den r) -n> wiurel_ofe w) A B A' B'.
Proof.
intros w I I' A A' B B' Heq.
unfold iuintersect in Heq.
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
