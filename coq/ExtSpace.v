
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
Require Import Intensional.
Require Import Ordinal.
Require Import Candidate.
Require Import System.
Require Import MapTerm.
Require Import Extend.
Require Import Model.
Require Import Standard.
Require Import Truncate.
Require Import Equivalences.
Require Import Ceiling.
Require Import Page.
Require Import Urelsp.


Definition ext_action (w u : ordinal) (hu : u << w) (i : nat) : nat -> relation (wterm w)
  :=
  fun j m m' =>
    j <= i
    /\ exists Q Q' (h : level (pi1 Q) <<= u) (h' : level (pi1 Q') <<= u),
         hygiene clo m
         /\ hygiene clo m'
         /\ star step m (ext (objin (objsome Q (le_lt_ord_trans _#3 h hu))))
         /\ star step m' (ext (objin (objsome Q' (le_lt_ord_trans _#3 h' hu))))
         /\ projc j Q = projc j Q'.


Definition ext_uniform :
  forall w u hu i, uniform _ (ext_action w u hu i).
Proof.
intros w u hu i.
do2 3 split.

(* closed *)
{
intros j m n H.
decompose H; auto.
}

(* equiv *)
{
intros j m m' n n' Hclm Hcln Hm Hn H.
destruct H as (Hj & Q & Q' & h & h' & _ & _ & Hstepsm & Hstepsn & Heq).
split; auto.
exists Q, Q', h, h'.
do2 4 split; auto.
  {
  so (equiv_eval _#4 Hm (conj Hstepsm value_ext)) as (x & (Hstepsm' & _) & Hmc).
  invertc_mc Hmc.
  intros <-.
  exact Hstepsm'.
  }

  {
  so (equiv_eval _#4 Hn (conj Hstepsn value_ext)) as (x & (Hstepsn' & _) & Hmc).
  invertc_mc Hmc.
  intros <-.
  exact Hstepsn'.
  }
}

(* zigzag *)
{
intros j m n p q Hmn Hpn Hpq.
destruct Hmn as (Hj & Q1 & Q2 & h1 & h2 & Hclm & _ & Hstepsm & Hstepsn & Heq12).
destruct Hpn as (_ & Q3 & Q2' & h3 & h2' & _ & _ & Hstepsp & Hstepsn' & Heq32).
destruct Hpq as (_ & Q3' & Q4 & h3' & h4 & _ & Hclq & Hstepsp' & Hstepsq & Heq34).
so (determinism_eval _#4 (conj Hstepsn value_ext) (conj Hstepsn' value_ext)) as H.
injectionc H.
intros H.
so (objin_inj _ _ _ H) as H'.
injection H'.
intros <-.
clear H H'.
so (determinism_eval _#4 (conj Hstepsp value_ext) (conj Hstepsp' value_ext)) as H.
injectionc H.
intros H.
so (objin_inj _ _ _ H) as H'.
injection H'.
intros <-.
clear H H'.
split; auto.
exists Q1, Q4, h1, h4.
do2 4 split; auto.
exact (eqtrans Heq12 (eqtrans (eqsymm Heq32) Heq34)).
}

(* downward *)
{
intros j m n H.
destruct H as (Hj & Q & Q' & h & h' & Hclm & Hcln & Hstepsm & Hstepsn & Heq).
split.
  {
  omega.
  }
exists Q, Q', h, h'.
do2 4 split; auto.
so (f_equal (projc j) Heq) as Heq'.
rewrite -> !projc_combine_le in Heq'; auto.
}
Qed.


Definition ext_urel w u huw i :=
  mk_urel (ext_action w u huw i) (ext_uniform w u huw i).


Lemma rel_ext_intro :
  forall w u i j Q Q' h h' (hu : u << w),
    level (pi1 Q) <<= u
    -> level (pi1 Q') <<= u
    -> j <= i
    -> projc j Q = projc j Q'
    -> rel (ext_urel w u hu i) j (ext (objin (objsome Q h))) (ext (objin (objsome Q' h'))).
Proof.
intros w u i j Q Q' h h' Huw Hlev Hlev' Hj Heq.
cbn.
split; auto.
exists Q, Q', Hlev, Hlev'.
so (proof_irrelevance _ h (le_lt_ord_trans _#3 Hlev Huw)); subst h.
so (proof_irrelevance _ h' (le_lt_ord_trans _#3 Hlev' Huw)); subst h'.
do2 4 split; auto using star_refl.
  {
  apply hygiene_auto; cbn; auto.
  }

  {
  apply hygiene_auto; cbn; auto.
  }
Qed.


Lemma rel_ext_refl :
  forall w u (hu : u << w) i j Q h,
    level (pi1 Q) <<= u
    -> j <= i
    -> rel (ext_urel w u hu i) j (ext (objin (objsome Q h))) (ext (objin (objsome Q h))).
Proof.
intros w u hu i j Q h Hlev Hj.
apply rel_ext_intro; auto.
Qed.


Lemma rel_ext_invert :
  forall w u (hu : u << w) i j Q Q' h h',
    rel (ext_urel w u hu i) j (ext (objin (objsome Q h))) (ext (objin (objsome Q' h')))
    -> projc j Q = projc j Q'.
Proof.
intros w u hu i j Q1 Q2 h1 h2 H.
destruct H as (Hj & Q1' & Q2' & h1' & h2' & _ & _ & Hsteps1 & Hsteps2 & Heq).
so (determinism_normal_value _#3 value_ext Hsteps1) as H.
injectionc H.
intros H.
so (objin_inj _ _ _ H) as H'.
injection H'.
intros <-.
clear H H'.
so (determinism_normal_value _#3 value_ext Hsteps2) as H.
injectionc H.
intros H.
so (objin_inj _ _ _ H) as H'.
injection H'.
intros <-.
clear H H'.
exact Heq.
Qed.


Lemma ceiling_ext_urel :
  forall w u hu i j,
    ceiling (S i) (ext_urel w u hu j) = ext_urel w u hu (min i j).
Proof.
intros w u hu i j.
apply urel_extensionality.
fextensionality 3.
intros k m p.
cbn.
pextensionality.
  {
  intros (Hki & H).
  destruct H as (Hkj & H).
  split; auto.
  apply Nat.min_glb; omega.
  }

  {
  intros (Hk & H).
  do2 2 split; auto.
    {
    so (Nat.min_glb_l _#3 Hk).
    omega.
    }

    {
    exact (Nat.min_glb_r _#3 Hk).
    }
  }
Qed.

       

Lemma extend_ext_urel :
  forall v w u hu i (hvw : v <<= w),
    extend_urel v w (ext_urel v u hu i) = ext_urel w u (lt_le_ord_trans _#3 hu hvw) i.
Proof.
intros v w u hu i Hvw.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intro H.
  destruct H as (Hj & Q & Q' & h & h' & Hclm & Hclp & Hstepsm & Hstepsp & Heq).
  split; auto.
  exists Q, Q', h, h'.
  do2 4 split; eauto using map_hygiene_conv.
    {
    so (map_steps_form _#5 Hstepsm) as (m' & Heqm & Hsteps).
    so (map_eq_ext_invert _#5 (eqsymm Heqm)) as (x & -> & Heqx).
    so (extend_eq_objsome_form _#5 Heqx) as (h'' & ->).
    so (proof_irrelevance _ h'' (le_lt_ord_trans _#3 h (lt_le_ord_trans _#3 hu Hvw))); subst h''.
    exact Hsteps.
    }

    {
    so (map_steps_form _#5 Hstepsp) as (m' & Heqm & Hsteps).
    so (map_eq_ext_invert _#5 (eqsymm Heqm)) as (x & -> & Heqx).
    so (extend_eq_objsome_form _#5 Heqx) as (h'' & ->).
    so (proof_irrelevance _ h'' (le_lt_ord_trans _#3 h' (lt_le_ord_trans _#3 hu Hvw))); subst h''.
    exact Hsteps.
    }
  }

  {
  intro H.
  destruct H as (Hj & Q & Q' & h & h' & Hclm & Hclp & Hstepsm & Hstepsp & Heq).
  split; auto.
  exists Q, Q', h, h'.
  do2 4 split; auto using map_hygiene.
    {
    so (map_steps _ _ (extend w v) _ _ Hstepsm) as Hsteps.
    simpmapin Hsteps.
    rewrite -> (extend_some _#4 (le_lt_ord_trans _#3 h hu)) in Hsteps.
    exact Hsteps.
    }

    {
    so (map_steps _ _ (extend w v) _ _ Hstepsp) as Hsteps.
    simpmapin Hsteps.
    rewrite -> (extend_some _#4 (le_lt_ord_trans _#3 h' hu)) in Hsteps.
    exact Hsteps.
    }
  }
Qed.


Definition meta_ext {w : ordinal} u (hu : u << w) i (Q : candidate) (h : level (pi1 Q) <<= u) : meta (obj w)
  :=
  meta_term (ext_urel w u hu i) (urelspinj (ext_urel w u hu i) i _ _ (rel_ext_refl w u hu i i Q (le_lt_ord_trans _#3 h hu) h (le_refl _))).


Lemma meta_ext_inj :
  forall w u hu i Q Q' h h',
    @meta_ext w u hu i Q h = @meta_ext w u hu i Q' h'
    -> projc i Q = projc i Q'.
Proof.
intros w u hu i Q Q' h h' Heqmeta.
unfold meta_ext in Heqmeta.
so (meta_term_inj _#5 Heqmeta) as Heq.
injectionT Heq.
intros Heq.
so (urelspinj_equal_invert _#10 Heq) as (_ & Hrel).
exact (rel_ext_invert _#9 Hrel).
Qed.


Lemma meta_truncate_ext :
  forall cur u (hu : u << cur) n i Q (h : level (pi1 Q) <<= u) (h' : level (approx n (pi1 Q)) <<= u),
    meta_truncate (S n) (meta_ext u hu i Q h)
    =
    meta_ext u hu (min n i) (projc n Q) h'.
Proof.
intros cur u hu  n i Q h h'.
unfold meta_ext.
assert (S n > 0) as Hpos by omega.
rewrite -> (meta_truncate_term _#4 Hpos).
apply f_equal_dep.
apply (eq_impl_eq_dep _#6 (ceiling_ext_urel cur u hu n i)).
set (h'' := le_lt_ord_trans _#3 h hu).
assert (rel (ceiling (S n) (ext_urel cur u hu i)) (min i n) (ext (objin (objsome Q h''))) (ext (objin (objsome Q h'')))) as Hrel.
  {
  cbn.
  split.
    {
    apply Nat.min_lt_iff.
    right; omega.
    }
  apply rel_ext_refl; auto.
  apply Nat.le_min_l.
  }
rewrite -> (proj_ceiling_urelspinj _#8 Hrel).
so (rel_ext_refl cur u hu (min i n) (min i n) Q (le_lt_ord_trans _#3 h hu) h (le_refl _)) as Hrel'.
rewrite -> Nat.min_comm in Hrel' at 1.
rewrite -> (transport_urelspinj _#3 (ceiling_ext_urel cur u hu n i) _#4 Hrel').
apply urelspinj_equal'.
  {
  apply Nat.min_comm.
  }
apply rel_ext_intro; auto.
  {
  rewrite -> Nat.min_comm.
  apply le_refl.
  }
rewrite -> projc_combine_le; auto.
apply Nat.le_min_r.
Qed.


Lemma extend_meta_ext :
  forall v w (h : v <<= w) u (hu : u << v) i Q (lev : level (pi1 Q) <<= u),
    extend_meta h (meta_ext u hu i Q lev)
    =
    meta_ext u (lt_le_ord_trans _#3 hu h) i Q lev.
Proof.
intros v w hvw u huv i Q lev.
unfold meta_ext.
rewrite -> extend_meta_term.
apply f_equal_dep.
apply (eq_impl_eq_dep _#6 (extend_ext_urel v w u huv i hvw)).
set (lev' := le_lt_ord_trans _#3 lev (lt_le_ord_trans _#3 huv hvw)).
erewrite -> extend_urelspinj.
Unshelve.
2:{
  unfold extend_urel.
  cbn [rel].
  rewrite -> !extend_term_cancel; auto.
  apply rel_ext_refl; auto.
  }
erewrite -> (transport_urelspinj _ _ _ (extend_ext_urel v w u huv i hvw)).
Unshelve.
2:{
  simpmap.
  erewrite -> (extend_some _#4 lev').
  apply rel_ext_refl; auto.
  }
apply urelspinj_equal.
simpmap.
erewrite -> (extend_some _#4 lev').
apply rel_ext_refl; auto.
Qed.
