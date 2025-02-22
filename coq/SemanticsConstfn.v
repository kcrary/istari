
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


Definition constfn_action (w : ordinal) i : nat -> relation (wterm w)
  :=
  fun i' m m' =>
    exists l l',
      i' <= i
      /\ hygiene clo m
      /\ hygiene clo m'
      /\ equiv m (lam l)
      /\ equiv m' (lam l')
      /\ hygiene clo l
      /\ hygiene clo l'.


Lemma constfn_uniform :
  forall w i, uniform _ (constfn_action w i).
Proof.
intros w i.
do2 3 split.

(* closed *)
{
intros i' m n H.
decompose H.
auto.
}

(* equiv *)
{
intros i' m m' n n' Hclm' Hcln' Hequivm Hequivn Hact.
decompose Hact.
intros p q Hi _ _ Hequivp Hequivq Hclp Hclq.
exists p, q.
do2 6 split; eauto using equiv_trans, equiv_symm.
}

(* zigzag *)
{
intros i' m p n q Hmn _ Hpq.
decompose Hmn.
intros m' _ Hi Hclm _ Hm _ Hclm' _.
decompose Hpq.
intros _ q' _ _ Hclq _ Hq _ Hclq'.
exists m', q'.
do2 6 split; auto.
}

(* downward *)
{
intros i' m n Hmn.
decompose Hmn.
intros m' n' Hi Hclm Hcln Hm Hn Hclm' Hcln'.
exists m', n'.
do2 6 split; auto.
omega.
}
Qed.


Definition constfn_urel w i :=
  mk_urel (constfn_action w i) (constfn_uniform w i).


Lemma ceiling_constfn :
  forall n w i,
    ceiling (S n) (constfn_urel w i) = constfn_urel w (min i n).
Proof.
intros n w i.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros (Hjn & Hact).
  decompose Hact.
  intros m' p' Hji Hclm Hclp Hequivm Hequivp Hclm' Hclp'.
  exists m', p'.
  do2 6 split; auto.
  apply Nat.min_glb; omega.
  }

  {
  intros Hact.
  decompose Hact.
  intros m' p' Hj Hclm Hclp Hequivm Hequivp Hclm' Hclp'.
  split.
    {
    so (Nat.min_glb_r _#3 Hj); omega.
    }
  exists m', p'.
  do2 6 split; auto.
  so (Nat.min_glb_l _#3 Hj); omega.
  }
Qed.


Lemma extend_constfn :
  forall v w i (h : v <<= w),
    extend_urel v w (constfn_urel v i)
    =
    constfn_urel w i.
Proof.
intros v w i h.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros n q Hj Hclm Hclp Hequivm Hequivp Hcln Hclq.
  so (church_rosser _ _ _ Hequivm) as (x & Hemr & Hlnlr).
  so (reduces_lam_form _ _ _ Hlnlr) as (r & -> & Hnr).
  so (map_reduces_form _ _ _ _ _ Hemr) as (r' & Heqr & Hmr).
  so (map_eq_lam_invert _#5 (eqsymm Heqr)) as (r'' & -> & <-).
  so (church_rosser _ _ _ Hequivp) as (x & Hept & Hlqlt).
  so (reduces_lam_form _ _ _ Hlqlt) as (t & -> & Hqt).
  so (map_reduces_form _ _ _ _ _ Hept) as (t' & Heqt & Hpt).
  so (map_eq_lam_invert _#5 (eqsymm Heqt)) as (t'' & -> & <-).
  exists r'', t''.
  do2 6 split; auto.
    {
    eapply map_hygiene_conv; eauto.
    }

    {
    eapply map_hygiene_conv; eauto.
    }

    {
    apply reduces_equiv; auto.
    }

    {
    apply reduces_equiv; auto.
    }

    {
    apply (map_hygiene_conv _ _ (extend w v)).
    eapply reduces_hygiene; eauto.
    }

    {
    apply (map_hygiene_conv _ _ (extend w v)).
    eapply reduces_hygiene; eauto.
    }
  }

  {
  intro H.
  decompose H.
  intros n q Hj Hclm Hclp Hequivm Hequivp Hcln Hclq.
  exists (map_term (extend w v) n), (map_term (extend w v) q).
  do2 6 split; auto.
    {
    apply map_hygiene; auto.
    }

    {
    apply map_hygiene; auto.
    }

    {
    so (map_equiv _ _ (extend w v) _ _ Hequivm) as H.
    simpmapin H.
    exact H.
    }

    {
    so (map_equiv _ _ (extend w v) _ _ Hequivp) as H.
    simpmapin H.
    exact H.
    }

    {
    apply map_hygiene; auto.
    }

    {
    apply map_hygiene; auto.
    }
  }
Qed.
