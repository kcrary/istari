
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Tactics.
Require Import Sequence.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.
Require Import Promote.
Require Import Hygiene.
Require Import Rules.
Require Import DerivedRules.
Require Defs.
Require Import Obligations.
Require Import Morphism.
Require Import DefsEquiv.
Require Import Equivalence.
Require Import Dots.

Require Import ValidationUtil.


Hint Rewrite def_eq : prepare.


Lemma eqForm_valid : eqForm_obligation.
Proof.
prepare.
intros G a m p ext1 ext0 Hm Hp.
apply tr_equal_formation; auto.
eapply tr_inhabitation_formation; eauto.
Qed.


Lemma eqEq_valid : eqEq_obligation.
Proof.
prepare.
intros G a b m n p q ext2 ext1 ext0 Hab Hmn Hpq.
apply tr_equal_formation; auto.
Qed.


Lemma eqFormUniv_valid : eqFormUniv_obligation.
Proof.
prepare.
intros G a i m p ext2 ext1 ext0 Ha Hm Hp.
apply tr_equal_formation_univ; auto.
Qed.


Lemma eqEqUniv_valid : eqEqUniv_obligation.
Proof.
prepare.
intros G a b i m n p q ext2 ext1 ext0 Hab Hmn Hpq.
apply tr_equal_formation_univ; eauto.
Qed.


Lemma eqIntro_valid : eqIntro_obligation.
Proof.
prepare.
intros G a m n ext0 H.
auto.
Qed.


Lemma eqElim_valid : eqElim_obligation.
Proof.
prepare.
intros G a m n p ext0 H.
auto.
Qed.


Lemma eqTrivialize_valid : eqTrivialize_obligation.
Proof.
prepare.
intros G a m n ext0 H.
auto.
Qed.


Lemma eqExt_valid : eqExt_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a m n p q ext1 ext0 H H0.
autorewrite with prepare in * |- *.
unfold Defs.triv.
apply tr_equal_intro.
apply (tr_transitivity _ _ triv).
  {
  apply tr_equal_eta.
  apply tr_equal_elim; auto.
  eapply tr_equal_eta2; eauto.
  }

  {
  apply tr_symmetry.
  apply tr_equal_eta.
  apply tr_equal_elim; auto.
  eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma eqLeft_valid : eqLeft_obligation.
Proof.
prepare.
intros G1 G2 a b p q m H.
apply tr_equal_eta_hyp.
exact H.
Qed.


Lemma eqRefl_valid : eqRefl_obligation.
Proof.
prepare.
intros G a m ext0 H.
auto.
Qed.


Lemma eqSymm_valid : eqSymm_obligation.
Proof.
prepare.
intros G a m n ext0 H.
apply tr_symmetry; auto.
Qed.


Lemma eqTrans_valid : eqTrans_obligation.
Proof.
prepare.
intros G a m n p ext1 ext0 Hmn Hnp.
eapply tr_transitivity; eauto.
Qed.


Lemma eqFormInv1_valid : eqFormInv1_obligation.
Proof.
prepare.
intros G a m n ext0 H.
eapply tr_equal_formation_invert1; eauto.
Qed.


Lemma eqFormInv2_valid : eqFormInv2_obligation.
Proof.
prepare.
intros G a m n ext0 H.
eapply tr_equal_formation_invert2; eauto.
Qed.


Lemma eqFormInv3_valid : eqFormInv3_obligation.
Proof.
prepare.
intros G a m n ext0 H.
eapply tr_equal_formation_invert3; eauto.
Qed.
