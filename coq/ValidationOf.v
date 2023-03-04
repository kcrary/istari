
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


Lemma ofForm_valid : ofForm_obligation.
Proof.
prepare.
intros G a m ext0 H.
eapply tr_equal_formation; eauto.
eapply tr_inhabitation_formation; eauto.
Qed.


Lemma ofEq_valid : ofEq_obligation.
Proof.
prepare.
intros G a b m n ext1 ext0 Hab Hmn.
eapply tr_equal_formation; eauto.
Qed.


Lemma ofFormUniv_valid : ofFormUniv_obligation.
Proof.
prepare.
intros G a i m ext1 ext0 Ha Hm.
apply tr_equal_formation_univ; eauto.
Qed.


Lemma ofEqUniv_valid : ofEqUniv_obligation.
Proof.
prepare.
intros G a b i m n ext1 ext0 Hab Hmn.
apply tr_equal_formation_univ; eauto.
Qed.


Lemma ofIntro_valid : ofIntro_obligation.
Proof.
prepare.
intros G a m ext0 H.
auto.
Qed.


Lemma ofElim_valid : ofElim_obligation.
Proof.
prepare.
intros G a m p ext0 H.
auto.
Qed.


Lemma ofTrivialize_valid : ofTrivialize_obligation.
Proof.
prepare.
intros G a m ext0 H.
auto.
Qed.


Lemma ofExt_valid : ofExt_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a m p q ext1 ext0 Hp Hq.
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


Lemma ofLeft_valid : ofLeft_obligation.
Proof.
prepare.
intros G1 G2 a b p m H.
apply tr_equal_eta_hyp; auto.
Qed.


Lemma ofEquand1_valid : ofEquand1_obligation.
Proof.
prepare.
intros G a m n ext0 H.
apply (tr_transitivity _ _ n); auto.
apply tr_symmetry; auto.
Qed.


Lemma ofEquand2_valid : ofEquand2_obligation.
Proof.
prepare.
intros G a m n ext0 H.
apply (tr_transitivity _ _ m); auto.
apply tr_symmetry; auto.
Qed.
