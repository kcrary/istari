
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


Hint Rewrite def_istp : prepare.


Lemma istpForm_valid : istpForm_obligation.
Proof.
prepare.
intros G a ext0 H.
apply tr_eqtype_formation; auto.
Qed.


Lemma istpEq_valid : istpEq_obligation.
Proof.
prepare.
intros G a b ext0 H.
apply tr_eqtype_formation; auto.
Qed.


Lemma istpFormUniv_valid : istpFormUniv_obligation.
Proof.
prepare.
intros G a i ext0 H.
apply tr_eqtype_formation_univ; auto.
Qed.


Lemma istpEqUniv_valid : istpEqUniv_obligation.
Proof.
prepare.
intros G a b i ext0 H.
apply tr_eqtype_formation_univ; auto.
Qed.


Lemma istpIntro_valid : istpIntro_obligation.
Proof.
prepare.
intros G a ext0 H.
auto.
Qed.


Lemma istpElim_valid : istpElim_obligation.
Proof.
prepare.
intros G a p ext0 H.
auto.
Qed.


Lemma istpExt_valid : istpExt_obligation.
Proof.
unfoldtop.
intros G a p q ext1 ext0 Hp Hq.
unfold Defs.dof, Defs.triv in * |- *.
rewrite -> def_of in * |- *.
rewrite -> def_istp in * |- *.
rewrite -> def_eq in * |- *.
apply tr_equal_intro.
apply (tr_transitivity _ _ triv).
  {
  apply tr_eqtype_eta; auto.
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  apply tr_symmetry.
  apply tr_eqtype_eta; auto.
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma istpLeft_valid : istpLeft_obligation.
Proof.
prepare.
intros G1 G2 a b m H.
unfold Defs.triv in H.
apply tr_eqtype_eta_hyp; auto.
Qed.


Lemma inhabitedForm_valid : inhabitedForm_obligation.
Proof.
prepare.
intros G a ext0 H.
eapply tr_inhabitation_formation; eauto.
Qed.
