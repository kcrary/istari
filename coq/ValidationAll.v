
Require Import Coq.Lists.List.
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

Require Import ValidationUtil.
Require Import NatLemmas.


Hint Rewrite def_iforall def_kind def_lleq : prepare.



Lemma iforallForm_valid : iforallForm_obligation.
Proof.
prepare.
intros G a i k ext1 ext0 Hk Ha.
apply tr_all_formation; auto.
Qed.



Lemma iforallEq_valid : iforallEq_obligation.
Proof.
prepare.
intros G a b i k l ext1 ext0 Hkl Hab.
apply tr_all_formation; auto.
Qed.



Lemma iforallFormUniv_valid : iforallFormUniv_obligation.
Proof.
prepare.
intros G a i j k ext3 ext2 ext1 ext0 Hk Hj Hleq Ha.
apply tr_all_formation_univ; auto.
unfold Defined.leqpagetp.
eapply tr_leqtp_eta2; eauto.
apply tr_kuniv_formation_invert.
eapply tr_inhabitation_formation; eauto.
Qed.


Lemma iforallEqUniv_valid : iforallEqUniv_obligation.
Proof.
prepare.
intros G a b i j k l ext3 ext2 ext1 ext0 Hkl Hj Hleq Hab.
apply tr_all_formation_univ; auto.
unfold Defined.leqpagetp.
eapply tr_leqtp_eta2; eauto.
apply tr_kuniv_formation_invert.
eapply tr_inhabitation_formation; eauto.
Qed.


Lemma iforallIntroOf_valid : iforallIntroOf_obligation.
Proof.
prepare.
intros G a i k m ext1 ext0 Hk Hm.
apply tr_all_intro; auto.
Qed.


Lemma iforallIntroEq_valid : iforallIntroEq_obligation.
Proof.
prepare.
intros G a i k m n ext1 ext0 Hk Hmn.
apply tr_all_intro; auto.
Qed.


Lemma iforallIntro_valid : iforallIntro_obligation.
Proof.
prepare.
intros G a i k ext0 m Hhyg Hk Hm.
apply tr_all_intro; auto.
simpsub.
replace (subst (dot triv sh1) m) with m; auto.
so (subst_into_absent_single _#3 triv Hhyg) as Heq.
simpsubin Heq.
symmetry; auto.
Qed.


Lemma iforallElimOf_valid : iforallElimOf_obligation.
Proof.
prepare.
intros G a i k m p ext2 ext1 ext0 Ha Hm Hp.
eapply tr_all_elim; eauto.
Qed.


Lemma iforallElimEq_valid : iforallElimEq_obligation.
Proof.
prepare.
intros G a i k m n p ext2 ext1 ext0 Ha Hmn Hp.
eapply tr_all_elim; eauto.
Qed.


Lemma iforallElim_valid : iforallElim_obligation.
Proof.
prepare.
intros G a i k p ext1 m ext0 Ha Hm Hp.
replace a with (subst1 p (subst (sh 1) a)) by (simpsub; auto).
eapply tr_all_elim; eauto.
  {
  simpsub.
  exact Hm.
  }

  {
  simpsub.
  exact Ha.
  }
Qed.
