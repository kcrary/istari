
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


Hint Rewrite def_subtype : prepare.


Lemma subtypeForm_valid : subtypeForm_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_subtype_formation; auto.
Qed.


Lemma subtypeEq_valid : subtypeEq_obligation.
Proof.
prepare.
intros G a b c d ext1 ext0 Hab Hcd.
apply tr_subtype_formation; auto.
Qed.


Lemma subtypeFormUniv_valid : subtypeFormUniv_obligation.
Proof.
prepare.
intros G a b i ext1 ext0 Ha Hb.
apply tr_subtype_formation_univ; auto.
Qed.


Lemma subtypeEqUniv_valid : subtypeEqUniv_obligation.
Proof.
prepare.
intros G a b c d i ext1 ext0 Hab Hcd.
apply tr_subtype_formation_univ; auto.
Qed.


Lemma subtypeIntro_valid : subtypeIntro_obligation.
Proof.
prepare.
intros G a b ext2 ext1 ext0 Ha Hb Hsub.
eapply tr_subtype_intro; eauto.
Qed.


Lemma subtypeExt_valid : subtypeExt_obligation.
Proof.
unfoldtop.
intros G a b p q ext1 ext0 Hp Hq.
unfold Defs.dof in * |- *.
autorewrite with prepare in Hp, Hq |- *.
unfold Defs.triv.
apply tr_equal_intro.
apply (tr_transitivity _ _ triv).
  {
  apply tr_subtype_eta; auto.
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  apply tr_symmetry.
  apply tr_subtype_eta; auto.
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma subtypeLeft_valid : subtypeLeft_obligation.
Proof.
prepare.
intros G1 G2 a b c m H.
unfold Defs.triv in H.
apply tr_subtype_eta_hyp; auto.
Qed.


Lemma subsumptionOf_valid : subsumptionOf_obligation.
Proof.
prepare.
intros G a b m ext1 ext0 Hab Hm.
eapply tr_subtype_elim; eauto.
Qed.


Lemma subsumptionEq_valid : subsumptionEq_obligation.
Proof.
prepare.
intros G a b m n ext1 ext0 Hab Hm.
eapply tr_subtype_elim; eauto.
Qed.


Lemma subsumption_valid : subsumption_obligation.
Proof.
prepare.
intros G a b ext1 m Hab Hm.
eapply tr_subtype_elim; eauto.
Qed.


Lemma subsumptionLeft_valid : subsumptionLeft_obligation.
Proof.
prepare.
intros G1 G2 a b c p m Hb Hm.
rewrite -> def_eeqtp in Hb.
simpsubin Hm.
eapply tr_subtype_convert_hyp; eauto.
  {
  apply (tr_subtype_eta2 _ _ _ (ppi1 p) (ppi1 p)).
  eapply tr_prod_elim1; eauto.
  }

  {
  apply (tr_subtype_eta2 _ _ _ (ppi2 p) (ppi2 p)).
  eapply tr_prod_elim2; eauto.
  }
Qed.


Lemma subtypeRefl_valid : subtypeRefl_obligation.
Proof.
prepare.
intros G a ext0 H.
apply tr_subtype_intro; auto.
eapply hypothesis; eauto using index_0.
Qed.


Lemma subtypeReflEqtype_valid : subtypeReflEqtype_obligation.
Proof.
prepare.
intros G a b ext0 H.
apply tr_subtype_intro.
  {
  apply (tr_eqtype_transitivity _ _ b); auto.
  apply tr_eqtype_symmetry; auto.
  }

  {
  apply (tr_eqtype_transitivity _ _ a); auto.
  apply tr_eqtype_symmetry; auto.
  }
apply (tr_eqtype_convert _#3 (subst sh1 a)).
  {
  eapply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  exact H.
  }

  {
  eapply hypothesis; eauto using index_0.
  }
Qed.


Lemma subtypeTrans_valid : subtypeTrans_obligation.
Proof.
prepare.
intros G a b c ext1 ext0 Hab Hbc.
apply tr_subtype_intro.
  {
  eapply tr_subtype_formation_invert1.
  eapply tr_inhabitation_formation; eauto.
  }

  {
  eapply tr_subtype_formation_invert2.
  eapply tr_inhabitation_formation; eauto.
  }
eapply (tr_subtype_elim _ (subst sh1 b)).
  {
  eapply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  exact Hbc.
  }
eapply (tr_subtype_elim _ (subst sh1 a)).
  {
  eapply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  exact Hab.
  }
eapply hypothesis; eauto using index_0.
Qed.


Lemma subtypeIstp1_valid : subtypeIstp1_obligation.
Proof.
prepare.
intros G a b ext0 H.
eapply tr_subtype_formation_invert1.
eapply tr_inhabitation_formation; eauto.
Qed.


Lemma subtypeIstp2_valid : subtypeIstp2_obligation.
Proof.
prepare.
intros G a b ext0 H.
eapply tr_subtype_formation_invert2.
eapply tr_inhabitation_formation; eauto.
Qed.
