
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Tactics.
Require Import Sequence.
Require Import Relation.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.
Require Import Dynamic.
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
Require Import Defined.
Require Import ValidationSum.
Require Import ValidationNat.



Lemma def_lleq : Defs.lleq = leqtp.
Proof.
auto.
Qed.


Hint Rewrite def_lleq : prepare.



Lemma levelForm_valid : levelForm_obligation.
Proof.
prepare.
intros G.
apply tr_nattp_formation.
Qed.
 

Lemma levelEq_valid : levelEq_obligation.
Proof.
prepare.
intros G.
apply tr_nattp_formation.
Qed.


Lemma levelFormUniv_valid : levelFormUniv_obligation.
Proof.
prepare.
intros G i ext0 Hi.
apply (tr_univ_cumulative _ nzero).
  {
  apply tr_nattp_formation_univ.
  }

  {
  unfold pagetp.
  exact Hi.
  }

  {
  rewrite -> leqpagetp_nzero_equiv.
  apply tr_unittp_intro.
  }
Qed.
 

Lemma levelEqUniv_valid : levelEqUniv_obligation.
Proof.
prepare.
intros G i ext0 Hi.
apply (tr_univ_cumulative _ nzero).
  {
  apply tr_nattp_formation_univ.
  }

  {
  unfold pagetp.
  exact Hi.
  }

  {
  rewrite -> leqpagetp_nzero_equiv.
  apply tr_unittp_intro.
  }
Qed.


Lemma lleqForm_valid : lleqForm_obligation.
Proof.
prepare.
intros G i j ext1 ext0 Hi Hj.
apply (tr_formation_weaken _ nzero).
apply tr_leqtp_formation_univ; auto.
Qed.


Lemma lleqEq_valid : lleqEq_obligation.
Proof.
prepare.
intros G i i' j j' ext1 ext0 Hi Hj.
apply (tr_formation_weaken _ nzero).
apply tr_leqtp_formation_univ; auto.
Qed.


Lemma lleqFormUniv_valid : lleqFormUniv_obligation.
Proof.
prepare.
intros G i j k ext2 ext1 ext0 Hi Hj Hk.
apply (tr_univ_cumulative _ nzero).
  {
  apply tr_leqtp_formation_univ; auto.
  }

  {
  exact Hk.
  }

  {
  unfold leqpagetp.
  rewrite -> unroll_leqtp.
  unfold nzero.
  rewrite -> sumcase_left.
  simpsub.
  apply tr_unittp_intro.
  }
Qed.


Lemma lleqEqUniv_valid : lleqEqUniv_obligation.
Proof.
prepare.
intros G i i' j j' k ext2 ext1 ext0 Hi Hj Hk.
apply (tr_univ_cumulative _ nzero).
  {
  apply tr_leqtp_formation_univ; auto.
  }

  {
  exact Hk.
  }

  {
  unfold leqpagetp.
  rewrite -> unroll_leqtp.
  unfold nzero.
  rewrite -> sumcase_left.
  simpsub.
  apply tr_unittp_intro.
  }
Qed.


Lemma lleqZero_valid : lleqZero_obligation.
Proof.
prepare.
intros G m ext0 H.
unfold Defs.lleq.
rewrite -> def_lzero.
rewrite -> leqtp_nzero_equiv.
apply tr_unittp_intro.
Qed.
