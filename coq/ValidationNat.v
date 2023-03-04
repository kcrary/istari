
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
Require Import Equivalences.
Require Import Dots.

Require Import ValidationUtil.
Require Import Defined.
Require Import PageType.
Require Import SumLemmas.
Require Import NatLemmas.



Hint Rewrite def_nat def_zero def_succ def_natcase : prepare.


Lemma natForm_valid : natForm_obligation.
Proof.
prepare.
intro G.
apply tr_nattp_formation.
Qed.


Lemma natEq_valid : natEq_obligation.
Proof.
prepare.
intro G.
apply tr_nattp_formation.
Qed.


Lemma natFormUniv_valid : natFormUniv_obligation.
Proof.
prepare.
intros G i ext H.
apply (tr_univ_cumulative _ nzero); auto.
  {
  apply tr_nattp_formation_univ.
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


Lemma natEqUniv_valid : natEqUniv_obligation.
Proof.
prepare.
intros G i ext H.
apply (tr_univ_cumulative _ nzero); auto.
  {
  apply tr_nattp_formation_univ.
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


Lemma natElimEq_valid : natElimEq_obligation.
Proof.
prepare.
intros G a m n p q r s ext2 ext1 ext0 Hmn Hpq Hrs.
unfold natcase.
eapply (tr_sumtype_elim _ unittp); eauto.
  {
  apply (tr_subtype_elim _ nattp); auto.
  unfold nattp.
  apply tr_mu_unroll.
    {
    apply tr_sumtype_formation.
      {
      apply tr_unittp_istype.
      }

      {
      apply tr_hyp_tp; eauto using index_0.
      }
    }

    {
    apply tr_positive_nattp_body.
    }
  }
apply (tr_unittp_eta_hyp _ []).
simpsub.
auto.
Qed.


Lemma natElimEqtype_valid : natElimEqtype_obligation.
Proof.
prepare.
intros G a b c d m n ext2 ext1 ext0 Hmn Hab Hcd.
unfold natcase.
eapply (tr_sumtype_elim_eqtype _ unittp); eauto.
  {
  apply (tr_subtype_elim _ nattp); auto.
  unfold nattp.
  apply tr_mu_unroll.
    {
    apply tr_sumtype_formation.
      {
      apply tr_unittp_istype.
      }

      {
      apply tr_hyp_tp; eauto using index_0.
      }
    }

    {
    apply tr_positive_nattp_body.
    }
  }
unfold deqtype.
exploit (tr_unittp_eta_hyp G [] triv triv (subst sh1 (eqtype a b))) as H.
  {
  simpsub.
  exact Hab.
  }
cbn [length List.app under] in H.
simpsubin H.
exact H.
Qed.


Lemma zeroType_valid : zeroType_obligation.
Proof.
prepare.
intro G.
apply tr_nzero_nattp.
Qed.


Lemma succType_valid : succType_obligation.
Proof.
prepare.
intro G.
unfold Defs.succ.
rewrite -> def_arrow.
apply tr_pi_intro.
  {
  apply tr_nattp_formation.
  }
rewrite -> def_inr.
fold (@nsucc obj (var 0)).
simpsub.
apply tr_nsucc_nattp.
eapply hypothesis; eauto using index_0.
Qed.
