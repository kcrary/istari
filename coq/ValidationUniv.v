
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

Require Import ValidationUtil.
Require Import Defined.
Require Import NatLemmas.
Require Import LevelLemmas.


Hint Rewrite def_lsucc : prepare.



Lemma univKind_valid : univKind_obligation.
Proof.
prepare.
intros G i j ext0 H.
apply tr_univ_kind_formation; auto.
eapply tr_eq_reflexivity; eauto.
Qed.


Lemma univKindEq_valid : univKindEq_obligation.
Proof.
prepare.
intros G i j k ext1 ext0 Hjk Hji.
apply tr_univ_kind_formation; auto.
Qed.


Lemma univForm_valid : univForm_obligation.
Proof.
prepare.
intros G i ext0 H.
apply tr_univ_formation; auto.
Qed.


Lemma univEq_valid : univEq_obligation.
Proof.
prepare.
intros G i j ext0 H.
apply tr_univ_formation; auto.
Qed.


Lemma univFormUniv_valid : univFormUniv_obligation.
Proof.
prepare.
intros G i j ext Hleq.
so (lleq_explode _#5 Hleq) as (H & Hsj & Hi).
so (tr_nsucc_nattp_invert _#3 Hsj) as Hj.
apply tr_univ_formation_univ; auto.
unfold ltpagetp.
rewrite -> equiv_lttp.
auto.
Qed.


Lemma univFormUnivSucc_valid : univFormUnivSucc_obligation.
Proof.
prepare.
intros G i ext0 H.
apply tr_univ_formation_univ; auto.
  {
  unfold pagetp.
  apply tr_nsucc_nattp; auto.
  }

  {
  unfold ltpagetp.
  rewrite -> equiv_lttp.
  apply tr_leqtp_refl.
  apply tr_nsucc_nattp; auto.
  }
Qed.


Lemma univEqUniv_valid : univEqUniv_obligation.
Proof.
prepare.
intros G i j k ext1 ext Hjk Hleq.
so (lleq_explode _#5 Hleq) as (H & Hsj & Hi).
so (tr_nsucc_nattp_invert _#3 Hsj) as Hj.
apply tr_univ_formation_univ; auto.
unfold ltpagetp.
rewrite -> equiv_lttp.
eapply tr_leqtp_eta2; eauto.
Qed.


Lemma univCumulativeOf_valid : univCumulativeOf_obligation.
Proof.
prepare.
intros G a i j ext1 ext0 Ha Hleq.
so (lleq_explode _#5 Hleq) as (H & Hi & Hj).
eapply tr_univ_cumulative; eauto.
Qed.


Lemma univCumulativeEq_valid : univCumulativeEq_obligation.
Proof.
prepare.
intros G a b i j ext1 ext0 Hab Hleq.
so (lleq_explode _#5 Hleq) as (H & Hi & Hj).
eapply tr_univ_cumulative; eauto.
Qed.


Lemma univCumulativeSuccOf_valid : univCumulativeSuccOf_obligation.
Proof.
prepare.
intros G a i ext0 H.
eapply tr_univ_cumulative; eauto.
  {
  unfold pagetp.
  apply tr_nsucc_nattp.
  fold (@pagetp obj).
  apply tr_univ_formation_invert.
  eapply tr_inhabitation_formation; eauto.
  }

  {
  unfold leqpagetp.
  apply tr_leqtp_succ.
  fold (@pagetp obj).
  apply tr_univ_formation_invert.
  eapply tr_inhabitation_formation; eauto.
  }
Qed.


Lemma univSub_valid : univSub_obligation.
Proof.
prepare.
intros G i j ext0 Hleq.
so (lleq_explode _#5 Hleq) as (H & Hi & Hj).
apply tr_subtype_intro; auto using tr_univ_formation.
simpsub.
apply (tr_univ_cumulative _ (subst sh1 i)).
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  eapply (weakening _ [_] []).
    {
    cbn [length Dots.unlift].
    simpsub.
    reflexivity.
    }

    {
    cbn [length Dots.unlift].
    simpsub.
    reflexivity.
    }
  cbn [length Dots.unlift].
  simpsub.
  auto.
  }

  {
  eapply (weakening _ [_] []).
    {
    cbn [length Dots.unlift].
    simpsub.
    reflexivity.
    }

    {
    cbn [length Dots.unlift].
    simpsub.
    reflexivity.
    }
  cbn [length Dots.unlift].
  simpsub.
  unfold leqpagetp.
  eapply tr_leqtp_eta2; eauto.
  }
Qed.


Lemma univForgetOf_valid : univForgetOf_obligation.
Proof.
prepare.
intros G a i ext0 H.
eapply tr_formation_weaken; eauto.
Qed.


Lemma univForgetEq_valid : univForgetEq_obligation.
Proof.
prepare.
intros G a b i ext0 H.
eapply tr_formation_weaken; eauto.
Qed.


Lemma univIntroEqtype_valid : univIntroEqtype_obligation.
Proof.
prepare.
intros G a b i ext2 ext1 ext0 Hab Ha Hb.
eapply tr_formation_strengthen; eauto.
Qed.
  

Lemma univFormInv_valid : univFormInv_obligation.
Proof.
prepare.
intros G I ext0 Huniv.
apply tr_univ_formation_invert.
auto.
Qed.


Lemma kindForm_valid : kindForm_obligation.
Proof.
prepare.
intros G i ext0 H.
apply tr_kuniv_formation; auto.
Qed.


Lemma kindEq_valid : kindEq_obligation.
Proof.
prepare.
intros G i j ext0 H.
apply tr_kuniv_formation; eauto.
Qed.


Lemma kindFormUniv_valid : kindFormUniv_obligation.
Proof.
prepare.
intros G i k ext0 Hleq.
so (lleq_explode _#5 Hleq) as (H & Hssi & Hk).
so (tr_nsucc_nattp_invert _#3 Hssi) as Hsi.
so (tr_nsucc_nattp_invert _#3 Hsi) as Hi.
apply tr_kuniv_formation_univ; auto.
unfold ltpagetp.
rewrite -> equiv_lttp.
eapply tr_leqtp_eta2; eauto.
Qed.


Lemma kindEqUniv_valid : kindEqUniv_obligation.
Proof.
prepare.
intros G i j k ext1 ext0 Hij Hleq.
so (lleq_explode _#5 Hleq) as (H & _ & Hk).
apply tr_kuniv_formation_univ; auto.
unfold ltpagetp.
rewrite -> equiv_lttp.
eapply tr_leqtp_eta2; eauto.
apply tr_nsucc_nattp.
apply tr_nsucc_nattp.
eapply tr_eq_reflexivity; eauto.
Qed.


Lemma kindForgetOf_valid : kindForgetOf_obligation.
Proof.
prepare.
intros G a i ext0 H.
apply tr_kuniv_weaken; auto.
Qed.


Lemma kindForgetEq_valid : kindForgetEq_obligation.
Proof.
prepare.
intros G a b i ext0 H.
apply tr_kuniv_weaken; auto.
Qed.


Lemma kindUnivSub_valid : kindUnivSub_obligation.
Proof.
prepare.
intros G i j ext0 Hleq.
so (lleq_explode _#5 Hleq) as (H & Hsi & Hj).
so (tr_nsucc_nattp_invert _#3 Hsi) as Hi.
apply tr_subtype_intro.
  {
  apply tr_kuniv_formation; eauto.
  }

  {
  apply tr_univ_formation; eauto.
  }
simpsub.
apply (tr_univ_cumulative _ (nsucc (subst sh1 i))).
  {
  apply tr_kuniv_weaken.
  eapply hypothesis; eauto using index_0.
  }

  {
  eapply (weakening _ [_] []).
    {
    cbn [length Dots.unlift].
    simpsub.
    reflexivity.
    }

    {
    cbn [length Dots.unlift].
    simpsub.
    reflexivity.
    }
  cbn [length Dots.unlift].
  simpsub.
  auto.
  }

  {
  eapply (weakening _ [_] []).
    {
    cbn [length Dots.unlift].
    simpsub.
    reflexivity.
    }

    {
    cbn [length Dots.unlift].
    simpsub.
    reflexivity.
    }
  cbn [length Dots.unlift].
  simpsub.
  unfold leqpagetp.
  eapply tr_leqtp_eta2; eauto.
  }
Qed.
