
Require Import Coq.Setoids.Setoid.

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
Require Import Equivalences.
Require Import Dots.

Require Import Relation.
Require Import Dynamic.
Require Import ValidationUtil.


Lemma substitution_valid : substitution_obligation.
Proof.
prepare.
intros G1 G2 a b m ext1 ext0 n Hb Hm Hn.
simpsubin Hb.
simpsubin Hm.
eapply tr_substitution; eauto.
Qed.


Lemma substitutionSimple_valid : substitutionSimple_obligation.
Proof.
prepare.
intros G1 G2 a b m ext0 n Hm Hn.
simpsubin Hm.
eapply tr_substitution_simple; eauto.
Qed.


Lemma generalize_valid : generalize_obligation.
Proof.
prepare.
intros G a b m ext0 n Hm Hn.
cut (tr G (substj (dot m id) (deq n n b))).
  {
  intro H.
  simpsubin H.
  exact H.
  }
eapply tr_generalize; eauto.
Qed.


Lemma def_lett :
  forall m n,
    equiv (app (app Defs.lett m) (lam n)) (app (lam n) m).
Proof.
intros a m.
unfold Defs.lett.
eapply equiv_trans.
  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app1.
    apply step_app2.
    }
  simpsub.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
apply equiv_refl.
Qed.


Lemma assert_valid : assert_obligation.
Proof.
prepare.
intros G a b m n Hm Hn.
rewrite -> def_lett.
eapply tr_pi_elim'; eauto.
  {
  apply tr_pi_intro; eauto.
  eapply tr_inhabitation_formation; eauto.
  }

  {
  simpsub.
  auto.
  }
Qed.


Lemma assert'_valid : assert'_obligation.
Proof.
prepare.
intros G a b m n Hm Hn.
cut (tr G (substj (dot m id) (deq n n (subst sh1 b)))).
  {
  intro H.
  simpsubin H.
  exact H.
  }
eapply tr_generalize; eauto.
Qed.


Lemma inhabitant_valid : inhabitant_obligation.
Proof.
prepare.
intros G a m ext0 H.
auto.
Qed.


Lemma letForm_valid : letForm_obligation.
Proof.
prepare.
intros G a b m n ext1 ext0 Hm Hn.
unfold Defs.lett.
rewrite -> equiv_beta.
simpsub.
rewrite -> equiv_beta.
simpsub.
eapply tr_pi_elim'; eauto.
  {
  apply tr_pi_intro.
    {
    eapply tr_inhabitation_formation; eauto.
    }
  exact Hn.
  }

  {
  simpsub.
  auto.
  }
Qed.
