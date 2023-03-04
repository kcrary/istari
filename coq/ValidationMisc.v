
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


Lemma eeqtpSymm_valid : eeqtpSymm_obligation.
Proof.
prepare.
intros G a b m H.
rewrite -> def_eeqtp in H |- *.
apply tr_prod_intro.
  {
  apply (tr_subtype_eta2 _#3 (ppi2 m) (ppi2 m)).
  eapply tr_prod_elim2; eauto.
  }

  {
  apply (tr_subtype_eta2 _#3 (ppi1 m) (ppi1 m)).
  eapply tr_prod_elim1; eauto.
  }
Qed.


Lemma weakenEqtpEeqtp_valid : weakenEqtpEeqtp_obligation.
Proof.
prepare.
intros G a b ext0 H.
rewrite -> def_eeqtp.
apply tr_prod_intro.
  {
  apply tr_subtype_intro.
    {
    eapply tr_eqtype_formation_left; eauto.
    }

    {
    eapply tr_eqtype_formation_right; eauto.
    }
  apply (tr_eqtype_convert _ _ _ (subst sh1 a)).
    {
    apply (weakening _ [_] []).
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
    auto.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }

  {
  apply tr_subtype_intro.
    {
    eapply tr_eqtype_formation_right; eauto.
    }

    {
    eapply tr_eqtype_formation_left; eauto.
    }
  apply (tr_eqtype_convert _ _ _ (subst sh1 b)).
    {
    apply tr_eqtype_symmetry.
    apply (weakening _ [_] []).
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
    auto.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }
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
