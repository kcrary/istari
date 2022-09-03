
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Tactics.
Require Import Sequence.
Require Import Relation.
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
Require Import Dynamic.
Require MuIndExtract.


Lemma muForm_valid : muForm_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a ext1 ext0 Ha Hpos.
rewrite -> def_istp in Ha.
rewrite -> def_positive in Hpos.
rewrite -> def_istp.
unfold Defs.triv.
rewrite -> def_mu.
apply tr_mu_formation.
  {
  eapply tr_eqtype_eta2; eauto.
  }

  {
  eapply tr_positive_eta2; eauto.
  }

  {
  eapply tr_positive_eta2; eauto.
  }
Qed.


Lemma muEq_valid : muEq_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b ext2 ext1 ext0 Ha Hposa Hposb.
rewrite -> def_eqtp in Ha.
rewrite -> def_positive in Hposa, Hposb.
rewrite -> def_eqtp.
unfold Defs.triv.
rewrite -> !def_mu.
apply tr_mu_formation.
  {
  eapply tr_eqtype_eta2; eauto.
  }

  {
  eapply tr_positive_eta2; eauto.
  }

  {
  eapply tr_positive_eta2; eauto.
  }
Qed.


Lemma muFormUniv_valid : muFormUniv_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a i ext2 ext1 ext0 Hi Ha Hpos.
rewrite -> def_of in Hi, Ha |- *.
rewrite -> def_positive in Hpos.
unfold Defs.triv.
rewrite -> !def_univ.
rewrite -> !def_univ in Ha.
unfold Defs.level in Hi.
rewrite -> def_mu.
apply tr_equal_intro.
apply tr_mu_formation_univ.
  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  eapply tr_positive_eta2; eauto.
  }

  {
  eapply tr_positive_eta2; eauto.
  }
Qed.


Lemma muEqUniv_valid : muEqUniv_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b i ext3 ext2 ext1 ext0 Hi Hab Hposa Hposb.
rewrite -> def_eq in Hab |- *.
rewrite -> def_of in Hi.
rewrite -> def_positive in Hposa, Hposb.
unfold Defs.triv.
rewrite -> !def_univ.
rewrite -> !def_univ in Hab.
unfold Defs.level in Hi.
rewrite -> !def_mu.
apply tr_equal_intro.
apply tr_mu_formation_univ.
  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  eapply tr_positive_eta2; eauto.
  }

  {
  eapply tr_positive_eta2; eauto.
  }
Qed.


Lemma def_eeqtp :
  forall a b,
    equiv (app (app Defs.eeqtp a) b) (prod (subtype a b) (subtype b a)).
Proof.
intros a b.
unfold Defs.eeqtp.
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
Qed.



Hint Rewrite def_eeqtp def_mu def_positive : prepare.


Lemma tr_prod_intro :
  forall G a b m m' n n',
    tr G (deq m m' a)
    -> tr G (deq n n' b)
    -> tr G (deq (ppair m n) (ppair m' n') (prod a b)).
Proof.
intros G a b m m' n n' Hm Hn.
apply (tr_eqtype_convert _#3 (sigma a (subst sh1 b))).
  {
  apply tr_eqtype_symmetry.
  apply tr_prod_sigma_equal.
    {
    eapply tr_inhabitation_formation; eauto.
    }

    {
    eapply tr_inhabitation_formation; eauto.
    }
  }
apply tr_sigma_intro; auto.
  {
  simpsub.
  auto.
  }

  {
  eapply (weakening _ [_] []).
    {
    cbn [length unlift].
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
  eapply tr_inhabitation_formation; eauto.
  }
Qed.


Lemma muUnroll_valid : muUnroll_obligation.
Proof.
prepare.
intros G a ext1 ext0 Ha Hpos.
apply tr_prod_intro.
  {
  apply tr_mu_unroll; auto.
  eapply tr_positive_eta2; eauto.
  }

  {
  apply tr_mu_roll; auto.
  eapply tr_positive_eta2; eauto.
  }
Qed.


Lemma muUnrollUniv_valid : muUnrollUniv_obligation.
Proof.
prepare.
intros G a i ext2 ext1 ext0 Hlv Ha Hpos.
apply tr_prod_intro.
  {
  eapply tr_mu_unroll_univ; eauto.
  eapply tr_positive_eta2; eauto.
  }

  {
  eapply tr_mu_roll_univ; eauto.
  eapply tr_positive_eta2; eauto.
  }
Qed.


Lemma muInd_valid : muInd_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m ext2 ext1 n ext0 Hhide Ha Hpos Hb Hm.
unfold Defs.theta.
unfold Defs.triv.
rewrite -> def_istp in Ha.
rewrite -> def_of in Hm.
rewrite -> def_pi in Hb.
rewrite -> def_subtype in Hb.
rewrite -> def_mu in Hb, Hm.
rewrite -> def_positive in Hpos.
replace (subst (dot (var 1) (dot triv (dot (var 0) (dot triv (sh 2))))) n)
  with  (subst (dot (var 1) (dot triv (dot (var 0) (sh 2))))
           (subst (under 3 (dot triv id)) n)).
2:{
  simpsub.
  auto.
  }
eapply MuIndExtract.tr_mu_ind_extract.
  {
  eapply tr_eqtype_eta2; eauto.
  }

  {
  eapply tr_positive_eta2; eauto.
  }

  {
  simpsub.
  cbn [Nat.add].
  rewrite <- (subst_into_absent_single _ _ _ triv Hhide) in Hb.
  simpsubin Hb.
  cbn [Nat.add] in Hb.
  exact Hb.
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma muIndUniv_valid : muIndUniv_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b i m ext3 ext2 ext1 n ext0 Hhide Hi Ha Hpos Hb Hm.
unfold Defs.theta.
unfold Defs.triv.
unfold Defs.level in Hi.
rewrite -> !def_univ in Ha, Hb.
rewrite -> def_of in Hm, Ha, Hi, Hb.
rewrite -> def_pi in Hb.
rewrite -> def_subtype in Hb.
rewrite -> def_mu in Hb, Hm.
rewrite -> def_positive in Hpos.
rewrite -> def_prod in Hb.
replace (ppi1 (subst (dot (var 1) (dot triv (dot (var 0) (dot triv (sh 2))))) n))
  with  (subst (dot (var 1) (dot triv (dot (var 0) (sh 2))))
           (subst (under 3 (dot triv id)) (ppi1 n))).
2:{
  simpsub.
  auto.
  }
eapply (MuIndExtract.tr_mu_ind_univ_extract _ i a).
  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  eapply tr_positive_eta2; eauto.
  }

  {
  simpsub.
  cbn [Nat.add].
  rewrite <- (subst_into_absent_single _ _ _ triv Hhide) in Hb.
  simpsubin Hb.
  cbn [Nat.add] in Hb.
  apply tr_equal_elim.
  apply (tr_equal_eta2 _#4 (ppi2 (subst (dot (var 0) (dot (var 1) (dot (var 2) (dot triv (sh 4))))) n)) (ppi2 (subst (dot (var 0) (dot (var 1) (dot (var 2) (dot triv (sh 4))))) n))).
  eapply tr_prod_elim2.
  exact Hb.
  }

  {
  simpsub.
  cbn [Nat.add].
  rewrite <- (subst_into_absent_single _ _ _ triv Hhide) in Hb.
  simpsubin Hb.
  cbn [Nat.add] in Hb.
  eapply tr_prod_elim1.
  exact Hb.
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }
Qed.
