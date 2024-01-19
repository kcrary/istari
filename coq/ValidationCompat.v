
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
Require Import Defined.
Require Import SumLemmas.
Require Import ValidationPi.
Require Import ValidationSigma.
Require Import ValidationSum.
Require Import ValidationFuture.

(* The order of some of these matters, for some reason. *)
Hint Rewrite def_iff def_eeqtp def_guard def_arrow def_pi def_sigma def_prod def_sum def_set def_iset def_inl def_inr def_sum_case def_fut def_letnext def_intersect def_union : prepare.


Lemma eeqtpRefl_valid : eeqtpRefl_obligation.
Proof.
prepare.
intros G a ext0 Ha.
apply tr_prod_intro; apply tr_subtype_refl; auto.
Qed.


Lemma eeqtpSymm_valid : eeqtpSymm_obligation.
Proof.
prepare.
intros G a b m H.
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


Lemma eeqtpTrans_valid : eeqtpTrans_obligation.
Proof.
prepare.
intros G a b c m n Hab Hbc.
apply tr_prod_intro.
  {
  apply (tr_subtype_trans _ _ b).
    {
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }

    {
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }
  }

  {
  apply (tr_subtype_trans _ _ b).
    {
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }

    {
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }
  }
Qed.


Lemma weakenEqtpEeqtp_valid : weakenEqtpEeqtp_obligation.
Proof.
prepare.
intros G a b ext0 H.
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


Lemma weakenSubtypeArrow_valid : weakenSubtypeArrow_obligation.
Proof.
prepare.
intros G a b ext0 H.
apply tr_pi_intro.
  {
  eapply tr_subtype_istype1; eauto.
  }
apply (tr_subtype_elim _ (subst sh1 a)).
  {
  apply (weakening _ [_] []).
    {
    simpsub.
    reflexivity.
    }
    
    {
    cbn [length].
    simpsub.
    rewrite <- compose_assoc.
    unfold sh1.
    rewrite -> compose_sh_unlift.
    simpsub.
    reflexivity.
    }
  cbn [length].
  simpsub.
  exact H.
  }

  {
  eapply hypothesis; eauto using index_0.
  }
Qed.


Lemma weakenEeqtpIff_valid : weakenEeqtpIff_obligation.
Proof.
prepare.
intros G a b ext0 H.
assert (tr G (deqtype a a)) as Ha.
  {
  eapply tr_subtype_istype1.
  eapply tr_subtype_eta2.
  eapply tr_prod_elim1; eauto.
  }
assert (tr G (deqtype b b)) as Hb.
  {
  eapply tr_subtype_istype2.
  eapply tr_subtype_eta2.
  eapply tr_prod_elim1; eauto.
  }
apply tr_prod_intro.
  {
  apply tr_pi_intro; auto.
  apply (tr_subtype_elim _ (subst sh1 a)).
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }

  {
  apply tr_pi_intro; auto.
  apply (tr_subtype_elim _ (subst sh1 b)).
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }
Qed.


Lemma compatGuardIff0_valid : compatGuardIff0_obligation.
Proof.
prepare.
intros G a a' b m ext0 Ha Hb.
apply (tr_guard_formation_iff _#5 (app (subst sh1 (ppi1 m)) (var 0)) (app (subst sh1 (ppi2 m)) (var 0))).
  {
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation.
  eapply tr_prod_elim1; eauto.
  }

  {
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation.
  eapply tr_prod_elim2; eauto.
  }

  {
  apply (tr_pi_elim' _ (subst sh1 a) (subst (sh 2) a')).
    {
    simpsub.
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_prod_elim1; eauto.
    }

    {
    eapply hypothesis; eauto using index_0.
    }

    {
    simpsub.
    reflexivity.
    }
  }

  {
  apply (tr_pi_elim' _ (subst sh1 a') (subst (sh 2) a)).
    {
    simpsub.
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_prod_elim2; eauto.
    }

    {
    eapply hypothesis; eauto using index_0.
    }

    {
    simpsub.
    reflexivity.
    }
  }

  {
  apply (weakening _ [_] []).
    {
    simpsub.
    reflexivity.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  exact Hb.
  }
Qed.


Lemma compatSetEqtp0_valid : compatSetEqtp0_obligation.
Proof.
prepare.
intros G a a' b ext1 ext0 Ha Hb.
apply (tr_set_formation _#5 (var 0) (var 0)); auto.
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  eapply hypothesis; eauto using index_0.
  }
Qed.


Lemma compatSetIff1_valid : compatSetIff1_obligation.
Proof.
prepare.
intros G a b b' ext m Ha Hb.
apply (tr_set_formation _#5 (app (subst sh1 (ppi1 m)) (var 0)) (app (subst sh1 (ppi2 m)) (var 0))); auto.
  {
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation.
  eapply tr_prod_elim1; eauto.
  }

  {
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation.
  eapply tr_prod_elim2; eauto.
  }

  {
  apply (tr_pi_elim' _ (subst sh1 b) (subst (sh 2) b')).
    {
    simpsub.
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_prod_elim1; eauto.
    }

    {
    eapply hypothesis; eauto using index_0.
    }

    {
    simpsub.
    reflexivity.
    }
  }

  {
  apply (tr_pi_elim' _ (subst sh1 b') (subst (sh 2) b)).
    {
    simpsub.
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_prod_elim2; eauto.
    }

    {
    eapply hypothesis; eauto using index_0.
    }

    {
    simpsub.
    reflexivity.
    }
  }
Qed.


Lemma forallEeq_valid : forallEeq_obligation.
Proof.
prepare.
intros G a a' b b' m n Ha Hb.
apply tr_prod_intro.
  {
  apply tr_pi_sub.
    {
    unfold dsubtype.
    apply (tr_subtype_eta2 _ _ _ (ppi2 m) (ppi2 m)).
    eapply tr_prod_elim2; eauto.
    }

    {
    unfold dsubtype.
    apply (tr_subtype_convert_hyp' _ [] _ a).
      {
      unfold subtype.
      apply (tr_subtype_eta2 _ _ _ (ppi2 m) (ppi2 m)).
      eapply tr_prod_elim2; eauto.
      }

      {
      unfold subtype.
      apply (tr_subtype_eta2 _ _ _ (ppi1 m) (ppi1 m)).
      eapply tr_prod_elim1; eauto.
      }
    cbn [List.app].
    apply (tr_subtype_eta2 _ _ _ (ppi1 n) (ppi1 n)).
    eapply tr_prod_elim1; eauto.
    }

    {
    apply (tr_subtype_formation_invert1 _ _ _ b' b').
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim1; eauto.
    }
  }

  {
  apply tr_pi_sub.
    {
    unfold dsubtype.
    apply (tr_subtype_eta2 _ _ _ (ppi1 m) (ppi1 m)).
    eapply tr_prod_elim1; eauto.
    }

    {
    unfold dsubtype.
    apply (tr_subtype_eta2 _ _ _ (ppi2 n) (ppi2 n)).
    eapply tr_prod_elim2; eauto.
    }

    {
    apply (tr_subtype_convert_hyp' _ [] _ a).
      {
      unfold subtype.
      apply (tr_subtype_eta2 _ _ _ (ppi2 m) (ppi2 m)).
      eapply tr_prod_elim2; eauto.
      }

      {
      unfold subtype.
      apply (tr_subtype_eta2 _ _ _ (ppi1 m) (ppi1 m)).
      eapply tr_prod_elim1; eauto.
      }
    cbn [List.app].
    apply (tr_subtype_formation_invert1 _ _ _ b b).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim2; eauto.
    }
  }
Qed.


Lemma existsEeq_valid : existsEeq_obligation.
Proof.
prepare.
intros G a a' b b' m n Ha Hb.
apply tr_prod_intro.
  {
  apply tr_sigma_sub.
    {
    unfold dsubtype.
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }

    {
    unfold dsubtype.
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }

    {
    apply (tr_subtype_convert_hyp' _ [] _ a).
      {
      unfold subtype.
      eapply tr_subtype_eta2.
      eapply tr_prod_elim2; eauto.
      }

      {
      unfold subtype.
      eapply tr_subtype_eta2.
      eapply tr_prod_elim1; eauto.
      }
    cbn [List.app].
    apply (tr_subtype_formation_invert1 _ _ _ b b).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim2; eauto.
    }
  }

  {
  apply tr_sigma_sub.
    {
    unfold dsubtype.
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }

    {
    unfold dsubtype.
    apply (tr_subtype_convert_hyp' _ [] _ a).
      {
      unfold subtype.
      eapply tr_subtype_eta2.
      eapply tr_prod_elim2; eauto.
      }

      {
      unfold subtype.
      eapply tr_subtype_eta2.
      eapply tr_prod_elim1; eauto.
      }
    cbn [List.app].
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }

    {
    apply (tr_subtype_formation_invert1 _ _ _ b' b').
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim1; eauto.
    }
  }
Qed.


Lemma arrowEeq_valid : arrowEeq_obligation.
Proof.
prepare.
intros G a a' b b' m n Ha Hb.
apply tr_prod_intro.
  {
  apply tr_pi_sub.
    {
    unfold dsubtype.
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }

    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }

    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    eapply tr_subtype_istype1.
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }
  }

  {
  apply tr_pi_sub.
    {
    unfold dsubtype.
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }

    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }

    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    eapply tr_subtype_istype2.
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }
  }
Qed.



Lemma prodEeq_valid : prodEeq_obligation.
Proof.
prepare.
intros G a a' b b' m n Ha Hb.
apply tr_prod_intro.
  {
  apply tr_prod_sub.
    {
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }

    {
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }
  }

  {
  apply tr_prod_sub.
    {
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }

    {
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }
  }
Qed.


Lemma sumEeq_valid : sumEeq_obligation.
Proof.
prepare.
intros G a a' b b' m n Ha Hb.
apply tr_prod_intro.
  {
  apply tr_sum_sub.
    {
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }

    {
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }
  }

  {
  apply tr_sum_sub.
    {
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }

    {
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }
  }
Qed.


Lemma futureEeq_valid : futureEeq_obligation.
Proof.
prepare.
intros G a a' m H.
apply tr_prod_intro.
  {
  apply tr_future_sub.
  eapply (tr_subtype_eta2 _ _ _ (ppi1 m) (ppi1 m)).
  eapply tr_prod_elim1; eauto.
  }

  {
  apply tr_future_sub.
  eapply (tr_subtype_eta2 _ _ _ (ppi2 m) (ppi2 m)).
  eapply tr_prod_elim2; eauto.
  }
Qed.


Lemma intersectEeq_valid : intersectEeq_obligation.
Proof.
prepare.
intros G a a' b b' m n Ha Hb.
apply tr_prod_intro.
  {
  apply tr_intersect_sub.
    {
    unfold dsubtype.
    apply (tr_subtype_eta2 _ _ _ (ppi2 m) (ppi2 m)).
    eapply tr_prod_elim2; eauto.
    }

    {
    unfold dsubtype.
    apply (tr_subtype_convert_hyp' _ [] _ a).
      {
      unfold subtype.
      apply (tr_subtype_eta2 _ _ _ (ppi2 m) (ppi2 m)).
      eapply tr_prod_elim2; eauto.
      }

      {
      unfold subtype.
      apply (tr_subtype_eta2 _ _ _ (ppi1 m) (ppi1 m)).
      eapply tr_prod_elim1; eauto.
      }
    cbn [List.app].
    apply (tr_subtype_eta2 _ _ _ (ppi1 n) (ppi1 n)).
    eapply tr_prod_elim1; eauto.
    }

    {
    apply (tr_subtype_formation_invert1 _ _ _ b' b').
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim1; eauto.
    }
  }

  {
  apply tr_intersect_sub.
    {
    unfold dsubtype.
    apply (tr_subtype_eta2 _ _ _ (ppi1 m) (ppi1 m)).
    eapply tr_prod_elim1; eauto.
    }

    {
    unfold dsubtype.
    apply (tr_subtype_eta2 _ _ _ (ppi2 n) (ppi2 n)).
    eapply tr_prod_elim2; eauto.
    }

    {
    apply (tr_subtype_convert_hyp' _ [] _ a).
      {
      unfold subtype.
      apply (tr_subtype_eta2 _ _ _ (ppi2 m) (ppi2 m)).
      eapply tr_prod_elim2; eauto.
      }

      {
      unfold subtype.
      apply (tr_subtype_eta2 _ _ _ (ppi1 m) (ppi1 m)).
      eapply tr_prod_elim1; eauto.
      }
    cbn [List.app].
    apply (tr_subtype_formation_invert1 _ _ _ b b).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim2; eauto.
    }
  }
Qed.


Lemma unionEeq_valid : unionEeq_obligation.
Proof.
prepare.
intros G a a' b b' m n Ha Hb.
apply tr_prod_intro.
  {
  apply tr_union_sub.
    {
    unfold dsubtype.
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }

    {
    unfold dsubtype.
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }

    {
    apply (tr_subtype_convert_hyp' _ [] _ a).
      {
      unfold subtype.
      eapply tr_subtype_eta2.
      eapply tr_prod_elim2; eauto.
      }

      {
      unfold subtype.
      eapply tr_subtype_eta2.
      eapply tr_prod_elim1; eauto.
      }
    cbn [List.app].
    apply (tr_subtype_formation_invert1 _ _ _ b b).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim2; eauto.
    }
  }

  {
  apply tr_union_sub.
    {
    unfold dsubtype.
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }

    {
    unfold dsubtype.
    apply (tr_subtype_convert_hyp' _ [] _ a).
      {
      unfold subtype.
      eapply tr_subtype_eta2.
      eapply tr_prod_elim2; eauto.
      }

      {
      unfold subtype.
      eapply tr_subtype_eta2.
      eapply tr_prod_elim1; eauto.
      }
    cbn [List.app].
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }

    {
    apply (tr_subtype_formation_invert1 _ _ _ b' b').
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim1; eauto.
    }
  }
Qed.


Lemma compatGuardEeq1_valid : compatGuardEeq1_obligation.
Proof.
prepare.
intros G a b b' ext1 m Ha Hb.
assert (tr G (deqtype (guard a b) (guard a b))) as Hform.
  {
  apply tr_guard_formation; auto.
  apply (weakening _ [_] []).
    {
    simpsub.
    reflexivity.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  eapply tr_subtype_istype1.
  eapply tr_subtype_eta2.
  eapply tr_prod_elim1; eauto.
  }
assert (tr G (deqtype (guard a b') (guard a b'))) as Hform'.
  {
  apply tr_guard_formation; auto.
  apply (weakening _ [_] []).
    {
    simpsub.
    reflexivity.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  eapply tr_subtype_istype1.
  eapply tr_subtype_eta2.
  eapply tr_prod_elim2; eauto.
  }
apply tr_prod_intro.
  {
  apply tr_subtype_intro; auto.
  simpsub.
  apply tr_guard_intro.
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    exact Ha.
    }
  simpsub.
  cbn [Nat.add].
  apply (tr_subtype_elim _ (subst (sh 2) b)).
    {
    apply (weakening _ [_; _] []).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }
    
    {
    apply (tr_guard_elim _ (subst (sh 2) a) _ _ _ (var 0) (var 0)).
      {
      eapply hypothesis; eauto using index_S, index_0.
      }

      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
    }
  }

  {
  apply tr_subtype_intro; auto.
  simpsub.
  apply tr_guard_intro.
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    exact Ha.
    }
  simpsub.
  cbn [Nat.add].
  apply (tr_subtype_elim _ (subst (sh 2) b')).
    {
    apply (weakening _ [_; _] []).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }
    
    {
    apply (tr_guard_elim _ (subst (sh 2) a) _ _ _ (var 0) (var 0)).
      {
      eapply hypothesis; eauto using index_S, index_0.
      }

      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
    }
  }
Qed.


Lemma compatSetEeq0_valid : compatSetEeq0_obligation.
Proof.
prepare.
intros G a a' b m ext0 Ha Hb.
assert (tr (hyp_tm a' :: G) (deqtype b b)) as Hb'.
  {
  apply (tr_subtype_convert_hyp G [] _ a).
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }

    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }
  cbn [List.app].
  exact Hb.
  }
assert (tr G (deqtype (set a b) (set a b))) as Hform.
  {
  apply (tr_set_formation _#5 (var 0) (var 0)); eauto.
    {
    eapply tr_subtype_istype1.
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }

    {
    eapply hypothesis; eauto using index_0.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }
assert (tr G (deqtype (set a' b) (set a' b))) as Hform'.
  {
  apply (tr_set_formation _#5 (var 0) (var 0)); eauto.
    {
    eapply tr_subtype_istype1.
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }

    {
    eapply hypothesis; eauto using index_0.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }
apply tr_prod_intro.
  {
  apply tr_subtype_intro; auto.
  simpsub.
  cbn [Nat.add].
  apply (tr_set_elim2 _ (subst sh1 a) (subst (dot (var 0) (sh 2)) b) (var 0)).
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    apply (weakening _ [_] [_]).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    rewrite -> subst_var0_sh1.
    exact Hb.
    }

    {
    simpsub.
    cbn [Nat.add].
    apply (tr_set_intro _#5 (var 0)).
      {
      apply (tr_subtype_elim _ (subst (sh 2) a)).
        {
        apply (weakening _ [_; _] []).
          {
          cbn [length unlift].
          simpsub.
          reflexivity.
          }
    
          {
          cbn [length unlift].
          simpsub.
          reflexivity.
          }
        cbn [length unlift].
        simpsub.
        cbn [List.app].
        eapply tr_subtype_eta2.
        eapply tr_prod_elim1; eauto.
        }

        {
        apply (tr_set_elim1 _ _ (subst (dot (var 0) (sh 3)) b)).
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        reflexivity.
        }
      }

      {
      simpsub.
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }

      {
      apply (weakening _ [_; _] [_]).
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
  
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
      cbn [length unlift].
      simpsub.
      cbn [List.app].
      rewrite -> subst_var0_sh1.
      exact Hb'.
      }
    }
  }

  {
  apply tr_subtype_intro; auto.
  simpsub.
  cbn [Nat.add].
  apply (tr_set_elim2 _ (subst sh1 a') (subst (dot (var 0) (sh 2)) b) (var 0)).
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    apply (weakening _ [_] [_]).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    rewrite -> subst_var0_sh1.
    exact Hb'.
    }

    {
    simpsub.
    cbn [Nat.add].
    apply (tr_set_intro _#5 (var 0)).
      {
      apply (tr_subtype_elim _ (subst (sh 2) a')).
        {
        apply (weakening _ [_; _] []).
          {
          cbn [length unlift].
          simpsub.
          reflexivity.
          }
    
          {
          cbn [length unlift].
          simpsub.
          reflexivity.
          }
        cbn [length unlift].
        simpsub.
        cbn [List.app].
        eapply tr_subtype_eta2.
        eapply tr_prod_elim2; eauto.
        }

        {
        apply (tr_set_elim1 _ _ (subst (dot (var 0) (sh 3)) b)).
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        reflexivity.
        }
      }

      {
      simpsub.
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }

      {
      apply (weakening _ [_; _] [_]).
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
  
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
      cbn [length unlift].
      simpsub.
      cbn [List.app].
      rewrite -> subst_var0_sh1.
      exact Hb.
      }
    }
  }
Qed.


Lemma compatIsetEeq0_valid : compatIsetEeq0_obligation.
Proof.
prepare.
intros G a a' b m ext0 Ha Hb.
assert (tr (hyp_tm a' :: G) (deqtype b b)) as Hb'.
  {
  apply (tr_subtype_convert_hyp G [] _ a).
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }

    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }
  cbn [List.app].
  exact Hb.
  }
assert (tr G (deqtype (iset a b) (iset a b))) as Hform.
  {
  apply tr_iset_formation; eauto.
    {
    eapply tr_subtype_istype1.
    eapply tr_subtype_eta2.
    eapply tr_prod_elim1; eauto.
    }
  }
assert (tr G (deqtype (iset a' b) (iset a' b))) as Hform'.
  {
  apply tr_iset_formation; eauto.
    {
    eapply tr_subtype_istype1.
    eapply tr_subtype_eta2.
    eapply tr_prod_elim2; eauto.
    }
  }
apply tr_prod_intro.
  {
  apply tr_subtype_intro; auto.
  simpsub.
  cbn [Nat.add].
  apply (tr_iset_elim2 _ (subst sh1 a) (subst (dot (var 0) (sh 2)) b) (var 0)).
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    simpsub.
    cbn [Nat.add].
    apply (tr_iset_intro _#5 (var 0)).
      {
      apply (tr_subtype_elim _ (subst (sh 2) a)).
        {
        apply (weakening _ [_; _] []).
          {
          cbn [length unlift].
          simpsub.
          reflexivity.
          }
    
          {
          cbn [length unlift].
          simpsub.
          reflexivity.
          }
        cbn [length unlift].
        simpsub.
        cbn [List.app].
        eapply tr_subtype_eta2.
        eapply tr_prod_elim1; eauto.
        }

        {
        apply (tr_iset_elim1 _ _ (subst (dot (var 0) (sh 3)) b)).
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        reflexivity.
        }
      }

      {
      simpsub.
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }

      {
      apply (weakening _ [_; _] [_]).
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
  
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
      cbn [length unlift].
      simpsub.
      cbn [List.app].
      rewrite -> subst_var0_sh1.
      exact Hb'.
      }
    }
  }

  {
  apply tr_subtype_intro; auto.
  simpsub.
  cbn [Nat.add].
  apply (tr_iset_elim2 _ (subst sh1 a') (subst (dot (var 0) (sh 2)) b) (var 0)).
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    simpsub.
    cbn [Nat.add].
    apply (tr_iset_intro _#5 (var 0)).
      {
      apply (tr_subtype_elim _ (subst (sh 2) a')).
        {
        apply (weakening _ [_; _] []).
          {
          cbn [length unlift].
          simpsub.
          reflexivity.
          }
    
          {
          cbn [length unlift].
          simpsub.
          reflexivity.
          }
        cbn [length unlift].
        simpsub.
        cbn [List.app].
        eapply tr_subtype_eta2.
        eapply tr_prod_elim2; eauto.
        }

        {
        apply (tr_iset_elim1 _ _ (subst (dot (var 0) (sh 3)) b)).
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        reflexivity.
        }
      }

      {
      simpsub.
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }

      {
      apply (weakening _ [_; _] [_]).
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
  
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
      cbn [length unlift].
      simpsub.
      cbn [List.app].
      rewrite -> subst_var0_sh1.
      exact Hb.
      }
    }
  }
Qed.


Lemma compatIsetIff1_valid : compatIsetIff1_obligation.
Proof.
prepare.
intros G a b b' ext1 m Ha Hb.
assert (tr G (deqtype (iset a b) (iset a b))) as Hform.
  {
  apply tr_iset_formation; auto.
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation.
  eapply tr_prod_elim1; eauto.
  }
assert (tr G (deqtype (iset a b') (iset a b'))) as Hform'.
  {
  apply tr_iset_formation; auto.
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation.
  eapply tr_prod_elim2; eauto.
  }
apply tr_prod_intro.
  {
  apply tr_subtype_intro; auto.
  simpsub.
  cbn [Nat.add].
  apply (tr_iset_elim2 _ (subst sh1 a) (subst (dot (var 0) (sh 2)) b) (var 0)).
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    simpsub.
    cbn [Nat.add].
    apply (tr_iset_intro _#5 (app (subst sh1 (ppi1 m)) (var 0))).
      {
      apply (tr_iset_elim1 _ _ (subst (dot (var 0) (sh 3)) b)).
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      reflexivity.
      }

      {
      simpsub.
      eapply (tr_pi_elim' _ (subst sh1 b) (subst (sh 2) b')).
        {
        apply (weakening _ [_] []).
          {
          cbn [length unlift].
          simpsub.
          reflexivity.
          }
    
          {
          cbn [length unlift].
          simpsub.
          reflexivity.
          }
        cbn [length unlift].
        simpsub.
        cbn [List.app].
        replace (deq (ppi1 m) (ppi1 m) (pi b (subst sh1 b'))) with (substj (dot (var 0) id) (deq (ppi1 (subst (dot (var 0) (sh 2)) m)) (ppi1 (subst (dot (var 0) (sh 2)) m)) (pi (subst (dot (var 0) (sh 2)) b) (subst (dot (var 1) (sh 3)) b')))).
        2:{
          simpsub.
          rewrite -> !subst_var0_sh1.
          rewrite -> subst_var1_sh2.
          reflexivity.
          }
        apply (tr_generalize _ (subst sh1 a) (var 0)).
          {
          apply (tr_iset_elim1 _ _ (subst (dot (var 0) (sh 2)) b)).
          eapply hypothesis; eauto using index_0.
          simpsub.
          reflexivity.
          }

          {
          apply (weakening _ [_] [_]).
            {
            cbn [length unlift].
            simpsub.
            reflexivity.
            }
      
            {
            cbn [length unlift].
            simpsub.
            reflexivity.
            }
          cbn [length unlift].
          simpsub.
          cbn [List.app].
          cbn [Nat.add].
          rewrite -> !subst_var0_sh1.
          rewrite -> subst_var1_sh2.
          eapply tr_prod_elim1; eauto.
          }
        }

        {
        eapply hypothesis; eauto using index_0.
        simpsub.
        cbn [Nat.add].
        rewrite -> subst_var1_sh2.
        reflexivity.
        }
  
        {
        simpsub.
        rewrite -> subst_var1_sh2.
        reflexivity.
        }
      }

      {
      apply (weakening _ [_; _] [_]).
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
  
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
      cbn [length unlift].
      simpsub.
      cbn [List.app].
      rewrite -> subst_var0_sh1.
      eapply tr_pi_formation_invert1.
      eapply tr_inhabitation_formation.
      eapply tr_prod_elim2; eauto.
      }
    }
  }

  {
  apply tr_subtype_intro; auto.
  simpsub.
  cbn [Nat.add].
  apply (tr_iset_elim2 _ (subst sh1 a) (subst (dot (var 0) (sh 2)) b') (var 0)).
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    simpsub.
    cbn [Nat.add].
    apply (tr_iset_intro _#5 (app (subst sh1 (ppi2 m)) (var 0))).
      {
      apply (tr_iset_elim1 _ _ (subst (dot (var 0) (sh 3)) b')).
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      reflexivity.
      }

      {
      simpsub.
      eapply (tr_pi_elim' _ (subst sh1 b') (subst (sh 2) b)).
        {
        apply (weakening _ [_] []).
          {
          cbn [length unlift].
          simpsub.
          reflexivity.
          }
    
          {
          cbn [length unlift].
          simpsub.
          reflexivity.
          }
        cbn [length unlift].
        simpsub.
        cbn [List.app].
        replace (deq (ppi2 m) (ppi2 m) (pi b' (subst sh1 b))) with (substj (dot (var 0) id) (deq (ppi2 (subst (dot (var 0) (sh 2)) m)) (ppi2 (subst (dot (var 0) (sh 2)) m)) (pi (subst (dot (var 0) (sh 2)) b') (subst (dot (var 1) (sh 3)) b)))).
        2:{
          simpsub.
          rewrite -> !subst_var0_sh1.
          rewrite -> subst_var1_sh2.
          reflexivity.
          }
        apply (tr_generalize _ (subst sh1 a) (var 0)).
          {
          apply (tr_iset_elim1 _ _ (subst (dot (var 0) (sh 2)) b')).
          eapply hypothesis; eauto using index_0.
          simpsub.
          reflexivity.
          }

          {
          apply (weakening _ [_] [_]).
            {
            cbn [length unlift].
            simpsub.
            reflexivity.
            }
      
            {
            cbn [length unlift].
            simpsub.
            reflexivity.
            }
          cbn [length unlift].
          simpsub.
          cbn [List.app].
          cbn [Nat.add].
          rewrite -> !subst_var0_sh1.
          rewrite -> subst_var1_sh2.
          eapply tr_prod_elim2; eauto.
          }
        }

        {
        eapply hypothesis; eauto using index_0.
        simpsub.
        cbn [Nat.add].
        rewrite -> subst_var1_sh2.
        reflexivity.
        }
  
        {
        simpsub.
        rewrite -> subst_var1_sh2.
        reflexivity.
        }
      }

      {
      apply (weakening _ [_; _] [_]).
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
  
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
      cbn [length unlift].
      simpsub.
      cbn [List.app].
      rewrite -> subst_var0_sh1.
      eapply tr_pi_formation_invert1.
      eapply tr_inhabitation_formation.
      eapply tr_prod_elim1; eauto.
      }
    }
  }
Qed.


Lemma compatForallSubtype0_valid : compatForallSubtype0_obligation.
Proof.
prepare.
intros G a a' b ext1 ext0 Ha Hb.
apply tr_pi_sub; auto.
replace (dsubtype b b) with (substj (dot (var 0) id) (dsubtype (subst (dot (var 0) (sh 2)) b) (subst (dot (var 0) (sh 2)) b))).
2:{
  simpsub.
  rewrite -> subst_var0_sh1.
  reflexivity.
  }
apply (tr_generalize _ (subst sh1 a)).
  {
  apply (tr_subtype_elim _ (subst sh1 a')); auto.
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length].
      simpsub.
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    exact Ha.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }

  {
  apply (weakening _ [_] [_]).
    {
    simpsub.
    reflexivity.
    }

    {
    cbn [length].
    simpsub.
    rewrite <- compose_assoc.
    unfold sh1.
    rewrite -> compose_sh_unlift.
    simpsub.
    reflexivity.
    }
  cbn [length].
  simpsub.
  rewrite <- compose_assoc.
  unfold sh1.
  rewrite -> compose_sh_unlift.
  simpsub.
  cbn [List.app].
  rewrite -> subst_var0_sh1.
  apply tr_subtype_refl; auto.
  }
Qed.


Lemma compatForallSubtype1_valid : compatForallSubtype1_obligation.
Proof.
prepare.
intros G a b b' ext1 ext0 Ha Hb.
apply tr_pi_sub; auto.
  {
  apply tr_subtype_refl; auto.
  }
  
  {
  eapply tr_subtype_istype1; eauto.
  }
Qed.


Lemma compatExistsSubtype0_valid : compatExistsSubtype0_obligation.
Proof.
prepare.
intros G a a' b ext1 ext0 Ha Hb.
apply tr_sigma_sub; auto.
replace (dsubtype b b) with (substj (dot (var 0) id) (dsubtype (subst (dot (var 0) (sh 2)) b) (subst (dot (var 0) (sh 2)) b))).
2:{
  simpsub.
  rewrite -> subst_var0_sh1.
  reflexivity.
  }
apply (tr_generalize _ (subst sh1 a')).
  {
  apply (tr_subtype_elim _ (subst sh1 a)); auto.
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length].
      simpsub.
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    exact Ha.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }

  {
  apply (weakening _ [_] [_]).
    {
    simpsub.
    reflexivity.
    }

    {
    cbn [length].
    simpsub.
    rewrite <- compose_assoc.
    unfold sh1.
    rewrite -> compose_sh_unlift.
    simpsub.
    reflexivity.
    }
  cbn [length].
  simpsub.
  rewrite <- compose_assoc.
  unfold sh1.
  rewrite -> compose_sh_unlift.
  simpsub.
  cbn [List.app].
  rewrite -> subst_var0_sh1.
  apply tr_subtype_refl; auto.
  }
Qed.


Lemma compatExistsSubtype1_valid : compatExistsSubtype1_obligation.
Proof.
prepare.
intros G a b b' ext1 ext0 Ha Hb.
apply tr_sigma_sub; auto.
  {
  apply tr_subtype_refl; auto.
  }
  
  {
  eapply tr_subtype_istype2; eauto.
  }
Qed.


Lemma compatIntersectSubtype0_valid : compatIntersectSubtype0_obligation.
Proof.
prepare.
intros G a a' b ext1 ext0 Ha Hb.
apply tr_intersect_sub; auto.
  {
  eapply tr_subtype_convert_hyp_last; eauto.
  apply tr_subtype_refl; auto.
  }
Qed.


Lemma compatIntersectSubtype1_valid : compatIntersectSubtype1_obligation.
Proof.
prepare.
intros G a b b' ext1 ext0 Ha Hb.
apply tr_intersect_sub; auto.
  {
  apply tr_subtype_refl; auto.
  }

  {
  eapply tr_subtype_istype1; eauto.
  }
Qed.


Lemma compatUnionSubtype0_valid : compatUnionSubtype0_obligation.
Proof.
prepare.
intros G a a' b ext1 ext0 Ha Hb.
apply tr_union_sub; auto.
  {
  eapply tr_subtype_convert_hyp_last; eauto.
  apply tr_subtype_refl; auto.
  }
Qed.


Lemma compatUnionSubtype1_valid : compatUnionSubtype1_obligation.
Proof.
prepare.
intros G a b b' ext1 ext0 Ha Hb.
apply tr_union_sub; auto.
  {
  apply tr_subtype_refl; auto.
  }

  {
  eapply tr_subtype_istype2; eauto.
  }
Qed.


Lemma compatGuardArrow0_valid : compatGuardArrow0_obligation.
Proof.
prepare.
intros G a a' b ext2 ext1 m Ha Hb Hm.
apply tr_subtype_intro.
  {
  apply tr_guard_formation; auto.
  apply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  exact Hb.
  }

  {
  apply tr_guard_formation.
    {
    eapply tr_pi_formation_invert1.
    eapply tr_inhabitation_formation; eauto.
    }
  apply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  exact Hb.
  }
simpsub.
apply tr_guard_intro.
  {
  apply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation; eauto.
  }
simpsub.
cbn [Nat.add].
apply (tr_guard_elim _ (subst (sh 2) a) _ _ _ (app (subst (sh 2) m) (var 0)) (app (subst (sh 2) m) (var 0))).
  {
  eapply hypothesis; eauto using index_S, index_0.
  }

  {
  apply (tr_pi_elim' _ (subst (sh 2) a') (subst (sh 3) a)).
    {
    apply (weakening _ [_; _] []).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    exact Hm.
    }

    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    simpsub.
    reflexivity.
    }
  }
Qed.


Lemma compatGuardSubtype1_valid : compatGuardSubtype1_obligation.
Proof.
prepare.
intros G a b b' ext1 ext0 Ha Hb.
apply tr_subtype_intro.
  {
  apply tr_guard_formation; auto.
  apply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  eapply tr_subtype_istype1; eauto.
  }

  {
  apply tr_guard_formation; auto.
  apply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  eapply tr_subtype_istype2; eauto.
  }
simpsub.
apply tr_guard_intro.
  {
  apply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  exact Ha.
  }
simpsub.
cbn [Nat.add].
apply (tr_subtype_elim _ (subst (sh 2) b)).
  {
  apply (weakening _ [_; _] []).
    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  exact Hb.
  }
apply (tr_guard_elim _ (subst (sh 2) a) _ _ _ (var 0) (var 0)).
  {
  eapply hypothesis; eauto using index_S, index_0.
  }

  {
  eapply hypothesis; eauto using index_0.
  simpsub.
  reflexivity.
  }
Qed.


Lemma compatSetSubtype0_valid : compatSetSubtype0_obligation.
Proof.
prepare.
intros G a a' b ext1 ext0 Ha Hb'.
assert (tr (hyp_tm a :: G) (deqtype b b)) as Hb.
  {
  apply (tr_subtype_convert_hyp_last _ _ a'); auto.
  }
assert (tr G (deqtype (set a b) (set a b))) as Hform.
  {
  apply (tr_set_formation _#5 (var 0) (var 0)); eauto.
    {
    eapply tr_subtype_istype1; eauto.
    }

    {
    eapply hypothesis; eauto using index_0.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }
assert (tr G (deqtype (set a' b) (set a' b))) as Hform'.
  {
  apply (tr_set_formation _#5 (var 0) (var 0)); eauto.
    {
    eapply tr_subtype_istype2; eauto.
    }

    {
    eapply hypothesis; eauto using index_0.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }
apply tr_subtype_intro; auto.
simpsub.
cbn [Nat.add].
apply (tr_set_elim2 _ (subst sh1 a) (subst (dot (var 0) (sh 2)) b) (var 0)).
  {
  eapply hypothesis; eauto using index_0.
  simpsub.
  reflexivity.
  }

  {
  apply (weakening _ [_] [_]).
    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  rewrite -> subst_var0_sh1.
  exact Hb.
  }

  {
  simpsub.
  cbn [Nat.add].
  apply (tr_set_intro _#5 (var 0)).
    {
    apply (tr_subtype_elim _ (subst (sh 2) a)).
      {
      apply (weakening _ [_; _] []).
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
  
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
      cbn [length unlift].
      simpsub.
      cbn [List.app].
      exact Ha.
      }

      {
      apply (tr_set_elim1 _ _ (subst (dot (var 0) (sh 3)) b)).
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      reflexivity.
      }
    }

    {
    simpsub.
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    apply (weakening _ [_; _] [_]).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    rewrite -> subst_var0_sh1.
    exact Hb'.
    }
  }
Qed.


Lemma compatSetArrow1_valid : compatSetArrow1_obligation.
Proof.
prepare.
intros G a b b' ext2 ext1 m Ha Hb' Hm.
assert (tr (hyp_tm a :: G) (deqtype b b)) as Hb.
  {
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation; eauto.
  }
assert (tr G (deqtype (set a b) (set a b))) as Hform.
  {
  apply (tr_set_formation _#5 (var 0) (var 0)); eauto.
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }
assert (tr G (deqtype (set a b') (set a b'))) as Hform'.
  {
  apply (tr_set_formation _#5 (var 0) (var 0)); eauto.
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }
apply tr_subtype_intro; auto.
simpsub.
cbn [Nat.add].
apply (tr_set_elim2 _ (subst sh1 a) (subst (under 1 sh1) b) (var 0)).
  {
  eapply hypothesis; auto using index_0.
  simpsub.
  reflexivity.
  }

  {
  apply (weakening _ [_] [_]).
    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  rewrite -> subst_var0_sh1.
  exact Hb.
  }

  {
  simpsub.
  cbn [Nat.add].
  rewrite -> subst_var0_sh1.
  apply (tr_set_hyp_weaken _ []).
  cbn [List.app].
  apply (tr_set_intro _#5 (app (subst sh1 m) (var 0))).
    {
    eapply hypothesis; eauto using index_S, index_0.
    }

    {
    apply (tr_pi_elim' _ (subst sh1 b) (subst (sh 2) b')).
      {
      apply (weakening _ [_] []).
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
  
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
      cbn [length unlift].
      simpsub.
      cbn [List.app].
      exact Hm.
      }

      {
      eapply hypothesis; eauto using index_S, index_0.
      }

      {
      simpsub.
      rewrite -> subst_var1_sh2.
      reflexivity.
      }
    }

    {
    apply (weakening _ [_; _] [_]).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    rewrite -> subst_var0_sh1.
    exact Hb'.
    }
  }
Qed.


Lemma compatIsetSubtype0_valid : compatIsetSubtype0_obligation.
Proof.
prepare.
intros G a a' b ext1 ext0 Ha Hb'.
assert (tr (hyp_tm a :: G) (deqtype b b)) as Hb.
  {
  apply (tr_subtype_convert_hyp_last _ _ a'); auto.
  }
assert (tr G (deqtype (iset a b) (iset a b))) as Hform.
  {
  apply tr_iset_formation; auto.
  eapply tr_subtype_istype1; eauto.
  }
assert (tr G (deqtype (iset a' b) (iset a' b))) as Hform'.
  {
  apply tr_iset_formation; auto.
  eapply tr_subtype_istype2; eauto.
  }
apply tr_subtype_intro; auto.
simpsub.
cbn [Nat.add].
apply (tr_iset_elim2 _ (subst sh1 a) (subst (dot (var 0) (sh 2)) b) (var 0)).
  {
  eapply hypothesis; eauto using index_0.
  simpsub.
  reflexivity.
  }

  {
  simpsub.
  cbn [Nat.add].
  apply (tr_iset_intro _#5 (var 0)).
    {
    apply (tr_subtype_elim _ (subst (sh 2) a)).
      {
      apply (weakening _ [_; _] []).
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
  
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
      cbn [length unlift].
      simpsub.
      cbn [List.app].
      exact Ha.
      }

      {
      apply (tr_iset_elim1 _ _ (subst (dot (var 0) (sh 3)) b)).
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      reflexivity.
      }
    }

    {
    simpsub.
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    apply (weakening _ [_; _] [_]).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    rewrite -> subst_var0_sh1.
    exact Hb'.
    }
  }
Qed.


Lemma compatIsetArrow1_valid : compatIsetArrow1_obligation.
Proof.
prepare.
intros G a b b' ext2 ext1 m Ha Hb' Hm.
assert (tr (hyp_tm a :: G) (deqtype b b)) as Hb.
  {
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation; eauto.
  }
assert (tr G (deqtype (iset a b) (iset a b))) as Hform.
  {
  apply tr_iset_formation; eauto.
  }
assert (tr G (deqtype (iset a b') (iset a b'))) as Hform'.
  {
  apply tr_iset_formation; eauto.
  }
apply tr_subtype_intro; auto.
simpsub.
cbn [Nat.add].
apply (tr_iset_elim2 _ (subst sh1 a) (subst (under 1 sh1) b) (var 0)).
  {
  eapply hypothesis; auto using index_0.
  simpsub.
  reflexivity.
  }

  {
  simpsub.
  cbn [Nat.add].
  rewrite -> subst_var0_sh1.
  apply (tr_iset_hyp_weaken _ []).
  cbn [List.app].
  apply (tr_iset_intro _#5 (app (subst sh1 m) (var 0))).
    {
    eapply hypothesis; eauto using index_S, index_0.
    }

    {
    apply (tr_pi_elim' _ (subst sh1 b) (subst (sh 2) b')).
      {
      apply (weakening _ [_] []).
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
  
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
      cbn [length unlift].
      simpsub.
      cbn [List.app].
      exact Hm.
      }

      {
      eapply hypothesis; eauto using index_S, index_0.
      }

      {
      simpsub.
      rewrite -> subst_var1_sh2.
      reflexivity.
      }
    }

    {
    apply (weakening _ [_; _] [_]).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    rewrite -> subst_var0_sh1.
    exact Hb'.
    }
  }
Qed.


Lemma compatForallIff1_valid : compatForallIff1_obligation.
Proof.
prepare.
intros G a b b' ext0 m Ha Hm.
simpsub.
cbn [Nat.add].
apply tr_prod_intro.
  {
  apply tr_pi_intro.
    {
    apply tr_pi_formation; auto.
    apply (tr_pi_formation_invert1 _ _ _ (subst sh1 b') (subst sh1 b')).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim1; eauto.
    }
  apply tr_pi_intro.
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    exact Ha.
    }
  eapply (tr_pi_elim' _ (subst (dot (var 0) (sh 2)) b) (subst (dot (var 1) (sh 3)) b')).
    {
    apply (weakening _ [_] [_]).
      {
      cbn [length].
      simpsub.
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      cbn [Nat.add].
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app Nat.add].
    rewrite <- !compose_assoc.
    unfold sh1.
    rewrite -> !compose_sh_unlift.
    simpsub.
    rewrite -> !subst_var0_sh1.
    rewrite <- (subst_var0_sh1 _ b') in Hm.
    simpsubin Hm.
    eapply tr_prod_elim1; eauto.
    }
  
    {
    eapply tr_pi_elim'.
      {
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      cbn [Nat.add].
      reflexivity.
      }
  
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
  
      {
      simpsub.
      reflexivity.
      }
    }
  
    {
    simpsub.
    reflexivity.
    }
  }

  {
  apply tr_pi_intro.
    {
    apply tr_pi_formation; auto.
    apply (tr_pi_formation_invert1 _ _ _ (subst sh1 b) (subst sh1 b)).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim2; eauto.
    }
  apply tr_pi_intro.
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    exact Ha.
    }
  eapply (tr_pi_elim' _ (subst (dot (var 0) (sh 2)) b') (subst (dot (var 1) (sh 3)) b)).
    {
    apply (weakening _ [_] [_]).
      {
      cbn [length].
      simpsub.
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      cbn [Nat.add].
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app Nat.add].
    rewrite <- !compose_assoc.
    unfold sh1.
    rewrite -> !compose_sh_unlift.
    simpsub.
    rewrite -> !subst_var0_sh1.
    rewrite <- (subst_var0_sh1 _ b) in Hm.
    simpsubin Hm.
    eapply tr_prod_elim2; eauto.
    }
  
    {
    eapply tr_pi_elim'.
      {
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      cbn [Nat.add].
      reflexivity.
      }
  
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
  
      {
      simpsub.
      reflexivity.
      }
    }
  
    {
    simpsub.
    reflexivity.
    }
  }
Qed.


Lemma compatExistsIff1_valid : compatExistsIff1_obligation.
Proof.
prepare.
intros G a b b' ext0 m Ha Hm.
apply tr_prod_intro.
  {
  apply tr_pi_intro.
    {
    apply tr_sigma_formation; auto.
    apply (tr_pi_formation_invert1 _ _ _ (subst sh1 b') (subst sh1 b')).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim1; eauto.
    }
  simpsub.
  apply tr_sigma_intro.
    {
    eapply tr_sigma_elim1.
    eapply hypothesis; eauto using index_0.
    simpsub.
    cbn [Nat.add].
    reflexivity.
    }
  
    {
    simpsub.
    eapply (tr_pi_elim' _ (subst (dot (ppi1 (var 0)) (sh 1)) b) (subst (dot (ppi1 (var 1)) (sh 2)) b')).
      {
      exploit (tr_generalize (hyp_tm (sigma a b) :: G) (subst sh1 a) (ppi1 (var 0)) (substj (dot (var 0) (sh 2)) (deq (ppi1 m) (ppi1 m) (pi b (subst sh1 b'))))) as H.
        {
        eapply tr_sigma_elim1.
        eapply hypothesis; eauto using index_0.
        simpsub.
        cbn [Nat.add].
        reflexivity.
        }
  
        {
        apply (weakening _ [_] [_]).
          {
          cbn [length].
          simpsub.
          rewrite <- compose_assoc.
          unfold sh1.
          rewrite -> compose_sh_unlift.
          simpsub.
          reflexivity.
          }
      
          {
          cbn [length].
          simpsub.
          cbn [Nat.add].
          rewrite <- !compose_assoc.
          unfold sh1.
          rewrite -> !compose_sh_unlift.
          simpsub.
          reflexivity.
          }
        cbn [length].
        simpsub.
        cbn [List.app Nat.add].
        rewrite <- !compose_assoc.
        unfold sh1.
        rewrite -> !compose_sh_unlift.
        simpsub.
        rewrite -> !subst_var0_sh1.
        rewrite <- (subst_var0_sh1 _ b') in Hm.
        simpsubin Hm.
        cbn [Nat.add] in Hm |- *.
        eapply tr_prod_elim1; eauto.
        }
      simpsubin H.
      exact H.
      }
  
      {
      eapply tr_sigma_elim2'.
        {
        eapply hypothesis; eauto using index_0.
        simpsub.
        cbn [Nat.add].
        reflexivity.
        }
  
        {
        simpsub.
        reflexivity.
        }
      }
  
      {
      simpsub.
      reflexivity.
      }
    }
  
    {
    apply (weakening _ [_] [_]).
      {
      cbn [length].
      simpsub.
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      cbn [Nat.add].
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app Nat.add].
    rewrite <- !compose_assoc.
    unfold sh1.
    rewrite -> !compose_sh_unlift.
    simpsub.
    rewrite -> !subst_var0_sh1.
    rewrite <- (subst_var0_sh1 _ b') in Hm.
    simpsubin Hm.
    eapply tr_pi_formation_invert1.
    eapply tr_inhabitation_formation.
    rewrite -> !subst_var0_sh1 in Hm.
    eapply tr_prod_elim2; eauto.
    }
  }

  {
  apply tr_pi_intro.
    {
    apply tr_sigma_formation; auto.
    apply (tr_pi_formation_invert1 _ _ _ (subst sh1 b) (subst sh1 b)).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim2; eauto.
    }
  simpsub.
  apply tr_sigma_intro.
    {
    eapply tr_sigma_elim1.
    eapply hypothesis; eauto using index_0.
    simpsub.
    cbn [Nat.add].
    reflexivity.
    }
  
    {
    simpsub.
    eapply (tr_pi_elim' _ (subst (dot (ppi1 (var 0)) (sh 1)) b') (subst (dot (ppi1 (var 1)) (sh 2)) b)).
      {
      exploit (tr_generalize (hyp_tm (sigma a b') :: G) (subst sh1 a) (ppi1 (var 0)) (substj (dot (var 0) (sh 2)) (deq (ppi2 m) (ppi2 m) (pi b' (subst sh1 b))))) as H.
        {
        eapply tr_sigma_elim1.
        eapply hypothesis; eauto using index_0.
        simpsub.
        cbn [Nat.add].
        reflexivity.
        }
  
        {
        apply (weakening _ [_] [_]).
          {
          cbn [length].
          simpsub.
          rewrite <- compose_assoc.
          unfold sh1.
          rewrite -> compose_sh_unlift.
          simpsub.
          reflexivity.
          }
      
          {
          cbn [length].
          simpsub.
          cbn [Nat.add].
          rewrite <- !compose_assoc.
          unfold sh1.
          rewrite -> !compose_sh_unlift.
          simpsub.
          reflexivity.
          }
        cbn [length].
        simpsub.
        cbn [List.app Nat.add].
        rewrite <- !compose_assoc.
        unfold sh1.
        rewrite -> !compose_sh_unlift.
        simpsub.
        rewrite -> !subst_var0_sh1.
        rewrite <- (subst_var0_sh1 _ b) in Hm.
        simpsubin Hm.
        cbn [Nat.add] in Hm |- *.
        eapply tr_prod_elim2; eauto.
        }
      simpsubin H.
      exact H.
      }
  
      {
      eapply tr_sigma_elim2'.
        {
        eapply hypothesis; eauto using index_0.
        simpsub.
        cbn [Nat.add].
        reflexivity.
        }
  
        {
        simpsub.
        reflexivity.
        }
      }
  
      {
      simpsub.
      reflexivity.
      }
    }
  
    {
    apply (weakening _ [_] [_]).
      {
      cbn [length].
      simpsub.
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      cbn [Nat.add].
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app Nat.add].
    rewrite <- !compose_assoc.
    unfold sh1.
    rewrite -> !compose_sh_unlift.
    simpsub.
    rewrite -> !subst_var0_sh1.
    rewrite <- (subst_var0_sh1 _ b) in Hm.
    simpsubin Hm.
    eapply tr_pi_formation_invert1.
    eapply tr_inhabitation_formation.
    rewrite -> !subst_var0_sh1 in Hm.
    eapply tr_prod_elim1; eauto.
    }
  }
Qed.


Lemma compatArrowIff0_valid : compatArrowIff0_obligation.
Proof.
prepare.
intros G a a' b ext0 m Hb Hiff.
assert (tr G (deqtype a a)) as Ha.
  {
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation.
  eapply tr_prod_elim1; eauto.
  }
assert (tr G (deqtype a' a')) as Ha'.
  {
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation.
  eapply tr_prod_elim2; eauto.
  }
apply tr_prod_intro.
  {
  apply tr_pi_intro.
    {
    apply tr_pi_formation; auto.
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    exact Hb.
    }
  simpsub.
  apply tr_pi_intro.
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    auto.
    }
  cbn [Nat.add].
  eapply tr_pi_elim'.
    {
    eapply hypothesis; eauto using index_S, index_0.
    simpsub.
    cbn [Nat.add].
    reflexivity.
    }
  
    {
    eapply (tr_pi_elim' _ (subst (sh 2) a') (subst (sh 3) a)).
      {
      apply (weakening _ [_; _] []).
        {
        simpsub.
        reflexivity.
        }
  
        {
        cbn [length].
        simpsub.
        rewrite <- !compose_assoc.
        rewrite -> compose_sh_unlift.
        simpsub.
        cbn [Nat.add].
        reflexivity.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      rewrite <- compose_assoc.
      rewrite -> compose_sh_unlift.
      simpsub.
      eapply tr_prod_elim2; eauto.
      }
  
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
  
      {
      simpsub.
      reflexivity.
      }
    }
  
    {
    simpsub.
    reflexivity.
    }
  }

  {
  apply tr_pi_intro.
    {
    apply tr_pi_formation; auto.
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    exact Hb.
    }
  simpsub.
  apply tr_pi_intro.
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    auto.
    }
  cbn [Nat.add].
  eapply tr_pi_elim'.
    {
    eapply hypothesis; eauto using index_S, index_0.
    simpsub.
    cbn [Nat.add].
    reflexivity.
    }
  
    {
    eapply (tr_pi_elim' _ (subst (sh 2) a) (subst (sh 3) a')).
      {
      apply (weakening _ [_; _] []).
        {
        simpsub.
        reflexivity.
        }
  
        {
        cbn [length].
        simpsub.
        rewrite <- !compose_assoc.
        rewrite -> compose_sh_unlift.
        simpsub.
        cbn [Nat.add].
        reflexivity.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      rewrite <- compose_assoc.
      rewrite -> compose_sh_unlift.
      simpsub.
      eapply tr_prod_elim1; eauto.
      }
  
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
  
      {
      simpsub.
      reflexivity.
      }
    }
  
    {
    simpsub.
    reflexivity.
    }
  }
Qed.


Lemma compatArrowIff1_valid : compatArrowIff1_obligation.
Proof.
prepare.
intros G a b b' ext0 m Ha Hm.
simpsub.
cbn [Nat.add].
apply tr_prod_intro.
  {
  apply tr_pi_intro.
    {
    apply tr_pi_formation; auto.
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    apply (tr_pi_formation_invert1 _ _ _ (subst sh1 b') (subst sh1 b')).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim1; eauto.
    }
  apply tr_pi_intro.
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    exact Ha.
    }
  apply (tr_pi_elim' _ (subst (sh 2) b) (subst (sh 3) b')).
    {
    apply (weakening _ [_; _] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    rewrite <- compose_assoc.
    rewrite -> compose_sh_unlift.
    simpsub.
    eapply tr_prod_elim1; eauto.
    }
  
    {
    eapply tr_pi_elim'.
      {
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      cbn [Nat.add].
      reflexivity.
      }
  
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      cbn [Nat.add].
      reflexivity.
      }
    
      {
      simpsub.
      reflexivity.
      }
    }
    
    {
    simpsub.
    reflexivity.
    }
  }

  {
  apply tr_pi_intro.
    {
    apply tr_pi_formation; auto.
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    apply (tr_pi_formation_invert1 _ _ _ (subst sh1 b) (subst sh1 b)).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim2; eauto.
    }
  apply tr_pi_intro.
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    exact Ha.
    }
  apply (tr_pi_elim' _ (subst (sh 2) b') (subst (sh 3) b)).
    {
    apply (weakening _ [_; _] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    rewrite <- compose_assoc.
    rewrite -> compose_sh_unlift.
    simpsub.
    eapply tr_prod_elim2; eauto.
    }
  
    {
    eapply tr_pi_elim'.
      {
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      cbn [Nat.add].
      reflexivity.
      }
  
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      cbn [Nat.add].
      reflexivity.
      }
    
      {
      simpsub.
      reflexivity.
      }
    }
    
    {
    simpsub.
    reflexivity.
    }
  }
Qed.


Lemma compatProdIff0_valid : compatProdIff0_obligation.
Proof.
prepare.
intros G a a' b ext0 m Hb Hm.
simpsub.
apply tr_prod_intro.
  {
  apply tr_pi_intro.
    {
    apply tr_prod_formation; auto.
    apply (tr_pi_formation_invert1 _ _ _ (subst sh1 a') (subst sh1 a')).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim1; eauto.
    }
  apply tr_prod_intro.
    {
    apply (tr_pi_elim' _ (subst sh1 a) (subst (sh 2) a')).
      {
      apply (weakening _ [_] []).
        {
        simpsub.
        reflexivity.
        }
    
        {
        cbn [length].
        simpsub.
        rewrite <- !compose_assoc.
        unfold sh1.
        rewrite -> !compose_sh_unlift.
        simpsub.
        reflexivity.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      eapply tr_prod_elim1; eauto.
      }
  
      {
      eapply tr_prod_elim1.
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
  
      {
      simpsub.
      reflexivity.
      }
    }
  
    {
    eapply tr_prod_elim2.
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }
  }

  {
  apply tr_pi_intro.
    {
    apply tr_prod_formation; auto.
    apply (tr_pi_formation_invert1 _ _ _ (subst sh1 a) (subst sh1 a)).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim2; eauto.
    }
  apply tr_prod_intro.
    {
    apply (tr_pi_elim' _ (subst sh1 a') (subst (sh 2) a)).
      {
      apply (weakening _ [_] []).
        {
        simpsub.
        reflexivity.
        }
    
        {
        cbn [length].
        simpsub.
        rewrite <- !compose_assoc.
        unfold sh1.
        rewrite -> !compose_sh_unlift.
        simpsub.
        reflexivity.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      eapply tr_prod_elim2; eauto.
      }
  
      {
      eapply tr_prod_elim1.
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
  
      {
      simpsub.
      reflexivity.
      }
    }
  
    {
    eapply tr_prod_elim2.
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }
  }
Qed.


Lemma compatProdIff1_valid : compatProdIff1_obligation.
Proof.
prepare.
intros G a b b' ext0 m Hb Hm.
simpsub.
apply tr_prod_intro.
  {
  apply tr_pi_intro.
    {
    apply tr_prod_formation; auto.
    apply (tr_pi_formation_invert1 _ _ _ (subst sh1 b') (subst sh1 b')).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim1; eauto.
    }
  apply tr_prod_intro.
    {
    eapply tr_prod_elim1.
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }
  
    {
    apply (tr_pi_elim' _ (subst sh1 b) (subst (sh 2) b')).
      {
      apply (weakening _ [_] []).
        {
        simpsub.
        reflexivity.
        }
    
        {
        cbn [length].
        simpsub.
        rewrite <- !compose_assoc.
        unfold sh1.
        rewrite -> !compose_sh_unlift.
        simpsub.
        reflexivity.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      eapply tr_prod_elim1; eauto.
      }
  
      {
      simpsub.
      eapply tr_prod_elim2.
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
      
      {
      simpsub.
      reflexivity.
      }
    }
  }

  {
  apply tr_pi_intro.
    {
    apply tr_prod_formation; auto.
    apply (tr_pi_formation_invert1 _ _ _ (subst sh1 b) (subst sh1 b)).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim2; eauto.
    }
  apply tr_prod_intro.
    {
    eapply tr_prod_elim1.
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }
  
    {
    apply (tr_pi_elim' _ (subst sh1 b') (subst (sh 2) b)).
      {
      apply (weakening _ [_] []).
        {
        simpsub.
        reflexivity.
        }
    
        {
        cbn [length].
        simpsub.
        rewrite <- !compose_assoc.
        unfold sh1.
        rewrite -> !compose_sh_unlift.
        simpsub.
        reflexivity.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      eapply tr_prod_elim2; eauto.
      }
  
      {
      simpsub.
      eapply tr_prod_elim2.
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
      
      {
      simpsub.
      reflexivity.
      }
    }
  }
Qed.


Lemma compatSumIff0_valid : compatSumIff0_obligation.
Proof.
prepare.
intros G a a' b ext0 m Hb Hm.
simpsub.
apply tr_prod_intro.
  {
  apply tr_pi_intro.
    {
    apply tr_sumtype_formation; auto.
    apply (tr_pi_formation_invert1 _ _ _ (subst sh1 a') (subst sh1 a')).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim1; eauto.
    }
  replace (sumtype (subst sh1 a') (subst sh1 b)) with (subst1 (var 0) (sumtype (subst (sh 2) a') (subst (sh 2) b))) by (simpsub; reflexivity).
  eapply tr_sumtype_elim.
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }
  
    {
    simpsub.
    apply tr_sumtype_intro1.
      {
      apply (tr_pi_elim' _ (subst (sh 2) a) (subst (sh 3) a')).
        {
        apply (weakening _ [_; _] []).
          {
          simpsub.
          reflexivity.
          }
      
          {
          cbn [length].
          simpsub.
          rewrite <- !compose_assoc.
          unfold sh1.
          rewrite -> !compose_sh_unlift.
          simpsub.
          reflexivity.
          }
        cbn [length].
        simpsub.
        cbn [List.app].
        rewrite <- compose_assoc.
        unfold sh1.
        rewrite -> compose_sh_unlift.
        simpsub.
        eapply tr_prod_elim1; eauto.
        }
      
        {
        eapply hypothesis; eauto using index_0.
        simpsub.
        reflexivity.
        }
    
        {
        simpsub.
        reflexivity.
        }
      }
  
      {
      apply (weakening _ [_; _] []).
        {
        simpsub.
        reflexivity.
        }
    
        {
        cbn [length].
        simpsub.
        rewrite <- !compose_assoc.
        unfold sh1.
        rewrite -> !compose_sh_unlift.
        simpsub.
        reflexivity.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      exact Hb.
      }
    }
  
    {
    simpsub.
    apply tr_sumtype_intro2.
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
  
      {
      apply (weakening _ [_; _] []).
        {
        simpsub.
        reflexivity.
        }
    
        {
        cbn [length].
        simpsub.
        rewrite <- !compose_assoc.
        unfold sh1.
        rewrite -> !compose_sh_unlift.
        simpsub.
        reflexivity.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      eapply tr_pi_formation_invert1.
      eapply tr_inhabitation_formation.
      eapply tr_prod_elim2; eauto.
      }
    }
  }

  {
  apply tr_pi_intro.
    {
    apply tr_sumtype_formation; auto.
    apply (tr_pi_formation_invert1 _ _ _ (subst sh1 a) (subst sh1 a)).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim2; eauto.
    }
  replace (sumtype (subst sh1 a) (subst sh1 b)) with (subst1 (var 0) (sumtype (subst (sh 2) a) (subst (sh 2) b))) by (simpsub; reflexivity).
  eapply tr_sumtype_elim.
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }
  
    {
    simpsub.
    apply tr_sumtype_intro1.
      {
      apply (tr_pi_elim' _ (subst (sh 2) a') (subst (sh 3) a)).
        {
        apply (weakening _ [_; _] []).
          {
          simpsub.
          reflexivity.
          }
      
          {
          cbn [length].
          simpsub.
          rewrite <- !compose_assoc.
          unfold sh1.
          rewrite -> !compose_sh_unlift.
          simpsub.
          reflexivity.
          }
        cbn [length].
        simpsub.
        cbn [List.app].
        rewrite <- compose_assoc.
        unfold sh1.
        rewrite -> compose_sh_unlift.
        simpsub.
        eapply tr_prod_elim2; eauto.
        }
      
        {
        eapply hypothesis; eauto using index_0.
        simpsub.
        reflexivity.
        }
    
        {
        simpsub.
        reflexivity.
        }
      }
  
      {
      apply (weakening _ [_; _] []).
        {
        simpsub.
        reflexivity.
        }
    
        {
        cbn [length].
        simpsub.
        rewrite <- !compose_assoc.
        unfold sh1.
        rewrite -> !compose_sh_unlift.
        simpsub.
        reflexivity.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      exact Hb.
      }
    }
  
    {
    simpsub.
    apply tr_sumtype_intro2.
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
  
      {
      apply (weakening _ [_; _] []).
        {
        simpsub.
        reflexivity.
        }
    
        {
        cbn [length].
        simpsub.
        rewrite <- !compose_assoc.
        unfold sh1.
        rewrite -> !compose_sh_unlift.
        simpsub.
        reflexivity.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      eapply tr_pi_formation_invert1.
      eapply tr_inhabitation_formation.
      eapply tr_prod_elim1; eauto.
      }
    }
  }
Qed.


Lemma compatSumIff1_valid : compatSumIff1_obligation.
Proof.
prepare.
intros G a b b' ext0 m Ha Hm.
simpsub.
apply tr_prod_intro.
  {
  apply tr_pi_intro.
    {
    apply tr_sumtype_formation; auto.
    apply (tr_pi_formation_invert1 _ _ _ (subst sh1 b') (subst sh1 b')).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim1; eauto.
    }
  replace (sumtype (subst sh1 a) (subst sh1 b')) with (subst1 (var 0) (sumtype (subst (sh 2) a) (subst (sh 2) b'))) by (simpsub; reflexivity).
  eapply tr_sumtype_elim.
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }
  
    {
    simpsub.
    apply tr_sumtype_intro1.
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
  
      {
      apply (weakening _ [_; _] []).
        {
        simpsub.
        reflexivity.
        }
    
        {
        cbn [length].
        simpsub.
        rewrite <- !compose_assoc.
        unfold sh1.
        rewrite -> !compose_sh_unlift.
        simpsub.
        reflexivity.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      eapply tr_pi_formation_invert1.
      eapply tr_inhabitation_formation.
      eapply tr_prod_elim2; eauto.
      }
    }
  
    {
    simpsub.
    apply tr_sumtype_intro2.
      {
      apply (tr_pi_elim' _ (subst (sh 2) b) (subst (sh 3) b')).
        {
        apply (weakening _ [_; _] []).
          {
          simpsub.
          reflexivity.
          }
      
          {
          cbn [length].
          simpsub.
          rewrite <- !compose_assoc.
          unfold sh1.
          rewrite -> !compose_sh_unlift.
          simpsub.
          reflexivity.
          }
        cbn [length].
        simpsub.
        cbn [List.app].
        rewrite <- compose_assoc.
        unfold sh1.
        rewrite -> compose_sh_unlift.
        simpsub.
        eapply tr_prod_elim1; eauto.
        }
      
        {
        eapply hypothesis; eauto using index_0.
        simpsub.
        reflexivity.
        }
    
        {
        simpsub.
        reflexivity.
        }
      }
  
      {
      apply (weakening _ [_; _] []).
        {
        simpsub.
        reflexivity.
        }
    
        {
        cbn [length].
        simpsub.
        rewrite <- !compose_assoc.
        unfold sh1.
        rewrite -> !compose_sh_unlift.
        simpsub.
        reflexivity.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      exact Ha.
      }
    }
  }

  {
  apply tr_pi_intro.
    {
    apply tr_sumtype_formation; auto.
    apply (tr_pi_formation_invert1 _ _ _ (subst sh1 b) (subst sh1 b)).
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim2; eauto.
    }
  replace (sumtype (subst sh1 a) (subst sh1 b)) with (subst1 (var 0) (sumtype (subst (sh 2) a) (subst (sh 2) b))) by (simpsub; reflexivity).
  eapply tr_sumtype_elim.
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }
  
    {
    simpsub.
    apply tr_sumtype_intro1.
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
  
      {
      apply (weakening _ [_; _] []).
        {
        simpsub.
        reflexivity.
        }
    
        {
        cbn [length].
        simpsub.
        rewrite <- !compose_assoc.
        unfold sh1.
        rewrite -> !compose_sh_unlift.
        simpsub.
        reflexivity.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      eapply tr_pi_formation_invert1.
      eapply tr_inhabitation_formation.
      eapply tr_prod_elim1; eauto.
      }
    }
  
    {
    simpsub.
    apply tr_sumtype_intro2.
      {
      apply (tr_pi_elim' _ (subst (sh 2) b') (subst (sh 3) b)).
        {
        apply (weakening _ [_; _] []).
          {
          simpsub.
          reflexivity.
          }
      
          {
          cbn [length].
          simpsub.
          rewrite <- !compose_assoc.
          unfold sh1.
          rewrite -> !compose_sh_unlift.
          simpsub.
          reflexivity.
          }
        cbn [length].
        simpsub.
        cbn [List.app].
        rewrite <- compose_assoc.
        unfold sh1.
        rewrite -> compose_sh_unlift.
        simpsub.
        eapply tr_prod_elim2; eauto.
        }
      
        {
        eapply hypothesis; eauto using index_0.
        simpsub.
        reflexivity.
        }
    
        {
        simpsub.
        reflexivity.
        }
      }
  
      {
      apply (weakening _ [_; _] []).
        {
        simpsub.
        reflexivity.
        }
    
        {
        cbn [length].
        simpsub.
        rewrite <- !compose_assoc.
        unfold sh1.
        rewrite -> !compose_sh_unlift.
        simpsub.
        reflexivity.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      exact Ha.
      }
    }
  }
Qed.


Lemma compatFutureIff_valid : compatFutureIff_obligation.
Proof.
prepare.
intros G a a' m Ha.
apply tr_prod_intro.
  {
  apply tr_pi_intro.
    {
    apply tr_fut_formation.
    eapply tr_pi_formation_invert1; eauto.
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim1; eauto.
    }
  simpsub.
  cut (tr (hyp_tm (fut a) :: G) (substj (dot (prev (var 0)) id) (deq (next (app (subst (sh 2) (ppi1 m)) (var 0))) (next (app (subst (sh 2) (ppi1 m)) (var 0))) (fut (subst (sh 2) a'))))).
    {
   intro H.
   simpsubin H.
   exact H.
   }
  apply (tr_fut_elim _ _ _ (subst sh1 a)); auto.
    {
    eapply hypothesis; eauto using index_0.
    }
  
    {
    cbn [promote map promote_hyp].
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
    eapply tr_pi_formation_invert1.
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim1; eauto.
    }
  
    {
    apply tr_fut_intro.
    cbn [promote map promote_hyp].
    eapply (tr_pi_elim' _ (subst (sh 2) a) (subst (sh 3) a')).
      {
      apply (weakening _ [_; _] []).
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
      eapply tr_prod_elim1; eauto.
      }
  
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
  
  
      {
      simpsub.
      reflexivity.
      }
    }
  }

  {
  apply tr_pi_intro.
    {
    apply tr_fut_formation.
    eapply tr_pi_formation_invert1; eauto.
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim2; eauto.
    }
  simpsub.
  cut (tr (hyp_tm (fut a') :: G) (substj (dot (prev (var 0)) id) (deq (next (app (subst (sh 2) (ppi2 m)) (var 0))) (next (app (subst (sh 2) (ppi2 m)) (var 0))) (fut (subst (sh 2) a))))).
   {
   intro H.
   simpsubin H.
   exact H.
   }
  apply (tr_fut_elim _ _ _ (subst sh1 a')); auto.
    {
    eapply hypothesis; eauto using index_0.
    }
  
    {
    cbn [promote map promote_hyp].
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
    eapply tr_pi_formation_invert1.
    eapply tr_inhabitation_formation.
    eapply tr_prod_elim2; eauto.
    }
  
    {
    apply tr_fut_intro.
    cbn [promote map promote_hyp].
    eapply (tr_pi_elim' _ (subst (sh 2) a') (subst (sh 3) a)).
      {
      apply (weakening _ [_; _] []).
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
      eapply tr_prod_elim2; eauto.
      }
  
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
  
      {
      simpsub.
      reflexivity.
      }
    }
  }
Qed.


Lemma compatForallArrow1_valid : compatForallArrow1_obligation.
Proof.
prepare.
intros G a b b' ext0 m Ha Hm.
simpsub.
cbn [Nat.add].
apply tr_pi_intro.
  {
  apply tr_pi_formation; auto.
  apply (tr_pi_formation_invert1 _ _ _ (subst sh1 b') (subst sh1 b')).
  eapply tr_inhabitation_formation; eauto.
  }
apply tr_pi_intro.
  {
  apply (weakening _ [_] []).
    {
    simpsub.
    reflexivity.
    }

    {
    cbn [length].
    simpsub.
    rewrite <- compose_assoc.
    unfold sh1.
    rewrite -> compose_sh_unlift.
    simpsub.
    reflexivity.
    }
  cbn [length].
  simpsub.
  exact Ha.
  }
eapply (tr_pi_elim' _ (subst (dot (var 0) (sh 2)) b) (subst (dot (var 1) (sh 3)) b')).
  {
  apply (weakening _ [_] [_]).
    {
    cbn [length].
    simpsub.
    rewrite <- compose_assoc.
    unfold sh1.
    rewrite -> compose_sh_unlift.
    simpsub.
    reflexivity.
    }

    {
    cbn [length].
    simpsub.
    cbn [Nat.add].
    rewrite <- !compose_assoc.
    unfold sh1.
    rewrite -> !compose_sh_unlift.
    simpsub.
    reflexivity.
    }
  cbn [length].
  simpsub.
  cbn [List.app Nat.add].
  rewrite <- !compose_assoc.
  unfold sh1.
  rewrite -> !compose_sh_unlift.
  simpsub.
  rewrite -> !subst_var0_sh1.
  rewrite <- (subst_var0_sh1 _ b') in Hm.
  simpsubin Hm.
  exact Hm.
  }

  {
  eapply tr_pi_elim'.
    {
    eapply hypothesis; eauto using index_S, index_0.
    simpsub.
    cbn [Nat.add].
    reflexivity.
    }

    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    simpsub.
    reflexivity.
    }
  }

  {
  simpsub.
  reflexivity.
  }
Qed.


Lemma compatExistsArrow1_valid : compatExistsArrow1_obligation.
Proof.
prepare.
intros G a b b' ext1 ext0 m Ha Hb Hm.
apply tr_pi_intro.
  {
  apply tr_sigma_formation; auto.
  apply (tr_pi_formation_invert1 _ _ _ (subst sh1 b') (subst sh1 b')).
  eapply tr_inhabitation_formation; eauto.
  }
simpsub.
apply tr_sigma_intro.
  {
  eapply tr_sigma_elim1.
  eapply hypothesis; eauto using index_0.
  simpsub.
  cbn [Nat.add].
  reflexivity.
  }

  {
  simpsub.
  eapply (tr_pi_elim' _ (subst (dot (ppi1 (var 0)) (sh 1)) b) (subst (dot (ppi1 (var 1)) (sh 2)) b')).
    {
    exploit (tr_generalize (hyp_tm (sigma a b) :: G) (subst sh1 a) (ppi1 (var 0)) (substj (dot (var 0) (sh 2)) (deq m m (pi b (subst sh1 b'))))) as H.
      {
      eapply tr_sigma_elim1.
      eapply hypothesis; eauto using index_0.
      simpsub.
      cbn [Nat.add].
      reflexivity.
      }

      {
      apply (weakening _ [_] [_]).
        {
        cbn [length].
        simpsub.
        rewrite <- compose_assoc.
        unfold sh1.
        rewrite -> compose_sh_unlift.
        simpsub.
        reflexivity.
        }
    
        {
        cbn [length].
        simpsub.
        cbn [Nat.add].
        rewrite <- !compose_assoc.
        unfold sh1.
        rewrite -> !compose_sh_unlift.
        simpsub.
        reflexivity.
        }
      cbn [length].
      simpsub.
      cbn [List.app Nat.add].
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      rewrite -> !subst_var0_sh1.
      rewrite <- (subst_var0_sh1 _ b') in Hm.
      simpsubin Hm.
      exact Hm.
      }
    simpsubin H.
    exact H.
    }

    {
    eapply tr_sigma_elim2'.
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      cbn [Nat.add].
      reflexivity.
      }

      {
      simpsub.
      reflexivity.
      }
    }

    {
    simpsub.
    reflexivity.
    }
  }

  {
  apply (weakening _ [_] [_]).
    {
    cbn [length].
    simpsub.
    rewrite <- compose_assoc.
    unfold sh1.
    rewrite -> compose_sh_unlift.
    simpsub.
    reflexivity.
    }

    {
    cbn [length].
    simpsub.
    cbn [Nat.add].
    rewrite <- !compose_assoc.
    unfold sh1.
    rewrite -> !compose_sh_unlift.
    simpsub.
    reflexivity.
    }
  cbn [length].
  simpsub.
  cbn [List.app Nat.add].
  rewrite <- !compose_assoc.
  unfold sh1.
  rewrite -> !compose_sh_unlift.
  simpsub.
  rewrite -> !subst_var0_sh1.
  rewrite <- (subst_var0_sh1 _ b') in Hm.
  simpsubin Hm.
  exact Hb.
  }
Qed.


Lemma compatArrowArrow0_valid : compatArrowArrow0_obligation.
Proof.
prepare.
intros G a a' b ext1 ext0 m Ha Hb Hm.
apply tr_pi_intro.
  {
  apply tr_pi_formation; auto.
  apply (weakening _ [_] []).
    {
    simpsub.
    reflexivity.
    }

    {
    cbn [length].
    simpsub.
    rewrite <- compose_assoc.
    unfold sh1.
    rewrite -> compose_sh_unlift.
    simpsub.
    reflexivity.
    }
  cbn [length].
  simpsub.
  cbn [List.app].
  exact Hb.
  }
simpsub.
apply tr_pi_intro.
  {
  apply (weakening _ [_] []).
    {
    simpsub.
    reflexivity.
    }

    {
    cbn [length].
    simpsub.
    rewrite <- compose_assoc.
    unfold sh1.
    rewrite -> compose_sh_unlift.
    simpsub.
    reflexivity.
    }
  cbn [length].
  simpsub.
  cbn [List.app].
  apply (tr_pi_formation_invert1 _ _ _ (subst sh1 a) (subst sh1 a)).
  eapply tr_inhabitation_formation; eauto.
  }
cbn [Nat.add].
eapply tr_pi_elim'.
  {
  eapply hypothesis; eauto using index_S, index_0.
  simpsub.
  cbn [Nat.add].
  reflexivity.
  }

  {
  eapply (tr_pi_elim' _ (subst (sh 2) a') (subst (sh 3) a)).
    {
    apply (weakening _ [_; _] []).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      rewrite -> compose_sh_unlift.
      simpsub.
      cbn [Nat.add].
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    rewrite <- compose_assoc.
    rewrite -> compose_sh_unlift.
    simpsub.
    exact Hm.
    }

    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    simpsub.
    reflexivity.
    }
  }

  {
  simpsub.
  reflexivity.
  }
Qed.


Lemma compatArrowArrow1_valid : compatArrowArrow1_obligation.
Proof.
prepare.
intros G a b b' ext0 m Ha Hm.
simpsub.
cbn [Nat.add].
apply tr_pi_intro.
  {
  apply tr_pi_formation; auto.
  apply (weakening _ [_] []).
    {
    simpsub.
    reflexivity.
    }

    {
    cbn [length].
    simpsub.
    rewrite <- !compose_assoc.
    unfold sh1.
    rewrite -> !compose_sh_unlift.
    simpsub.
    reflexivity.
    }
  cbn [length].
  simpsub.
  cbn [List.app].
  apply (tr_pi_formation_invert1 _ _ _ (subst sh1 b') (subst sh1 b')).
  eapply tr_inhabitation_formation; eauto.
  }
apply tr_pi_intro.
  {
  apply (weakening _ [_] []).
    {
    simpsub.
    reflexivity.
    }

    {
    cbn [length].
    simpsub.
    rewrite <- !compose_assoc.
    unfold sh1.
    rewrite -> !compose_sh_unlift.
    simpsub.
    reflexivity.
    }
  cbn [length].
  simpsub.
  cbn [List.app].
  exact Ha.
  }
apply (tr_pi_elim' _ (subst (sh 2) b) (subst (sh 3) b')).
  {
  apply (weakening _ [_; _] []).
    {
    simpsub.
    reflexivity.
    }

    {
    cbn [length].
    simpsub.
    rewrite <- !compose_assoc.
    unfold sh1.
    rewrite -> !compose_sh_unlift.
    simpsub.
    reflexivity.
    }
  cbn [length].
  simpsub.
  cbn [List.app].
  rewrite <- compose_assoc.
  rewrite -> compose_sh_unlift.
  simpsub.
  exact Hm.
  }

  {
  eapply tr_pi_elim'.
    {
    eapply hypothesis; eauto using index_S, index_0.
    simpsub.
    cbn [Nat.add].
    reflexivity.
    }

    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    cbn [Nat.add].
    reflexivity.
    }
  
    {
    simpsub.
    reflexivity.
    }
  }
  
  {
  simpsub.
  reflexivity.
  }
Qed.


Lemma compatProdArrow0_valid : compatProdArrow0_obligation.
Proof.
prepare.
intros G a a' b ext0 m Hb Hm.
simpsub.
apply tr_pi_intro.
  {
  apply tr_prod_formation; auto.
  apply (tr_pi_formation_invert1 _ _ _ (subst sh1 a') (subst sh1 a')).
  eapply tr_inhabitation_formation; eauto.
  }
apply tr_prod_intro.
  {
  apply (tr_pi_elim' _ (subst sh1 a) (subst (sh 2) a')).
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    rewrite <- compose_assoc.
    unfold sh1.
    rewrite -> compose_sh_unlift.
    simpsub.
    exact Hm.
    }

    {
    eapply tr_prod_elim1.
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    simpsub.
    reflexivity.
    }
  }

  {
  eapply tr_prod_elim2.
  eapply hypothesis; eauto using index_0.
  simpsub.
  reflexivity.
  }
Qed.


Lemma compatProdArrow1_valid : compatProdArrow1_obligation.
Proof.
prepare.
intros G a a' b ext0 m Hb Hm.
simpsub.
apply tr_pi_intro.
  {
  apply tr_prod_formation; auto.
  apply (tr_pi_formation_invert1 _ _ _ (subst sh1 b) (subst sh1 b)).
  eapply tr_inhabitation_formation; eauto.
  }
apply tr_prod_intro.
  {
  eapply tr_prod_elim1.
  eapply hypothesis; eauto using index_0.
  simpsub.
  reflexivity.
  }

  {
  apply (tr_pi_elim' _ (subst sh1 a') (subst (sh 2) b)).
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    rewrite <- compose_assoc.
    unfold sh1.
    rewrite -> compose_sh_unlift.
    simpsub.
    exact Hm.
    }

    {
    simpsub.
    eapply tr_prod_elim2.
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }
    
    {
    simpsub.
    reflexivity.
    }
  }
Qed.


Lemma compatSumArrow0_valid : compatSumArrow0_obligation.
Proof.
prepare.
intros G a a' b ext0 ext1 m Ha' Hb Hm.
simpsub.
apply tr_pi_intro.
  {
  apply tr_sumtype_formation; auto.
  apply (tr_pi_formation_invert1 _ _ _ (subst sh1 a') (subst sh1 a')).
  eapply tr_inhabitation_formation; eauto.
  }
replace (sumtype (subst sh1 a') (subst sh1 b)) with (subst1 (var 0) (sumtype (subst (sh 2) a') (subst (sh 2) b))) by (simpsub; reflexivity).
eapply tr_sumtype_elim.
  {
  eapply hypothesis; eauto using index_0.
  simpsub.
  reflexivity.
  }

  {
  simpsub.
  apply tr_sumtype_intro1.
    {
    apply (tr_pi_elim' _ (subst (sh 2) a) (subst (sh 3) a')).
      {
      apply (weakening _ [_; _] []).
        {
        simpsub.
        reflexivity.
        }
    
        {
        cbn [length].
        simpsub.
        rewrite <- !compose_assoc.
        unfold sh1.
        rewrite -> !compose_sh_unlift.
        simpsub.
        reflexivity.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      exact Hm.
      }
    
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
  
      {
      simpsub.
      reflexivity.
      }
    }

    {
    apply (weakening _ [_; _] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    exact Hb.
    }
  }

  {
  simpsub.
  apply tr_sumtype_intro2.
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    apply (weakening _ [_; _] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    exact Ha'.
    }
  }
Qed.


Lemma compatSumArrow1_valid : compatSumArrow1_obligation.
Proof.
prepare.
intros G a b b' ext0 ext1 m Ha Hb' Hm.
simpsub.
apply tr_pi_intro.
  {
  apply tr_sumtype_formation; auto.
  apply (tr_pi_formation_invert1 _ _ _ (subst sh1 b') (subst sh1 b')).
  eapply tr_inhabitation_formation; eauto.
  }
replace (sumtype (subst sh1 a) (subst sh1 b')) with (subst1 (var 0) (sumtype (subst (sh 2) a) (subst (sh 2) b'))) by (simpsub; reflexivity).
eapply tr_sumtype_elim.
  {
  eapply hypothesis; eauto using index_0.
  simpsub.
  reflexivity.
  }

  {
  simpsub.
  apply tr_sumtype_intro1.
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    apply (weakening _ [_; _] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    exact Hb'.
    }
  }

  {
  simpsub.
  apply tr_sumtype_intro2.
    {
    apply (tr_pi_elim' _ (subst (sh 2) b) (subst (sh 3) b')).
      {
      apply (weakening _ [_; _] []).
        {
        simpsub.
        reflexivity.
        }
    
        {
        cbn [length].
        simpsub.
        rewrite <- !compose_assoc.
        unfold sh1.
        rewrite -> !compose_sh_unlift.
        simpsub.
        reflexivity.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      rewrite <- compose_assoc.
      unfold sh1.
      rewrite -> compose_sh_unlift.
      simpsub.
      exact Hm.
      }
    
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      reflexivity.
      }
  
      {
      simpsub.
      reflexivity.
      }
    }

    {
    apply (weakening _ [_; _] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    exact Ha.
    }
  }
Qed.


Lemma compatFutureArrow_valid : compatFutureArrow_obligation.
Proof.
prepare.
intros G a a' m Ha.
apply tr_pi_intro.
  {
  apply tr_fut_formation.
  eapply tr_pi_formation_invert1; eauto.
  eapply tr_inhabitation_formation; eauto.
  }
simpsub.
cut (tr (hyp_tm (fut a) :: G) (substj (dot (prev (var 0)) id) (deq (next (app (subst (sh 2) m) (var 0))) (next (app (subst (sh 2) m) (var 0))) (fut (subst (sh 2) a'))))).
  {
 intro H.
 simpsubin H.
 exact H.
 }
apply (tr_fut_elim _ _ _ (subst sh1 a)); auto.
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  cbn [promote map promote_hyp].
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
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation; eauto.
  }

  {
  apply tr_fut_intro.
  cbn [promote map promote_hyp].
  eapply (tr_pi_elim' _ (subst (sh 2) a) (subst (sh 3) a')).
    {
    apply (weakening _ [_; _] []).
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
    exact Ha.
    }

    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }


    {
    simpsub.
    reflexivity.
    }
  }
Qed.


Lemma compatForallEntails1_valid : compatForallEntails1_obligation.
Proof.
prepare.
intros G a b b' m f Hm Hf.
apply tr_pi_intro.
  {
  apply (tr_pi_formation_invert1 _ _ _ b b).
  eapply tr_inhabitation_formation; eauto.
  }
simpsub.
exploit (tr_generalize (hyp_tm a :: G) b (app (subst sh1 f) (var 0)) (deq m m (subst sh1 b'))) as H; auto.
  {
  apply (tr_pi_elim' _ (subst sh1 a) (subst (dot (var 0) (sh 2)) b)).
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    rewrite <- compose_assoc.
    unfold sh1.
    rewrite -> compose_sh_unlift.
    simpsub.
    rewrite -> subst_var0_sh1.
    exact Hf.
    }

    {
    eapply hypothesis; eauto using index_0.
    }

    {
    simpsub.
    rewrite -> subst_var0_sh1.
    reflexivity.
    }
  }
simpsubin H.
exact H.
Qed.


Lemma compatArrowEntails1_valid : compatArrowEntails1_obligation.
Proof.
prepare.
intros G a b b' m f Hm Hf.
apply tr_pi_intro.
  {
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation; eauto.
  }
simpsub.
exploit (tr_generalize (hyp_tm a :: G) (subst sh1 b) (app (subst sh1 f) (var 0)) (deq (subst (dot (var 0) (sh 2)) m) (subst (dot (var 0) (sh 2)) m) (subst (sh 2) b'))) as H.
  {
  apply (tr_pi_elim' _ (subst sh1 a) (subst (sh 2) b)).
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    rewrite <- compose_assoc.
    unfold sh1.
    rewrite -> compose_sh_unlift.
    simpsub.
    exact Hf.
    }

    {
    eapply hypothesis; eauto using index_0.
    }

    {
    simpsub.
    reflexivity.
    }
  }

  {
  apply (weakening _ [_] [_]).
    {
    simpsub.
    reflexivity.
    }

    {
    cbn [length].
    simpsub.
    rewrite <- !compose_assoc.
    unfold sh1.
    rewrite -> !compose_sh_unlift.
    simpsub.
    reflexivity.
    }
  cbn [length].
  simpsub.
  cbn [List.app].
  rewrite <- compose_assoc.
  unfold sh1.
  rewrite -> compose_sh_unlift.
  simpsub.
  rewrite -> subst_var0_sh1.
  exact Hm.
  }
simpsubin H.
exact H.
Qed.


Lemma compatProdEntails0_valid : compatProdEntails0_obligation.
Proof.
prepare.
intros G a a' b m p Hm Hp.
apply tr_prod_intro.
  {
  exploit (tr_generalize G a (ppi1 p) (deq m m (subst (sh 1) a'))) as H; auto.
    {
    eapply tr_prod_elim1; eauto.
    }
  simpsubin H.
  simpsub.
  exact H.
  }

  {
  eapply tr_prod_elim2; eauto.
  }
Qed.


Lemma compatProdEntails1_valid : compatProdEntails1_obligation.
Proof.
prepare.
intros G a b b' m p Hm Hp.
apply tr_prod_intro.
  {
  eapply tr_prod_elim1; eauto.
  }

  {
  exploit (tr_generalize G b (ppi2 p) (deq m m (subst (sh 1) b'))) as H; auto.
    {
    eapply tr_prod_elim2; eauto.
    }
  simpsubin H.
  simpsub.
  exact H.
  }
Qed.
