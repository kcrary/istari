
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
Require Import ValidationPi.
Require Import Judgement.


Hint Rewrite def_forallfut def_intersectfut def_pi : prepare.


Lemma forallfutForm_valid : forallfutForm_obligation.
Proof.
prepare.
intros G a b m n Ha Hb.
apply tr_pi_formation; auto.
  {
  apply tr_semifut_formation; auto.
  }

  {
  replace (deqtype b b) with (deqtype (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
  2:{
    simpsub.
    rewrite -> subst_var0_sh1; auto.
    }
  apply (tr_semifut_elim_eqtype _ _ _ (subst sh1 a)).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    exact Ha.
    }

    {
    cbn.
    eapply (weakening _ [_] [_]).
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
    rewrite -> subst_var0_sh1.
    exact Hb.
    }
  }
Qed.


Lemma forallfutEq_valid : forallfutEq_obligation.
Proof.
prepare.
intros G a a' b b' m n Ha Hb.
apply tr_pi_formation; auto.
  {
  apply tr_semifut_formation; auto.
  }

  {
  replace (deqtype b b') with (deqtype (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b'))).
  2:{
    simpsub.
    rewrite -> !subst_var0_sh1; auto.
    }
  apply (tr_semifut_elim_eqtype _ _ _ (subst sh1 a)).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    eapply tr_eqtype_formation_left; eauto.
    }

    {
    cbn.
    eapply (weakening _ [_] [_]).
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
    rewrite -> !subst_var0_sh1.
    exact Hb.
    }
  }
Qed.


Lemma forallfutFormUniv_valid : forallfutFormUniv_obligation.
Proof.
prepare.
intros G a b lv ext2 ext1 ext0 Hlv Ha Hb.
apply tr_pi_formation_univ; auto.
  {
  apply tr_semifut_formation_univ; auto.
  }

  {
  replace (deq b b (univ (subst sh1 lv))) with (deq (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)) (subst1 (var 0) (univ (subst (sh 2) lv)))).
  2:{
    simpsub.
    rewrite -> subst_var0_sh1; auto.
    }
  apply (tr_semifut_elim _ _ _ (subst sh1 a)).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    apply (tr_formation_weaken _ lv).
    exact Ha.
    }

    {
    cbn.
    eapply (weakening _ [_] [_]).
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
    rewrite -> subst_var0_sh1.
    exact Hb.
    }
  }
Qed.


Lemma forallfutEqUniv_valid : forallfutEqUniv_obligation.
Proof.
prepare.
intros G a a' b b' lv ext2 ext1 ext0 Hlv Ha Hb.
apply tr_pi_formation_univ; auto.
  {
  apply tr_semifut_formation_univ; auto.
  }

  {
  replace (deq b b' (univ (subst sh1 lv))) with (deq (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b')) (subst1 (var 0) (univ (subst (sh 2) lv)))).
  2:{
    simpsub.
    rewrite -> !subst_var0_sh1; auto.
    }
  apply (tr_semifut_elim _ _ _ (subst sh1 a)).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    apply (tr_formation_weaken _ lv).
    eapply tr_eq_reflexivity; eauto.
    }

    {
    cbn.
    eapply (weakening _ [_] [_]).
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
    rewrite -> !subst_var0_sh1.
    exact Hb.
    }
  }
Qed.


Lemma forallfutSub_valid : forallfutSub_obligation.
Proof.
prepare.
intros G a a' b b' ext2 ext1 ext0 Ha Hb Hb'.
apply tr_pi_sub.
  {
  apply tr_semifut_sub; auto.
  }

  {
  unfold dsubtype.
  replace (deq triv triv (subtype b b')) with (deq (subst1 (var 0) triv) (subst1 (var 0) triv) (subst1 (var 0) (subst (dot (var 0) (sh 2)) (subtype b b')))).
  2:{
    simpsub.
    rewrite -> !subst_var0_sh1.
    auto.
    }
  apply (tr_semifut_elim _#3 (subst sh1 a')).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    eapply tr_subtype_istype1; eauto.
    }

    {
    eapply (weakening _ [_] [_]).
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
    rewrite -> !subst_var0_sh1.
    exact Hb.
    }
  }

  {
  replace (deqtype b b) with (deqtype (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
  2:{
    simpsub.
    rewrite -> !subst_var0_sh1.
    auto.
    }
  apply (tr_semifut_elim_eqtype _#3 (subst sh1 a)).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    eapply tr_subtype_istype2; eauto.
    }

    {
    eapply (weakening _ [_] [_]).
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
    rewrite -> !subst_var0_sh1.
    exact Hb'.
    }
  }
Qed.


Lemma forallfutForallVoidSub_valid : forallfutForallVoidSub_obligation.
Proof.
prepare.
intros G a b b' ext1 ext0 Ha Hb.
unfold Defs.void.
apply tr_pi_sub.
  {
  apply tr_subtype_intro.
    {
    apply tr_voidtp_istype.
    }

    {
    apply tr_semifut_formation; auto.
    }

    {
    eapply (tr_voidtp_elim _ (var 0) (var 0)).
    eapply hypothesis; eauto using index_0.
    }
  }

  {
  eapply (tr_voidtp_elim _ (var 0) (var 0)).
  eapply hypothesis; eauto using index_0.
  }

  {
  replace (deqtype b b) with (deqtype (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
  2:{
    simpsub.
    rewrite -> subst_var0_sh1; auto.
    }
  apply (tr_semifut_elim_eqtype _ _ _ (subst sh1 a)).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    exact Ha.
    }

    {
    cbn.
    eapply (weakening _ [_] [_]).
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
    rewrite -> subst_var0_sh1.
    exact Hb.
    }
  }
Qed.


Lemma forallfutIntroOf_valid : forallfutIntroOf_obligation.
Proof.
prepare.
intros G a b m ext1 ext0 Ha Hm.
apply tr_pi_intro.
  {
  apply tr_semifut_formation; auto.
  }
replace (deq m m b) with (deq (subst1 (var 0) (subst (dot (var 0) (sh 2)) m)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) m)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
2:{
  simpsub.
  rewrite -> !subst_var0_sh1; auto.
  }
apply (tr_semifut_elim _ _ _ (subst sh1 a)).
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  cbn.
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
  exact Ha.
  }

  {
  eapply (weakening _ [_] [_]).
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
  rewrite -> !subst_var0_sh1.
  exact Hm.
  }
Qed.


Lemma forallfutIntroEq_valid : forallfutIntroEq_obligation.
Proof.
prepare.
intros G a b m n ext1 ext0 Ha Hmn.
apply tr_pi_intro.
  {
  apply tr_semifut_formation; auto.
  }
replace (deq m n b) with (deq (subst1 (var 0) (subst (dot (var 0) (sh 2)) m)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) n)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
2:{
  simpsub.
  rewrite -> !subst_var0_sh1; auto.
  }
apply (tr_semifut_elim _ _ _ (subst sh1 a)).
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  cbn.
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
  exact Ha.
  }

  {
  eapply (weakening _ [_] [_]).
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
  rewrite -> !subst_var0_sh1.
  exact Hmn.
  }
Qed.


Lemma forallfutIntro_valid : forallfutIntro_obligation.
Proof.
prepare.
intros G a b ext1 m Ha Hm.
apply tr_pi_intro.
  {
  apply tr_semifut_formation; auto.
  }
replace (deq m m b) with (deq (subst1 (var 0) (subst (dot (var 0) (sh 2)) m)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) m)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
2:{
  simpsub.
  rewrite -> !subst_var0_sh1; auto.
  }
apply (tr_semifut_elim _ _ _ (subst sh1 a)).
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  cbn.
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
  exact Ha.
  }

  {
  eapply (weakening _ [_] [_]).
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
  rewrite -> !subst_var0_sh1.
  exact Hm.
  }
Qed.


Lemma forallfutElimOf_valid : forallfutElimOf_obligation.
Proof.
prepare.
intros G a b m p ext1 ext0 Hm Hp.
eapply tr_pi_elim; eauto.
apply tr_semifut_intro; auto.
Qed.


Lemma forallfutElimEq_valid : forallfutElimEq_obligation.
Proof.
prepare.
intros G a b m n p q ext1 ext0 Hmn Hpq.
eapply tr_pi_elim; eauto.
apply tr_semifut_intro; auto.
Qed.


Lemma forallfutElim_valid : forallfutElim_obligation.
Proof.
prepare.
intros G a b p m ext0 Hm Hp.
eapply tr_pi_elim; eauto.
apply tr_semifut_intro; auto.
Qed.


Lemma forallfutExt_valid : forallfutExt_obligation.
Proof.
prepare.
intros G a b m n ext3 ext2 ext1 ext0 Ha Hm Hn Hmn.
apply (tr_pi_ext _#5 (semifut a) (semifut a) b b); auto.
  {
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation; eauto.
  }
replace (deq (app (subst sh1 m) (var 0)) (app (subst sh1 n) (var 0)) b) with (deq (subst1 (var 0) (app (subst (sh 2) m) (var 0))) (subst1 (var 0) (app (subst (sh 2) n) (var 0))) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
2:{
  simpsub.
  rewrite -> !subst_var0_sh1; auto.
  }
apply (tr_semifut_elim _ _ _ (subst sh1 a)).
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  cbn.
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
  exact Ha.
  }

  {
  eapply (weakening _ [_] [_]).
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
  rewrite -> !subst_var0_sh1.
  exact Hmn.
  }
Qed.


Lemma forallfutExt'_valid : forallfutExt'_obligation.
Proof.
prepare.
intros G a a' a'' b b' b'' m n ext3 ext2 ext1 ext0 Ha Halt Halt' Hm.
apply (tr_pi_ext _#5 a' a'' b' b''); auto.
  {
  apply tr_semifut_formation; auto.
  }
replace (deq (app (subst sh1 m) (var 0)) (app (subst sh1 n) (var 0)) b) with (deq (subst1 (var 0) (app (subst (sh 2) m) (var 0))) (subst1 (var 0) (app (subst (sh 2) n) (var 0))) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
2:{
  simpsub.
  rewrite -> !subst_var0_sh1; auto.
  }
apply (tr_semifut_elim _ _ _ (subst sh1 a)).
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  cbn.
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
  exact Ha.
  }

  {
  eapply (weakening _ [_] [_]).
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
  rewrite -> !subst_var0_sh1.
  exact Hm.
  }
Qed.


Lemma forallfutOfExt_valid : forallfutOfExt_obligation.
Proof.
prepare.
intros G a a' b b' m ext2 ext1 ext0 Ha Halt Hm.
apply (tr_pi_ext _#5 a' a' b' b'); auto.
  {
  apply tr_semifut_formation; auto.
  }
replace (deq (app (subst sh1 m) (var 0)) (app (subst sh1 m) (var 0)) b) with (deq (subst1 (var 0) (app (subst (sh 2) m) (var 0))) (subst1 (var 0) (app (subst (sh 2) m) (var 0))) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
2:{
  simpsub.
  rewrite -> !subst_var0_sh1; auto.
  }
apply (tr_semifut_elim _ _ _ (subst sh1 a)).
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  cbn.
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
  exact Ha.
  }

  {
  eapply (weakening _ [_] [_]).
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
  rewrite -> !subst_var0_sh1.
  exact Hm.
  }
Qed.


Lemma intersectfutForm_valid : intersectfutForm_obligation.
Proof.
prepare.
intros G a b m n Ha Hb.
apply tr_intersect_formation; auto.
  {
  apply tr_semifut_formation; auto.
  }

  {
  replace (deqtype b b) with (deqtype (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
  2:{
    simpsub.
    rewrite -> subst_var0_sh1; auto.
    }
  apply (tr_semifut_elim_eqtype _ _ _ (subst sh1 a)).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    exact Ha.
    }

    {
    cbn.
    eapply (weakening _ [_] [_]).
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
    rewrite -> subst_var0_sh1.
    exact Hb.
    }
  }
Qed.


Lemma intersectfutEq_valid : intersectfutEq_obligation.
Proof.
prepare.
intros G a a' b b' m n Ha Hb.
apply tr_intersect_formation; auto.
  {
  apply tr_semifut_formation; auto.
  }

  {
  replace (deqtype b b') with (deqtype (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b'))).
  2:{
    simpsub.
    rewrite -> !subst_var0_sh1; auto.
    }
  apply (tr_semifut_elim_eqtype _ _ _ (subst sh1 a)).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    eapply tr_eqtype_formation_left; eauto.
    }

    {
    cbn.
    eapply (weakening _ [_] [_]).
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
    rewrite -> !subst_var0_sh1.
    exact Hb.
    }
  }
Qed.


Lemma intersectfutFormUniv_valid : intersectfutFormUniv_obligation.
Proof.
prepare.
intros G a b lv ext2 ext1 ext0 Hlv Ha Hb.
apply tr_intersect_formation_univ; auto.
  {
  apply tr_semifut_formation_univ; auto.
  }

  {
  replace (deq b b (univ (subst sh1 lv))) with (deq (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)) (subst1 (var 0) (univ (subst (sh 2) lv)))).
  2:{
    simpsub.
    rewrite -> subst_var0_sh1; auto.
    }
  apply (tr_semifut_elim _ _ _ (subst sh1 a)).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    apply (tr_formation_weaken _ lv).
    exact Ha.
    }

    {
    cbn.
    eapply (weakening _ [_] [_]).
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
    rewrite -> subst_var0_sh1.
    exact Hb.
    }
  }
Qed.


Lemma intersectfutEqUniv_valid : intersectfutEqUniv_obligation.
Proof.
prepare.
intros G a a' b b' lv ext2 ext1 ext0 Hlv Ha Hb.
apply tr_intersect_formation_univ; auto.
  {
  apply tr_semifut_formation_univ; auto.
  }

  {
  replace (deq b b' (univ (subst sh1 lv))) with (deq (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b')) (subst1 (var 0) (univ (subst (sh 2) lv)))).
  2:{
    simpsub.
    rewrite -> !subst_var0_sh1; auto.
    }
  apply (tr_semifut_elim _ _ _ (subst sh1 a)).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    apply (tr_formation_weaken _ lv).
    eapply tr_eq_reflexivity; eauto.
    }

    {
    cbn.
    eapply (weakening _ [_] [_]).
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
    rewrite -> !subst_var0_sh1.
    exact Hb.
    }
  }
Qed.


Lemma intersectfutSub_valid : intersectfutSub_obligation.
Proof.
prepare.
intros G a a' b b' ext2 ext1 ext0 Ha Hb Hb'.
apply tr_intersect_sub.
  {
  apply tr_semifut_sub; auto.
  }

  {
  unfold dsubtype.
  replace (deq triv triv (subtype b b')) with (deq (subst1 (var 0) triv) (subst1 (var 0) triv) (subst1 (var 0) (subst (dot (var 0) (sh 2)) (subtype b b')))).
  2:{
    simpsub.
    rewrite -> !subst_var0_sh1.
    auto.
    }
  apply (tr_semifut_elim _#3 (subst sh1 a')).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    eapply tr_subtype_istype1; eauto.
    }

    {
    eapply (weakening _ [_] [_]).
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
    rewrite -> !subst_var0_sh1.
    exact Hb.
    }
  }

  {
  replace (deqtype b b) with (deqtype (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
  2:{
    simpsub.
    rewrite -> !subst_var0_sh1.
    auto.
    }
  apply (tr_semifut_elim_eqtype _#3 (subst sh1 a)).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    eapply tr_subtype_istype2; eauto.
    }

    {
    eapply (weakening _ [_] [_]).
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
    rewrite -> !subst_var0_sh1.
    exact Hb'.
    }
  }
Qed.


Lemma intersectfutIntroOf_valid : intersectfutIntroOf_obligation.
Proof.
prepare.
intros G a b m ext1 ext0 Ha Hm.
apply tr_intersect_intro.
  {
  apply tr_semifut_formation; auto.
  }
replace (deq (subst sh1 m) (subst sh1 m) b) with (deq (subst1 (var 0) (subst (sh 2) m)) (subst1 (var 0) (subst (sh 2) m)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
2:{
  simpsub.
  rewrite -> !subst_var0_sh1; auto.
  }
apply (tr_semifut_elim _ _ _ (subst sh1 a)).
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  cbn.
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
  exact Ha.
  }

  {
  eapply (weakening _ [_] [_]).
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
  rewrite -> !subst_var0_sh1.
  exact Hm.
  }
Qed.


Lemma intersectfutIntroEq_valid : intersectfutIntroEq_obligation.
Proof.
prepare.
intros G a b m n ext1 ext0 Ha Hmn.
apply tr_intersect_intro.
  {
  apply tr_semifut_formation; auto.
  }
replace (deq (subst sh1 m) (subst sh1 n) b) with (deq (subst1 (var 0) (subst (sh 2) m)) (subst1 (var 0) (subst (sh 2) n)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
2:{
  simpsub.
  rewrite -> !subst_var0_sh1; auto.
  }
apply (tr_semifut_elim _ _ _ (subst sh1 a)).
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  cbn.
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
  exact Ha.
  }

  {
  eapply (weakening _ [_] [_]).
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
  rewrite -> !subst_var0_sh1.
  exact Hmn.
  }
Qed.


Lemma intersectfutIntro_valid : intersectfutIntro_obligation.
Proof.
prepare.
intros G a b ext0 m Hhyg Ha Hm.
apply tr_intersect_intro.
  {
  apply tr_semifut_formation; auto.
  }
simpsub.
replace (deq (subst (dot triv sh1) m) (subst (dot triv sh1) m) b) with (deq (subst1 (var 0) (subst (dot triv (sh 2)) m)) (subst1 (var 0) (subst (dot triv (sh 2)) m)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
2:{
  simpsub.
  rewrite -> !subst_var0_sh1; auto.
  }
apply (tr_semifut_elim _ _ _ (subst sh1 a)).
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  cbn.
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
  exact Ha.
  }

  {
  eapply (weakening _ [_] [_]).
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
  rewrite -> !subst_var0_sh1.
  replace (subst (dot triv sh1) m) with m; auto.
  so (subst_into_absent_single _ _ _ triv Hhyg) as H.
  simpsubin H.
  symmetry.
  auto.
  }
Qed.


Lemma intersectfutElimOf_valid : intersectfutElimOf_obligation.
Proof.
prepare.
intros G a b m p ext1 ext0 Hm Hp.
eapply tr_intersect_elim; eauto.
apply tr_semifut_intro; eauto.
Qed.


Lemma intersectfutElimEq_valid : intersectfutElimEq_obligation.
Proof.
prepare.
intros G a b m n p ext1 ext0 Hmn Hp.
eapply tr_intersect_elim; eauto.
apply tr_semifut_intro; eauto.
Qed.


Lemma intersectfutElim_valid : intersectfutElim_obligation.
Proof.
prepare.
intros G a b p m ext0 Hm Hp.
eapply tr_intersect_elim; eauto.
apply tr_semifut_intro; eauto.
Qed.
