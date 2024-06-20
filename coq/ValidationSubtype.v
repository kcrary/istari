
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


Hint Rewrite def_subtype def_eeqtp : prepare.


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
intros G a b ext0 H.
auto.
Qed.


Lemma subtypeElim_valid : subtypeElim_obligation.
Proof.
prepare.
intros G a b p ext0 H.
auto.
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


Lemma subtypeEstablish_valid : subtypeEstablish_obligation.
Proof.
prepare.
intros G a b ext2 ext1 ext0 Ha Hb Hsub.
eapply tr_subtype_intro; eauto.
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


Lemma subsumptionAlt_valid : subsumptionAlt_obligation.
Proof.
prepare.
intros G a b n m Heq Hm.
apply (tr_subtype_elim _ a); auto.
apply (tr_subtype_eta2 _ _ _ (ppi2 n) (ppi2 n)).
eapply tr_prod_elim2; eauto.
Qed.


Lemma subsumptionLeft_valid : subsumptionLeft_obligation.
Proof.
prepare.
intros G1 G2 a b c p m Hb Hm.
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


Lemma subsumptionLeftAlt_valid : subsumptionLeftAlt_obligation.
Proof.
prepare.
intros G1 G2 a b c ext m Heq Hc.
rewrite -> substctx_id in Heq, Hc.
cbn [Nat.add] in Heq, Hc.
replace (deq m m c) with (substj (dot ext id) (deq (subst sh1 m) (subst sh1 m) (subst sh1 c))) by (simpsub; reflexivity).
eapply tr_generalize; eauto.
apply (exchange_1_n _ G2 _ nil).
  {
  simpsub.
  rewrite <- !compose_assoc.
  rewrite -> !compose_sh_unlift_ge; [| omega].
  replace (S (length G2) - length G2) with 1 by omega.
  simpsub.
  reflexivity.
  }
simpsub.
cbn [List.app].
rewrite -> !compose_sh_unlift_ge; [| omega].
replace (S (length G2) - length G2) with 1 by omega.
simpsub.
rewrite <- (compose_sh_sh _ 1 (length G2)).
rewrite <- under_dots.
apply exchange_1_1.
  {
  simpsub.
  reflexivity.
  }
simpsub.
rewrite -> length_substctx.
rewrite <- compose_under.
simpsub.
apply (tr_subtype_convert_hyp (hyp_tm (prod (subtype a b) (subtype b a)) :: G1) _ _ (subst sh1 b)).
  {
  simpsub.
  unfold dsubtype.
  apply (tr_subtype_eta2 _ _ _ (ppi1 (var 1)) (ppi1 (var 1))).
  eapply tr_prod_elim1.
  eapply hypothesis; eauto using index_0, index_S.
  simpsub.
  reflexivity.
  }

  {
  simpsub.
  unfold dsubtype.
  apply (tr_subtype_eta2 _ _ _ (ppi2 (var 1)) (ppi2 (var 1))).
  eapply tr_prod_elim2.
  eapply hypothesis; eauto using index_0, index_S.
  simpsub.
  reflexivity.
  }

  {
  replace (substctx (dot (var 0) (sh 2)) G2 ++ hyp_tm (subst sh1 b) :: hyp_tm (prod (subtype a b) (subtype b a)) :: G1) with ((substctx (dot (var 0) (sh 2)) G2 ++ [hyp_tm (subst sh1 b)]) ++ [hyp_tm (prod (subtype a b) (subtype b a))] ++ G1).
  2:{
    rewrite <- app_assoc.
    cbn [List.app].
    reflexivity.
    }
  apply weakening.
    {
    cbn [length].
    rewrite -> !substctx_append.
    rewrite <- substctx_compose.
    cbn [length].
    replace (dot (var 0) (sh 2)) with (@under obj 1 (sh 1)) by (simpsub; reflexivity).
    rewrite <- compose_under.
    rewrite <- compose_assoc.
    rewrite -> compose_sh_unlift.
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
    rewrite -> app_length.
    cbn [length].
    rewrite -> length_substctx.
    replace (dot (var 0) (sh 2)) with (@under obj 1 (sh 1)) by (simpsub; reflexivity).
    rewrite -> under_sum.
    rewrite <- !compose_under.
    rewrite <- compose_assoc.
    rewrite -> compose_sh_unlift.
    simpsub.
    reflexivity.
    }
  cbn [length].
  simpsub.
  rewrite -> !substctx_append.
  rewrite <- substctx_compose.
  rewrite -> app_length.
  cbn [length].
  replace (dot (var 0) (sh 2)) with (@under obj 1 (sh 1)) by (simpsub; reflexivity).
  rewrite -> under_sum.
  rewrite -> length_substctx.
  rewrite <- !compose_under.
  rewrite -> compose_sh_unlift.
  simpsub.
  rewrite <- app_assoc.
  cbn [List.app].
  rewrite -> (substctx_eqsub _ _ id).
    {
    simpsub.
    exact Hc.
    }

    {
    apply eqsub_symm.
    apply eqsub_expand_id.
    }
  }
Qed.


Lemma subsumptionLast_valid : subsumptionLast_obligation.
Proof.
prepare.
intros G1 G2 a b c ext0 m Hab Hc.
cbn [Nat.add].
apply (weakening _ G2 []).
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
  reflexivity.
  }
cbn [length].
simpsub.
cbn [List.app].
rewrite -> compose_sh_unlift.
simpsub.
replace (deq m m c) with (substj (dot (var 0) id) (substj (dot (var 0) (sh 2)) (deq m m c))).
2:{
  simpsub.
  rewrite -> !subst_var0_sh1.
  reflexivity.
  }
apply (tr_generalize _ (subst sh1 b) (var 0)).
  {
  apply (tr_subtype_elim _ (subst sh1 a)).
    {
    exact Hab.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
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
  rewrite -> !subst_var0_sh1.
  exact Hc.
  }
Qed.


Lemma tighten_valid : tighten_obligation.
Proof.
prepare.
intros G1 G2 a b c ext1 ext0 m Hsub Hof Hc.
rewrite -> substctx_id in Hsub, Hof, Hc.
eapply tr_tighten_better; eauto.
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


Lemma eeqtpForm_valid : eeqtpForm_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_prod_formation; apply tr_subtype_formation; auto.
Qed.


Lemma eeqtpEq_valid : eeqtpEq_obligation.
Proof.
prepare.
intros G a b c d ext1 ext0 Hab Hcd.
apply tr_prod_formation; apply tr_subtype_formation; auto.
Qed.


Lemma eeqtpFormUniv_valid : eeqtpFormUniv_obligation.
Proof.
prepare.
intros G a b i ext1 ext0 Ha Hb.
apply tr_prod_formation_univ; apply tr_subtype_formation_univ; auto.
Qed.


Lemma eeqtpEqUniv_valid : eeqtpEqUniv_obligation.
Proof.
prepare.
intros G a b c d i ext1 ext0 Hab Hcd.
apply tr_prod_formation_univ; apply tr_subtype_formation_univ; auto.
Qed.
