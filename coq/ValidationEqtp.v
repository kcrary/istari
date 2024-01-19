
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


Hint Rewrite def_eqtp : prepare.


Lemma eqtpForm_valid : eqtpForm_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_eqtype_formation; auto.
Qed.


Lemma eqtpEq_valid : eqtpEq_obligation.
Proof.
prepare.
intros G a b c d ext1 ext0 Hab Hcd.
apply tr_eqtype_formation; auto.
Qed.


Lemma eqtpFormUniv_valid : eqtpFormUniv_obligation.
Proof.
prepare.
intros G a b i ext1 ext0 Ha Hb.
apply tr_eqtype_formation_univ; auto.
Qed.


Lemma eqtpEqUniv_valid : eqtpEqUniv_obligation.
Proof.
prepare.
intros G a b c d i ext1 ext0 Hab Hcd.
apply tr_eqtype_formation_univ; auto.
Qed.


Lemma eqtpIntro_valid : eqtpIntro_obligation.
Proof.
prepare.
intros G a b ext0 H.
auto.
Qed.


Lemma eqtpElim_valid : eqtpElim_obligation.
Proof.
prepare.
intros G a b p ext0 H.
auto.
Qed.


Lemma eqtpExt_valid : eqtpExt_obligation.
Proof.
unfoldtop.
intros G a b p q ext1 ext0 Hp Hq.
unfold Defs.dof in * |- *.
autorewrite with prepare in Hp, Hq |- *.
unfold Defs.triv.
apply tr_equal_intro.
apply (tr_transitivity _ _ triv).
  {
  apply tr_eqtype_eta; auto.
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  apply tr_symmetry.
  apply tr_eqtype_eta; auto.
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma eqtpLeft_valid : eqtpLeft_obligation.
Proof.
prepare.
intros G1 G2 a b c m H.
unfold Defs.triv in H.
apply tr_eqtype_eta_hyp; auto.
Qed.


Lemma eqtpFunct_valid : eqtpFunct_obligation.
Proof.
prepare.
intros G a b m n ext1 ext0 Hb Hmn.
eapply tr_functionality_type_term; eauto.
Qed.


Lemma eqtpFunctType_valid : eqtpFunctType_obligation.
Proof.
prepare.
intros G A B B' ext1 ext0 Ha Hb.
apply tr_functionality_type_type; auto.
Qed.


Lemma equivalenceOf_valid : equivalenceOf_obligation.
Proof.
prepare.
intros G a b m ext1 ext0 Hab Hm.
eapply tr_eqtype_convert; eauto.
Qed.


Lemma equivalenceEq_valid : equivalenceEq_obligation.
Proof.
prepare.
intros G a b m n ext1 ext0 Hab Hmn.
eapply tr_eqtype_convert; eauto.
Qed.


Lemma equivalence_valid : equivalence_obligation.
Proof.
prepare.
intros G a b ext0 m Hab Hm.
eapply tr_eqtype_convert; eauto.
Qed.


Lemma equivalenceLeft_valid : equivalenceLeft_obligation.
Proof.
prepare.
intros G1 G2 a b c ext0 m Hab Hm.
replace (deq m m c) with (substj (dot triv id) (deq (subst sh1 m) (subst sh1 m) (subst sh1 c))) by (simpsub; auto).
set (k := length G2).
apply (tr_generalize _ (subst (sh (S k)) (eqtype a a)) triv).
  {
  simpsub.
  fold (deqtype (subst (sh (S k)) a) (subst (sh (S k)) a)).
  apply (tr_inhabitation_formation _ (var k) (var k)).
  eapply hypothesis; eauto.
  eapply (index_app_right _ _ _ 0).
  apply index_0.
  }
eapply (exchange_1_n _ G2 _ []).
  {
  simpsub.
  rewrite <- compose_assoc.
  rewrite -> compose_sh_unlift_ge; try omega.
  replace (S k - length G2) with 1 by omega.
  simpsub.
  reflexivity.
  }
simpsub.
rewrite -> compose_sh_unlift_ge; try omega.
replace (S k - length G2) with 1 by omega.
cbn [List.app].
rewrite <- (compose_sh_sh _ 1 k).
rewrite <- under_dots.
apply (exchange_1_1 _ _ _ (substctx sh1 G2)).
  {
  simpsub.
  reflexivity.
  }
simpsub.
rewrite -> length_substctx.
fold k.
rewrite <- compose_under.
simpsub.
eapply tr_eqtype_convert_hyp; eauto.
cut (tr (substctx (dot (var 0) (sh 2)) G2 ++ [hyp_tm (subst (sh 1) b)] ++ hyp_tm (eqtype a a) :: G1) (deq (subst (under k (dot (var 0) (sh 2))) m) (subst (under k (dot (var 0) (sh 2))) m) (subst (under k (dot (var 0) (sh 2))) c))).
  {
  intro H.
  cbn [List.app] in H.
  exact H.
  }
rewrite -> app_assoc.
apply (weakening _ [_] _).
  {
  cbn [length unlift].
  simpsub.
  rewrite -> substctx_append.
  cbn [length].
  simpsub.
  reflexivity.
  }

  {
  cbn [length unlift].
  simpsub.
  rewrite -> app_length.
  rewrite length_substctx.
  cbn [length].
  fold k.
  rewrite <- under_sum.
  rewrite <- compose_under.
  simpsub.
  reflexivity.
  }
cbn [length unlift].
rewrite -> app_length.
rewrite -> length_substctx.
cbn [length].
simpsub.
rewrite <- under_sum.
fold k.
rewrite <- compose_under.
simpsub.
rewrite -> substctx_append.
cbn [length].
simpsub.
rewrite <- app_assoc.
cbn [List.app].
rewrite -> (substctx_eqsub _#4 (eqsub_symm _#3 (eqsub_expand_id _))).
simpsub.
rewrite -> !(subst_eqsub _#4 (eqsub_symm _#3 (eqsub_under _ k _ _ (eqsub_expand_id _)))).
simpsub.
simpsubin Hm.
exact Hm.
Qed.


Lemma equivalenceLeftAlt_valid : equivalenceLeftAlt_obligation.
Proof.
prepare.
intros G1 G2 a b c ext m Heq Hc.
rewrite -> substctx_id in Heq, Hc.
cbn [Nat.add] in Heq, Hc.
unfold deqtype in Heq.
replace (deq m m c) with (substj (dot triv id) (deq (subst sh1 m) (subst sh1 m) (subst sh1 c))) by (simpsub; reflexivity).
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
apply (tr_eqtype_convert_hyp (hyp_tm (eqtype a b) :: G1) _ _ (subst sh1 b)).
  {
  unfold deqtype.
  eapply tr_eqtype_eta2.
  eapply hypothesis; eauto using index_0, index_S.
  }

  {
  replace (substctx (dot (var 0) (sh 2)) G2 ++ hyp_tm (subst sh1 b) :: hyp_tm (eqtype a b) :: G1) with ((substctx (dot (var 0) (sh 2)) G2 ++ [hyp_tm (subst sh1 b)]) ++ [hyp_tm (eqtype a b)] ++ G1).
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


Lemma eqtpRefl_valid : eqtpRefl_obligation.
Proof.
prepare.
intros G a ext0 H.
auto.
Qed.


Lemma eqtpSymm_valid : eqtpSymm_obligation.
Proof.
prepare.
intros G a b ext0 H.
apply tr_eqtype_symmetry; auto.
Qed.


Lemma eqtpTrans_valid : eqtpTrans_obligation.
Proof.
prepare.
intros G a b c ext1 ext0 Hab Hbc.
eapply tr_eqtype_transitivity; eauto.
Qed.
