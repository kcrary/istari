
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
Require Import Defined.


Hint Rewrite def_sequal : prepare.


Lemma sequalForm_valid : sequalForm_obligation.
Proof.
prepare.
intros G m.
apply tr_sequal_formation.
Qed.


Lemma sequalIntroOf_valid : sequalIntroOf_obligation.
Proof.
prepare.
intros G m.
apply tr_sequal_intro.
Qed.


Lemma sequalIntro_valid : sequalIntro_obligation.
Proof.
prepare.
intros G m.
apply tr_sequal_intro.
Qed.


Lemma sequalTrivialize_valid : sequalTrivialize_obligation.
Proof.
prepare.
intros G m n ext0 H.
eapply tr_sequal_eta2; eauto.
Qed.


Lemma sequalExt_valid : sequalExt_obligation.
Proof.
prepare.
intros G m n p q ext1 ext0 Hp Hq.
apply (tr_transitivity _ _ triv).
  {
  eapply tr_sequal_eta; eauto.
  }

  {
  apply tr_symmetry.
  eapply tr_sequal_eta; eauto.
  }
Qed.


Lemma sequalLeft_valid : sequalLeft_obligation.
Proof.
prepare.
intros G1 G2 c m n p H.
unfold Defs.triv in H.
apply tr_sequal_eta_hyp; auto.
Qed.


Lemma sequalEq_valid : sequalEq_obligation.
Proof.
prepare.
intros G a m n ext1 ext0 Hmn Hm.
apply tr_sequal_equal; auto.
eapply tr_sequal_eta2; eauto.
Qed.


Lemma sequalEqtp_valid : sequalEqtp_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Hab Ha.
apply tr_sequal_eqtype; auto.
eapply tr_sequal_eta2; eauto.
Qed.


Lemma sequivalence_valid : sequivalence_obligation.
Proof.
prepare.
intros G a b ext0 m Heq H.
apply (tr_eqtype_convert _#3 a); auto.
apply tr_sequal_eqtype.
  {
  eapply tr_sequal_eta2; eauto.
  }

  {
  eapply tr_inhabitation_formation; eauto.
  }
Qed.


Lemma sequivalenceLeft_valid : sequivalenceLeft_obligation.
Proof.
prepare.
intros G1 G2 a b c ext0 m Hab Hc.
simpsubin Hab.
simpsubin Hc.
eapply (tr_assert _ (eqtype (subst (sh (1 + length G2)) a) (subst (sh (1 + length G2)) b)) triv).
  {
  apply tr_sequal_eqtype.
    {
    eapply tr_sequal_eta2; eauto.
    }

    {
    apply (tr_inhabitation_formation _ (var (length G2)) (var (length G2))).
    apply tr_hyp_tm.
    apply (index_app_right _#3 0).
    apply index_0.
    }
  }
replace (G2 ++ hyp_tm a :: G1) with ((G2 ++ [hyp_tm a]) ++ G1).
2:{
  rewrite <- app_assoc.
  auto.
  }
apply (exchange_1_n G1 (G2 ++ [hyp_tm a]) _ []).
  {
  simpsub.
  rewrite -> app_length.
  cbn [length].
  rewrite <- compose_assoc.
  rewrite -> compose_sh_unlift_ge; [| omega].
  replace (1 + length G2 - (length G2 + 1)) with 0 by omega.
  simpsub.
  f_equal.
  f_equal; f_equal; f_equal; omega.
  }
rewrite -> app_length.
cbn [length].
simpsub.
cbn [List.app].
rewrite -> !compose_sh_unlift_ge; [| omega].
replace (1 + length G2 - (length G2 + 1)) with 0 by omega.
simpsub.
rewrite <- (compose_sh_sh _ 1).
rewrite <- under_dots.
simpsub.
rewrite -> substctx_append.
cbn [length].
rewrite <- app_assoc.
simpsub.
rewrite <- app_comm_cons.
cbn [List.app Nat.add].
apply (tr_eqtype_convert_hyp _#3 (subst sh1 b)).
  {
  apply (tr_eqtype_eta2 _#3 (var 0) (var 0)).
  eapply hypothesis; eauto using index_0.
  }
replace (hyp_tm (subst sh1 b) :: hyp_tm (eqtype a b) :: G1) with ([hyp_tm (subst sh1 b)] ++ [hyp_tm (eqtype a b)] ++ G1) by reflexivity.
rewrite -> app_assoc.
eapply weakening.
  {
  cbn [unlift length].
  simpsub.
  rewrite -> substctx_append.
  cbn [length].
  simpsub.
  reflexivity.
  }

  {
  cbn [unlift length].
  simpsub.
  rewrite -> app_length.
  cbn [length].
  rewrite -> length_substctx.
  rewrite <- compose_under.
  simpsub.
  reflexivity.
  }
cbn [unlift length].
simpsub.
rewrite -> app_length.
rewrite -> length_substctx.
cbn [length].
rewrite -> substctx_append.
cbn [length].
simpsub.
rewrite <- compose_under.
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
Qed.


Lemma substitutionSyntactic_valid : substitutionSyntactic_obligation.
Proof.
prepare.
intros G1 G2 a b m ext0 n Heq Hn.
apply (tr_assert _ (sequal (var (length G2)) (subst (sh (S (length G2))) m)) triv).
  {
  simpsubin Heq.
  eapply tr_sequal_eta2; eauto.
  }
eapply (exchange_1_n (hyp_tm a :: G1) G2 _ []).
  {
  simpsub.
  rewrite -> project_unlift_ge; auto.
  rewrite -> Nat.sub_diag.
  simpsub.
  rewrite <- compose_assoc.
  rewrite -> compose_sh_unlift_ge; [| omega].
  replace (S (length G2) - length G2) with 1 by omega.
  simpsub.
  rewrite -> Nat.add_comm.
  reflexivity.
  }
simpsub.
rewrite -> project_unlift_ge; auto.
rewrite -> Nat.sub_diag.
rewrite -> compose_sh_unlift_ge; [| omega].
replace (S (length G2) - length G2) with 1 by omega.
simpsub.
rewrite <- (compose_sh_sh _ 1).
rewrite <- under_dots.
rewrite <- compose_under.
simpsub.
cbn [Nat.add List.app].
apply tr_syntactic_substitution.
rewrite -> length_substctx.
replace (hyp_tm (sequal (var 0) (subst sh1 m)) :: hyp_tm a :: G1) with ((hyp_tm (sequal (var 0) (subst sh1 m)) :: hyp_tm a :: nil) ++ G1) by reflexivity.
apply (weakening _ [_;_] _).
  {
  cbn [length unlift].
  simpsub.
  reflexivity.
  }

  {
  cbn [length unlift].
  rewrite -> !length_substctx.
  simpsub.
  rewrite <- !compose_under.
  simpsub.
  rewrite <- !compose_under.
  simpsub.
  cbn [Nat.add].
  reflexivity.
  }
cbn [length unlift].
rewrite -> !length_substctx.
simpsub.
rewrite <- !compose_under.
simpsub.
rewrite <- compose_under.
simpsub.
exact Hn.
Qed.


Lemma sequalSymm_valid : sequalSymm_obligation.
Proof.
prepare.
intros G m n ext0 H.
apply tr_sequal_symm.
eapply tr_sequal_eta2; eauto.
Qed.


Lemma sequalTrans_valid : sequalTrans_obligation.
Proof.
prepare.
intros G m n p ext1 ext0 Hmn Hnp.
eapply tr_sequal_trans; eauto using tr_sequal_eta2.
Qed.


Lemma sequalCompat_valid : sequalCompat_obligation.
Proof.
prepare.
intros G m n p ext0 H.
apply tr_sequal_compat.
eapply tr_sequal_eta2; eauto.
Qed.


Hint Rewrite def_pi : prepare.

Lemma forallEtaSequal_valid : forallEtaSequal_obligation.
Proof.
prepare.
intros G a b m ext Hm.
eapply tr_pi_eta_sequal; eauto.
Qed.


Hint Rewrite def_arrow : prepare.

Lemma arrowEtaSequal_valid : arrowEtaSequal_obligation.
Proof.
prepare.
intros G a b m ext Hm.
eapply tr_pi_eta_sequal; eauto.
Qed.


Hint Rewrite def_sigma : prepare.

Lemma existsEtaSequal_valid : existsEtaSequal_obligation.
Proof.
prepare.
intros G a b m ext0 Hm.
eapply tr_sigma_eta_sequal; eauto.
Qed.


Hint Rewrite def_prod : prepare.

Lemma prodEtaSequal_valid : prodEtaSequal_obligation.
Proof.
prepare.
intros G a b m ext0 Hm.
apply (tr_sigma_eta_sequal _ a (subst sh1 b)).
eapply tr_eqtype_convert; eauto.
apply tr_prod_sigma_equal.
  {
  eapply tr_prod_formation_invert1.
  eapply tr_inhabitation_formation; eauto.
  }

  {
  replace (deqtype b b) with (substj (dot (ppi1 m) id) (deqtype (subst sh1 b) (subst sh1 b))).
  2:{
    simpsub.
    reflexivity.
    }
  apply (tr_generalize _ a).
    {
    eapply tr_prod_elim1; eauto.
    }

    {
    eapply tr_prod_formation_invert2.
    eapply tr_inhabitation_formation; eauto.
    }
  }
Qed.



Hint Rewrite def_fut : prepare.

Lemma futureEtaSequal_valid : futureEtaSequal_obligation.
Proof.
prepare.
intros G a m ext0 Hm.
eapply tr_fut_eta_sequal; eauto.
Qed.
