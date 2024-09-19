
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Tactics.
Require Import Relation.
Require Import Sequence.
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
Require Import Dots.

Require Import ValidationUtil.
Require Import Equivalences.


Hint Rewrite def_quotient : prepare.


Lemma quotientForm_valid : quotientForm_obligation.
Proof.
prepare.
intros G a b ext3 ext2 ext1 ext0 Ha Hb Hsymm Htrans.
apply (tr_quotient_formation G a a b b (var 0) (var 0) ext1 ext0); auto.
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  eapply hypothesis; eauto using index_0.
  }

  {
  force_exact Htrans.
  f_equal.
  f_equal.
  apply subst_eqsub.
  apply eqsub_dotv.
  apply eqsub_expand_sh.
  }
Qed.


Lemma quotientEq_valid : quotientEq_obligation.
Proof.
prepare.
intros G a a' b b' ext6 ext5 ext4 ext3 ext2 ext1 ext0 Ha Hb Hb' Hl Hr Hsymm Htrans.
apply (tr_quotient_formation G a a' b b' ext3 ext2 ext1 ext0); auto.
force_exact Htrans.
f_equal.
f_equal.
apply subst_eqsub.
apply eqsub_dotv.
apply eqsub_expand_sh.
Qed.


Lemma quotientFormUniv_valid : quotientFormUniv_obligation.
Proof.
prepare.
intros G a b lv ext3 ext2 ext1 ext0 Ha Hb Hsymm Htrans.
apply (tr_quotient_formation_univ G lv a a b b (var 0) (var 0) ext1 ext0); auto.
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  eapply hypothesis; eauto using index_0.
  }

  {
  force_exact Htrans.
  f_equal.
  f_equal.
  apply subst_eqsub.
  apply eqsub_dotv.
  apply eqsub_expand_sh.
  }
Qed.


Lemma quotientEqUniv_valid : quotientEqUniv_obligation.
Proof.
prepare.
intros G a a' b b' lv ext6 ext5 ext4 ext3 ext2 ext1 ext0 Ha Hb Hb' Hl Hr Hsymm Htrans.
apply (tr_quotient_formation_univ G lv a a' b b' ext3 ext2 ext1 ext0); auto.
force_exact Htrans.
f_equal.
f_equal.
apply subst_eqsub.
apply eqsub_dotv.
apply eqsub_expand_sh.
Qed.


Lemma quotientIntroOf_valid : quotientIntroOf_obligation.
Proof.
prepare.
intros G a b m ext2 ext1 ext0 Hq Hm Hrel.
apply (tr_quotient_intro _#5 ext0); auto.
Qed.


Lemma quotientIntroEq_valid : quotientIntroEq_obligation.
Proof.
prepare.
intros G A B M N ext3 ext2 ext1 ext0 Hq Hm Hn Hrel.
apply (tr_quotient_intro _#5 ext0); auto.
Qed.


Lemma quotientElimOf_valid : quotientElimOf_obligation.
Proof.
prepare.
intros G a b c m p ext3 ext2 ext1 ext0 Hq Hb Hc Hp.
apply (tr_quotient_elim _ a b); auto.
Qed.


Lemma quotientElimEq_valid : quotientElimEq_obligation.
Proof.
prepare.
intros G a b c m n p q ext3 ext2 ext1 ext0 H2 H1 H3 H0.
apply (tr_quotient_elim _ a b); auto.
Qed.


Lemma quotientElimIstype_valid : quotientElimIstype_obligation.
Proof.
prepare.
intros G a b c m ext2 ext1 ext0 H0 H1 H2.
apply (tr_quotient_elim_eqtype _ a b); auto.
Qed.


Lemma quotientElimEqtype_valid : quotientElimEqtype_obligation.
Proof.
prepare.
intros G a b c d m n ext2 ext1 ext0 H0 H1 H2.
apply (tr_quotient_elim_eqtype _ a b); auto.
Qed.


Lemma quotientDescent_valid : quotientDescent_obligation.
Proof.
prepare.
intros G a b c m n ext4 ext3 ext2 ext1 ext0 p Hhide Hb Hc Hm Hn Hmn Hp.
apply (tr_descent _ a b c m n); auto.
simpsub.
erewrite -> (subst_into_absent _#3 p); eauto.
intros i Hi.
cbn in Hi.
destruct i as [| i]; [omega |].
simpsub.
auto.
Qed.


Lemma subst_under_triv_sh :
  forall j m,
    @subst obj (under j (dot triv (sh 1))) m = subst (under j sh1) (subst (under j (dot triv id)) m).
Proof.
intros j m.
rewrite <- subst_compose.
rewrite <- compose_under.
simpsub.
reflexivity.
Qed.


Lemma subst_under_triv_sh_2 :
  forall j m,
    @subst obj (under j (dot triv (dot triv (sh 1)))) m = subst (under j (sh 1)) (subst (under j (dot triv (dot triv id))) m).
Proof.
intros j m.
rewrite <- subst_compose.
rewrite <- compose_under.
simpsub.
reflexivity.
Qed.


Lemma hidden_form_2 :
  forall j m,
    @hygiene obj (fun i => i <> j) m
    -> hygiene (fun i => i <> S j) m
    -> subst (under j (dot triv (dot triv (sh 2)))) m = m.
Proof.
intros j m Hhide0 Hhide1.
replace (under j (dot triv (dot triv (sh 2)))) with (@compose obj (under (S j) (dot triv sh1)) (under j (dot triv sh1))).
2:{
  replace (S j) with (j + 1) by omega.
  rewrite <- under_sum.
  rewrite <- compose_under.
  cbn [under].
  simpsub.
  reflexivity.
  }
rewrite -> subst_compose.
setoid_rewrite -> subst_into_absent_single at 2; auto.
apply subst_into_absent_single; auto.
Qed.


Lemma quotientLeft_valid : quotientLeft_obligation.
Proof.
prepare.
intros G1 G2 a b c ext0 m Hhide Hc Hm.
rewrite -> subst_under_triv_sh.
apply tr_quotient_hyp.
  {
  simpsubin Hc.
  exact Hc.
  }

  {
  simpsubin Hm.
  rewrite <- subst_under_triv_sh.
  rewrite -> subst_into_absent_single; auto.
  }
Qed.


Lemma quotientLeftRefl_valid : quotientLeftRefl_obligation.
Proof.
prepare.
intros G1 G2 a b c ext1 ext0 m Hhide0 Hhide1 Hb Hc Hm.
rewrite -> subst_under_triv_sh_2.
apply tr_quotient_hyp_with_refl; auto.
  {
  simpsubin Hc.
  exact Hc.
  }

  {
  simpsubin Hm.
  simpsub.
  rewrite <- !compose_under.
  simpsub.
  rewrite -> hidden_form_2; auto.
  force_exact Hm.
  do 4 f_equal.
  apply subst_eqsub.
  apply eqsub_dotv.
  apply eqsub_expand_id.
  }
Qed.


Lemma quotientLeftIstype_valid : quotientLeftIstype_obligation.
Proof.
prepare.
intros G1 G2 a b c ext1 ext0 Hb Hc.
apply tr_quotient_hyp_eqtype; auto.
Qed.


Lemma quotientLeftEqtype_valid : quotientLeftEqtype_obligation.
Proof.
prepare.
intros G1 G2 a b c d ext1 ext0 Hb Hcd.
apply tr_quotient_hyp_eqtype; auto.
Qed.


Lemma quotientLeftOf_valid : quotientLeftOf_obligation.
Proof.
prepare.
intros G1 G2 A B C M ext1 ext0 Hb Hm.
apply tr_quotient_hyp_eq; auto.
Qed.


Lemma quotientLeftEq_valid : quotientLeftEq_obligation.
Proof.
prepare.
intros G1 G2 a b c m n ext1 ext0 Hb Hmn.
apply tr_quotient_hyp_eq; auto.
Qed.


Lemma quotientLeftOfDep_valid : quotientLeftOfDep_obligation.
Proof.
prepare.
intros G1 G2 a b c m ext2 ext1 ext0 Hb Hc Hm.
apply tr_quotient_hyp_eq_dep; auto.
Qed.


Lemma quotientLeftEqDep_valid : quotientLeftEqDep_obligation.
Proof.
prepare.
intros G1 G2 a b c m n ext2 ext1 ext0 Hb Hc Hmn.
apply tr_quotient_hyp_eq_dep; auto.
Qed.


Lemma quotientFormInv_valid : quotientFormInv_obligation.
Proof.
prepare.
intros G a b ext0 H.
eapply tr_quotient_formation_invert; eauto.
Qed.
