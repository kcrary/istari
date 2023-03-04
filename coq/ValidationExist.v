
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
Require Import NatLemmas.
Require Import LevelLemmas.


Hint Rewrite def_iexists : prepare.


Lemma iexistsForm_valid : iexistsForm_obligation.
Proof.
prepare.
intros G a i k ext1 ext0 Hk Ha.
apply tr_exist_formation; auto.
Qed.


Lemma iexistsEq_valid : iexistsEq_obligation.
Proof.
prepare.
intros G a b i k l ext1 ext0 Hkl Hab.
apply tr_exist_formation; auto.
Qed.


Lemma iexistsFormUniv_valid : iexistsFormUniv_obligation.
Proof.
prepare.
intros G a i j k ext2 ext1 ext0 Hk Hleq Ha.
so (lleq_explode _#5 Hleq) as (Hleq' & Hi & Hj).
apply tr_exist_formation_univ; auto.
Qed.


Lemma iexistsEqUniv_valid : iexistsEqUniv_obligation.
Proof.
prepare.
intros G a b i j k l ext2 ext1 ext0 Hkl Hleq Hab.
so (lleq_explode _#5 Hleq) as (Hleq' & Hi & Hj).
apply tr_exist_formation_univ; auto.
Qed.


Lemma iexistsIntroOf_valid : iexistsIntroOf_obligation.
Proof.
prepare.
intros G a b i k m ext3 ext2 ext1 ext0 Hk Ha Hb Hm.
eapply tr_exist_intro; eauto.
Qed.


Lemma iexistsIntroEq_valid : iexistsIntroEq_obligation.
Proof.
prepare.
intros G a b i k m n ext3 ext2 ext1 ext0 Hk Ha Hb Hmn.
eapply tr_exist_intro; eauto.
Qed.


Lemma iexistsIntro_valid : iexistsIntro_obligation.
Proof.
prepare.
intros G a b i k ext2 ext1 ext0 m Hk Ha Hb Hm.
eapply tr_exist_intro; eauto.
Qed.


Lemma iexistsElimOf_valid : iexistsElimOf_obligation.
Proof.
prepare.
intros G a b i k m p ext3 ext2 ext1 ext0 Hk Ha Hp Hm.
eapply tr_exist_elim; eauto.
Qed.


Lemma iexistsElimEq_valid : iexistsElimEq_obligation.
Proof.
prepare.
intros G a b i k m n p q ext3 ext2 ext1 ext0 Hk Ha Hpq Hmn.
eapply tr_exist_elim; eauto.
Qed.


Lemma iexistsElim_valid : iexistsElim_obligation.
Proof.
prepare.
intros G a b i k m ext2 ext1 p ext0 Hhyg Hk Ha Hp Hm.
replace (subst (dot m (dot triv (sh 0))) p) with (subst1 m (subst (under 1 (dot triv id)) p)) by (simpsub; auto).
eapply tr_exist_elim; eauto.
simpsub.
so (subst_into_absent_single _ 1 p triv Hhyg) as H.
simpsubin H.
cbn [Nat.add] in H.
rewrite -> H.
auto.
Qed.


Lemma iexistsElimIstype_valid : iexistsElimIstype_obligation.
Proof.
prepare.
intros G a b i k m ext3 ext2 ext1 ext0 Hk Ha Hb Hm.
eapply tr_exist_elim_eqtype; eauto.
Qed.


Lemma iexistsElimEqtype_valid : iexistsElimEqtype_obligation.
Proof.
prepare.
intros G a b c i k m n ext3 ext2 ext1 ext0 Hk Ha Hc Hmn.
eapply tr_exist_elim_eqtype; eauto.
Qed.
