
Require Import Coq.Lists.List.
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

Require Import ValidationUtil.


Lemma iforallIntro_valid : iforallIntro_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a i k n m Hhyg Hk Hm.
unfold Defs.triv.
rewrite -> def_iforall.
rewrite -> def_of in Hk.
rewrite -> def_kind in Hk.
apply tr_all_intro.
  {
  eapply deq_intro; eauto.
  }
simpsub.
replace (subst (dot triv sh1) m) with m; auto.
so (subst_into_absent_single _#3 triv Hhyg) as Heq.
simpsubin Heq.
symmetry; auto.
Qed.


