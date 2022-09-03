
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Tactics.
Require Import Sequence.
Require Import Relation.
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

Require Import ValidationUtil.
Require Import Defined.



Lemma def_lleq : Defs.lleq = leqtp.
Proof.
auto.
Qed.


Hint Rewrite def_lleq : prepare.



Lemma univFormInv_valid : univFormInv_obligation.
Proof.
prepare.
intros G I ext0 Huniv.
apply tr_univ_formation_invert.
auto.
Qed.
