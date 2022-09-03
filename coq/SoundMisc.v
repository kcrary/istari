
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Tactics.
Require Import Axioms.
Require Import Sigma.
Require Import Equality.
Require Import Sequence.
Require Import Relation.
Require Import Ordinal.
Require Import Syntax.
Require Import SimpSub.
Require Import Dynamic.
Require Import Ofe.
Require Import Uniform.
Require Import Intensional.
Require Import Candidate.
Require Import System.
Require Import Semantics.
Require Import SemanticsKnot.
Require Import Judgement.
Require Import Hygiene.
Require Import ProperClosed.
Require Import ProperFun.
Require Import Shut.

Lemma sound_inhabitation_formation :
  forall G m n a,
    pseq G (deq m n a)
    -> pseq G (deqtype a a).
Proof.
intros G m n a.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype.
rewrite -> seq_deq in Hseq.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hl & Hr & _).
eauto.
Qed.
