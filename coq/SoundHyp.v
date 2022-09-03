
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

Require Import ContextHygiene.
Require Import MapTerm.


Lemma cloctx_index :
  forall object i G (h : @hyp object),
    index i G h
    -> cloctx G
    -> hygieneh (fun j => j < length G - i - 1) h.
Proof.
intros object i G h Hindex.
induct Hindex.

(* 0 *)
{
intros h G Hcl.
cbn.
invertc Hcl.
intros _ Hcl.
rewrite -> ctxpred_length in Hcl.
eapply hygieneh_weaken; eauto.
intros j Hj.
omega.
}

(* S *)
{
intros j h' G h _ IH Hcl.
invertc Hcl.
intros Hcl _.
cbn.
apply IH; auto.
}
Qed.


Lemma seqctx_index :
  forall i s s' G j h,
    seqctx i s s' G
    -> index j G h
    -> seqhyp i (project s j) (project s' j) (substh (compose (sh (S j)) s) h) (substh (compose (sh (S j)) s') h).
Proof.
intros i s s' G j h Hseq Hindex.
revert s s' Hseq.
induct Hindex.

(* 0 *)
{
intros h G s1 s2 Hseq.
invert Hseq; [].
intros m1 m2 s1' s2' Hss Hm <- <-.
simpsub.
auto.
}

(* S *)
{
intros j h' G h Hindex IH s s' Hss.
invertc Hss; [].
intros m1 m2 s1' s2' Hss' _ <- <-.
simpsub.
auto.
}
Qed.


Lemma sound_hyp_tm_pre :
  forall G i a,
    index i G (hyp_tm a)
    -> seq G (deq (var i) (var i) (subst (sh (S i)) a)).
Proof.
intros G j a Hindex.
apply seq_i.
intros i s s' Hs.
so (seqctx_index _#6 (pwctx_impl_seqctx _#4 Hs) Hindex) as H.
simpsubin H.
(* For some reason, inversion is fouling up (sh (S j)), so we'll hide the ball. *)
remember (sh (S j)) as shsj eqn:Heqshsj.
invertc H.
intros R Hal Har Hm.
subst shsj.
exists R.
simpsub.
do2 4 split; auto.
Qed.


Lemma sound_hyp_tm :
  forall G i a,
    index i G (hyp_tm a)
    -> pseq G (deq (var i) (var i) (subst (sh (S i)) a)).
Proof.
intros G i a Hindex.
exists 0.
intros j _.
apply sound_hyp_tm_pre.
apply index_app_left; auto.
Qed.


Lemma sound_hyp_tp_pre :
  forall G i,
    index i G hyp_tp
    -> seq G (deqtype (var i) (var i)).
Proof.
intros G j Hindex.
rewrite -> seq_eqtype.
intros i s s' Hs.
so (seqctx_index _#6 (pwctx_impl_seqctx _#4 Hs) Hindex) as H.
simpsubin H.
invertc H.
intros R Hal Har.
exists R.
simpsub.
do2 3 split; auto.
Qed.


Lemma sound_hyp_tp :
  forall G i,
    index i G hyp_tp
    -> pseq G (deqtype (var i) (var i)).
Proof.
intros G i Hindex.
exists 0.
intros j _.
apply sound_hyp_tp_pre.
apply index_app_left; auto.
Qed.
