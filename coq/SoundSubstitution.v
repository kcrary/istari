
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

Require Import ProperLevel.
Require Import ProperDownward.
Require Import Truncate.
Require Import ProperEquiv.
Require Import Equivalence.
Require Import Subsumption.


(* Since I can't rewrite under a lambda. *)
Lemma ctxpred_app_substctx_length :
  forall object (G1 G2 : @context object) s,
    ctxpred (substctx s G2 ++ G1) = (fun i => i < length G2 + length G1).
Proof.
intros object G1 G2 s.
rewrite -> ctxpred_length.
fextensionality 1.
intro i.
rewrite -> app_length.
rewrite -> length_substctx.
pextensionality; omega.
Qed.


Lemma seqhyp_relhyp_1 :
  forall i m1 m2 h1 h1' h2,
    relhyp i true h1 h1'
    -> seqhyp i m1 m2 h1 h2
    -> seqhyp i m1 m2 h1' h2.
Proof.
intros i m1 m2 h1 h1' h2 Hh2 Hm.
eapply seqhyp_relhyp; eauto.
exact (relhyp_refl _#5 Hm ander).
Qed.


Lemma seqhyp_relhyp_2 :
  forall i m1 m2 h1 h2 h2',
    relhyp i false h2 h2'
    -> seqhyp i m1 m2 h1 h2
    -> seqhyp i m1 m2 h1 h2'.
Proof.
intros i m1 m2 h1 h2 h2' Hh2 Hm.
eapply seqhyp_relhyp; eauto.
exact (relhyp_refl _#5 Hm andel).
Qed.


Lemma extend_seqctx_left :
  forall i s s' t G1 G2,
    pwctx i s s' (G2 ++ G1)
    -> seqctx i (compose (sh (length G2)) s) t G1
    -> exists t',
         pwctx i s t' (G2 ++ G1)
         /\ compose (sh (length G2)) t' = t.
Proof.
intros i s s' t G1 G2 Hs Ht.
cut (exists t', seqctx i s t' (G2 ++ G1) /\ compose (sh (length G2)) t' = t).
  {
  intros (t' & H & Heq).
  exists t'.
  split; auto.
  eapply seqctx_pwctx_left; eauto.
  }
revert s s' Hs Ht.
induct G2.

(* nil *)
{
intros s s' Hs Ht.
exists t.
cbn in Hs.
cbn in Ht.
cbn.
split; auto.
}

(* cons *)
{
intros h G2 IH ss ss' Hss Ht.
invertc Hss.
intros m p s s' Hs Hmq Hleft Hright <- <-.
cbn [length] in Ht.
simpsubin Ht.
so (IH _ _ Hs Ht) as (t' & Ht' & Heq).
exists (dot p t').
split; auto.
cbn.
apply seqctx_cons; auto.
eapply seqhyp_relhyp_2; eauto.
apply (Hleft i false); auto using smaller_le.
}
Qed.


Lemma extend_seqctx_right :
  forall i s s' t G1 G2,
    pwctx i s s' (G2 ++ G1)
    -> seqctx i t (compose (sh (length G2)) s') G1
    -> exists t',
         pwctx i t' s' (G2 ++ G1)
         /\ compose (sh (length G2)) t' = t.
Proof.
intros i s s' t G1 G2 Hs Ht.
cut (exists t', seqctx i t' s' (G2 ++ G1) /\ compose (sh (length G2)) t' = t).
  {
  intros (t' & H & Heq).
  exists t'.
  split; auto.
  eapply seqctx_pwctx_right; eauto.
  }
revert s s' Hs Ht.
induct G2.

(* nil *)
{
intros s s' Hs Ht.
exists t.
cbn in Hs.
cbn in Ht.
cbn.
split; auto.
}

(* cons *)
{
intros h G2 IH ss ss' Hss Ht.
invertc Hss.
intros m p s s' Hs Hmq Hleft Hright <- <-.
cbn [length] in Ht.
simpsubin Ht.
so (IH _ _ Hs Ht) as (t' & Ht' & Heq).
exists (dot m t').
split; auto.
cbn.
apply seqctx_cons; auto.
eapply seqhyp_relhyp_1; eauto.
apply (Hright i false); auto using smaller_le.
}
Qed.


Lemma subst_pwctx :
  forall G1 G2 a m i s s' A,
    pwctx i s s' (G2 ++ cons (hyp_tm a) G1)
    -> (forall j t t',
          pwctx j t t' (G2 ++ cons (hyp_tm a) G1)
          -> exists R,
               interp toppg true j (subst (compose (sh (S (length G2))) t) a) R
               /\ interp toppg false j (subst (compose (sh (S (length G2))) t') a) R
               /\ rel (den R) j (subst (compose (sh (S (length G2))) t) m) (subst (compose (sh (S (length G2))) t') m))
    -> interp toppg true i (subst (compose (sh (S (length G2))) s) a) A
    -> interp toppg false i (subst (compose (sh (S (length G2))) s') a) A
    -> rel (den A) i (subst (compose (sh (S (length G2))) s) m) (subst (compose (sh (S (length G2))) s') m)
    -> rel (den A) i (project s (length G2)) (subst (compose (sh (S (length G2))) s') m)
    -> pwctx i (compose (under (length G2) sh1) s) (compose (under (length G2) sh1) s') (substctx (dot m id) G2 ++ G1).
Proof.
intros G1 G2 a m i s s' A Hs Hseqmm Hal Har Hm Hvm.
assert (forall j d s'',
          smaller j i d
          -> seqctx j (compose (sh (S (length G2))) s) s'' (qpromote d G1)
          -> rel (den A) j (subst (compose (sh (S (length G2))) s) m) (subst s'' m)) as Hseqm.
  {
  intros j d t Hsmall Ht.
  so (smaller_impl_le _#3 Hsmall) as Hj.
  exploit (extend_seqctx_left j s s' t G1 (G2 ++ hyp_tm a :: nil)) as H.
    {
    rewrite <- app_assoc.
    cbn.
    apply (pwctx_downward i); eauto.
    }

    {
    rewrite -> app_length.
    cbn [length].
    replace (length G2 + 1) with (S (length G2)) by omega.
    eapply seqctx_qdemote; eauto.
    }
  destruct H as (t' & Ht' & Heq).
  rewrite <- app_assoc in Ht'.
  cbn [List.app] in Ht'.
  so (Hseqmm _#3 Ht') as (A' & Hal' & _ & Hm').
  so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst A'.
  simpsubin Hm'.
  rewrite -> app_length in Heq.
  cbn [length] in Heq.
  replace (length G2 + 1) with (S (length G2)) in Heq by omega.
  rewrite -> Heq in Hm'.
  destruct Hm'; auto.
  }
assert (forall j d s'',
          smaller j i d
          -> seqctx j s'' (compose (sh (S (length G2))) s') (qpromote d G1)
          -> rel (den A) j (subst s'' m) (subst (compose (sh (S (length G2))) s') m)) as Hseqm'.
  {
  intros j d t Hsmall Ht.
  so (smaller_impl_le _#3 Hsmall) as Hj.
  exploit (extend_seqctx_right j s s' t G1 (G2 ++ hyp_tm a :: nil)) as H.
    {
    rewrite <- app_assoc.
    cbn.
    apply (pwctx_downward i); eauto.
    }

    {
    rewrite -> app_length.
    cbn [length].
    replace (length G2 + 1) with (S (length G2)) by omega.
    eapply seqctx_qdemote; eauto.
    }
  destruct H as (t' & Ht' & Heq).
  rewrite <- app_assoc in Ht'.
  cbn [List.app] in Ht'.
  so (Hseqmm _#3 Ht') as (A' & _ & Har' & Hm').
  so (basic_fun _#7 (basic_downward _#7 Hj Har) Har'); subst A'.
  simpsubin Hm'.
  rewrite -> app_length in Heq.
  cbn [length] in Heq.
  replace (length G2 + 1) with (S (length G2)) in Heq by omega.
  rewrite -> Heq in Hm'.
  destruct Hm'; auto.
  }
clear Hseqmm.
simpsubin Hal.
simpsubin Har.
simpsubin Hm.
simpsubin Hvm.
revert s s' Hs Hal Har Hm Hvm Hseqm Hseqm'.
induct G2.
  (* nil *)
  {
  intros ss ss' Hss Hal Har _ _ _ _.
  simpsub.
  cbn [List.app].
  cbn in Hss.
  invert Hss.
  intros n q s s' H _ _ _ <- <-.
  simpsub.
  exact H.
  }

  (* cons *)
  {
  intros h G2 IH ss ss' Hss Hal Har Hm Hvm Hseqm Hseqm'.
  cbn [length].
  cbn in Hss.
  invertc Hss.
  intros n q s s' Hs Hnq Hleft Hright <- <-.
  cbn [length] in Hvm.
  simpsubin Hvm.
  cbn [length] in Hm.
  simpsubin Hm.
  cbn [length] in Har.
  simpsubin Har.
  cbn [length] in Hal.
  simpsubin Hal.
  simpsub.
  rewrite <- app_comm_cons.
  (* The following proofs of Hmod and Hmod' are the essentially the same, but enough
     differences that it's hard to factor them out.
  *)
  assert (seqctx i (compose (under (length G2) (dot (subst sh1 m) sh1)) s) s' (G2 ++ hyp_tm a :: G1)) as Hmod.
    {
    clear n q h Hnq Hleft Hright Hal IH Hseqm Hseqm'.
    revert s s' Hs Har Hm Hvm.
    induct G2.
      (* nil *)
      {
      intros ss ss' Hss Har Hm Hvm.
      cbn in Hss.
      invertc Hss.
      intros n q s s' Hs Hh _ _ <- <-.
      cbn.
      simpsub.
      apply seqctx_cons; auto using pwctx_impl_seqctx.
      simpsub.
      cbn in Hm.
      cbn in Hvm.
      cbn in Har.
      simpsubin Hh.
      invertc Hh.
      intros A' Hal Har' Hnq.
      so (basic_fun _#7 Har Har'); subst A'.
      apply (seqhyp_tm _#5 A); auto.
      eapply urel_zigzag; eauto.
      }

      (* cons *)
      {
      intros h G2 IH ss ss' Hss Har Hm Hvm.
      cbn [List.app].
      cbn in Hss.
      invertc Hss.
      intros n q s s' Hs Hh Hleft Hright <- <-.
      cbn [length].
      simpsub.
      apply seqctx_cons; auto.
      refine (seqhyp_relhyp _#7 _ (relhyp_refl _#5 Hh ander) Hh).
      apply (Hright i false); auto using smaller_le.
      }
    }
  assert (seqctx i s (compose (under (length G2) (dot (subst sh1 m) sh1)) s') (G2 ++ hyp_tm a :: G1)) as Hmod'.
    {
    clear n q h Hnq Hleft Hright Hal IH Hm Hmod Hseqm Hseqm'.
    revert s s' Hs Har Hvm.
    induct G2.
      (* nil *)
      {
      intros ss ss' Hss Har Hvm.
      cbn in Hss.
      invertc Hss.
      intros n q s s' Hs Hh _ _ <- <-.
      cbn.
      simpsub.
      apply seqctx_cons; auto using pwctx_impl_seqctx.
      simpsub.
      cbn in Hvm.
      cbn in Har.
      simpsubin Hh.
      invertc Hh.
      intros A' Hal Har' Hnq.
      so (basic_fun _#7 Har Har'); subst A'.
      apply (seqhyp_tm _#5 A); auto.
      }

      (* cons *)
      {
      intros h G2 IH ss ss' Hss Har Hvm.
      cbn [List.app].
      cbn in Hss.
      invertc Hss.
      intros n q s s' Hs Hh Hleft Hright <- <-.
      cbn [length].
      simpsub.
      apply seqctx_cons; auto.
      refine (seqhyp_relhyp _#7 (relhyp_refl _#5 Hh andel) _ Hh).
      apply (Hleft i false); auto using smaller_le.
      }
    }
  apply pwctx_cons; auto; clear IH.
    {
    simpsub.
    rewrite <- !compose_assoc.
    rewrite <- compose_under.
    simpsub.
    refine (seqhyp_relhyp _#7 _ _ Hnq).
      {
      apply (Hright _ false); auto using smaller_le.  (* uses Hmod *)
      }

      {
      apply (Hleft _ false); auto using smaller_le.  (* uses Hmod' *)
      }
    }

    (* The following proofs of pwctx's left and right are almost the same, but
       enough differences that it's hard to factor them out.
    *)

    {
    intros j d s'' Hsmall Hs'.
    rewrite <- !substh_qpromote_hyp.
    simpsub.
    rewrite <- compose_assoc.
    rewrite <- compose_under.
    simpsub.
    eapply relhyp_trans.
      {
      apply relhyp_symm.
      so (relhyp_smaller _#6 Hsmall (Hleft _#3 (smaller_le _ _ (le_refl _)) Hmod')) as H.
      rewrite <- !substh_qpromote_hyp in H.
      rewrite -> qpromote_hyp_combine in H.
      rewrite -> Bool.orb_false_r in H.
      exact H.
      }
    apply Hleft; auto.
    cbn [length] in Hseqm.
    simpsubin Hseqm.
    clear h n q Hnq Hleft Hright Hmod' Hseqm'.
    revert s s' s'' Hs Hs' Hal Har Hm Hvm Hseqm Hmod.
    induct G2.
      (* nil *)
      {
      intros ss ss' s'' Hss Hs' Hal Har Hm Hvm Hseqm _.
      cbn in Hss.
      invertc Hss.
      intros n q s s' Hs Hnq Hleft _ <- <-.
      cbn in Hs'.
      cbn.
      rewrite -> qpromote_cons.
      rewrite -> qpromote_hyp_tm.
      apply seqctx_cons; auto.
      simpsub.
      cbn in Hm.
      cbn in Hvm.
      cbn in Hseqm.
      cbn in Hal.
      cbn in Har.
      so (Hseqm _#3 Hsmall Hs') as Hm'.
      so (smaller_impl_le _#3 Hsmall) as Hj.
      apply (seqhyp_relhyp_2 _#4 (hyp_tm (subst s' a))).
        {
        so (Hleft _#3 Hsmall Hs') as H.
        rewrite -> qpromote_hyp_tm in H.
        exact H.
        }

        {
        apply (seqhyp_tm _#5 (iutruncate (S j) A)); auto.
          {
          eapply basic_downward; eauto.
          }

          {
          eapply basic_downward; eauto.
          }
        split; [omega |].
        exact (urel_zigzag _#7 (urel_downward_leq _#6 Hj Hvm) (urel_downward_leq _#6 Hj Hm) Hm').
        }
      }

      (* cons *)
      {
      intros h G2 IH ss ss' ss'' Hss Hs' Hal Har Hm Hvm Hseqm Hmod.
      invertc Hss.
      intros n q s s' Hs Hnq Hleft Hright <- <-.
      cbn [length] in Hs'.
      simpsubin Hs'.
      rewrite <- app_comm_cons in Hs'.
      rewrite -> qpromote_cons in Hs'.
      invertc Hs'.
      intros r s'' Hs' Hr <-.
      cbn [List.app length].
      rewrite -> qpromote_cons.
      simpsub.
      cbn [List.app length] in Hmod.
      simpsubin Hmod.
      invertc Hmod.
      intros Hmod _.
      apply seqctx_cons; eauto.
      rewrite <- substh_qpromote_hyp in Hr.
      simpsubin Hr.
      rewrite <- compose_assoc in Hr.
      rewrite <- compose_under in Hr.
      simpsubin Hr.
      eapply seqhyp_relhyp_1; eauto.
      apply relhyp_symm.
      apply Hright; auto.
      eapply seqctx_smaller; eauto.
      }
    }

    {
    intros j d s'' Hsmall Hs'.
    rewrite <- !substh_qpromote_hyp.
    simpsub.
    rewrite <- compose_assoc.
    rewrite <- compose_under.
    simpsub.
    eapply relhyp_trans.
      {
      apply relhyp_symm.
      so (relhyp_smaller _#6 Hsmall (Hright _#3 (smaller_le _ _ (le_refl _)) Hmod)) as H.
      rewrite <- !substh_qpromote_hyp in H.
      rewrite -> qpromote_hyp_combine in H.
      rewrite -> Bool.orb_false_r in H.
      exact H.
      }
    apply Hright; auto.
    cbn [length] in Hseqm'.
    simpsubin Hseqm'.
    clear h n q Hnq Hleft Hright Hmod Hseqm.
    revert s s' s'' Hs Hs' Hal Har Hm Hvm Hseqm' Hmod'.
    induct G2.
      (* nil *)
      {
      intros ss ss' s'' Hss Hs' Hal Har Hm Hvm Hseqm' _.
      cbn in Hss.
      invertc Hss.
      intros n q s s' Hs Hnq _ Hright <- <-.
      cbn in Hs'.
      cbn.
      rewrite -> qpromote_cons.
      rewrite -> qpromote_hyp_tm.
      apply seqctx_cons; auto.
      simpsub.
      cbn in Hm.
      cbn in Hvm.
      cbn in Hseqm'.
      cbn in Hal.
      cbn in Har.
      so (Hseqm' _#3 Hsmall Hs') as Hm'.
      so (smaller_impl_le _#3 Hsmall) as Hj.
      apply (seqhyp_relhyp_1 _#3 (hyp_tm (subst s a))).
        {
        so (Hright _#3 Hsmall Hs') as H.
        rewrite -> qpromote_hyp_tm in H.
        exact H.
        }

        {
        apply (seqhyp_tm _#5 (iutruncate (S j) A)); auto.
          {
          eapply basic_downward; eauto.
          }

          {
          eapply basic_downward; eauto.
          }
        split; [omega |].
        simpsubin Hnq.
        invertc Hnq.
        intros A' Hal' _ Hnq.
        so (basic_fun _#7 Hal Hal'); subst A'.
        exact (urel_zigzag _#7 Hm' (urel_downward_leq _#6 Hj Hvm) (urel_downward_leq _#6 Hj Hnq)).
        }
      }

      (* cons *)
      {
      intros h G IH ss ss' ss'' Hss Hs' Hal Har Hm Hvm Hseqm' Hmod'.
      invertc Hss.
      intros n q s s' Hs Hnq Hleft Hright <- <-.
      cbn [length] in Hs'.
      simpsubin Hs'.
      rewrite <- app_comm_cons in Hs'.
      rewrite -> qpromote_cons in Hs'.
      invertc Hs'.
      intros r s'' Hs' Hr <-.
      cbn [List.app length].
      rewrite -> qpromote_cons.
      simpsub.
      cbn [List.app length] in Hmod'.
      simpsubin Hmod'.
      invertc Hmod'.
      intros Hmod' _.
      apply seqctx_cons; eauto.
      rewrite <- substh_qpromote_hyp in Hr.
      simpsubin Hr.
      rewrite <- compose_assoc in Hr.
      rewrite <- compose_under in Hr.
      simpsubin Hr.
      eapply seqhyp_relhyp_2; eauto.
      apply relhyp_symm.
      apply Hleft; auto.
      eapply seqctx_smaller; eauto.
      }
    }
  }
Qed.


(* This proof is messier than it seems like it should be, because of the nested inductions on
   G2 within an induction on G2, and because of the need to do everything twice.
*)

Lemma sound_substitution_pre :
  forall G1 G2 a m n n' b,
    seq (G2 ++ cons (hyp_tm a) G1) (deqtype b b)
    -> seq (G2 ++ cons (hyp_tm a) G1) (deq (var (length G2)) (subst (sh (S (length G2))) m) (subst (sh (S (length G2))) a))
    -> seq (substctx (dot m id) G2 ++ G1) (deq n n' (subst (under (length G2) (dot m id)) b))
    -> seq (G2 ++ cons (hyp_tm a) G1) (deq (subst (under (length G2) sh1) n) (subst (under (length G2) sh1) n') b).
Proof.
intros G1 G2 a m r1 r2 b Hseqb Hseqvm Hseqr.
rewrite -> seq_eqtype in Hseqb.
apply seq_i.
invertc Hseqvm; intro Hseqvm.
invertc Hseqr; intro Hseqr.
intros i s s' Hs.
so (Hseqvm _#3 Hs) as (A & Hal & Har & Hvar & Hm & Hvm).
simpsubin Hal.
simpsubin Har.
simpsubin Hvar.
simpsubin Hm.
simpsubin Hvm.
exploit (subst_pwctx G1 G2 a m i s s' A) as Ht; auto.
  {
  intros j t t' Ht.
  so (Hseqvm _#3 Ht) as (R & Hl & Hr & _ & H & _).
  exists R.
  simpsubin Hl.
  simpsubin Hr.
  simpsubin H.
  do2 2 split; auto.
  }
set (t := compose (under (length G2) sh1) s) in Ht.
set (t' := compose (under (length G2) sh1) s') in Ht.
so (Hseqb _#3 Hs) as (B & Hbl & Hbr & _).
so (Hseqr _#3 Ht) as (B' & _ & Hbr' & Hr1 & Hr2 & Hr12).
assert (B = B').
  {
  unfold t' in Hbr'.
  rewrite <- subst_compose in Hbr'.
  rewrite <- compose_assoc in Hbr'.
  rewrite <- compose_under in Hbr'.
  simpsubin Hbr'.
  set (u := compose (under (length G2) (dot (subst sh1 m) sh1)) s') in Hbr'.
  assert (pwctx i s u (G2 ++ hyp_tm a :: G1)) as Hsu.
    {
    clear t t' Ht B B' Hbl Hbr Hbr' Hr1 Hr2 Hr12 Hseqb Hseqr Hseqvm.
    subst u.
    eapply seqctx_pwctx_left; eauto.
    simpsubin Hal.
    simpsubin Har.
    simpsubin Hvar.
    simpsubin Hm.
    simpsubin Hvm.
    revert s s' Hs Hal Har Hvar Hm Hvm.
    induct G2.
      (* nil *)
      {
      intros ss ss' Hss Hal Har _ _ Hvm.
      cbn [List.app length].
      cbn [List.app] in Hss.
      invertc Hss.
      intros n q s s' Hs _ _ _ <- <-.
      simpsub.
      apply seqctx_cons; auto using pwctx_impl_seqctx.
      simpsub.
      apply (seqhyp_tm _#5 A); auto.
      }

      (* cons *)
      {
      intros h G2 IH ss ss' Hss Hal Har Hvar Hm Hvm.
      cbn [List.app].
      cbn in Hss.
      invertc Hss.
      intros n q s s' Hs Hnq Hleft Hright <- <-.
      cbn [length].
      simpsub.
      apply seqctx_cons; auto.
      refine (seqhyp_relhyp _#7 (relhyp_refl _#5 Hnq andel) _ Hnq).
      refine (Hleft _#3 (smaller_refl _) _).
      cbn.
      apply IH; auto.
      }
    }
  so (Hseqb _#3 Hsu) as (B'' & Hbl' & Hbr'' & _).
  so (interp_fun _#7 Hbl Hbl'); subst B''.
  so (interp_fun _#7 Hbr' Hbr''); subst B'.
  reflexivity.
  }
subst B'.
exists B.
simpsub.
do2 4 split; eauto using interp_increase, toppg_max.
Qed.



Lemma sound_substitution :
  forall G1 G2 a m n n' b,
    pseq (G2 ++ cons (hyp_tm a) G1) (deqtype b b)
    -> pseq (G2 ++ cons (hyp_tm a) G1) (deq (var (length G2)) (subst (sh (S (length G2))) m) (subst (sh (S (length G2))) a))
    -> pseq (substctx (dot m id) G2 ++ G1) (deq n n' (subst (under (length G2) (dot m id)) b))
    -> pseq (G2 ++ cons (hyp_tm a) G1) (deq (subst (under (length G2) sh1) n) (subst (under (length G2) sh1) n') b).
Proof.
intros G1 G2 a m n n' b.
revert G1.
refine (seq_pseq_hyp 0 3 _ [_] _ _ [_] _ _ [] _ _ [_] _ _).
cbn.
intros G H1 H2 H3 _.
eapply sound_substitution_pre; eauto.
Qed.



(* If the variable doesn't appear in the conclusion, we can drop the type formation premise. *)
Lemma sound_substitution_simple_pre :
  forall G1 G2 a m n n' b,
    seq (G2 ++ cons (hyp_tm a) G1) (deq (var (length G2)) (subst (sh (S (length G2))) m) (subst (sh (S (length G2))) a))
    -> seq (substctx (dot m id) G2 ++ G1) (deq n n' b)
    -> seq (G2 ++ cons (hyp_tm a) G1) (deq (subst (under (length G2) sh1) n) (subst (under (length G2) sh1) n') (subst (under (length G2) sh1) b)).
Proof.
intros G1 G2 a m r1 r2 b Hseqvm Hseqr.
apply seq_i.
invertc Hseqvm; intro Hseqvm.
invertc Hseqr; intro Hseqr.
intros i s s' Hs.
so (Hseqvm _#3 Hs) as (A & Hal & Har & Hvar & Hm & Hvm).
simpsubin Hal.
simpsubin Har.
simpsubin Hvar.
simpsubin Hm.
simpsubin Hvm.
exploit (subst_pwctx G1 G2 a m i s s' A) as Ht; auto.
  {
  intros j t t' Ht.
  so (Hseqvm _#3 Ht) as (R & Hl & Hr & _ & H & _).
  exists R.
  simpsubin Hl.
  simpsubin Hr.
  simpsubin H.
  do2 2 split; auto.
  }
set (t := compose (under (length G2) sh1) s) in Ht.
set (t' := compose (under (length G2) sh1) s') in Ht.
so (Hseqr _#3 Ht) as (B & Hbl & Hbr & Hr1 & Hr2 & Hr12).
exists B.
simpsub.
do2 4 split; eauto using interp_increase, toppg_max.
Qed.


Lemma sound_substitution_simple :
  forall G1 G2 a m n n' b,
    pseq (G2 ++ cons (hyp_tm a) G1) (deq (var (length G2)) (subst (sh (S (length G2))) m) (subst (sh (S (length G2))) a))
    -> pseq (substctx (dot m id) G2 ++ G1) (deq n n' b)
    -> pseq (G2 ++ cons (hyp_tm a) G1) (deq (subst (under (length G2) sh1) n) (subst (under (length G2) sh1) n') (subst (under (length G2) sh1) b)).
Proof.
intros G1 G2 a m n n' b.
revert G1.
refine (seq_pseq_hyp 0 2 _ [_] _ _ [] _ _ [_] _ _).
cbn.
intros G H1 H2 _.
eapply sound_substitution_simple_pre; eauto.
Qed.


Lemma sound_strengthen_context_pre :
  forall G1 G2 a b J,
    seq G1 (deqtype a a)
    -> seq (G2 ++ hyp_tm b :: G1) (dsubtype (subst (sh (S (length G2))) a) (subst (sh (S (length G2))) b))
    -> seq (G2 ++ hyp_tm b :: G1) (deq (var (length G2)) (var (length G2)) (subst (sh (S (length G2))) a))
    -> seq (G2 ++ hyp_tm a :: G1) J
    -> seq (G2 ++ hyp_tm b :: G1) J.
Proof.
intros G1 G2 a b J Ha Hsub Hof HseqJ.
destruct J as [m n c].
rewrite -> seq_eqtype in Ha.
rewrite -> seq_subtype in Hsub.
rewrite -> seq_deq in Hof, HseqJ |- *.
intros i s s' Hs.
apply HseqJ.
clear m n c HseqJ.
so (Hsub _#3 Hs) as (A & B & Hal & Har & Hbl & Hbr & H).
renameover H into Hsub.
so (Hof _#3 Hs) as (A' & Hal' & _ & H & _).
renameover H into Hof.
simpsubin Hof.
so (interp_fun _#7 Hal Hal'); subst A'.
clear Hal'.
cut (pwctx i s s' (G2 ++ hyp_tm a :: G1)
     /\ (forall j d s'',
           smaller j i d
           -> seqctx j s s'' (qpromote d (G2 ++ hyp_tm a :: G1))
           -> seqctx j s s'' (qpromote d (G2 ++ hyp_tm b :: G1)))
     /\ (forall j d s'',
           smaller j i d
           -> seqctx j s'' s' (qpromote d (G2 ++ hyp_tm a :: G1))
           -> seqctx j s'' s' (qpromote d (G2 ++ hyp_tm b :: G1)))).
  {
  intros (H & _).
  exact H.
  }
revert s s' Hs Hal Har Hbl Hbr Hsub Hof.
induct G2.

(* nil *)
{
intros ss ss' Hss Hal Har Hbl Hbr Hsub Hof.
cbn [List.app length] in * |- *.
invertc Hss.
intros m p s s' Hs _ Hleft Hright <- <-.
simpsubin Hal.
simpsubin Har.
simpsubin Hbl.
simpsubin Hbr.
simpsubin Hof.
do2 2 split.
  {
  apply pwctx_cons_tm_seq; auto.
    {
    simpsub.
    apply (seqhyp_tm _#5 A); auto.
    }

    {
    intros j t t' Ht.
    so (Ha _#3 Ht) as (R & Hl & Hr & _).
    eauto.
    }
  }

  {
  intros j d tt Hsmall Htt.
  so (smaller_impl_le _#3 Hsmall) as Hj.
  rewrite -> qpromote_cons in Htt |- *.
  rewrite -> qpromote_hyp_tm in Htt |- *.
  invertc Htt.
  intros q t Ht Hmq <-.
  simpsubin Hmq.
  invertc Hmq.
  intros A' Hal' Hat Hmq.
  so (interp_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst A'.
  apply seqctx_cons; auto.
  apply (seqhyp_tm _#5 (iutruncate (S j) B)); auto.
    {
    eapply basic_downward; eauto.
    }

    {
    so (Hleft _#3 Hsmall Ht) as H.
    rewrite -> qpromote_hyp_tm in H.
    simpsubin H.
    invertc H.
    intros B' Hbr' Hbt.
    so (interp_fun _#7 (basic_downward _#7 Hj Hbr) Hbr'); subst B'.
    auto.
    }

    {
    destruct Hmq as (Hjj & Hmq).
    split; auto.
    }
  }

  {
  intros j d tt Hsmall Htt.
  so (smaller_impl_le _#3 Hsmall) as Hj.
  rewrite -> qpromote_cons in Htt |- *.
  rewrite -> qpromote_hyp_tm in Htt |- *.
  invertc Htt.
  intros q t Ht Hmq <-.
  simpsubin Hmq.
  invertc Hmq.
  intros A' Hat Har' Hmq.
  so (interp_fun _#7 (basic_downward _#7 Hj Har) Har'); subst A'.
  apply seqctx_cons; auto.
  apply (seqhyp_tm _#5 (iutruncate (S j) B)); auto.
    {
    so (Hright _#3 Hsmall Ht) as H.
    rewrite -> qpromote_hyp_tm in H.
    simpsubin H.
    invertc H.
    intros B' Hbl' Hbt.
    so (interp_fun _#7 (basic_downward _#7 Hj Hbl) Hbl'); subst B'.
    auto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    destruct Hmq as (Hjj & Hmq).
    split; auto.
    }
  }
}

(* cons *)
{
intros h G2 IH ss ss' Hss Hal Har Hbl Hbr Hsub Hof.
cbn [length List.app] in * |- *.
invertc Hss.
intros m p s s' Hs Hmp Hleft Hright <- <-.
exploit (IH s s') as H; auto.
  {
  simpsub.
  simpsubin Hal.
  auto.
  }

  {
  simpsub.
  simpsubin Har.
  auto.
  }

  {
  simpsub.
  simpsubin Hbl.
  auto.
  }

  {
  simpsub.
  simpsubin Hbr.
  auto.
  }
clear IH Hal Har Hbl Hbr Hsub Hof.
destruct H as (IH1 & IH2 & IH3).
do2 2 split.
  {
  apply pwctx_cons; auto.
  }

  {
  intros j d tt Hsmall Htt.
  rewrite -> qpromote_cons in Htt |- *.
  invertc Htt.
  intros q t Ht Hmq <-.
  apply seqctx_cons; auto.
  }

  {
  intros j d tt Hsmall Htt.
  rewrite -> qpromote_cons in Htt |- *.
  invertc Htt.
  intros q t Ht Hmq <-.
  apply seqctx_cons; auto.
  }
}
Qed.
  


Lemma sound_strengthen_context :
  forall G1 G2 a b J,
    pseq G1 (deqtype a a)
    -> pseq (G2 ++ hyp_tm b :: G1) (dsubtype (subst (sh (S (length G2))) a) (subst (sh (S (length G2))) b))
    -> pseq (G2 ++ hyp_tm b :: G1) (deq (var (length G2)) (var (length G2)) (subst (sh (S (length G2))) a))
    -> pseq (G2 ++ hyp_tm a :: G1) J
    -> pseq (G2 ++ hyp_tm b :: G1) J.
Proof.
intros G1 G2 a b J.
revert G1.
refine (seq_pseq_hyp 0 4 [] [] _ _ [_] _ _ [_] _ _ [_] _ _ [_] _ _).
cbn.
intros G1 Ha Hsub Hof HJ _.
eapply sound_strengthen_context_pre; eauto.
Qed.


(* Alas, the more general rule that generalizes in the context as well
   appears to be unsound.  For each hypothesis y:B[m] that we want to
   generalize to y:B[x], we would need to know that x:A |- B[x] : Type.

   Note that there's no need for a version that places the binding earlier
   than last.  If you want it earlier, you can move it up using exchange.
*)

Lemma sound_generalize_pre :
  forall G a m J,
    seq G (deq m m a)
    -> seq (cons (hyp_tm a) G) J
    -> seq G (substj (dot m id) J).
Proof.
intros G a m J Hseqm HseqJ.
destruct J as [r1 r2 b].
apply seq_i.
invertc Hseqm; intro Hseqm.
invertc HseqJ; intro Hseqr.
intros i s s' Hs.
cut (pwctx i (dot (subst s m) s) (dot (subst s' m) s') (cons (hyp_tm a) G)).
  {
  intros Hs'.
  so (Hseqr _#3 Hs') as (B & Hbl & Hbr & Hr1 & Hr2 & Hr12).
  exists B.
  simpsub.
  do2 4 split; auto.
  }
so (Hseqm _#3 Hs) as (A & Hal & Har & Hm & _).
clear Hseqr.
apply pwctx_cons_tm_seq; auto.
  {
  eapply seqhyp_tm; eauto.
  }

  {
  intros j t t' Ht.
  so (Hseqm _#3 Ht) as (R & Hl & Hr & _).
  eauto.
  }
Qed.


Lemma sound_generalize :
  forall G a m J,
    pseq G (deq m m a)
    -> pseq (cons (hyp_tm a) G) J
    -> pseq G (substj (dot m id) J).
Proof.
intros G a m J.
revert G.
refine (seq_pseq 0 2 [] _ [_] _ _ _).
cbn.
intros G Hseqm HseqJ.
eapply sound_generalize_pre; eauto.
Qed.


Lemma sound_generalize_tp_pre :
  forall G a J,
    seq G (deqtype a a)
    -> seq (cons hyp_tp G) J
    -> seq G (substj (dot a id) J).
Proof.
intros G a J Hseqa HseqJ.
destruct J as [r1 r2 b].
simpsub.
rewrite -> seq_eqtype in Hseqa.
rewrite -> seq_deq in HseqJ |- *.
intros i s s' Hs.
cut (pwctx i (dot (subst s a) s) (dot (subst s' a) s') (cons hyp_tp G)).
  {
  intros Hs'.
  so (HseqJ _#3 Hs') as (B & Hbl & Hbr & Hr1 & Hr2 & Hr12).
  exists B.
  simpsub.
  do2 4 split; auto.
  }
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
clear HseqJ.
apply pwctx_cons_tp; auto.
apply (seqhyp_tp _#3 A); auto.
Qed.


Lemma sound_generalize_tp :
  forall G a J,
    pseq G (deqtype a a)
    -> pseq (cons hyp_tp G) J
    -> pseq G (substj (dot a id) J).
Proof.
intros G a J.
revert G.
refine (seq_pseq 0 2 [] _ [_] _ _ _).
cbn.
intros G Hseqm HseqJ.
eapply sound_generalize_tp_pre; eauto.
Qed.


Lemma sound_generalize_eq :
  forall G a b m n p q,
    pseq G (deq m n a)
    -> pseq (cons (hyp_tm a) G) (deq p q b)
    -> pseq G (deq (subst1 m p) (subst1 n q) (subst1 m b)).
Proof.
intros G a b m n p q.
revert G.
refine (seq_pseq 0 2 [] _ [_] _ _ _).
cbn.
intros G Hseqmn Hseqpq.
rewrite -> seq_deq in Hseqmn, Hseqpq |- *.
intros i s s' Hs.
so (Hseqmn _ _ _ Hs) as (A & Hal & Har & Hm & Hn & Hmn).
assert (pwctx i (dot (subst s m) s) (dot (subst s' n) s') (cons (hyp_tm a) G)) as Hsmn.
  {
  apply pwctx_cons_tm_seq; auto.
    {
    eapply seqhyp_tm; eauto.
    }
    
    {
    intros j t t' Ht.
    so (Hseqmn _ _ _ Ht) as (R & Hl & Hr & _).
    eauto.
    }
  }
assert (pwctx i (dot (subst s m) s) (dot (subst s' m) s') (cons (hyp_tm a) G)) as Hsm.
  {
  apply pwctx_cons_tm_seq; auto.
    {
    eapply seqhyp_tm; eauto.
    }
    
    {
    intros j t t' Ht.
    so (Hseqmn _ _ _ Ht) as (R & Hl & Hr & _).
    eauto.
    }
  }
assert (pwctx i (dot (subst s n) s) (dot (subst s' n) s') (cons (hyp_tm a) G)) as Hsn.
  {
  apply pwctx_cons_tm_seq; auto.
    {
    eapply seqhyp_tm; eauto.
    }
    
    {
    intros j t t' Ht.
    so (Hseqmn _ _ _ Ht) as (R & Hl & Hr & _).
    eauto.
    }
  }
so (Hseqpq _ _ _ Hsm) as (R & Hbml & Hbmr & Hp & _).
so (Hseqpq _ _ _ Hsn) as (R' & Hbnl & Hbnr & _ & Hq & _).
so (Hseqpq _ _ _ Hsmn) as (R'' & Hbml' & Hbnr' & _ & _ & Hpq).
so (interp_fun _#7 Hbml Hbml'); subst R''.
so (interp_fun _#7 Hbnr Hbnr'); subst R'.
exists R.
simpsub.
do2 4 split; auto.
Qed.



Lemma sound_generalize_eq_type :
  forall G a b m n p q,
    pseq G (deq m n a)
    -> pseq (cons (hyp_tm a) G) (deq p q b)
    -> pseq G (deqtype (subst1 m b) (subst1 n b)).
Proof.
intros G a b m n p q.
revert G.
refine (seq_pseq 0 2 [] _ [_] _ _ _).
cbn.
intros G Hseqmn Hseqb.
rewrite -> seq_eqtype.
rewrite -> seq_deq in Hseqmn, Hseqb.
intros i s s' Hs.
so (Hseqmn _ _ _ Hs) as (A & Hal & Har & Hm & Hn & Hmn).
assert (pwctx i (dot (subst s m) s) (dot (subst s' n) s') (cons (hyp_tm a) G)) as Hsmn.
  {
  apply pwctx_cons_tm_seq; auto.
    {
    eapply seqhyp_tm; eauto.
    }
    
    {
    intros j t t' Ht.
    so (Hseqmn _ _ _ Ht) as (R & Hl & Hr & _).
    eauto.
    }
  }
assert (pwctx i (dot (subst s m) s) (dot (subst s' m) s') (cons (hyp_tm a) G)) as Hsm.
  {
  apply pwctx_cons_tm_seq; auto.
    {
    eapply seqhyp_tm; eauto.
    }
    
    {
    intros j t t' Ht.
    so (Hseqmn _ _ _ Ht) as (R & Hl & Hr & _).
    eauto.
    }
  }
assert (pwctx i (dot (subst s n) s) (dot (subst s' n) s') (cons (hyp_tm a) G)) as Hsn.
  {
  apply pwctx_cons_tm_seq; auto.
    {
    eapply seqhyp_tm; eauto.
    }
    
    {
    intros j t t' Ht.
    so (Hseqmn _ _ _ Ht) as (R & Hl & Hr & _).
    eauto.
    }
  }
so (Hseqb _ _ _ Hsm) as (R & Hbml & Hbmr & _).
so (Hseqb _ _ _ Hsn) as (R' & Hbnl & Hbnr & _).
so (Hseqb _ _ _ Hsmn) as (R'' & Hbml' & Hbnr' & _).
so (interp_fun _#7 Hbml Hbml'); subst R''.
so (interp_fun _#7 Hbnr Hbnr'); subst R'.
exists R.
simpsub.
auto.
Qed.


Lemma sound_compute_pre :
  forall G a a' m m' n n',
    hygiene (ctxpred G) a
    -> hygiene (ctxpred G) m
    -> hygiene (ctxpred G) n
    -> equiv a a'
    -> equiv m m'
    -> equiv n n'
    -> seq G (deq m' n' a')
    -> seq G (deq m n a).
Proof.
intros G a a' m m' n n' Hclaif Hclmif Hclnif Hequiva Hequivm Hequivn Hseq.
apply seq_i.
invertc Hseq; intro Hseq.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq _#3 Hs) as (A & Hal & Har & Hm & Hn & Hmn).
exists A.
do2 4 split.
  {
  eapply basic_equiv; eauto using subst_closub, equiv_symm, equiv_subst.
  }

  {
  eapply basic_equiv; eauto using subst_closub, equiv_symm, equiv_subst.
  }

  {
  refine (urel_equiv _#7 _ _ _ _ Hm); eauto using subst_closub, equiv_symm, equiv_subst.
  }

  {
  refine (urel_equiv _#7 _ _ _ _ Hn); eauto using subst_closub, equiv_symm, equiv_subst.
  }

  {
  refine (urel_equiv _#7 _ _ _ _ Hmn); eauto using subst_closub, equiv_symm, equiv_subst.
  }
Qed.


Lemma sound_compute :
  forall G a a' m m' n n',
    equiv a a'
    -> equiv m m'
    -> equiv n n'
    -> pseq G (deq m' n' a')
    -> pseq G (deq m n a).
Proof.
intros G a a' m m' n n' Heqa Heqb Heqn (i1, Hseq).
so (shut_term _ G a) as (i2 & Hcla).
so (shut_term _ G m) as (i3 & Hclm).
so (shut_term _ G n) as (i4 & Hcln).
so (upper_bound_all 4 i1 i2 i3 i4) as (i & Hi1 & Hi2 & Hi3 & Hi4 & _).
exists i; intros j Hj.
eapply sound_compute_pre; eauto using le_trans.
Qed.


Lemma sound_compute_hyp_pre :
  forall G1 G2 h h' J,
    hygieneh (ctxpred G1) h
    -> hygieneh (ctxpred G1) h'
    -> hygienej (ctxpred (G2 ++ h :: G1)) J
    -> equivh h h'
    -> seq (G2 ++ cons h' G1) J
    -> seq (G2 ++ cons h G1) J.
Proof.
intros G1 G2 h h' J Hclh Hclh' HclJ Hequivh Hseq.
cut (subsume (G2 ++ cons h G1) (G2 ++ cons h' G1) (under (length G2) id) (under (length G2) id)).
  {
  intro Hsubsume.
  eapply subsume_seq; eauto using hygienej_deq.
  simpsub.
  auto.
  }
replace G2 with (substctx id G2) at 2 by (simpsub; auto).
apply subsume_under.
clear J HclJ Hseq.
do2 2 split.
  {
  intros j.
  rewrite -> !ctxpred_length.
  split.
    {
    simpsub.
    intros Hj.
    apply hygiene_var.
    cbn in Hj |- *.
    auto.
    }

    {
    simpsub.
    intros H.
    invertc H.
    intros Hj.
    cbn in Hj |- *.
    auto.
    }
  }

  {
  intros j.
  rewrite -> !ctxpred_length.
  split.
    {
    simpsub.
    intros Hj.
    apply hygiene_var.
    cbn in Hj |- *.
    auto.
    }

    {
    simpsub.
    intros H.
    invertc H.
    intros Hj.
    cbn in Hj |- *.
    auto.
    }
  }
intros i ss ss' Hss.
invertc Hss.
intros m n s s' Hs Hmn Hleft Hright <- <-.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
simpsub.
do2 4 split; auto using equivsub_refl.
  {
  apply pwctx_cons; auto.
    {
    eapply seqhyp_equivh; eauto using equivh_subst.
      {
      eapply hygieneh_subst; eauto.
      }

      {
      eapply hygieneh_subst; eauto.
      }
    }

    {
    intros j b u Hj Hu.
    so (seqctx_impl_closub _#4 Hu) as (_ & Hclu).
    so (Hleft _#3 Hj Hu) as H.
    eapply relhyp_equiv_1; eauto.
    3:{
      eapply relhyp_equiv_2; eauto.
        {
        apply equivh_subst.
        apply equivh_qpromote_hyp; auto.
        }
        
        {
        rewrite -> substh_qpromote_hyp.
        rewrite <- hygieneh_qpromote.
        eapply hygieneh_subst; eauto.
        intros; eapply project_closub; eauto.
        rewrite -> ctxpred_qpromote; auto.
        }
      }

      {
      apply equivh_subst.
      apply equivh_qpromote_hyp; auto.
      }
    
      {
      rewrite -> substh_qpromote_hyp.
      rewrite <- hygieneh_qpromote.
      eapply hygieneh_subst; eauto.
      }
    }

    {
    intros j b u Hj Hu.
    so (seqctx_impl_closub _#4 Hu) as (Hclu & _).
    so (Hright _#3 Hj Hu) as H.
    eapply relhyp_equiv_1; eauto.
    3:{
      eapply relhyp_equiv_2; eauto.
        {
        apply equivh_subst.
        apply equivh_qpromote_hyp; auto.
        }
        
        {
        rewrite -> substh_qpromote_hyp.
        rewrite <- hygieneh_qpromote.
        eapply hygieneh_subst; eauto.
        intros; eapply project_closub; eauto.
        rewrite -> ctxpred_qpromote; auto.
        }
      }

      {
      apply equivh_subst.
      apply equivh_qpromote_hyp; auto.
      }
    
      {
      rewrite -> substh_qpromote_hyp.
      rewrite <- hygieneh_qpromote.
      eapply hygieneh_subst; eauto.
      }
    }
  }

  {
  intros j b uu Hj Huu.
  simpsub.
  rewrite -> qpromote_cons in Huu |- *.
  invertc Huu.
  intros p u Hu Hmp <-.
  apply seqctx_cons; auto.
  so (seqctx_impl_closub _#4 Hu) as (_ & Hclu).
  eapply seqhyp_equivh; eauto.
    {      
    apply equivh_subst.
    apply equivh_qpromote_hyp; auto.
    apply equivh_symm; auto.
    }

    {      
    apply equivh_subst.
    apply equivh_qpromote_hyp; auto.
    apply equivh_symm; auto.
    }

    {
    rewrite -> substh_qpromote_hyp.
    rewrite <- hygieneh_qpromote.
    eapply substh_closub; eauto.
    }

    {
    rewrite -> substh_qpromote_hyp.
    rewrite <- hygieneh_qpromote.
    eapply substh_closub; eauto.
    rewrite -> ctxpred_qpromote; auto.
    }
  }

  {
  intros j b uu Hj Huu.
  simpsub.
  rewrite -> qpromote_cons in Huu |- *.
  invertc Huu.
  intros p u Hu Hmp <-.
  apply seqctx_cons; auto.
  so (seqctx_impl_closub _#4 Hu) as (Hclu & _).
  eapply seqhyp_equivh; eauto.
    {      
    apply equivh_subst.
    apply equivh_qpromote_hyp; auto.
    apply equivh_symm; auto.
    }

    {      
    apply equivh_subst.
    apply equivh_qpromote_hyp; auto.
    apply equivh_symm; auto.
    }

    {
    rewrite -> substh_qpromote_hyp.
    rewrite <- hygieneh_qpromote.
    eapply substh_closub; eauto.
    rewrite -> ctxpred_qpromote; auto.
    }

    {
    rewrite -> substh_qpromote_hyp.
    rewrite <- hygieneh_qpromote.
    eapply substh_closub; eauto.
    }
  }
Qed.


Lemma sound_compute_hyp :
  forall G1 G2 h h' J,
    equivh h h'
    -> pseq (G2 ++ cons h' G1) J
    -> pseq (G2 ++ cons h G1) J.
Proof.
intros G1 G2 h h' J Hequiv (i1, Hseq).
so (shut_judgement _ (G2 ++ h :: G1) J) as (i2 & HclJ).
so (shut_hyp _ G1 h) as (i3 & Hclh).
so (shut_hyp _ G1 h') as (i4 & Hclh').
so (upper_bound_all 4 i1 i2 i3 i4) as (i & Hi1 & Hi2 & Hi3 & Hi4 & _).
exists i; intros j Hj.
autorewrite with canonlist.
cbn.
eapply (sound_compute_hyp_pre _ _ h h'); finish_pseq j.
Qed.
