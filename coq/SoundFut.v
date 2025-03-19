
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

Require Import SemanticsFut.
Require Import Equivalence.
Require Import Equivalences.
Require Import ProperLevel.
Require Import Defined.
Require Import PageType.
Require Import Subsumption.


Local Ltac prove_hygiene :=
  repeat (apply hygiene_auto; cbn; repeat2 split; auto);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1, subst_closub;
  try (apply hygiene_var; cbn; auto; done).


Lemma pwctx_cons_tml :
  forall i m p s s' a G,
    pwctx i s s' G
    -> hygiene clo m
    -> hygiene clo p
    -> hygiene (ctxpred G) a
    -> (i > 0 -> seqhyp (pred i) m p (hyp_tm (subst s a)) (hyp_tm (subst s' a)))
    -> (forall j s'',
          j < i
          -> pwctx j s s'' G
          -> relhyp j false (hyp_tm (subst s' a)) (hyp_tm (subst s'' a)))
    -> (forall j s'',
          j < i
          -> pwctx j s'' s' G
          -> relhyp j true (hyp_tm (subst s a)) (hyp_tm (subst s'' a)))
    -> pwctx i (dot m s) (dot p s') (cons (hyp_tml a) G).
Proof.
intros i m p s s' a G Hs Hclm Hclp Hcla Hh Hleft Hright.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
apply pwctx_cons; auto.
  {
  simpsub.
  destruct i as [| i].
    {
    apply (seqhyp_tml _#5 (iubase empty_urel)); eauto using subst_closub; try (intro; omega).
    }
  assert (S i > 0) as Hpos by omega.
  invert (Hh Hpos).
  intros R Hal Har Hmp.
  apply (seqhyp_tml _#5 R); eauto using subst_closub.
  }

  {
  intros j b s'' Hsmall Hs'.
  destruct b.
    {
    cbn.
    invert Hsmall.
    intros Hji.
    apply Hleft; auto.
    eapply seqctx_pwctx_demote_left; eauto.
    }

    {
    cbn.
    invert Hsmall.
    intros Hji.
    so (seqctx_impl_closub _#4 Hs') as (_ & Hcls'').
    destruct j as [| j].
      {
      apply (relhyp_tml _#4 (iubase empty_urel)); eauto using subst_closub; intro; omega.
      }
    exploit (Hleft j s'') as H.
      {
      omega.
      }

      {
      cbn in Hs'.
      apply (pwctx_downward (S j)); [omega |].
      refine (seqctx_pwctx_left _#5 _ Hs').
      eapply pwctx_downward; eauto.
      }
    invertc H.
    intros R Hal Har.
    apply (relhyp_tml _#4 R); eauto using subst_closub.
    }
  }

  {
  intros j b s'' Hsmall Hs'.
  destruct b.
    {
    cbn.
    invert Hsmall.
    intros Hji.
    apply Hright; auto.
    eapply seqctx_pwctx_demote_right; eauto.
    }

    {
    cbn.
    invert Hsmall.
    intros Hji.
    so (seqctx_impl_closub _#4 Hs') as (Hcls'' & _).
    destruct j as [| j].
      {
      apply (relhyp_tml _#4 (iubase empty_urel)); eauto using subst_closub; try (intro; omega).
      }
    exploit (Hright j s'') as H.
      {
      omega.
      }

      {
      cbn in Hs'.
      apply (pwctx_downward (S j)); [omega |].
      refine (seqctx_pwctx_right _#5 _ Hs').
      eapply pwctx_downward; eauto.
      }
    invertc H.
    intros R Hal Har.
    apply (relhyp_tml _#4 R); eauto using subst_closub.
    }
  }
Qed.


Lemma pwctx_cons_tml_seq :
  forall i m p s s' a G,
    pwctx i s s' G
    -> hygiene clo m
    -> hygiene clo p
    -> hygiene (ctxpred G) a
    -> (i > 0 -> seqhyp (pred i) m p (hyp_tm (subst s a)) (hyp_tm (subst s' a)))
    -> (forall i t t',
          pwctx i t t' (promote G)
          -> exists pg R,
               interp pg true i (subst t a) R
               /\ interp pg false i (subst t' a) R)
    -> pwctx i (dot m s) (dot p s') (cons (hyp_tml a) G).
Proof.
intros i m p s s' a G Hs Hclm Hclp Hcla Hh Hact.
apply pwctx_cons; auto.
  {
  simpsub.
  so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
  destruct i as [| i].
    {
    apply (seqhyp_tml _#5 (iubase empty_urel)); eauto using subst_closub; try omega.
    }
  invert (Hh (Nat.lt_0_succ _)).
  intros R Hl Hr Hmp.
  apply (seqhyp_tml _#5 R); eauto using subst_closub.
  }

  {
  intros j b u Hsmall Hu.
  destruct b.
    {
    cbn.
    so (pwctx_smaller _#6 Hsmall Hs) as Hsj.
    so (Hact j s s' Hsj) as (pg & R & Hl & Hr).
    so (Hact j s u (seqctx_pwctx_left _#5 Hsj Hu)) as (pg' & R' & Hl' & Hr').
    so (interp_fun _#7 Hl Hl'); subst R'.
    eapply relhyp_tm; eauto using interp_increase, toppg_max.
    }

    {
    cbn.
    cbn in Hu.
    so (pwctx_impl_closub _#4 Hs) as (_ & Hcls').
    so (seqctx_impl_closub _#4 Hu) as (_ & Hclu).
    destruct j as [| j].
      {
      apply (relhyp_tml _#4 (iubase empty_urel)); try (intros; omega);
      eapply subst_closub; eauto.
      }
    so (seqctx_promote _#4 Hu) as Hu'.
    so (pwctx_promote _#4 (pwctx_smaller _#6 Hsmall Hs)) as Hsj.
    cbn in Hsj.
    fold (promote G) in Hsj.
    so (Hact j s s' Hsj) as (pg & R & Hl & Hr).
    so (Hact j s u (seqctx_pwctx_left _#5 Hsj Hu')) as (pg' & R' & Hl' & Hr').
    so (interp_fun _#7 Hl Hl'); subst R'.
    apply (relhyp_tml _#4 R); try (eapply subst_closub; eauto);
    intro; cbn; eauto using interp_increase, toppg_max.
    }
  }

  {
  intros j b u Hsmall Hu.
  destruct b.
    {
    cbn.
    so (pwctx_smaller _#6 Hsmall Hs) as Hsj.
    so (Hact j s s' Hsj) as (pg & R & Hl & Hr).
    so (Hact j u s' (seqctx_pwctx_right _#5 Hsj Hu)) as (pg' & R' & Hl' & Hr').
    so (interp_fun _#7 Hr Hr'); subst R'.
    eapply relhyp_tm; eauto using interp_increase, toppg_max.
    }

    {
    cbn.
    cbn in Hu.
    so (pwctx_impl_closub _#4 Hs) as (Hcls & _).
    so (seqctx_impl_closub _#4 Hu) as (Hclu & _).
    destruct j as [| j].
      {
      apply (relhyp_tml _#4 (iubase empty_urel)); try (intros; omega);
      eapply subst_closub; eauto.
      }
    so (seqctx_promote _#4 Hu) as Hu'.
    so (pwctx_promote _#4 (pwctx_smaller _#6 Hsmall Hs)) as Hsj.
    cbn in Hsj.
    fold (promote G) in Hsj.
    so (Hact j s s' Hsj) as (pg & R & Hl & Hr).
    so (Hact j u s' (seqctx_pwctx_right _#5 Hsj Hu')) as (pg' & R' & Hl' & Hr').
    so (interp_fun _#7 Hr Hr'); subst R'.
    apply (relhyp_tml _#4 R); try (eapply subst_closub; eauto);
    intro; cbn; eauto using interp_increase, toppg_max.
    }
  }
Qed.


Lemma sound_fut_kind_formation :
  forall G lv k k',
    pseq (promote G) (deq k k' (kind lv))
    -> pseq G (deq lv lv pagetp)
    -> pseq G (deq (fut k) (fut k') (kind lv)).
Proof.
intros G lv k l.
revert G.
refine (seq_pseq_promote 2 [] k [] l 2 true [] _ false [] _ _ _); cbn.
intros G Hclk Hcll Hseq Hseqlv.
rewrite -> seq_eqkind in Hseq |- *.
rewrite -> seq_deq in Hseqlv.
eassert _ as Hlv; [refine (seq_pagetp_invert G lv _) |].
  {
  intros i t t' Ht.
  so (Hseqlv _#3 Ht) as (R & Hl & _ & Hlv & _).
  eauto.
  }
clear Hseqlv.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
destruct i as [| i].
  {
  so (Hlv _#3 Hs) as (pg & Hlvl & Hlvr).
  exists pg, (qfut qone), (iufut0 stop), (pginterp_lt_top _ _ Hlvl).
  simpsub.
  do2 9 split; auto;
  try (apply kinterp_eval_refl; apply interp_kfut_zero; eapply subst_closub; eauto);
  try (apply interp_eval_refl; apply interp_fut_zero; eapply subst_closub; eauto).
  }
so (pwctx_promote _#4 Hs) as Hs'.
so (Hseq _#3 Hs') as (pg & K & R & h & Hlvl & Hlvr & Hkl & Hkr & Hll & Hlr & Hklt & Hkrt & Hllt & Hlrt).
exists pg, (qfut K), (iufut stop (S i) R), h.
simpsub.
do2 9 split; auto;
try (apply kinterp_eval_refl; apply interp_kfut; auto);
try (apply interp_eval_refl; apply interp_fut; auto).
Qed.

                     
Lemma sound_fut_formation :
  forall G a b,
    pseq (promote G) (deqtype a b)
    -> pseq G (deqtype (fut a) (fut b)).
Proof.
intros G a b.
revert G.
refine (seq_pseq_promote 2 [] a [] b 1 true [] _ _ _); cbn.
intros G Hcla Hclb Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
destruct i as [| i].
  {
  exists (iufut0 stop).
  simpsub.
  do2 3 split;
  apply interp_eval_refl; apply interp_fut_zero; eapply subst_closub; eauto.
  }
so (pwctx_promote _#4 Hs) as Hs'.
so (Hseq _#3 Hs') as (R & Hal & Har & Hbl & Hbr).
exists (iufut stop (S i) R).
do2 3 split;
apply interp_eval_refl; apply interp_fut; auto.
Qed.


Lemma sound_fut_formation_univ :
  forall G lv a b,
    pseq (promote G) (deq a b (univ lv))
    -> pseq G (deq lv lv pagetp)
    -> pseq G (deq (fut a) (fut b) (univ lv)).
Proof.
intros G lv a b.
revert G.
refine (seq_pseq_promote 2 [] a [] b 2 true [] _ false [] _ _ _); cbn.
intros G Hcla Hclb Hseq Hseqlv.
rewrite -> seq_univ in Hseq |- *.
rewrite -> seq_deq in Hseqlv.
eassert _ as Hlv; [refine (seq_pagetp_invert G lv _) |].
  {
  intros i t t' Ht.
  so (Hseqlv _#3 Ht) as (R & Hl & _ & Hlv & _).
  eauto.
  }
clear Hseqlv.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
destruct i as [| i].
  {
  so (Hlv _#3 Hs) as (pg & Hlvl & Hlvr).
  exists pg, (iufut0 stop).
  do2 5 split; auto;
  apply interp_eval_refl; apply interp_fut_zero; eapply subst_closub; eauto.
  }
so (pwctx_promote _#4 Hs) as Hs'.
so (Hseq _#3 Hs') as (pg & R & Hlvl & Hlvr & Hal & Har & Hbl & Hbr).
exists pg, (iufut stop (S i) R).
simpsub.
do2 5 split; auto;
apply interp_eval_refl; apply interp_fut; auto.
Qed.


Lemma sound_fut_intro :
  forall G m n a,
    pseq (promote G) (deq m n a)
    -> pseq G (deq (next m) (next n) (fut a)).
Proof.
intros G m n a.
revert G.
refine (seq_pseq_promote 3 [] m [] n [] a 1 true [] _ _ _); cbn.
intros G Hclm Hcln Hcla Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
destruct i as [| i].
  {
  exists (iufut0 stop).
  simpsub.
  do2 4 split;
  try (apply interp_eval_refl; apply interp_fut_zero; eapply subst_closub; eauto);
  rewrite -> den_iufut0;
  apply fut_action_next_zero; try prove_hygiene.
  }
so (pwctx_promote _#4 Hs) as Hs'.
so (Hseq _#3 Hs') as (R & Hal & Har & Hm & Hn & Hmn).
exists (iufut stop (S i) R).
simpsub.
do2 4 split;
try (apply interp_eval_refl; apply interp_fut; auto);
apply fut_action_next; auto; omega.
Qed.


Lemma sound_fut_elim :
  forall G m n a p q b,
    pseq G (deq m n (fut a))
    -> pseq (promote G) (deqtype a a)
    -> pseq (cons (hyp_tml a) G) (deq p q b)
    -> pseq G (deq (subst1 (prev m) p) (subst1 (prev n) q) (subst1 (prev m) b)).
Proof.
intros G m n a p q b.
revert G.
refine (seq_pseq_promote 1 [] a 3 false [] _ true [] _ false [_] _ _ _); cbn.
intros G Hcla Hseqmn Hseqa Hseqpq.
rewrite -> seq_eqtype in Hseqa.
rewrite -> seq_deq in Hseqmn, Hseqpq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmn _#3 Hs) as (Af & Hal & Har & Hm & Hn & Hmn).
assert (forall c d,
          rel (den Af) i c d
          -> pwctx i (dot (prev c) s) (dot (prev d) s') (cons (hyp_tml a) G)) as Hs'.
  {
  intros c d Hcd.
  so (urel_closed _#5 Hcd) as (Hclc & Hcld).
  apply pwctx_cons_tml_seq; auto; try prove_hygiene.
    {
    intro Hpos.
    destruct i as [| i]; [omega |].
    cbn [pred].
    simpsubin Hal.
    simpsubin Har.
    invert (basic_value_inv _#6 value_fut Hal).
    intros A Hal' Heq1.
    invert (basic_value_inv _#6 value_fut Har).
    intros A' Har' Heq2.
    so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
    clear Heq2.
    subst Af.
    so (iufut_inj _#5 Heq); subst A'.
    apply (seqhyp_tm _#5 A); auto.
    apply (fut_action_prev _ (S i)).
    exact Hcd.
    }

    {
    intros j t t' Ht.
    so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
    exists toppg, R.
    auto.
    }
  }
clear Hseqmn.
so (Hseqpq _#3 (Hs' _ _ Hm)) as (B & Hbml & Hbmr & Hmp & _).
so (Hseqpq _#3 (Hs' _ _ Hn)) as (B' & _ & Hbnr & _ & Hnq & _).
so (Hseqpq _#3 (Hs' _ _ Hmn)) as (B'' & Hbml' & Hbnr' & _ & _ & Hmnpq).
so (basic_fun _#7 Hbml Hbml'); subst B''.
so (basic_fun _#7 Hbnr Hbnr'); subst B'.
exists B.
simpsub.
do2 4 split; auto.
Qed.


Lemma sound_fut_elim_eqtype :
  forall G m n a b c,
    pseq G (deq m n (fut a))
    -> pseq (promote G) (deqtype a a)
    -> pseq (cons (hyp_tml a) G) (deqtype b c)
    -> pseq G (deqtype (subst1 (prev m) b) (subst1 (prev n) c)).
Proof.
intros G m n a b c.
revert G.
refine (seq_pseq_promote 1 [] a 3 false [] _ true [] _ false [_] _ _ _); cbn.
intros G Hcla Hseqmn Hseqa Hseqbc.
rewrite -> seq_eqtype in Hseqa, Hseqbc |- *.
rewrite -> seq_deq in Hseqmn.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmn _#3 Hs) as (Af & Hal & Har & Hm & Hn & Hmn).
assert (forall p q,
          rel (den Af) i p q
          -> pwctx i (dot (prev p) s) (dot (prev q) s') (cons (hyp_tml a) G)) as Hs'.
  {
  intros p q Hpq.
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  apply pwctx_cons_tml_seq; auto; try prove_hygiene.
    {
    intro Hpos.
    destruct i as [| i]; [omega |].
    cbn [pred].
    simpsubin Hal.
    simpsubin Har.
    invert (basic_value_inv _#6 value_fut Hal).
    intros A Hal' Heq1.
    invert (basic_value_inv _#6 value_fut Har).
    intros A' Har' Heq2.
    so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
    clear Heq2.
    subst Af.
    so (iufut_inj _#5 Heq); subst A'.
    apply (seqhyp_tm _#5 A); auto.
    apply (fut_action_prev _ (S i)).
    exact Hpq.
    }

    {
    intros j t t' Ht.
    so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
    exists toppg, R.
    auto.
    }
  }
clear Hseqmn.
so (Hseqbc _#3 (Hs' _ _ Hm)) as (R & Hmbl & Hmbr & _).
so (Hseqbc _#3 (Hs' _ _ Hn)) as (R' & _ & _ & Hncl & Hncr).
so (Hseqbc _#3 (Hs' _ _ Hmn)) as (R'' & Hmbl' & _ & _ & Hncr').
so (basic_fun _#7 Hmbl Hmbl'); subst R''.
so (basic_fun _#7 Hncr Hncr'); subst R'.
exists R.
simpsub.
do2 3 split; auto.
Qed.


(* This almost follows from sound_fut_eta_hyp, but not quite. *)
Lemma sound_fut_eta :
  forall G m a,
    pseq G (deq m m (fut a))
    -> pseq G (deq m (next (prev m)) (fut a)).
Proof.
intros G m a.
revert G.
refine (seq_pseq 1 [] m 1 [] _ _ _); cbn.
intros G Hclm Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq i s s' Hs) as (R & Hfutl & Hfutr & Hm & _).
exists R.
do2 3 split; auto.
simpsubin Hfutl.
simpsubin Hfutr.
simpsub.
destruct i as [| i].
  {
  invert (basic_value_inv _#6 value_fut Hfutl).
  intros _ <-.
  rewrite -> den_iufut0 in Hm |- *.
  split.
    {
    apply fut_action_next_zero; prove_hygiene.
    }

    {
    destruct Hm as (n & _ & _ & _ & _ & Hsteps & _).
    refine (urel_equiv_1 _#6 _ (equiv_symm _#3 (steps_equiv _#3 Hsteps)) _).
      {
      prove_hygiene.
      }
    so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hsteps (subst_closub _#4 Hcls Hclm))) as H; cbn in H.
    destruct H.
    apply fut_action_next_zero; prove_hygiene.
    }
  }
invert (basic_value_inv _#6 value_fut Hfutl).
intros A Hal Heq1.
invert (basic_value_inv _#6 value_fut Hfutr).
intros A' Har Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iufut_inj _#5 Heq); subst A'.
cbn in Hm.
split.
  {
  apply fut_action_next; auto.
  eapply fut_action_prev; eauto.
  }

  {
  destruct Hm as (n & n' & _ & _ & _ & Hsteps & Hsteps' & Hn).
  refine (urel_equiv_1 _#6 _ (equiv_symm _#3 (steps_equiv _#3 Hsteps)) _).
    {
    prove_hygiene.
    }
  apply fut_action_next; auto.
  apply (urel_equiv_2 _#4 n').
    {
    prove_hygiene.
    }

    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_prev.
      eapply steps_equiv; eauto.
      }
    apply steps_equiv.
    apply star_one; apply step_prev2.
    }
  apply Hn.
  omega.
  }
Qed.


Lemma sound_fut_eta_hyp_pre :
  forall G1 G2 a m n b,
    hygiene (ctxpred G1) a
    -> hygiene (ctxpred (G2 ++ hyp_tm (fut a) :: G1)) b
    -> seq (promote G1) (deqtype a a)
    -> seq (substctx (dot (next (var 0)) sh1) G2 ++ cons (hyp_tml a) G1) (deq m n (subst (under (length G2) (dot (next (var 0)) sh1)) b))
    -> seq (G2 ++ cons (hyp_tm (fut a)) G1) (deq (subst (under (length G2) (dot (prev (var 0)) sh1)) m) (subst (under (length G2) (dot (prev (var 0)) sh1)) n) b).
Proof.
intros G1 G2 a m n b Hcla Hclb Hseqa Hseq.
rewrite -> seq_eqtype in Hseqa.
eapply subsume_seq_extract; eauto; clear Hseq.
apply subsume_under.
do2 2 split.
  {
  intros j.
  rewrite -> !ctxpred_length.
  cbn [length].
  destruct j as [| j].
    {
    simpsub.
    split; try omega.
    intros _.
    apply hygiene_auto; cbn.
    split; auto.
    apply hygiene_var.
    omega.
    }

    {
    simpsub.
    split.
      {
      intros H.
      apply hygiene_var.
      omega.
      }

      {
      intros H.
      invertc H.
      intro; omega.
      }
    }
  }

  {
  intros j.
  rewrite -> !ctxpred_length.
  cbn [length].
  destruct j as [| j].
    {
    simpsub.
    split; try omega.
    intros _.
    apply hygiene_auto; cbn.
    split; auto.
    apply hygiene_var.
    omega.
    }

    {
    simpsub.
    split.
      {
      intros H.
      apply hygiene_var.
      omega.
      }

      {
      intros H.
      invertc H.
      intro; omega.
      }
    }
  }
intros i ss ss' Hss.
invertc Hss.
intros p q s s' Hs Hpq Hleft Hright <- <-.
simpsubin Hpq.
so (seqhyp_impl_closed _#5 Hpq) as (Hclp & Hclq).
assert (exists p' q' A,
          star step p (next p') 
          /\ star step q (next q')
          /\ (i > 0
              -> interp toppg true (pred i) (subst s a) A
                 /\ interp toppg false (pred i) (subst s' a) A
                 /\ rel (den A) (pred i) p' q')) as H.
  {
  invertc Hpq.
  intros R Hfutl Hfutr Hpq.
  invert (basic_value_inv _#6 value_fut Hfutl).
    {
    intros _ <- <-.
    cbn in Hpq.
    decompose Hpq.
    intros p' q' _ _ _ Hp' Hq' _.
    exists p', q', (iubase empty_urel).
    do2 2 split; auto.
    omega.
    }

    {
    intros i' A Hal <- Heq1.
    invert (basic_value_inv _#6 value_fut Hfutr).
    intros A' Har Heq2.
    so (eqtrans Heq1 (eqsymm Heq2)) as Heq; clear Heq2.
    subst R.
    so (iufut_inj _#5 Heq); subst A'.
    cbn in Hpq.
    decompose Hpq.
    intros p' q' _ _ _ Hp' Hq' Hpq'.
    exists p', q', A.
    do2 2 split; auto.
    }
  }
destruct H as (p' & q' & A & Hstepsp & Hstepsq & Hif).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsp Hclp)) as H; cbn in H.
destruct H as (Hclp' & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsq Hclq)) as H; cbn in H.
destruct H as (Hclq' & _).
do2 4 split.
  {
  simpsub.
  apply pwctx_cons_tml_seq; auto; try prove_hygiene.
    {
    intros Hpos.
    so (Hif Hpos) as (Hal & Har & Hpq').
    apply (seqhyp_tm _#5 A); auto.
    eapply urel_equiv; eauto; try prove_hygiene.
      {
      apply equiv_symm.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ prev); auto using step_prev1.
        exact Hstepsp.
        }
      apply star_one; apply step_prev2.
      }

      {
      apply equiv_symm.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ prev); auto using step_prev1.
        exact Hstepsq.
        }
      apply star_one; apply step_prev2.
      }
    }

    {
    intros j t t' Ht.
    so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
    eauto.
    }
  }

  {
  simpsub.
  apply equivsub_dot; auto using equivsub_refl.
  apply (equiv_trans _ _ (next p')).
    {
    apply equiv_next.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ prev); auto using step_prev1.
      exact Hstepsp.
      }
    apply star_one.
    apply step_prev2.
    }

    {
    apply equiv_symm.
    apply steps_equiv; auto.
    }
  }

  {
  simpsub.
  apply equivsub_dot; auto using equivsub_refl.
  apply (equiv_trans _ _ (next q')).
    {
    apply equiv_next.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ prev); auto using step_prev1.
      exact Hstepsq.
      }
    apply star_one.
    apply step_prev2.
    }

    {
    apply equiv_symm.
    apply steps_equiv; auto.
    }
  }

  {
  intros j d uu Hj Huu.
  simpsub.
  simpsubin Huu.
  rewrite -> qpromote_cons in Huu |- *.
  rewrite -> qpromote_hyp_tm.
  invertc Huu.
  intros r u Hu Hr <-.
  simpsub.
  apply seqctx_cons; auto.
  simpsub.
  destruct j as [| j].
    {
    so (seqctx_impl_closub _#4 Hu) as (Hcls & Hclu).
    so (seqhyp_impl_closed _#5 Hr) as (_ & Hclr).
    rewrite -> ctxpred_qpromote in Hcls, Hclu.
    apply (seqhyp_tm _#5 (iufut0 stop)).
      {
      apply interp_eval_refl.
      apply interp_fut_zero; prove_hygiene.
      }

      {
      apply interp_eval_refl.
      apply interp_fut_zero; prove_hygiene.
      }

      {
      apply (urel_equiv_1 _#3 (next p')); try prove_hygiene.
        {
        apply equiv_symm; apply steps_equiv; eauto.
        }
      apply fut_action_next_zero; auto; prove_hygiene.
      }
    }
  rewrite -> !substh_qpromote_hyp in Hr.
  so (seqhyp_demote_maybe _#7 Hr) as H.
  simpsubin H.
  invertc H.
  intros A' Hal Hau Hr' _ _ _ _.
  apply (seqhyp_tm _#5 (iufut stop (S j) A')).
    {
    apply interp_eval_refl.
    apply interp_fut.
    apply Hal.
    omega.
    }

    {
    apply interp_eval_refl.
    apply interp_fut.
    apply Hau.
    omega.
    }

    {
    apply (urel_equiv_1 _#3 (next p')); try prove_hygiene.
      {
      apply equiv_symm; apply steps_equiv; eauto.
      }
    apply fut_action_next; auto.
    apply (urel_equiv_1 _#3 (prev p)); try prove_hygiene.
      {
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ prev); auto using step_prev1.
        exact Hstepsp.
        }
      apply star_one; apply step_prev2.
      }
    
      {
      apply Hr'.
      omega.
      }
    }
  }

  {
  intros j d uu Hj Huu.
  simpsub.
  simpsubin Huu.
  rewrite -> qpromote_cons in Huu |- *.
  rewrite -> qpromote_hyp_tm.
  invertc Huu.
  intros r u Hu Hr <-.
  simpsub.
  apply seqctx_cons; auto.
  simpsub.
  destruct j as [| j].
    {
    so (seqctx_impl_closub _#4 Hu) as (Hclu & Hcls').
    so (seqhyp_impl_closed _#5 Hr) as (Hclr & _).
    rewrite -> ctxpred_qpromote in Hcls', Hclu.
    apply (seqhyp_tm _#5 (iufut0 stop)).
      {
      apply interp_eval_refl.
      apply interp_fut_zero; prove_hygiene.
      }

      {
      apply interp_eval_refl.
      apply interp_fut_zero; prove_hygiene.
      }

      {
      apply (urel_equiv_2 _#4 (next q')); try prove_hygiene.
        {
        apply equiv_symm; apply steps_equiv; eauto.
        }
      apply fut_action_next_zero; auto; prove_hygiene.
      }
    }
  rewrite -> !substh_qpromote_hyp in Hr.
  so (seqhyp_demote_maybe _#7 Hr) as H.
  simpsubin H.
  invertc H.
  intros A' Hal Hau Hr' _ _ _ _.
  apply (seqhyp_tm _#5 (iufut stop (S j) A')).
    {
    apply interp_eval_refl.
    apply interp_fut.
    apply Hal.
    omega.
    }

    {
    apply interp_eval_refl.
    apply interp_fut.
    apply Hau.
    omega.
    }

    {
    apply (urel_equiv_2 _#4 (next q')); try prove_hygiene.
      {
      apply equiv_symm; apply steps_equiv; eauto.
      }
    apply fut_action_next; auto.
    apply (urel_equiv_2 _#4 (prev q)); try prove_hygiene.
      {
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ prev); auto using step_prev1.
        exact Hstepsq.
        }
      apply star_one; apply step_prev2.
      }
    
      {
      apply Hr'.
      omega.
      }
    }
  }
Qed.


Lemma sound_fut_eta_hyp :
  forall G1 G2 a m n b,
    pseq (promote G1) (deqtype a a)
    -> pseq (substctx (dot (next (var 0)) sh1) G2 ++ cons (hyp_tml a) G1) (deq m n (subst (under (length G2) (dot (next (var 0)) sh1)) b))
    -> pseq (G2 ++ cons (hyp_tm (fut a)) G1) (deq (subst (under (length G2) (dot (prev (var 0)) sh1)) m) (subst (under (length G2) (dot (prev (var 0)) sh1)) n) b).
Proof.
intros G1 G2 a m n b (i1, Hseqa) (i2, Hseq).
so (shut_term _ G1 a) as (i3 & Hcla).
so (shut_term _ (G2 ++ hyp_tm (fut a) :: G1) b) as (i4 & Hclb).
so (upper_bound_all 4 i1 i2 i3 i4) as (i & Hi1 & Hi2 & Hi3 & Hi4 & _).
exists i; intros j Hj.
autorewrite with canonlist.
eapply sound_fut_eta_hyp_pre; try (finish_pseq j).
rewrite -> promote_append.
rewrite -> promote_shut.
apply Hseqa; eauto using le_trans.
Qed.


Lemma sound_fut_ext :
  forall G a b c m n,
    pseq G (deq m m (fut b))
    -> pseq G (deq n n (fut c))
    -> pseq G (deq (next (prev m)) (next (prev n)) (fut a))
    -> pseq G (deq m n (fut a)).
Proof.
intros G a b c m n.
revert G.
refine (seq_pseq 0 3 [] _ [] _ [] _ _ _).
cbn.
intros G Hseqm Hseqn Hseq.
rewrite -> seq_deq in Hseqm, Hseqn, Hseq |- *.
intros i s s' Hs.
assert (exists m1 m2,
          hygiene clo (subst s m)
          /\ hygiene clo (subst s' m)
          /\ star step (subst s m) (next m1)
          /\ star step (subst s' m) (next m2)) as (m1 & m2 & Hclm & Hclm' & Hstepm1 & Hstepm2).
  {
  so (Hseqm _ _ _ Hs) as (R & Hl & _ & Hm & _).
  simpsubin Hl.
  invert (basic_value_inv _#6 value_fut Hl).
    {
    intros _ <- <-.
    rewrite -> den_iufut0 in Hm.
    destruct Hm as (m1 & m2 & _ & Hcl & Hcl' & Hstep & Hstep' & _).
    exists m1, m2.
    auto.
    }
  intros i' A _ <- <-.
  rewrite -> den_iufut in Hm.
  destruct Hm as (m1 & m2 & _ & Hcl & Hcl' & Hstep & Hstep' & _).
  exists m1, m2.
  auto.
  }
assert (exists n1 n2,
          hygiene clo (subst s n)
          /\ hygiene clo (subst s' n)
          /\ star step (subst s n) (next n1)
          /\ star step (subst s' n) (next n2)) as (n1 & n2 & Hcln & Hcln' & Hstepn1 & Hstepn2).
  {
  so (Hseqn _ _ _ Hs) as (R & Hl & _ & Hn & _).
  simpsubin Hl.
  invert (basic_value_inv _#6 value_fut Hl).
    {
    intros _ <- <-.
    rewrite -> den_iufut0 in Hn.
    destruct Hn as (n1 & n2 & _ & Hcl & Hcl' & Hstep & Hstep' & _).
    exists n1, n2.
    auto.
    }
  intros i' A _ <- <-.
  rewrite -> den_iufut in Hn.
  destruct Hn as (n1 & n2 & _ & Hcl & Hcl' & Hstep & Hstep' & _).
  exists n1, n2.
  auto.
  }
clear Hseqm Hseqn.
so (Hseq _ _ _ Hs) as (R & Hl & Hr & Hm & Hn & Hmn).
exists R.
do2 2 split; auto.
simpsubin Hl.
simpsubin Hr.
simpsubin Hm.
simpsubin Hn.
simpsubin Hmn.
destruct i as [| i].
  {
  invert (basic_value_inv _#6 value_fut Hl).
  intros _ <-.
  rewrite -> !den_iufut0.
  do2 2 split.
    {
    exists m1, m2.
    do2 5 split; auto.
    intros H.
    omega.
    }

    {
    exists n1, n2.
    do2 5 split; auto.
    intros H.
    omega.
    }

    {
    exists m1, n2.
    do2 5 split; auto.
    intros H.
    omega.
    }
  }
invert (basic_value_inv _#6 value_fut Hl).
intros A Hal <-.
rewrite -> !den_iufut in Hm, Hn, Hmn |- *.
destruct Hm as (m1' & m2' & _ & _ & _ & Hstep1 & Hstep2 & H).
so (determinism_normal_value _#3 value_next Hstep1) as Heq.
injection Heq.
intros <-.
so (H (Nat.lt_0_succ _)) as Hm.
clear Heq Hstep1 H.
so (determinism_normal_value _#3 value_next Hstep2) as Heq.
injection Heq.
intros <-.
clear Heq Hstep2.
cbn in Hm.
destruct Hn as (n1' & n2' & _ & _ & _ & Hstep1 & Hstep2 & H).
so (determinism_normal_value _#3 value_next Hstep1) as Heq.
injection Heq.
intros <-.
so (H (Nat.lt_0_succ _)) as Hn.
clear Heq Hstep1 H.
so (determinism_normal_value _#3 value_next Hstep2) as Heq.
injection Heq.
intros <-.
clear Heq Hstep2.
cbn in Hn.
destruct Hmn as (m1' & n2' & _ & _ & _ & Hstep1 & Hstep2 & H).
so (determinism_normal_value _#3 value_next Hstep1) as Heq.
injection Heq.
intros <-.
so (H (Nat.lt_0_succ _)) as Hmn.
clear Heq Hstep1 H.
so (determinism_normal_value _#3 value_next Hstep2) as Heq.
injection Heq.
intros <-.
clear Heq Hstep2.
cbn in Hmn.
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepm1 Hclm)) as H.
cbn in H.
destruct H as (Hclm1 & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepm2 Hclm')) as H.
cbn in H.
destruct H as (Hclm2 & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepn1 Hcln)) as H.
cbn in H.
destruct H as (Hcln1 & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepn2 Hcln')) as H.
cbn in H.
destruct H as (Hcln2 & _).
assert (equiv (prev (subst s m)) m1) as Hequivm1.
  {
  apply steps_equiv.
  eapply star_trans.
    {
    apply star_map'; eauto using step_prev1 with dynamic.
    }
  apply star_one.
  apply step_prev2.
  }
assert (equiv (prev (subst s' m)) m2) as Hequivm2.
  {
  apply steps_equiv.
  eapply star_trans.
    {
    apply star_map'; eauto using step_prev1 with dynamic.
    }
  apply star_one.
  apply step_prev2.
  }
assert (equiv (prev (subst s n)) n1) as Hequivn1.
  {
  apply steps_equiv.
  eapply star_trans.
    {
    apply star_map'; eauto using step_prev1 with dynamic.
    }
  apply star_one.
  apply step_prev2.
  }
assert (equiv (prev (subst s' n)) n2) as Hequivn2.
  {
  apply steps_equiv.
  eapply star_trans.
    {
    apply star_map'; eauto using step_prev1 with dynamic.
    }
  apply star_one.
  apply step_prev2.
  }
do2 2 split.
  {
  exists m1, m2.
  do2 5 split; auto.
  intros _.
  cbn.
  eapply urel_equiv; eauto.
  }

  {
  exists n1, n2.
  do2 5 split; auto.
  intros _.
  cbn.
  eapply urel_equiv; eauto.
  }

  {
  exists m1, n2.
  do2 5 split; auto.
  intros _.
  cbn.
  eapply urel_equiv; eauto.
  }
Qed.


Lemma sound_semifut_formation :
  forall G a b,
    pseq (promote G) (deqtype a b)
    -> pseq G (deqtype (semifut a) (semifut b)).
Proof.
intros G a b.
revert G.
refine (seq_pseq_promote 2 [] a [] b 1 true [] _ _ _); cbn.
intros G Hcla Hclb Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
destruct i as [| i].
  {
  exists (iusemifut0 stop).
  simpsub.
  do2 3 split;
  apply interp_eval_refl; apply interp_semifut_zero; eapply subst_closub; eauto.
  }
so (pwctx_promote _#4 Hs) as Hs'.
so (Hseq _#3 Hs') as (R & Hal & Har & Hbl & Hbr).
exists (iusemifut stop (S i) R).
do2 3 split;
apply interp_eval_refl; apply interp_semifut; auto.
Qed.


Lemma sound_semifut_formation_univ :
  forall G lv a b,
    pseq (promote G) (deq a b (univ lv))
    -> pseq G (deq lv lv pagetp)
    -> pseq G (deq (semifut a) (semifut b) (univ lv)).
Proof.
intros G lv a b.
revert G.
refine (seq_pseq_promote 2 [] a [] b 2 true [] _ false [] _ _ _); cbn.
intros G Hcla Hclb Hseq Hseqlv.
rewrite -> seq_univ in Hseq |- *.
rewrite -> seq_deq in Hseqlv.
eassert _ as Hlv; [refine (seq_pagetp_invert G lv _) |].
  {
  intros i t t' Ht.
  so (Hseqlv _#3 Ht) as (R & Hl & _ & Hlv & _).
  eauto.
  }
clear Hseqlv.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
destruct i as [| i].
  {
  so (Hlv _#3 Hs) as (pg & Hlvl & Hlvr).
  exists pg, (iusemifut0 stop).
  do2 5 split; auto;
  apply interp_eval_refl; apply interp_semifut_zero; eapply subst_closub; eauto.
  }
so (pwctx_promote _#4 Hs) as Hs'.
so (Hseq _#3 Hs') as (pg & R & Hlvl & Hlvr & Hal & Har & Hbl & Hbr).
exists pg, (iusemifut stop (S i) R).
simpsub.
do2 5 split; auto;
apply interp_eval_refl; apply interp_semifut; auto.
Qed.


(* no actual next, but we'll name consistently *)
Lemma semifut_action_next_zero :
  forall w i A m n,
    hygiene clo m
    -> hygiene clo n
    -> semifut_action w i A 0 m n.
Proof.
intros w i A m n Hcl Hcl'.
do2 3 split; auto; omega.
Qed.


Lemma semifut_action_next :
  forall w i A i' m n,
    S i' <= i
    -> rel A i' m n
    -> semifut_action w i A (S i') m n.
Proof.
intros w I A i m n Hi Hmn.
so (urel_closed _#5 Hmn) as (Hm & Hn).
do2 3 split; auto.
Qed.


Lemma semifut_action_prev :
  forall w i A i' m n,
    semifut_action w i A (S i') m n
    -> rel A i' m n.
Proof.
intros w I A i m n Hmn.
decompose Hmn.
intros Hi Hclm Hcln Hact.
lapply Hact; [| omega].
auto.
Qed.


Lemma sound_semifut_intro :
  forall G m n a,
    pseq (promote G) (deq m n a)
    -> pseq G (deq m n (semifut a)).
Proof.
intros G m n a.
revert G.
refine (seq_pseq_promote 3 [] m [] n [] a 1 true [] _ _ _); cbn.
intros G Hclm Hcln Hcla Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
destruct i as [| i].
  {
  exists (iusemifut0 stop).
  simpsub.
  do2 4 split;
  try (apply interp_eval_refl; apply interp_semifut_zero; eapply subst_closub; eauto);
  rewrite -> den_iusemifut0;
  apply semifut_action_next_zero; try prove_hygiene.
  }
so (pwctx_promote _#4 Hs) as Hs'.
so (Hseq _#3 Hs') as (R & Hal & Har & Hm & Hn & Hmn).
exists (iusemifut stop (S i) R).
simpsub.
do2 4 split;
try (apply interp_eval_refl; apply interp_semifut; auto);
apply semifut_action_next; auto; omega.
Qed.


Lemma sound_semifut_elim :
  forall G m n a p q b,
    pseq G (deq m n (semifut a))
    -> pseq (promote G) (deqtype a a)
    -> pseq (cons (hyp_tml a) G) (deq p q b)
    -> pseq G (deq (subst1 m p) (subst1 n q) (subst1 m b)).
Proof.
intros G m n a p q b.
revert G.
refine (seq_pseq_promote 1 [] a 3 false [] _ true [] _ false [_] _ _ _); cbn.
intros G Hcla Hseqmn Hseqa Hseqpq.
rewrite -> seq_eqtype in Hseqa.
rewrite -> seq_deq in Hseqmn, Hseqpq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmn _#3 Hs) as (Af & Hal & Har & Hm & Hn & Hmn).
assert (forall c d,
          rel (den Af) i c d
          -> pwctx i (dot c s) (dot d s') (cons (hyp_tml a) G)) as Hs'.
  {
  intros c d Hcd.
  so (urel_closed _#5 Hcd) as (Hclc & Hcld).
  apply pwctx_cons_tml_seq; auto; try prove_hygiene.
    {
    intro Hpos.
    destruct i as [| i]; [omega |].
    cbn [pred].
    simpsubin Hal.
    simpsubin Har.
    invert (basic_value_inv _#6 value_semifut Hal).
    intros A Hal' Heq1.
    invert (basic_value_inv _#6 value_semifut Har).
    intros A' Har' Heq2.
    so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
    clear Heq2.
    subst Af.
    so (iusemifut_inj _#5 Heq); subst A'.
    apply (seqhyp_tm _#5 A); auto.
    apply (semifut_action_prev _ (S i)).
    exact Hcd.
    }

    {
    intros j t t' Ht.
    so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
    exists toppg, R.
    auto.
    }
  }
clear Hseqmn.
so (Hseqpq _#3 (Hs' _ _ Hm)) as (B & Hbml & Hbmr & Hmp & _).
so (Hseqpq _#3 (Hs' _ _ Hn)) as (B' & _ & Hbnr & _ & Hnq & _).
so (Hseqpq _#3 (Hs' _ _ Hmn)) as (B'' & Hbml' & Hbnr' & _ & _ & Hmnpq).
so (basic_fun _#7 Hbml Hbml'); subst B''.
so (basic_fun _#7 Hbnr Hbnr'); subst B'.
exists B.
simpsub.
do2 4 split; auto.
Qed.


Lemma sound_semifut_elim_eqtype :
  forall G m n a b c,
    pseq G (deq m n (semifut a))
    -> pseq (promote G) (deqtype a a)
    -> pseq (cons (hyp_tml a) G) (deqtype b c)
    -> pseq G (deqtype (subst1 m b) (subst1 n c)).
Proof.
intros G m n a b c.
revert G.
refine (seq_pseq_promote 1 [] a 3 false [] _ true [] _ false [_] _ _ _); cbn.
intros G Hcla Hseqmn Hseqa Hseqbc.
rewrite -> seq_eqtype in Hseqa, Hseqbc |- *.
rewrite -> seq_deq in Hseqmn.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmn _#3 Hs) as (Af & Hal & Har & Hm & Hn & Hmn).
assert (forall p q,
          rel (den Af) i p q
          -> pwctx i (dot p s) (dot q s') (cons (hyp_tml a) G)) as Hs'.
  {
  intros p q Hpq.
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  apply pwctx_cons_tml_seq; auto; try prove_hygiene.
    {
    intro Hpos.
    destruct i as [| i]; [omega |].
    cbn [pred].
    simpsubin Hal.
    simpsubin Har.
    invert (basic_value_inv _#6 value_semifut Hal).
    intros A Hal' Heq1.
    invert (basic_value_inv _#6 value_semifut Har).
    intros A' Har' Heq2.
    so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
    clear Heq2.
    subst Af.
    so (iusemifut_inj _#5 Heq); subst A'.
    apply (seqhyp_tm _#5 A); auto.
    apply (semifut_action_prev _ (S i)).
    exact Hpq.
    }

    {
    intros j t t' Ht.
    so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
    exists toppg, R.
    auto.
    }
  }
clear Hseqmn.
so (Hseqbc _#3 (Hs' _ _ Hm)) as (R & Hmbl & Hmbr & _).
so (Hseqbc _#3 (Hs' _ _ Hn)) as (R' & _ & _ & Hncl & Hncr).
so (Hseqbc _#3 (Hs' _ _ Hmn)) as (R'' & Hmbl' & _ & _ & Hncr').
so (basic_fun _#7 Hmbl Hmbl'); subst R''.
so (basic_fun _#7 Hncr Hncr'); subst R'.
exists R.
simpsub.
do2 3 split; auto.
Qed.
