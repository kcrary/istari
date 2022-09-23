
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

Require Import Model.
Require Import Truncate.
Require Import ProperDownward.
Require Import ProperLevel.
Require Import SemanticsKuniv.
Require Import SemanticsUniv.
Require Import SoundFut.
Require Import Defined.
Require Import PageType.


Local Ltac prove_hygiene :=
  repeat (apply hygiene_auto; cbn; repeat2 split; auto);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1, subst_closub;
  try (apply hygiene_var; cbn; auto; done).


Lemma pwctx_cons_tpl :
  forall i m p s s' G,
    pwctx i s s' G
    -> hygiene clo m
    -> hygiene clo p
    -> (i > 0 -> seqhyp (pred i) m p hyp_tp hyp_tp)
    -> pwctx i (dot m s) (dot p s') (cons hyp_tpl G).
Proof.
intros i m p s s' G Hs Hclm Hclp Hmp.
apply pwctx_cons; auto.
  {
  simpsub.
  destruct i as [| i].
    {
    apply (seqhyp_tpl _#3 (iubase empty_urel)); auto; omega.
    }
  invert (Hmp (Nat.lt_0_succ _)).
  intros R Hm Hp.
  apply (seqhyp_tpl _#3 (iutruncate (S i) R)); auto;
  intros _; cbn; apply (basic_downward _#3 i); auto.
  }

  {
  intros j b u Hsmall Hu.
  destruct b; cbn; eauto using relhyp.
  }

  {
  intros j b u Hsmall Hu.
  destruct b; cbn; eauto using relhyp.
  }
Qed.


Lemma sound_rec_kind_formation :
  forall G lv k k',
    pseq (cons (hyp_tml (kuniv lv)) G) (deq k k' (kuniv (subst sh1 lv)))
    -> pseq G (deq lv lv pagetp)
    -> pseq G (deq (rec k) (rec k') (kuniv lv)).
Proof.
intros G lv k l.
revert G.
refine (seq_pseq 3 [hyp_emp] k [hyp_emp] l [] lv 2 [_] _ [] _ _ _); cbn.
intros G Hclk Hcll Hcllv Hseq Hseqlv.
rewrite -> seq_eqkind in Hseq |- *.
rewrite -> seq_deq in Hseqlv.
eassert _ as Hlv; [refine (seq_pagetp_invert G lv _) |].
  {
  intros i t t' Ht.
  so (Hseqlv _#3 Ht) as (R & Hl & _ & Hlv & _).
  eauto.
  }
clear Hseqlv.
intros i.
induct i.

(* 0 *)
{
intros s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
assert (pwctx 0 (dot (rec (subst (under 1 s) k)) s) (dot (rec (subst (under 1 s') k)) s') (cons (hyp_tml (kuniv lv)) G)) as Hsk.
  {
  apply pwctx_cons_tml; auto; try omega;
  try (prove_hygiene; eapply subst_closub_under_permit; eauto; done);
  intros; try omega.
  }
assert (pwctx 0 (dot (rec (subst (under 1 s) l)) s) (dot (rec (subst (under 1 s') l)) s') (cons (hyp_tml (kuniv lv)) G)) as Hsl.
  {
  apply pwctx_cons_tml; auto; try omega;
  try (prove_hygiene; eapply subst_closub_under_permit; eauto; done);
  intros; try omega.
  }
assert (pwctx 0 (dot (rec (subst (under 1 s) k)) s) (dot (rec (subst (under 1 s') l)) s') (cons (hyp_tml (kuniv lv)) G)) as Hskl.
  {
  apply pwctx_cons_tml; auto; try omega;
  try (prove_hygiene; eapply subst_closub_under_permit; eauto; done);
  intros; try omega.
  }
so (Hseq _#3 Hsk) as (pg & K & R & hl & Hlvl & Hlvr & Hkl & Hkr & _ & _ & Hklt & Hkrt & _ & _).
simpsubin Hlvl.
simpsubin Hlvr.
so (Hseq _#3 Hsl) as (pg' & K' & R' & hl' & Hlvl' & _ & _ & _ & Hll & Hlr & _ & _ & Hllt & Hlrt).
simpsubin Hlvl'.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'; clear Hlvl'.
so (proof_irrelevance _ hl hl'); subst hl'.
so (Hseq _#3 Hskl) as (pg' & K'' & R'' & hl'' & Hlvl' & _ & Hkl' & _ & _ & Hlr' & Hklt' & _ & _ & Hlrt').
simpsubin Hlvl'.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'; clear Hlvl'.
so (proof_irrelevance _ hl hl''); subst hl''.
so (kbasic_fun _#7 Hkl Hkl'); subst K''.
so (kbasic_fun _#7 Hlr Hlr'); subst K'.
so (basic_fun _#7 Hklt Hklt'); subst R''.
so (basic_fun _#7 Hlrt Hlrt'); subst R'.
exists pg, K, R, hl.
do2 9 split; auto; simpsub;
try (apply kinterp_eval_refl; apply interp_krec; simpsub; auto; done);
try (apply interp_eval_refl; apply interp_rec; simpsub; auto; done).
}

(* S *)
{
intros i IH s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (pwctx_downward _#5 (Nat.le_succ_diag_r i) Hs) as Hsi.
so (IH _ _ Hsi) as (pg & Ki & Ri & hl & Hlvl & Hlvr & Hkli & Hkri & Hlli & Hlri & Hklit & Hkrit & Hllit & Hlrit).
clear IH.
simpsubin Hkli.
simpsubin Hkri.
simpsubin Hlli.
simpsubin Hlri.
simpsubin Hklit.
simpsubin Hkrit.
simpsubin Hllit.
simpsubin Hlrit.
assert (forall j u,
          j < S i
          -> pwctx j s u G 
          -> relhyp j false (hyp_tm (subst s' (kuniv lv))) (hyp_tm (subst u (kuniv lv)))) as Hleft.
  {
  intros j u Hj Hu.
  so (Hlv _#3 Hu) as (pg' & Hl & Hr).
  so (pginterp_fun _#3 Hlvl Hl); subst pg'.
  simpsub.
  apply (relhyp_tm _#4 (iukuniv the_system j pg (pginterp_lt_top _ _ Hlvl))).
    {
    apply interp_eval_refl.
    apply interp_kuniv; auto.
    eapply pginterp_succ_lt_top; eauto.
    }

    {
    apply interp_eval_refl.
    apply interp_kuniv; auto.
    eapply pginterp_succ_lt_top; eauto.
    }
  }
assert (forall j u,
          j < S i
          -> pwctx j u s' G 
          -> relhyp j true (hyp_tm (subst s (kuniv lv))) (hyp_tm (subst u (kuniv lv)))) as Hright.
  {
  intros j u Hj Hu.
  so (Hlv _#3 Hu) as (pg' & Hl & Hr).
  so (pginterp_fun _#3 Hlvr Hr); subst pg'.
  simpsub.
  apply (relhyp_tm _#4 (iukuniv the_system j pg (pginterp_lt_top _ _ Hlvl))).
    {
    apply interp_eval_refl.
    apply interp_kuniv; auto.
    eapply pginterp_succ_lt_top; eauto.
    }

    {
    apply interp_eval_refl.
    apply interp_kuniv; auto.
    eapply pginterp_succ_lt_top; eauto.
    }
  }
assert (pwctx (S i) (dot (rec (subst (under 1 s) k)) s) (dot (rec (subst (under 1 s') k)) s') (cons (hyp_tml (kuniv lv)) G)) as Hsk.
  {
  apply pwctx_cons_tml; auto;
  try (prove_hygiene; eapply subst_closub_under_permit; eauto; done).
  intros _.
  cbn [pred].
  simpsub.
  apply (seqhyp_tm _#5 (iukuniv the_system i pg hl)).
    {
    apply interp_eval_refl.
    apply interp_kuniv; auto.
    eapply pginterp_succ_lt_top; eauto.
    }

    {
    apply interp_eval_refl.
    apply interp_kuniv; auto.
    eapply pginterp_succ_lt_top; eauto.
    }

    {
    cbn.
    split; auto.
    exists Ki, Ri.
    rewrite -> sintk_unroll, sint_unroll.
    auto.
    }
  }
assert (pwctx (S i) (dot (rec (subst (under 1 s) l)) s) (dot (rec (subst (under 1 s') l)) s') (cons (hyp_tml (kuniv lv)) G)) as Hsl.
  {
  apply pwctx_cons_tml; auto;
  try (prove_hygiene; eapply subst_closub_under_permit; eauto; done).
  intros _.
  cbn [pred].
  simpsub.
  apply (seqhyp_tm _#5 (iukuniv the_system i pg hl)).
    {
    apply interp_eval_refl.
    apply interp_kuniv; auto.
    eapply pginterp_succ_lt_top; eauto.
    }

    {
    apply interp_eval_refl.
    apply interp_kuniv; auto.
    eapply pginterp_succ_lt_top; eauto.
    }

    {
    cbn.
    split; auto.
    exists Ki, Ri.
    rewrite -> sintk_unroll, sint_unroll.
    auto.
    }
  }
assert (pwctx (S i) (dot (rec (subst (under 1 s) k)) s) (dot (rec (subst (under 1 s') l)) s') (cons (hyp_tml (kuniv lv)) G)) as Hskl.
  {
  apply pwctx_cons_tml; auto;
  try (prove_hygiene; eapply subst_closub_under_permit; eauto; done).
  intros _.
  cbn [pred].
  simpsub.
  apply (seqhyp_tm _#5 (iukuniv the_system i pg hl)).
    {
    apply interp_eval_refl.
    apply interp_kuniv; auto.
    eapply pginterp_succ_lt_top; eauto.
    }

    {
    apply interp_eval_refl.
    apply interp_kuniv; auto.
    eapply pginterp_succ_lt_top; eauto.
    }

    {
    cbn.
    split; auto.
    exists Ki, Ri.
    rewrite -> sintk_unroll, sint_unroll.
    auto.
    }
  }
so (Hseq _#3 Hsk) as (pg' & K & R & hl' & Hlvl' & _ & Hkl & Hkr & _ & _ & Hklt & Hkrt & _ & _).
simpsubin Hlvl'.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'; clear Hlvl'.
so (proof_irrelevance _ hl hl'); subst hl'.
so (Hseq _#3 Hsl) as (pg' & K' & R' & hl' & Hlvl' & _ & _ & _ & Hll & Hlr & _ & _ & Hllt & Hlrt).
simpsubin Hlvl'.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'; clear Hlvl'.
so (proof_irrelevance _ hl hl'); subst hl'.
so (Hseq _#3 Hskl) as (pg' & K'' & R'' & hl' & Hlvl' & _ & Hkl' & _ & _ & Hlr' & Hklt' & _ & _ & Hlrt').
simpsubin Hlvl'.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'; clear Hlvl'.
so (proof_irrelevance _ hl hl'); subst hl'.
so (kbasic_fun _#7 Hkl Hkl'); subst K''.
so (kbasic_fun _#7 Hlr Hlr'); subst K'.
so (basic_fun _#7 Hklt Hklt'); subst R''.
so (basic_fun _#7 Hlrt Hlrt'); subst R'.
exists pg, K, R, hl.
do2 9 split; auto; simpsub;
try (apply kinterp_eval_refl; apply interp_krec; simpsub; auto; done);
try (apply interp_eval_refl; apply interp_rec; simpsub; auto).
}
Qed.


Lemma sound_rec_formation_main :
  forall G a b,
    hygiene (permit (ctxpred G)) a
    -> hygiene (permit (ctxpred G)) b
    -> (forall i s s',
          pwctx i s s' (cons hyp_tpl G)
          -> exists R,
               interp toppg true i (subst s a) R
               /\ interp toppg false i (subst s' a) R
               /\ interp toppg true i (subst s b) R
               /\ interp toppg false i (subst s' b) R)
    -> forall i s s',
         pwctx i s s' G
         -> exists R,
              interp toppg true i (subst s (rec a)) R
              /\ interp toppg false i (subst s' (rec a)) R
              /\ interp toppg true i (subst s (rec b)) R
              /\ interp toppg false i (subst s' (rec b)) R.
Proof.
intros G a b Hcla Hclb Hseq i.
induct i.

(* 0 *)
{
intros s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
assert (pwctx 0 (dot (rec (subst (under 1 s) a)) s) (dot (rec (subst (under 1 s') a)) s') (cons hyp_tpl G)) as Hsa.
  {
  apply pwctx_cons_tpl; auto; try omega;
  prove_hygiene; eapply subst_closub_under_permit; eauto.
  }
assert (pwctx 0 (dot (rec (subst (under 1 s) b)) s) (dot (rec (subst (under 1 s') b)) s') (cons hyp_tpl G)) as Hsb.
  {
  apply pwctx_cons_tpl; auto; try omega;
  prove_hygiene; eapply subst_closub_under_permit; eauto.
  }
assert (pwctx 0 (dot (rec (subst (under 1 s) a)) s) (dot (rec (subst (under 1 s') b)) s') (cons hyp_tpl G)) as Hsab.
  {
  apply pwctx_cons_tpl; auto; try omega;
  prove_hygiene; eapply subst_closub_under_permit; eauto.
  }
so (Hseq _#3 Hsa) as (R & Hal & Har & _).
so (Hseq _#3 Hsb) as (R' & _ & _ & Hbl & Hbr).
so (Hseq _#3 Hsab) as (R'' & Hal' & _ & _ & Hbr').
so (basic_fun _#7 Hal Hal'); subst R''.
so (basic_fun _#7 Hbr Hbr'); subst R'.
exists R.
do2 3 split; auto; simpsub;
apply interp_eval_refl; apply interp_rec; simpsub; auto.
}

(* S *)
{
intros i IH s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (pwctx_downward _#5 (Nat.le_succ_diag_r i) Hs) as Hsi.
so (IH _ _ Hsi) as (Ri & Hali & Hari & Hbli & Hbri).
clear IH.
simpsubin Hali.
simpsubin Hari.
simpsubin Hbli.
simpsubin Hbri.
assert (pwctx (S i) (dot (rec (subst (under 1 s) a)) s) (dot (rec (subst (under 1 s') a)) s') (cons hyp_tpl G)) as Hsa.
  {
  apply pwctx_cons_tpl; auto;
  try (prove_hygiene; eapply subst_closub_under_permit; eauto; done).
  intros _.
  cbn [pred].
  apply (seqhyp_tp _#3 Ri); auto.
  }
assert (pwctx (S i) (dot (rec (subst (under 1 s) b)) s) (dot (rec (subst (under 1 s') b)) s') (cons hyp_tpl G)) as Hsb.
  {
  apply pwctx_cons_tpl; auto;
  try (prove_hygiene; eapply subst_closub_under_permit; eauto; done).
  intros _.
  cbn [pred].
  apply (seqhyp_tp _#3 Ri); auto.
  }
assert (pwctx (S i) (dot (rec (subst (under 1 s) a)) s) (dot (rec (subst (under 1 s') b)) s') (cons hyp_tpl G)) as Hsab.
  {
  apply pwctx_cons_tpl; auto;
  try (prove_hygiene; eapply subst_closub_under_permit; eauto; done).
  intros _.
  cbn [pred].
  apply (seqhyp_tp _#3 Ri); auto.
  }
so (Hseq _#3 Hsa) as (R & Hal & Har & _).
so (Hseq _#3 Hsb) as (R' & _ & _ & Hbl & Hbr).
so (Hseq _#3 Hsab) as (R'' & Hal' & _ & _ & Hbr').
so (basic_fun _#7 Hal Hal'); subst R''.
so (basic_fun _#7 Hbr Hbr'); subst R'.
exists R.
do2 3 split; auto; simpsub;
apply interp_eval_refl; apply interp_rec; simpsub; auto.
}
Qed.


Lemma sound_rec_formation :
  forall G a b,
    pseq (cons hyp_tpl G) (deqtype a b)
    -> pseq G (deqtype (rec a) (rec b)).
Proof.
intros G a b.
revert G.
refine (seq_pseq 2 [hyp_emp] a [hyp_emp] b 1 [_] _ _ _); cbn.
intros G Hcla Hclb Hseq.
rewrite -> seq_eqtype in Hseq |- *.
apply sound_rec_formation_main; auto.
Qed.


Lemma sound_rec_formation_univ_main :
  forall G a b lv,
    hygiene (permit (ctxpred G)) a
    -> hygiene (permit (ctxpred G)) b
    -> hygiene (ctxpred G) lv
    -> (forall i s s',
          pwctx i s s' (cons (hyp_tml (univ lv)) G)
          -> exists pg R,
               pginterp (subst s (subst sh1 lv)) pg
               /\ pginterp (subst s' (subst sh1 lv)) pg
               /\ interp pg true i (subst s a) R
               /\ interp pg false i (subst s' a) R
               /\ interp pg true i (subst s b) R
               /\ interp pg false i (subst s' b) R)
    -> (forall i s s',
          pwctx i s s' G
          -> exists pg,
               pginterp (subst s lv) pg
               /\ pginterp (subst s' lv) pg)
    -> forall i s s',
         pwctx i s s' G
         -> exists pg R,
              pginterp (subst s lv) pg
              /\ pginterp (subst s' lv) pg
              /\ interp pg true i (subst s (rec a)) R
              /\ interp pg false i (subst s' (rec a)) R
              /\ interp pg true i (subst s (rec b)) R
              /\ interp pg false i (subst s' (rec b)) R.
Proof.
intros G a b lv Hcla Hclb Hcllv Hseq Hlv.
intros i.
induct i.

(* 0 *)
{
intros s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hlv _#3 Hs) as (pg & Hlvl & Hlvr).
assert (pwctx 0 (dot (rec (subst (under 1 s) a)) s) (dot (rec (subst (under 1 s') a)) s') (cons (hyp_tml (univ lv)) G)) as Hsa.
  {
  apply pwctx_cons_tml; auto; prove_hygiene; 
  try (eapply subst_closub_under_permit; eauto);
  intros; omega.
  }
assert (pwctx 0 (dot (rec (subst (under 1 s) b)) s) (dot (rec (subst (under 1 s') b)) s') (cons (hyp_tml (univ lv)) G)) as Hsb.
  {
  apply pwctx_cons_tml; auto; prove_hygiene; 
  try (eapply subst_closub_under_permit; eauto);
  intros; omega.
  }
assert (pwctx 0 (dot (rec (subst (under 1 s) a)) s) (dot (rec (subst (under 1 s') b)) s') (cons (hyp_tml (univ lv)) G)) as Hsab.
  {
  apply pwctx_cons_tml; auto; prove_hygiene; 
  try (eapply subst_closub_under_permit; eauto);
  intros; omega.
  }
so (Hseq _#3 Hsa) as (pg' & R & Hlvl' & _ & Hal & Har & _).
simpsubin Hlvl'.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'; clear Hlvl'.
so (Hseq _#3 Hsb) as (pg' & R' & Hlvl' & _ & _ & _ & Hbl & Hbr).
simpsubin Hlvl'.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'; clear Hlvl'.
so (Hseq _#3 Hsab) as (pg' & R'' & Hlvl' & _ & Hal' & _ & _ & Hbr').
simpsubin Hlvl'.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'; clear Hlvl'.
so (basic_fun _#7 Hal Hal'); subst R''.
so (basic_fun _#7 Hbr Hbr'); subst R'.
exists pg, R.
do2 5 split; auto; simpsub;
apply interp_eval_refl; apply interp_rec; simpsub; auto.
}

(* S *)
{
intros i IH s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (pwctx_downward _#5 (Nat.le_succ_diag_r i) Hs) as Hsi.
so (IH _ _ Hsi) as (pg & Ri & Hlvl & Hlvr & Hali & Hari & Hbli & Hbri).
clear IH.
simpsubin Hali.
simpsubin Hari.
simpsubin Hbli.
simpsubin Hbri.
assert (pwctx (S i) (dot (rec (subst (under 1 s) a)) s) (dot (rec (subst (under 1 s') a)) s') (cons (hyp_tml (univ lv)) G)) as Hsa.
  {
  apply pwctx_cons_tml; auto;
  try (prove_hygiene; eapply subst_closub_under_permit; eauto; done).
    {
    intros _.
    cbn [pred].
    apply (seqhyp_tm _#5 (iuuniv the_system i pg)); simpsub; auto;
    try (apply interp_eval_refl; apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top; done).
    split; auto.
    exists Ri.
    rewrite -> sint_unroll; auto.
    }

    {
    intros j u Hj Hu.
    so (Hlv _#3 Hu) as (pg' & Hlvl' & Hlvu).
    so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
    apply (relhyp_tm _#4 (iuuniv the_system j pg)); simpsub; auto;
    apply interp_eval_refl; apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
    }

    {
    intros j u Hj Hu.
    so (Hlv _#3 Hu) as (pg' & Hlvu & Hlvr').
    so (pginterp_fun _#3 Hlvr Hlvr'); subst pg'.
    apply (relhyp_tm _#4 (iuuniv the_system j pg)); simpsub; auto;
    apply interp_eval_refl; apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
    }
  }
assert (pwctx (S i) (dot (rec (subst (under 1 s) b)) s) (dot (rec (subst (under 1 s') b)) s') (cons (hyp_tml (univ lv)) G)) as Hsb.
  {
  apply pwctx_cons_tml; auto;
  try (prove_hygiene; eapply subst_closub_under_permit; eauto; done).
    {
    intros _.
    cbn [pred].
    apply (seqhyp_tm _#5 (iuuniv the_system i pg)); simpsub; auto;
    try (apply interp_eval_refl; apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top; done).
    split; auto.
    exists Ri.
    rewrite -> sint_unroll; auto.
    }

    {
    intros j u Hj Hu.
    so (Hlv _#3 Hu) as (pg' & Hlvl' & Hlvu).
    so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
    apply (relhyp_tm _#4 (iuuniv the_system j pg)); simpsub; auto;
    apply interp_eval_refl; apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
    }

    {
    intros j u Hj Hu.
    so (Hlv _#3 Hu) as (pg' & Hlvu & Hlvr').
    so (pginterp_fun _#3 Hlvr Hlvr'); subst pg'.
    apply (relhyp_tm _#4 (iuuniv the_system j pg)); simpsub; auto;
    apply interp_eval_refl; apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
    }
  }
assert (pwctx (S i) (dot (rec (subst (under 1 s) a)) s) (dot (rec (subst (under 1 s') b)) s') (cons (hyp_tml (univ lv)) G)) as Hsab.
  {
  apply pwctx_cons_tml; auto;
  try (prove_hygiene; eapply subst_closub_under_permit; eauto; done).
    {
    intros _.
    cbn [pred].
    apply (seqhyp_tm _#5 (iuuniv the_system i pg)); simpsub; auto;
    try (apply interp_eval_refl; apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top; done).
    split; auto.
    exists Ri.
    rewrite -> sint_unroll; auto.
    }

    {
    intros j u Hj Hu.
    so (Hlv _#3 Hu) as (pg' & Hlvl' & Hlvu).
    so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
    apply (relhyp_tm _#4 (iuuniv the_system j pg)); simpsub; auto;
    apply interp_eval_refl; apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
    }

    {
    intros j u Hj Hu.
    so (Hlv _#3 Hu) as (pg' & Hlvu & Hlvr').
    so (pginterp_fun _#3 Hlvr Hlvr'); subst pg'.
    apply (relhyp_tm _#4 (iuuniv the_system j pg)); simpsub; auto;
    apply interp_eval_refl; apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
    }
  }
so (Hseq _#3 Hsa) as (pg' & R & Hlvl' & _ & Hal & Har & _).
simpsubin Hlvl'.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'; clear Hlvl'.
so (Hseq _#3 Hsb) as (pg' & R' & Hlvl' & _ & _ & _ & Hbl & Hbr).
simpsubin Hlvl'.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'; clear Hlvl'.
so (Hseq _#3 Hsab) as (pg' & R'' & Hlvl' & _ & Hal' & _ & _ & Hbr').
simpsubin Hlvl'.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'; clear Hlvl'.
so (basic_fun _#7 Hal Hal'); subst R''.
so (basic_fun _#7 Hbr Hbr'); subst R'.
exists pg, R.
do2 5 split; auto; simpsub;
apply interp_eval_refl; apply interp_rec; simpsub; auto.
}
Qed.


Lemma sound_rec_formation_univ :
  forall G lv a b,
    pseq (cons (hyp_tml (univ lv)) G) (deq a b (univ (subst sh1 lv)))
    -> pseq G (deq lv lv pagetp)
    -> pseq G (deq (rec a) (rec b) (univ lv)).
Proof.
intros G lv a b.
revert G.
refine (seq_pseq 3 [hyp_emp] a [hyp_emp] b [] lv 2 [_] _ [] _ _ _); cbn.
intros G Hcla Hclb Hcllv Hseq Hseqlv.
rewrite -> seq_univ in Hseq |- *.
rewrite -> seq_deq in Hseqlv.
eassert _ as Hlv; [refine (seq_pagetp_invert G lv _) |].
  {
  intros i t t' Ht.
  so (Hseqlv _#3 Ht) as (R & Hl & _ & Hlv & _).
  eauto.
  }
clear Hseqlv.
apply sound_rec_formation_univ_main; auto.
Qed.


Lemma sound_rec_unroll :
  forall G a,
    pseq (cons hyp_tpl G) (deqtype a a)
    -> pseq G (deqtype (rec a) (subst1 (rec a) a)).
Proof.
intros G a.
revert G.
refine (seq_pseq 1 [hyp_emp] a 1 [_] _ _ _); cbn.
intros G Hcla Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (sound_rec_formation_main _#3 Hcla Hcla Hseq _#3 Hs) as (R & Hal & Har & _).
simpsubin Hal.
simpsubin Har.
exists R.
simpsub.
do2 3 split; auto.
  {
  invert (basic_value_inv _#6 value_rec Hal).
  intros Hunroll.
  simpsubin Hunroll.
  exact Hunroll.
  }

  {
  invert (basic_value_inv _#6 value_rec Har).
  intros Hunroll.
  simpsubin Hunroll.
  exact Hunroll.
  }
Qed.


Lemma sound_rec_unroll_univ :
  forall G lv a,
    pseq (cons (hyp_tml (univ lv)) G) (deq a a (univ (subst sh1 lv)))
    -> pseq G (deq lv lv pagetp)
    -> pseq G (deq (rec a) (subst1 (rec a) a) (univ lv)).
Proof.
intros G lv a.
revert G.
refine (seq_pseq 2 [hyp_emp] a [] lv 2 [_] _ [] _ _ _); cbn.
intros G Hcla Hcllv Hseq Hseqlv.
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
so (sound_rec_formation_univ_main _#4 Hcla Hcla Hcllv Hseq Hlv _#3 Hs) as (pg & R & Hlvl & Hlvr & Hal & Har & _).
simpsubin Hal.
simpsubin Har.
exists pg, R.
simpsub.
do2 5 split; auto.
  {
  invert (basic_value_inv _#6 value_rec Hal).
  intros Hunroll.
  simpsubin Hunroll.
  exact Hunroll.
  }

  {
  invert (basic_value_inv _#6 value_rec Har).
  intros Hunroll.
  simpsubin Hunroll.
  exact Hunroll.
  }
Qed.


Lemma sound_rec_bisim :
  forall G a b,
    pseq (cons hyp_tpl G) (deqtype a a)
    -> pseq G (deqtype b (subst1 b a))
    -> pseq G (deqtype b (rec a)).
Proof.
intros G a b.
revert G.
refine (seq_pseq 2 [hyp_emp] a [] b 2 [_] _ [] _ _ _); cbn.
intros G Hcla Hclb Hseqa Hseqb.
rewrite -> seq_eqtype in Hseqa, Hseqb |- *.
intro i.
induct i.

(* 0 *)
{
intros s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
assert (pwctx 0 (dot (subst s b) s) (dot (rec (subst (under 1 s') a)) s') (cons hyp_tpl G)) as Hsbm.  {
  apply pwctx_cons_tpl; auto; try prove_hygiene; try omega.
  eapply subst_closub_under_permit; eauto.
  }
assert (pwctx 0 (dot (rec (subst (under 1 s) a)) s) (dot (rec (subst (under 1 s') a)) s') (cons hyp_tpl G)) as Hsm.  
  {
  apply pwctx_cons_tpl; auto; try prove_hygiene; try omega;
  eapply subst_closub_under_permit; eauto.
  }
so (Hseqa _#3 Hsbm) as (R & Hbal & Hmar & _).
so (Hseqa _#3 Hsm) as (R' & Hmal & Hmar' & _).
so (Hseqb _#3 Hs) as (R'' & Hbl & Hbr & Hbal' & _).
so (basic_fun _#7 Hmar Hmar'); subst R'.
simpsubin Hbal'.
so (basic_fun _#7 Hbal Hbal'); subst R''.
exists R.
do2 3 split; auto; simpsub;
apply interp_eval_refl;
apply interp_rec; simpsub; auto.
}

(* S *)
{
intros i IH s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
assert (i <= S i) as Hi by omega.
so (IH _ _ (pwctx_downward _#5 Hi Hs)) as (Q & Hbli & _ & Hmali & Hmari).
simpsubin Hmali.
simpsubin Hmari.
assert (pwctx (S i) (dot (subst s b) s) (dot (rec (subst (under 1 s') a)) s') (cons hyp_tpl G)) as Hsbm.
  {
  eapply pwctx_cons_tpl; auto; try prove_hygiene.
    {
    eapply subst_closub_under_permit; eauto.
    }
  intros _.
  cbn [pred].
  apply (seqhyp_tp _#3 Q); auto.
  }
assert (pwctx (S i) (dot (rec (subst (under 1 s) a)) s) (dot (rec (subst (under 1 s') a)) s') (cons hyp_tpl G)) as Hsm.  
  {
  apply pwctx_cons_tpl; auto; try (prove_hygiene; eapply subst_closub_under_permit; eauto; done).
  intros _.
  cbn [pred].
  simpsub.
  apply (seqhyp_tp _#3 Q); auto.
  }
so (Hseqa _#3 Hsbm) as (R & Hbal & Hmar & _).
so (Hseqa _#3 Hsm) as (R' & Hmal & Hmar' & _).
so (Hseqb _#3 Hs) as (R'' & Hbl & Hbr & Hbal' & _).
so (basic_fun _#7 Hmar Hmar'); subst R'.
simpsubin Hbal'.
so (basic_fun _#7 Hbal Hbal'); subst R''.
exists R.
do2 3 split; auto; simpsub;
apply interp_eval_refl;
apply interp_rec; simpsub; auto.
}
Qed.
