
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

Require Import SemanticsUniv.
Require Import Defined.
Require Import PageType.
Require Import ProperLevel.


Lemma sound_univ_kind_formation :
  forall G lv lv1 lv2,
    pseq G (deq lv1 lv2 pagetp)
    -> pseq G (deq lv1 lv pagetp)
    -> pseq G (deq (univ lv1) (univ lv2) (kuniv lv)).
Proof.
intros G lv3 lv1 lv2.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqlv12 Hseqlv13.
rewrite -> seq_eqkind.
rewrite -> seq_deq in Hseqlv12, Hseqlv13.
intros i s s' Hs.
so (Hseqlv12 _#3 Hs) as (R & Hpagetp & _ & Hlv1 & Hlv2 & Hlv12).
so (Hseqlv13 _#3 Hs) as (R' & Hpagetp' & _ & Hlv1' & Hlv3 & Hlv13).
simpsubin Hpagetp.
simpsubin Hpagetp'.
so (interp_pagetp_invert _#7 Hpagetp Hlv1) as (pg & Hlv1l & Hlv1r).
so (interp_pagetp_invert _#7 Hpagetp Hlv2) as (pg' & Hlv2l & Hlv2r).
so (interp_pagetp_invert _#7 Hpagetp Hlv12) as (pg'' & Hlv1l' & Hlv2r').
so (pginterp_fun _#3 Hlv1l Hlv1l'); subst pg''.
so (pginterp_fun _#3 Hlv2r Hlv2r'); subst pg'.
so (interp_pagetp_invert _#7 Hpagetp' Hlv3) as (pg' & Hlv3l & Hlv3r).
so (interp_pagetp_invert _#7 Hpagetp' Hlv13) as (pg'' & Hlv1l'' & Hlv3r').
so (pginterp_fun _#3 Hlv1l Hlv1l''); subst pg''.
so (pginterp_fun _#3 Hlv3r Hlv3r'); subst pg'.
so (pginterp_lt_top _ _ Hlv1l) as h.
exists pg, (qtype (cin pg)), (iuuniv the_system i pg), h.
simpsub.
do2 9 split; auto;
try (apply kinterp_eval_refl; apply interp_type; auto);
try (apply interp_eval_refl; apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top);
cbn; try apply succ_increase.
Qed.
    

Lemma sound_univ_formation :
  forall G lv lv',
    pseq G (deq lv lv' pagetp)
    -> pseq G (deqtype (univ lv) (univ lv')).
Proof.
intros G lv1 lv2.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype.
rewrite -> seq_deq in Hseq.
intros i s s' Hs.
so (Hseq i s s' Hs) as (R & Hpagetp & _ & Hlv1 & Hlv2 & Hlv12).
so (interp_pagetp_invert _#7 Hpagetp Hlv1) as (pg & Hlv1l & Hlv1r).
so (interp_pagetp_invert _#7 Hpagetp Hlv2) as (pg' & Hlv2l & Hlv2r).
so (interp_pagetp_invert _#7 Hpagetp Hlv12) as (pg'' & Hlv1l' & Hlv2r').
so (pginterp_fun _#3 Hlv1l Hlv1l'); subst pg''.
so (pginterp_fun _#3 Hlv2r Hlv2r'); subst pg'.
exists (iuuniv the_system i pg).
simpsub.
do2 3 split;
apply interp_eval_refl; apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
Qed.


Lemma sound_univ_formation_univ :
  forall G lv lv1 lv2,
    pseq G (deq lv1 lv2 pagetp)
    -> pseq G (deq lv lv pagetp)
    -> pseq G (deq triv triv (ltpagetp lv1 lv))
    -> pseq G (deq (univ lv1) (univ lv2) (univ lv)).
Proof.
intros G lv lv1 lv2.
revert G.
refine (seq_pseq 0 3 [] _ [] _ [] _ _ _); cbn.
intros G Hseqlv12 Hseqlv Hseqlt.
rewrite -> seq_deq in Hseqlv12, Hseqlv, Hseqlt |- *.
intros i s s' Hs.
so (Hseqlv12 _#3 Hs) as (R & Hpagetp & _ & Hlv1 & Hlv2 & Hlv12).
so (interp_pagetp_invert _#7 Hpagetp Hlv1) as (pg & Hlv1l & Hlv1r).
so (interp_pagetp_invert _#7 Hpagetp Hlv2) as (pg' & Hlv2l & Hlv2r).
so (interp_pagetp_invert _#7 Hpagetp Hlv12) as (pg'' & Hlv1l' & Hlv2r').
so (pginterp_fun _#3 Hlv1l Hlv1l'); subst pg''.
so (pginterp_fun _#3 Hlv2r Hlv2r'); subst pg'.
clear R Hpagetp Hlv1 Hlv2 Hlv12.
so (Hseqlv _#3 Hs) as (R & Hpagetp & _ & Hlv & _).
so (interp_pagetp_invert _#7 Hpagetp Hlv) as (pg' & Hlvl & Hlvr).
clear R Hpagetp Hlv.
so (Hseqlt _#3 Hs) as (R & Hintlt & _ & Hinhlt & _).
so (interp_ltpagetp_invert _#11 Hintlt Hinhlt Hlv1l Hlvl) as Hlt.
destruct Hlt as (Hltstr & Hltcex).
exists (iuuniv the_system i pg').
simpsub.
assert (sint the_system pg' true i (univ (subst s lv1)) (iuuniv the_system i pg)) as Hintlv1l.
  {
  rewrite -> sint_unroll.
  apply interp_eval_refl.
  apply interp_univ; auto.
  }
assert (sint the_system pg' false i (univ (subst s' lv1)) (iuuniv the_system i pg)) as Hintlv1r.
  {
  rewrite -> sint_unroll.
  apply interp_eval_refl.
  apply interp_univ; auto.
  }
assert (sint the_system pg' true i (univ (subst s lv2)) (iuuniv the_system i pg)) as Hintlv2l.
  {
  rewrite -> sint_unroll.
  apply interp_eval_refl.
  apply interp_univ; auto.
  }
assert (sint the_system pg' false i (univ (subst s' lv2)) (iuuniv the_system i pg)) as Hintlv2r.
  {
  rewrite -> sint_unroll.
  apply interp_eval_refl.
  apply interp_univ; auto.
  }
do2 4 split;
try (apply interp_eval_refl; apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top; done);
try (cbn; split; auto; exists (iuuniv the_system i pg); auto).
Qed.


Lemma sound_univ_cumulative :
  forall G lv lv' a b,
    pseq G (deq a b (univ lv))
    -> pseq G (deq lv' lv' pagetp)
    -> pseq G (deq triv triv (leqpagetp lv lv'))
    -> pseq G (deq a b (univ lv')).
Proof.
intros G glv lv a b.
revert G.
refine (seq_pseq 0 3 [] _ [] _ [] _ _ _); cbn.
intros G Hseqab Hseqlv Hseqleq.
rewrite -> seq_univ in Hseqab |- *.
rewrite -> seq_deq in Hseqlv, Hseqleq.
intros i s s' Hs.
so (Hseqab _#3 Hs) as (gpg & A & Hglvl & _ & Hal & Har & Hbl & Hbr).
so (Hseqlv _#3 Hs) as (R & Hpagetp & _ & Hlv & _).
so (interp_pagetp_invert _#7 Hpagetp Hlv) as (pg & Hlvl & Hlvr).
so (Hseqleq _#3 Hs) as (Q & Hleql & _ & Hleqinh & _).
so (interp_leqpagetp_invert _#11 Hleql Hleqinh Hglvl Hlvl) as Hle.
exists pg, A.
do2 5 split; eauto using interp_increase.
Qed.


Lemma sound_formation_weaken :
  forall G lv a b,
    pseq G (deq a b (univ lv))
    -> pseq G (deqtype a b).
Proof.
intros G lv a b.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype.
rewrite -> seq_deq in Hseq.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Huniv & _ & Ha & Hb & Hab).
simpsubin Huniv.
invert (basic_value_inv _#6 value_univ Huniv).
intros pg Hlv _ _ <-.
destruct Ha as (_ & R & Hal & Har).
destruct Hb as (_ & R' & Hbl & Hbr).
destruct Hab as (_ & R'' & Hal' & Hbr').
so (sint_fun _#7 Hal Hal'); subst R''.
so (sint_fun _#7 Hbr Hbr'); subst R'.
exists R.
rewrite -> sint_unroll in Hal, Har, Hbl, Hbr.
do2 3 split; eapply interp_increase; eauto using toppg_max.
Qed.


Lemma sound_formation_strengthen :
  forall G lv a b,
    pseq G (deqtype a b)
    -> pseq G (deq a a (univ lv))
    -> pseq G (deq b b (univ lv))
    -> pseq G (deq a b (univ lv)).
Proof.
intros G lv a b.
revert G.
refine (seq_pseq 0 3 [] _ [] _ [] _ _ _); cbn.
intros G Hseqab Hseqa Hseqb.
rewrite -> seq_eqtype in Hseqab.
rewrite -> seq_deq in Hseqa, Hseqb |- *.
intros i s s' Hs.
so (Hseqa _#3 Hs) as (R & Hunivl & Hunivr & Ha & _).
so (Hseqb _#3 Hs) as (R' & Hunivl' & _ & Hb & _).
so (basic_fun _#7 Hunivl Hunivl'); subst R'.
exists R.
do2 4 split; auto.
simpsubin Hunivl.
invert (basic_value_inv _#6 value_univ Hunivl).
intros pg Hpg _ _ <-.
split; auto.
destruct Ha as (_ & A & Hal & _).
destruct Hb as (_ & B & _ & Hbr).
rewrite -> sint_unroll in Hal, Hbr.
so (Hseqab _#3 Hs) as (C & Hal' & _ & _ & Hbr').
so (interp_fun _#7 Hal Hal'); subst C.
so (interp_fun _#7 Hbr Hbr'); subst B.
exists A.
rewrite -> sint_unroll; auto.
Qed.


Lemma sound_univ_formation_invert :
  forall G lv lv',
    pseq G (deqtype (univ lv) (univ lv'))
    -> pseq G (deq lv lv' pagetp).
Proof.
intros G l m.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq.
rewrite -> seq_deq.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hll & Hlr & Hml & Hmr).
simpsubin Hll.
simpsubin Hlr.
simpsubin Hml.
simpsubin Hmr.
invert (basic_value_inv _#6 value_univ Hll).
intros pg Hpgll _ _ Heq.
invert (basic_value_inv _#6 value_univ Hlr).
intros pg' Hpglr _ _ Heq'.
so (iuuniv_inj _#5 (eqtrans Heq (eqsymm Heq'))); subst pg'.
clear Heq'.
invert (basic_value_inv _#6 value_univ Hml).
intros pg' Hpgml _ _ Heq'.
so (iuuniv_inj _#5 (eqtrans Heq (eqsymm Heq'))); subst pg'.
clear Heq'.
invert (basic_value_inv _#6 value_univ Hmr).
intros pg' Hpgmr _ _ Heq'.
so (iuuniv_inj _#5 (eqtrans Heq (eqsymm Heq'))); subst pg'.
clear Heq Heq'.
exists (nattp_def top i).
simpsub.
destruct Hpgll as (w & Hpgll & Heq & _).
destruct Hpglr as (w' & Hpglr & Heq' & _).
so (eqtrans (eqsymm Heq) Heq'); clear Heq'; subst w'.
destruct Hpgml as (w' & Hpgml & Heq' & _).
so (eqtrans (eqsymm Heq) Heq'); clear Heq'; subst w'.
destruct Hpgmr as (w' & Hpgmr & Heq' & _).
so (eqtrans (eqsymm Heq) Heq'); clear Heq'; subst w'.
clear Heq pg.
destruct Hpgll as (j & Hpgll & Heq).
destruct Hpglr as (j' & Hpglr & Heq').
injection (eqtrans (eqsymm Heq) Heq').
intros <-; clear Heq'.
destruct Hpgml as (j' & Hpgml & Heq').
injection (eqtrans (eqsymm Heq) Heq').
intros <-; clear Heq'.
destruct Hpgmr as (j' & Hpgmr & Heq').
injection (eqtrans (eqsymm Heq) Heq').
intros <-; clear Heq'.
clear Heq.
so (succ_nodecrease top) as Htop.
do2 4 split.
  {
  apply interp_nattp.
  }

  {
  apply interp_nattp.
  }

  {
  rewrite -> nattp_nat_urel; auto.
  exists j.
  do2 2 split; auto.
  }

  {
  rewrite -> nattp_nat_urel; auto.
  exists j.
  do2 2 split; auto.
  }

  {
  rewrite -> nattp_nat_urel; auto.
  exists j.
  do2 2 split; auto.
  }
Qed.
