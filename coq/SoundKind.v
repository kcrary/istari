
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

Require Import SemanticsKind.
Require Import SemanticsUniv.
Require Import Defined.
Require Import PageType.
Require Import ProperLevel.



Lemma sound_kind_formation :
  forall G lv lv',
    pseq G (deq lv lv' pagetp)
    -> pseq G (deqtype (kind lv) (kind lv')).
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
so (pginterp_lt_top _ _ Hlv1l) as hl.
so (pginterp_succ_lt_top _ _ hl Hlv1l) as hls.
exists (iukind the_system i pg hl).
simpsub.
do2 3 split;
apply interp_eval_refl; apply interp_kind; eauto using pginterp_str_top, pginterp_cex_top.
Qed.


Local Ltac prove_hygiene :=
  repeat (first [ apply hygiene_shift_permit
                | apply hygiene_sumbool
                | apply natlit_closed
                | apply hygiene_auto; cbn; repeat2 split; auto
                ]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1;
  try (apply hygiene_var; cbn; auto; done).


Lemma pginterp_succ :
  forall lv pg h,
    pginterp lv pg
    -> pginterp (nsucc lv) (succ_page pg h).
Proof.
intros lv pg h Hlv.
destruct Hlv as (w & Hint & Hstr & Hcex & Hcin).
destruct Hint as (l & Hint & ->).
assert (natinterp (nsucc lv) (S l)) as Hint'.
  {
  apply natinterp_nsucc; auto.
  }
exists (fin (S l)); do2 3 split; cbn; auto.
  {
  exists (S l); auto.
  }

  {
  rewrite -> Hstr.
  apply succ_fin.
  }

  {
  rewrite -> Hcex.
  apply succ_fin.
  }

  {
  rewrite -> Hcex.
  apply succ_fin.
  }
Qed.


Lemma sound_kind_formation_univ :
  forall G lv lv1 lv2,
    pseq G (deq lv1 lv2 pagetp)
    -> pseq G (deq lv lv pagetp)
    -> pseq G (deq triv triv (ltpagetp (nsucc lv1) lv))
    -> pseq G (deq (kind lv1) (kind lv2) (univ lv)).
Proof.
intros G lv lv1 lv2.
revert G.
refine (seq_pseq 0 3 [] _ [] _ [] _ _ _); cbn.
intros G Hseqlv12 Hseqlv Hseqlt.
rewrite seq_deq in Hseqlv12, Hseqlv, Hseqlt |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
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
so (pginterp_lt_top _ _ Hlv1l) as hl.
simpsubin Hintlt.
so (pginterp_succ _ _ hl Hlv1l) as Hlvsucc.
so (interp_ltpagetp_invert _#11 Hintlt Hinhlt Hlvsucc Hlvl) as Hlt.
so (lt_le_page_trans _#3 (lt_page_succ _ hl) (lt_page_impl_le_page _ _ Hlt)) as Hlt'.
destruct Hlt as (Hltstr & Hltcex).
destruct Hlt' as (Hltstr' & Hltcex').
exists (iuuniv the_system i pg').
simpsub.
assert (sint the_system pg' true i (kind (subst s lv1)) (iukind the_system i pg hl)) as Hintlv1l.
  {
  rewrite -> sint_unroll.
  apply interp_eval_refl.
  apply interp_kind; auto.
  split; auto.
  }
assert (sint the_system pg' false i (kind (subst s' lv1)) (iukind the_system i pg hl)) as Hintlv1r.
  {
  rewrite -> sint_unroll.
  apply interp_eval_refl.
  apply interp_kind; auto.
  split; auto.
  }
assert (sint the_system pg' true i (kind (subst s lv2)) (iukind the_system i pg hl)) as Hintlv2l.
  {
  rewrite -> sint_unroll.
  apply interp_eval_refl.
  apply interp_kind; auto.
  split; auto.
  }
assert (sint the_system pg' false i (kind (subst s' lv2)) (iukind the_system i pg hl)) as Hintlv2r.
  {
  rewrite -> sint_unroll.
  apply interp_eval_refl.
  apply interp_kind; auto.
  split; auto.
  }
do2 4 split;
try (apply interp_eval_refl; apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top; done);
try (cbn; split; auto; exists (iukind the_system i pg hl); auto).
Qed.


Lemma sound_kind_weaken :
  forall G lv a b,
    pseq G (deq a b (kind lv))
    -> pseq G (deq a b (univ (nsucc lv))).
Proof.
intros G lv a b.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqkind in Hseq.
rewrite -> seq_univ.
intros i s s' Hs.
so (Hseq _#3 Hs) as (pg & K & R & hl & Hlvl & Hlvr & _ & _ & _ & _ & Hal & Har & Hbl & Hbr).
set (pg' := succ_page pg hl).
exists pg', R.
simpsub.
do2 5 split; auto.
  {
  apply pginterp_succ; auto.
  }

  {
  apply pginterp_succ; auto.
  }
Qed.


Lemma sound_kind_formation_invert :
  forall G lv lv',
    pseq G (deqtype (kind lv) (kind lv'))
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
invert (basic_value_inv _#6 value_kind Hll).
intros pg h Hpgll _ Heq.
invert (basic_value_inv _#6 value_kind Hlr).
intros pg' h' Hpglr _ Heq'.
so (iukind_inj _#7 (eqtrans Heq (eqsymm Heq'))); subst pg'.
clear Heq'.
so (proof_irrelevance _ h h'); subst h'.
invert (basic_value_inv _#6 value_kind Hml).
intros pg' h' Hpgml _ Heq'.
so (iukind_inj _#7 (eqtrans Heq (eqsymm Heq'))); subst pg'.
clear Heq'.
so (proof_irrelevance _ h h'); subst h'.
invert (basic_value_inv _#6 value_kind Hmr).
intros pg' h' Hpgmr _ Heq'.
so (iukind_inj _#7 (eqtrans Heq (eqsymm Heq'))); subst pg'.
clear Heq Heq'.
so (proof_irrelevance _ h h'); subst h'.
exists (nattp_def top i).
simpsub.
destruct Hpgll as (w & Hpgll & Heq & _).
destruct Hpglr as (w' & Hpglr & Heq' & _).
so (eqtrans (eqsymm Heq) Heq'); clear Heq'; subst w'.
destruct Hpgml as (w' & Hpgml & Heq' & _).
so (eqtrans (eqsymm Heq) Heq'); clear Heq'; subst w'.
destruct Hpgmr as (w' & Hpgmr & Heq' & _).
so (eqtrans (eqsymm Heq) Heq'); clear Heq'; subst w'.
clear h Heq pg.
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
