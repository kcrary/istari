
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

Require Import SemanticsEqtype.
Require Import Equivalence.
Require Import ContextHygiene.
Require Import Subsumption.
Require Import Truncate.
Require Import ProperDownward.


Local Ltac prove_hygiene :=
  repeat (apply hygiene_auto; cbn; repeat2 split; auto);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1, subst_closub;
  try (apply hygiene_var; cbn; auto; done).


Lemma sound_eqtype_formation :
  forall G a a' b b',
    pseq G (deqtype a a')
    -> pseq G (deqtype b b')
    -> pseq G (deqtype (eqtype a b) (eqtype a' b')).
Proof.
intros G a b c d.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqab Hseqcd.
rewrite -> seq_eqtype in Hseqab, Hseqcd |- *.
intros i s s' Hs.
so (Hseqab _#3 Hs) as (A & Hal & Har & Hbl & Hbr).
so (Hseqcd _#3 Hs) as (C & Hcl & Hcr & Hdl & Hdr).
exists (iueqtype stop i A C).
simpsub.
do2 3 split;
apply interp_eval_refl;
apply interp_eqtype; auto.
Qed.


Lemma sound_eqtype_formation_univ :
  forall G lv a a' b b',
    pseq G (deq a a' (univ lv))
    -> pseq G (deq b b' (univ lv))
    -> pseq G (deq (eqtype a b) (eqtype a' b') (univ lv)).
Proof.
intros G lv a b c d.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqab Hseqcd.
rewrite -> seq_univ in Hseqab, Hseqcd |- *.
intros i s s' Hs.
so (Hseqab _#3 Hs) as (pg & A & Hlvl & Hlvr & Hal & Har & Hbl & Hbr).
so (Hseqcd _#3 Hs) as (pg' & C & Hlvl' & _ & Hcl & Hcr & Hdl & Hdr).
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
exists pg, (iueqtype stop i A C).
simpsub.
do2 5 split; auto;
apply interp_eval_refl;
apply interp_eqtype; auto.
Qed.


Lemma sound_eqtype_convert :
  forall G m n a b,
    pseq G (deqtype a b)
    -> pseq G (deq m n a)
    -> pseq G (deq m n b).
Proof.
intros G m n a b.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqab Hseqmn.
rewrite -> seq_eqtype in Hseqab.
invertc Hseqmn; intro Hseqmn.
apply seq_i.
intros i s s' Hs.
so (Hseqab _#3 Hs) as (A & Hal & _  & Hbl & Hbr).
so (Hseqmn _#3 Hs) as (A' & Hal' & _ & Hm & Hn & Hmn).
so (basic_fun _#7 Hal Hal'); subst A'.
exists A.
do2 4 split; auto.
Qed.


(* now redundant *)
Lemma sound_eqtype_convert_hyp :
  forall G1 G2 a b J,
    pseq G1 (deqtype a b)
    -> pseq (G2 ++ hyp_tm b :: G1) J
    -> pseq (G2 ++ hyp_tm a :: G1) J.
Proof.
intros G1 G2 a b J.
revert G1.
refine (seq_pseq_hyp 0 2 [] [] _ _ [_] _ _ [_] _ _); cbn.
intros G Hseqab Hseq HclJ.
autorewrite with canonlist in Hseq |- *.
rewrite -> seq_eqtype in Hseqab.
replace J with (substj (under (length G2) id) J) in Hseq by (simpsub; reflexivity).
replace G2 with (substctx id G2) in Hseq by (simpsub; reflexivity).
refine (subsume_seq _ _ (under (length G2) id) _ _ _ _ Hseq); auto.
rewrite -> length_substctx.
apply subsume_under.
clear J HclJ Hseq.
do2 2 split.
  {
  intros j.
  split.
    {
    intro Hj.
    cbn.
    simpsub.
    apply hygiene_var; auto.
    }

    {
    intro Hj.
    cbn.
    simpsubin Hj.
    invert Hj.
    auto.
    }
  }

  {
  intros j.
  split.
    {
    intro Hj.
    cbn.
    simpsub.
    apply hygiene_var; auto.
    }

    {
    intro Hj.
    cbn.
    simpsubin Hj.
    invert Hj.
    auto.
    }
  }
intros i ss ss' Hss.
invertc Hss.
intros m n s s' Hs Hmn _ _ <- <-.
invertc Hmn.
intros A Hal Har Hmn.
so (Hseqab _#3 Hs) as (B & Hal' & _ & Hbl & Hbr).
so (basic_fun _#7 Hal Hal'); subst B.
clear Hal'.
do2 4 split.
  {
  simpsub.
  apply pwctx_cons_tm_seq; eauto using seqhyp_tm.
  intros j u u' Hu.
  so (Hseqab _#3 Hu) as (B & _ & _ & Hl & Hr).
  eauto.
  }

  {
  simpsub.
  apply equivsub_refl.
  }

  {
  simpsub.
  apply equivsub_refl.
  }

  {
  intros j d uu Hsmall Huu.
  simpsubin Huu.
  simpsub.
  rewrite -> qpromote_cons in Huu |- *.
  rewrite -> qpromote_hyp_tm in Huu |- *.
  invertc Huu.
  intros p u Hu Hmp <-.
  so (smaller_impl_le _#3 Hsmall) as Hj.
  apply seqctx_cons; auto.
  simpsub.
  simpsubin Hmp.
  invertc Hmp.
  intros B Hbl' Hbu Hmp.
  so (basic_fun _#7 (basic_downward _#7 Hj Hbl) Hbl'); subst B.
  apply (seqhyp_tm _#5 (iutruncate (S j) A)); auto.
    {
    eapply basic_downward; eauto.
    }

    {
    so (seqctx_pwctx_demote_left _#7 Hsmall Hs Hu) as Hu'.
    so (Hseqab _#3 Hu') as (B & _ & Hau & _ & Hbu').
    so (basic_fun _#7 Hbu Hbu'); subst B.
    exact Hau.
    }
  }

  {
  intros j d uu Hsmall Huu.
  simpsubin Huu.
  simpsub.
  rewrite -> qpromote_cons in Huu |- *.
  rewrite -> qpromote_hyp_tm in Huu |- *.
  invertc Huu.
  intros p u Hu Hmp <-.
  so (smaller_impl_le _#3 Hsmall) as Hj.
  apply seqctx_cons; auto.
  simpsub.
  simpsubin Hmp.
  invertc Hmp.
  intros B Hbu Hbr' Hmp.
  so (basic_fun _#7 (basic_downward _#7 Hj Hbr) Hbr'); subst B.
  apply (seqhyp_tm _#5 (iutruncate (S j) A)); auto.
    {
    so (seqctx_pwctx_demote_right _#7 Hsmall Hs Hu) as Hu'.
    so (Hseqab _#3 Hu') as (B & Hau & _ & Hbu' & _).
    so (basic_fun _#7 Hbu Hbu'); subst B.
    exact Hau.
    }

    {
    eapply basic_downward; eauto.
    }
  }
Qed.


Lemma sound_eqtype_symmetry :
  forall G a b,
    pseq G (deqtype a b)
    -> pseq G (deqtype b a).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hal & Har & Hbl & Hbr).
exists R; auto.
Qed.


Lemma sound_eqtype_transitivity :
  forall G a b c,
    pseq G (deqtype a b)
    -> pseq G (deqtype b c)
    -> pseq G (deqtype a c).
Proof.
intros G a b c.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hab Hbc.
rewrite -> seq_eqtype in Hab, Hbc |- *.
intros i s s' Hs.
so (Hab _#3 Hs) as (R & Hal & Har & Hbl & _).
so (Hbc _#3 Hs) as (R' & Hbl' & _ & Hcl & Hcr).
so (basic_fun _#7 Hbl Hbl'); subst R'.
exists R.
auto.
Qed.


Lemma sound_eqtype_eta :
  forall G a b p,
    pseq G (deq p p (eqtype a b))
    -> pseq G (deq p triv (eqtype a b)).
Proof.
intros G a b p.
revert G.
refine (seq_pseq 1 [] p 1 [] _ _ _); cbn.
intros G Hclp Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq _#3 Hs) as (R & Hequall & Hequalr & Htrue & _).
exists R.
do2 4 split; auto.
  {
  simpsub.
  simpsubin Hequall.
  invert (basic_value_inv _#6 value_eqtype Hequall).
  intros Q Q' Hl Hr <-.
  do2 5 split; auto using star_refl; try prove_hygiene.
  destruct Htrue as (H & _).
  exact H.
  }

  {
  simpsub.
  simpsubin Hequall.
  invert (basic_value_inv _#6 value_eqtype Hequall).
  intros Q Q' Hl Hr <-.
  destruct Htrue as (H & _ & _ & _ & Hsteps & _).
  do2 5 split; auto using star_refl; try prove_hygiene.
  }
Qed.


Lemma sound_eqtype_eta_hyp :
  forall G1 G2 a a' m n b,
    pseq (substctx (dot triv id) G2 ++ G1) (deq m n (subst (under (length G2) (dot triv id)) b))
    -> pseq (G2 ++ hyp_tm (eqtype a a') :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) b).
Proof.
intros G1 G2 a a' m n b Hseq.
eapply sound_property_eta_hyp; eauto.
intros s pg z i R H.
simpsubin H.
invert (basic_value_inv _#6 value_eqtype H).
intros A A' _ _ <-.
do 3 eexists.
reflexivity.
Qed.
