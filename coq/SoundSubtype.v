
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

Require Import SemanticsProperty.
Require Import SemanticsEqtype.
Require Import SemanticsSubtype.
Require Import Equivalence.
Require Import ContextHygiene.
Require Import Truncate.
Require Import ProperDownward.
Require Import Subsumption.


Local Ltac prove_hygiene :=
  repeat (apply hygiene_auto; cbn; repeat2 split; auto);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1, subst_closub;
  try (apply hygiene_var; cbn; auto; done).


Lemma sound_subtype_formation :
  forall G a a' b b',
    pseq G (deqtype a a')
    -> pseq G (deqtype b b')
    -> pseq G (deqtype (subtype a b) (subtype a' b')).
Proof.
intros G a b c d.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqab Hseqcd.
rewrite -> seq_eqtype in Hseqab, Hseqcd |- *.
intros i s s' Hs.
so (Hseqab _#3 Hs) as (A & Hal & Har & Hbl & Hbr).
so (Hseqcd _#3 Hs) as (C & Hcl & Hcr & Hdl & Hdr).
exists (iusubtype stop i A C).
simpsub.
do2 3 split;
apply interp_eval_refl;
apply interp_subtype; auto.
Qed.


Lemma sound_subtype_formation_univ :
  forall G lv a a' b b',
    pseq G (deq a a' (univ lv))
    -> pseq G (deq b b' (univ lv))
    -> pseq G (deq (subtype a b) (subtype a' b') (univ lv)).
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
exists pg, (iusubtype stop i A C).
simpsub.
do2 5 split; auto;
apply interp_eval_refl;
apply interp_subtype; auto.
Qed.


Lemma sound_subtype_intro :
  forall G a b,
    pseq G (deqtype a a)
    -> pseq G (deqtype b b)
    -> pseq (hyp_tm a :: G) (deq (var 0) (var 0) (subst sh1 b))
    -> pseq G (deq triv triv (subtype a b)).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 3 [] _ [] _ [_] _ _ _); cbn.
intros G Hseqa Hseqb Hseqincl.
rewrite -> seq_eqtype in Hseqa, Hseqb.
rewrite -> seq_deq in Hseqincl |- *.
intros i s s' Hs.
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
so (Hseqb _#3 Hs) as (B & Hbl & Hbr & _).
exists (iusubtype stop i A B).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl.
  apply interp_subtype; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_subtype; auto.
  }
cut (rel (den (iusubtype stop i A B)) i triv triv).
  {
  intro H; auto.
  }
cbn.
do2 5 split; auto using star_refl; try prove_hygiene.
intros j m p Hj Hmp.
assert (pwctx j (dot m s) (dot p s') (hyp_tm a :: G)) as Hs'.
  {
  apply pwctx_cons_tm_seq; eauto using pwctx_downward.
    {
    apply (seqhyp_tm _#5 (iutruncate (S j) A)).
      {
      eapply basic_downward; eauto.
      }

      {
      eapply basic_downward; eauto.
      }

      {
      split; auto.
      }
    }

    {
    intros k u u' Hu.
    so (Hseqa _#3 Hu) as (R & Hl & Hr & _).
    eauto.
    }
  }
so (Hseqincl _#3 Hs') as (R & Hbl' & _ & Hrel & _).
simpsubin Hbl'.
so (basic_fun _#7 (basic_downward _#7 Hj Hbl) Hbl'); subst R.
simpsubin Hrel.
destruct Hrel; auto.
Qed.


Lemma sound_subtype_elim :
  forall G a b m n,
    pseq G (deq triv triv (subtype a b))
    -> pseq G (deq m n a)
    -> pseq G (deq m n b).
Proof.
intros G a b m n.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqsub Hseqmn.
rewrite -> seq_deq in Hseqsub, Hseqmn |- *.
intros i s s' Hs.
so (Hseqsub _#3 Hs) as (R & Hsubl & Hsubr & Hinh & _).
simpsubin Hsubl.
simpsubin Hsubr.
invert (basic_value_inv _#6 value_subtype Hsubl).
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_subtype Hsubr).
intros A' B' Har Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iusubtype_inj _#6 Heq) as (<- & <-); clear Heq.
cbn in Hinh.
decompose Hinh.
intros Hsub _ _ _ _ _.
unfold subtype_property in Hsub.
assert (forall j p q,
          rel (den A) j p q
          -> rel (den B) j p q) as Hsub'.
  {
  intros j p q Hpq.
  so (basic_member_index _#9 Hal Hpq) as Hj.
  apply Hsub; auto.
  }
so (Hseqmn _#3 Hs) as (A' & Hal' & _ & Hm & Hn & Hmn).
so (basic_fun _#7 Hal Hal'); subst A'; clear Hal'.
exists B.
do2 4 split; auto.
Qed.


Lemma sound_subtype_eta :
  forall G a b p,
    pseq G (deq p p (subtype a b))
    -> pseq G (deq p triv (subtype a b)).
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
  invert (basic_value_inv _#6 value_subtype Hequall).
  intros Q Q' Hl Hr <-.
  do2 5 split; auto using star_refl; try prove_hygiene.
  destruct Htrue as (H & _).
  exact H.
  }

  {
  simpsub.
  simpsubin Hequall.
  invert (basic_value_inv _#6 value_subtype Hequall).
  intros Q Q' Hl Hr <-.
  destruct Htrue as (H & _ & _ & _ & Hsteps & _).
  do2 5 split; auto using star_refl; try prove_hygiene.
  }
Qed.


Lemma sound_subtype_eta_hyp :
  forall G1 G2 a a' m n b,
    pseq (substctx (dot triv id) G2 ++ G1) (deq m n (subst (under (length G2) (dot triv id)) b))
    -> pseq (G2 ++ hyp_tm (subtype a a') :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) b).
Proof.
intros G1 G2 a a' m n b Hseq.
eapply sound_property_eta_hyp; eauto.
intros s pg z i R H.
simpsubin H.
invert (basic_value_inv _#6 value_subtype H).
intros A A' _ _ <-.
do 3 eexists.
reflexivity.
Qed.


Lemma sound_subtype_convert_hyp :
  forall G1 G2 a b J,
    pseq (cons (hyp_tm (eqtype a a)) G1) (dsubtype (subst sh1 a) (subst sh1 b))
    -> pseq (cons (hyp_tm (eqtype a a)) G1) (dsubtype (subst sh1 b) (subst sh1 a))
    -> pseq (G2 ++ hyp_tm b :: G1) J
    -> pseq (G2 ++ hyp_tm a :: G1) J.
Proof.
intros G1 G2 a b J.
revert G1.
refine (seq_pseq_hyp 0 3 [] [_] _ [] [_] _ _ [_] _ _ [_] _ _); cbn.
intros G1 Hsubab Hsubba Hseq HclJ.
so (conj Hsubab Hsubba) as Hexteq.
simpsubin Hexteq.
rewrite -> seq_exteqtype in Hexteq.
clear Hsubab Hsubba.
replace J with (substj (under (length G2) id) J) in Hseq by (simpsub; reflexivity).
replace G2 with (substctx id G2) in Hseq by (simpsub; reflexivity).
refine (subsume_seq _ _ (under (length G2) id) _ _ HclJ _ Hseq).
rewrite -> length_substctx.
apply subsume_under.
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
intros m n s s' Hs Hmn Hleft Hright <- <-.
simpsubin Hmn.
invertc Hmn.
intros A Hal Har Hmn.
assert (forall j u,
          j <= i
          -> seqctx j s u G1
          -> pwctx j (dot triv s) (dot triv u) (cons (hyp_tm (eqtype a a)) G1)) as Hsl.
  {
  intros j u Hj Hu.
  apply pwctx_cons_tm; auto.
    {
    eapply (seqctx_pwctx_left _ _ s'); auto.
    eapply pwctx_downward; eauto.
    }

    {
    simpsub.
    exploit (Hleft j false u) as Hh; auto using smaller_le.
    cbn in Hh.
    invertc Hh.
    intros A' Har' Hau.
    so (basic_fun _#7 (basic_downward _#7 Hj Har) Har'); subst A'; clear Har'.
    apply (seqhyp_tm _#5 (iueqtype stop j (iutruncate (S j) A) (iutruncate (S j) A))).
      {
      apply interp_eval_refl.
      apply interp_eqtype; eauto using basic_downward.
      }

      {
      apply interp_eval_refl.
      apply interp_eqtype; eauto using basic_downward.
      }

      {
      cbn.
      do2 4 split; auto using star_refl; try prove_hygiene.
      reflexivity.
      }
    }

    {
    intros k v Hk Hsv.
    assert (k <= i) as Hki by omega.
    exploit (Hleft k false u) as H; eauto using smaller_le.
      {
      cbn.
      eapply (seqctx_downward j); eauto.
      }
    cbn in H.
    invertc H.
    intros A' Har' Hau.
    so (basic_fun _#7 (basic_downward _#7 Hki Har) Har'); subst A'; clear Har'.
    exploit (Hleft k false v) as H; eauto using smaller_le.
      {
      cbn.
      apply pwctx_impl_seqctx; eauto.
      }
    cbn in H.
    invertc H.
    intros A' Har' Hav.
    so (basic_fun _#7 (basic_downward _#7 Hki Har) Har'); subst A'; clear Har'.
    apply (relhyp_tm _#4 (iueqtype stop k (iutruncate (S k) A) (iutruncate (S k) A))).
      {
      simpsub.
      apply interp_eval_refl.
      apply interp_eqtype; auto.
      }

      {
      simpsub.
      apply interp_eval_refl.
      apply interp_eqtype; auto.
      }
    }

    {
    intros k v Hk Hvu.
    assert (k <= i) as Hki by omega.
    exploit (Hright k false v) as H; eauto using smaller_le.
      {
      cbn.
      exact (seqctx_zigzag _#6 (pwctx_impl_seqctx _#4 Hvu) (seqctx_downward _#5 Hk Hu) (seqctx_downward _#5 Hki (pwctx_impl_seqctx _#4 Hs))).
      }
    cbn in H.
    invertc H.
    intros A' Hal' Hau.
    so (basic_fun _#7 (basic_downward _#7 Hki Hal) Hal'); subst A'.
    apply (relhyp_tm _#4 (iueqtype stop k (iutruncate (S k) A) (iutruncate (S k) A))).
      {
      simpsub.
      apply interp_eval_refl.
      apply interp_eqtype; auto.
      }

      {
      simpsub.
      apply interp_eval_refl.
      apply interp_eqtype; auto.
      }
    }
  }
assert (forall j u,
          j <= i
          -> seqctx j u s' G1
          -> pwctx j (dot triv u) (dot triv s') (cons (hyp_tm (eqtype a a)) G1)) as Hsr.
  {
  intros j u Hj Hu.
  apply pwctx_cons_tm; auto.
    {
    eapply (seqctx_pwctx_right _ _ s'); auto.
    eapply pwctx_downward; eauto.
    }

    {
    simpsub.
    exploit (Hright j false u) as Hh; auto using smaller_le.
    cbn in Hh.
    invertc Hh.
    intros A' Hal' Hau.
    so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst A'; clear Hal'.
    apply (seqhyp_tm _#5 (iueqtype stop j (iutruncate (S j) A) (iutruncate (S j) A))).
      {
      apply interp_eval_refl.
      apply interp_eqtype; eauto using basic_downward.
      }

      {
      apply interp_eval_refl.
      apply interp_eqtype; eauto using basic_downward.
      }

      {
      cbn.
      do2 4 split; auto using star_refl; try prove_hygiene.
      reflexivity.
      }
    }

    {
    intros k v Hk Huv.
    assert (k <= i) as Hki by omega.
    exploit (Hleft k false v) as H; eauto using smaller_le.
      {
      cbn.
      exact (seqctx_zigzag _#6 (seqctx_downward _#5 Hki (pwctx_impl_seqctx _#4 Hs)) (seqctx_downward _#5 Hk Hu) (pwctx_impl_seqctx _#4 Huv)).
      }
    cbn in H.
    invertc H.
    intros A' Har' Hau.
    so (basic_fun _#7 (basic_downward _#7 Hki Har) Har'); subst A'.
    apply (relhyp_tm _#4 (iueqtype stop k (iutruncate (S k) A) (iutruncate (S k) A))).
      {
      simpsub.
      apply interp_eval_refl.
      apply interp_eqtype; auto.
      }

      {
      simpsub.
      apply interp_eval_refl.
      apply interp_eqtype; auto.
      }
    }

    {
    intros k v Hk Hsv.
    assert (k <= i) as Hki by omega.
    exploit (Hright k false u) as H; eauto using smaller_le.
      {
      cbn.
      eapply (seqctx_downward j); eauto.
      }
    cbn in H.
    invertc H.
    intros A' Hal' Hau.
    so (basic_fun _#7 (basic_downward _#7 Hki Hal) Hal'); subst A'; clear Hal'.
    exploit (Hright k false v) as H; eauto using smaller_le.
      {
      cbn.
      apply pwctx_impl_seqctx; eauto.
      }
    cbn in H.
    invertc H.
    intros A' Hal' Hav.
    so (basic_fun _#7 (basic_downward _#7 Hki Hal) Hal'); subst A'; clear Hal'.
    apply (relhyp_tm _#4 (iueqtype stop k (iutruncate (S k) A) (iutruncate (S k) A))).
      {
      simpsub.
      apply interp_eval_refl.
      apply interp_eqtype; auto.
      }

      {
      simpsub.
      apply interp_eval_refl.
      apply interp_eqtype; auto.
      }
    }
  }
so (Hsl i s' (le_refl _) (pwctx_impl_seqctx _#4 Hs)) as Hs'.
so (Hexteq _#3 Hs') as (A' & B & Hal' & _ & Hbl & Hbr & Heq).
simpsubin Hal'.
simpsubin Hbl.
simpsubin Hbr.
so (basic_fun _#7 Hal Hal'); subst A'.
clear Hal'.
do2 4 split.
  {
  simpsub.
  apply pwctx_cons_tm; eauto.
    {
    eapply seqhyp_tm; eauto.
    rewrite <- Heq; auto.
    }

    {
    intros j u Hj Hsu.
    exploit (Hleft j false u) as H.
      {
      apply smaller_le; auto.
      }

      {
      cbn.
      apply pwctx_impl_seqctx; auto.
      }

      {
      cbn in H.
      invertc H.
      intros A' Har' Hau.
      so (basic_fun _#7 (basic_downward _#7 Hj Har) Har'); subst A'.
      apply (relhyp_tm _#4 (iutruncate (S j) B)); auto.
        {
        eapply basic_downward; eauto.
        }

        {
        so (Hexteq _#3 (Hsl _ _ Hj (pwctx_impl_seqctx _#4 Hsu))) as (_ & B' & _ & _ & Hbl' & Hbu & _).
        simpsubin Hbl'.
        simpsubin Hbu.
        so (basic_fun _#7 (basic_downward _#7 Hj Hbl) Hbl'); subst B'; clear Hbl'.
        auto.
        }
      }
    }

    {
    intros j u Hj Hus.
    exploit (Hright j false u) as H.
      {
      apply smaller_le; auto.
      }

      {
      cbn.
      apply pwctx_impl_seqctx; auto.
      }

      {
      cbn in H.
      invertc H.
      intros A' Hal' Hau.
      so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst A'.
      apply (relhyp_tm _#4 (iutruncate (S j) B)); auto.
        {
        eapply basic_downward; eauto.
        }

        {
        so (Hexteq _#3 (Hsr _ _ Hj (pwctx_impl_seqctx _#4 Hus))) as (_ & B' & _ & _ & Hbu & Hbr' & _).
        simpsubin Hbr'.
        simpsubin Hbu.
        so (basic_fun _#7 (basic_downward _#7 Hj Hbr) Hbr'); subst B'; clear Hbr'.
        auto.
        }
      }
    }
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
  intros B' Hbl' Hbu Hmp.
  so (basic_fun _#7 (basic_downward _#7 Hj Hbl) Hbl'); subst B'.
  apply (seqhyp_tm _#5 (iutruncate (S j) A)).
    {
    eapply basic_downward; eauto.
    }

    {
    so (seqctx_pwctx_demote_left _#7 Hsmall Hs Hu) as Hu'.
    so (Hexteq _#3 (Hsl j u Hj (pwctx_impl_seqctx _#4 Hu'))) as (A' & _ & Hal' & Hau & _).
    simpsubin Hal'.
    simpsubin Hau.
    so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst A'.
    exact Hau.
    }

    {
    rewrite -> den_iutruncate in Hmp |- *.
    destruct Hmp as (_ & Hmp).
    split; auto.
    rewrite -> Heq; auto.
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
  intros B' Hbu Hbr' Hmp.
  so (basic_fun _#7 (basic_downward _#7 Hj Hbr) Hbr'); subst B'.
  apply (seqhyp_tm _#5 (iutruncate (S j) A)).
    {
    so (seqctx_pwctx_demote_right _#7 Hsmall Hs Hu) as Hu'.
    so (Hexteq _#3 (Hsr j u Hj (pwctx_impl_seqctx _#4 Hu'))) as (A' & _ & Hau & Har' & _).
    simpsubin Har'.
    simpsubin Hau.
    so (basic_fun _#7 (basic_downward _#7 Hj Har) Har'); subst A'.
    exact Hau.
    }

    {
    eapply basic_downward; eauto.
    }


    {
    rewrite -> den_iutruncate in Hmp |- *.
    destruct Hmp as (_ & Hmp).
    split; auto.
    rewrite -> Heq; auto.
    }
  }
Qed.


Lemma sound_subtype_formation_invert1 :
  forall G a a' b b',
    pseq G (deqtype (subtype a b) (subtype a' b'))
    -> pseq G (deqtype a a').
Proof.
intros G a a' b b'.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hl & Hr & Hl' & Hr').
simpsubin Hl.
simpsubin Hl'.
simpsubin Hr.
simpsubin Hr'.
invert (basic_value_inv _#6 value_subtype Hl).
intros A B Hal Hbl Heql.
invert (basic_value_inv _#6 value_subtype Hr).
intros A' B' Har Hbr Heqr.
so (iusubtype_inj _#6 (eqtrans Heql (eqsymm Heqr))) as (<- & <-).
invert (basic_value_inv _#6 value_subtype Hl').
intros A' B' Hal' Hbl' Heql'.
so (iusubtype_inj _#6 (eqtrans Heql (eqsymm Heql'))) as (<- & <-).
invert (basic_value_inv _#6 value_subtype Hr').
intros A' B' Har' Hbr' Heqr'.
so (iusubtype_inj _#6 (eqtrans Heql (eqsymm Heqr'))) as (<- & <-).
exists A.
auto.
Qed.


Lemma sound_subtype_formation_invert2 :
  forall G a a' b b',
    pseq G (deqtype (subtype a b) (subtype a' b'))
    -> pseq G (deqtype b b').
Proof.
intros G a a' b b'.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hl & Hr & Hl' & Hr').
simpsubin Hl.
simpsubin Hl'.
simpsubin Hr.
simpsubin Hr'.
invert (basic_value_inv _#6 value_subtype Hl).
intros A B Hal Hbl Heql.
invert (basic_value_inv _#6 value_subtype Hr).
intros A' B' Har Hbr Heqr.
so (iusubtype_inj _#6 (eqtrans Heql (eqsymm Heqr))) as (<- & <-).
invert (basic_value_inv _#6 value_subtype Hl').
intros A' B' Hal' Hbl' Heql'.
so (iusubtype_inj _#6 (eqtrans Heql (eqsymm Heql'))) as (<- & <-).
invert (basic_value_inv _#6 value_subtype Hr').
intros A' B' Har' Hbr' Heqr'.
so (iusubtype_inj _#6 (eqtrans Heql (eqsymm Heqr'))) as (<- & <-).
exists B.
auto.
Qed.
