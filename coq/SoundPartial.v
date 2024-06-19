
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

Require Import Defined.
Require Import PageCode.
Require Import ProperLevel.
Require Import Approximation.
Require Import Compactness.
Require Import SemanticsProperty.
Require Import SemanticsPartial.
Require Import SemanticsPi.
Require Import Ceiling.
Require Import SoundSimple.
Require Import Equivalence.
Require Import Truncate.
Require Import ProperDownward.
Require Import SemanticsSimple.
Require Import MapTerm.
Require Import SoundPartialUtil.
Require Import Subsumption.

Local Ltac prove_hygiene :=
  repeat (apply hygiene_auto; cbn; repeat2 split; auto);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1, subst_closub;
  try (eapply subst_closub_under_permit; eauto; done);
  try (apply hygiene_var; cbn; auto; done).


Lemma sound_partial_formation :
  forall G a a',
    pseq G (deqtype a a')
    -> pseq G (deqtype (partial a) (partial a')).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseqab.
rewrite -> seq_eqtype in Hseqab |- *.
intros i s s' Hs.
so (Hseqab i s s' Hs) as (A & Hal & Har & Hbl & Hbr).
exists (iupartial stop i A).
simpsub.
do2 3 split; apply interp_eval_refl; apply interp_partial; auto.
Qed.


Lemma sound_partial_formation_univ :
  forall G lv a a',
    pseq G (deq a a' (univ lv))
    -> pseq G (deq (partial a) (partial a') (univ lv)).
Proof.
intros G lv a b.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseqab.
rewrite -> seq_univ in Hseqab |- *.
intros i s s' Hs.
so (Hseqab i s s' Hs) as (pg & A & Hlvl & Hlvr & Hal & Har & Hbl & Hbr).
exists pg, (iupartial stop i A).
simpsub.
do2 5 split; auto; apply interp_eval_refl; apply interp_partial; auto.
Qed.


Lemma sound_halts_formation :
  forall G a m m',
    pseq G (deq m m' (partial a))
    -> pseq G (deqtype (halts m) (halts m')).
Proof.
intros G a m n.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseqmp.
rewrite -> seq_eqtype.
rewrite -> seq_deq in Hseqmp.
intros i s s' Hs.
so (Hseqmp i s s' Hs) as (R & Hl & _ & Hm & Hn & Hmn).
simpsubin Hl.
invert (basic_value_inv _#6 value_partial Hl).
intros A Hal <-.
rewrite -> den_iupartial in Hm, Hn, Hmn.
cbn in Hm, Hn, Hmn.
so Hm as (_ & Hclsm & Hclsm' & Hhaltm & _).
so Hn as (_ & Hclsn & Hclsn' & Hhaltn & _).
so Hmn as (_ & _ & _ & Hhaltmn & _).
exists (iubase (halts_urel stop i (subst s m))).
simpsub.
do2 3 split.
  {
  apply interp_eval_refl.
  eapply interp_halts; eauto.
  }

  {
  replace (halts_urel stop i (subst s m)) with (halts_urel stop i (subst s' m)).
    {
    apply interp_eval_refl; eapply interp_halts; eauto.
    }
  apply property_urel_extensionality; auto.
  intros j Hj.
  tauto.
  }

  {
  replace (halts_urel stop i (subst s m)) with (halts_urel stop i (subst s n)).
    {
    apply interp_eval_refl; eapply interp_halts; eauto.
    }
  apply property_urel_extensionality; auto.
  intros j Hj.
  tauto.
  }

  {
  replace (halts_urel stop i (subst s m)) with (halts_urel stop i (subst s' n)).
    {
    apply interp_eval_refl; eapply interp_halts; eauto.
    }
  apply property_urel_extensionality; auto.
  intros j Hj.
  tauto.
  }
Qed.


Lemma sound_halts_formation_univ :
  forall G a m m',
    pseq G (deq m m' (partial a))
    -> pseq G (deq (halts m) (halts m') (univ nzero)).
Proof.
intros G a m n.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseqmp.
rewrite -> seq_univ.
rewrite -> seq_deq in Hseqmp.
intros i s s' Hs.
so (Hseqmp i s s' Hs) as (R & Hl & _ & Hm & Hn & Hmn).
simpsubin Hl.
invert (basic_value_inv _#6 value_partial Hl).
intros A Hal <-.
rewrite -> den_iupartial in Hm, Hn, Hmn.
cbn in Hm, Hn, Hmn.
so Hm as (_ & Hclsm & Hclsm' & Hhaltm & _).
so Hn as (_ & Hclsn & Hclsn' & Hhaltn & _).
so Hmn as (_ & _ & _ & Hhaltmn & _).
exists zeropg, (iubase (halts_urel stop i (subst s m))).
simpsub.
do2 5 split; auto using pginterp_nzero.
  {
  apply interp_eval_refl.
  eapply interp_halts; eauto.
  }

  {
  replace (halts_urel stop i (subst s m)) with (halts_urel stop i (subst s' m)).
    {
    apply interp_eval_refl; eapply interp_halts; eauto.
    }
  apply property_urel_extensionality; auto.
  intros j Hj.
  tauto.
  }

  {
  replace (halts_urel stop i (subst s m)) with (halts_urel stop i (subst s n)).
    {
    apply interp_eval_refl; eapply interp_halts; eauto.
    }
  apply property_urel_extensionality; auto.
  intros j Hj.
  tauto.
  }

  {
  replace (halts_urel stop i (subst s m)) with (halts_urel stop i (subst s' n)).
    {
    apply interp_eval_refl; eapply interp_halts; eauto.
    }
  apply property_urel_extensionality; auto.
  intros j Hj.
  tauto.
  }
Qed.


Lemma sound_bottom_partial_void :
  forall G,
    pseq G (deq bottom bottom (partial voidtp)).
Proof.
refine (seq_pseq 0 0 _ _); cbn.
intros G.
rewrite -> seq_deq.
intros i s s' Hs.
assert (rel (den (iupartial stop i (iubase (void_urel stop)))) i bottom bottom) as Hbot.
  {
  do2 4 split; auto; try prove_hygiene.
    {
    split; auto.
    }
    
    {
    intro Hconv.
    exfalso.
    destruct Hconv as (v & Heval).
    eapply bottom_diverge; eauto.
    }
  }
exists (iupartial stop i (iubase (void_urel stop))).
simpsub.
do2 4 split; auto.
  {
  apply interp_eval_refl; apply interp_partial.
  apply interp_eval_refl; apply interp_void.
  }

  {
  apply interp_eval_refl; apply interp_partial.
  apply interp_eval_refl; apply interp_void.
  }
Qed.


Lemma sound_partial_elim :
  forall G a m m',
    pseq G (deq m m' (partial a))
    -> pseq G (deq triv triv (halts m))
    -> pseq G (deq m m' a).
Proof.
intros G a m n.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqmn Hseqhalt.
rewrite -> seq_deq in Hseqmn |- *.
rewrite -> seq_halts in Hseqhalt.
intros i s s' Hs.
so (Hseqmn i s s' Hs) as (R & Hl & Hr & Hm & Hn & Hmn).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_partial Hl).
intros A Hal Heql.
invert (basic_value_inv _#6 value_partial Hr).
intros A' Har Heqr.
so (iupartial_inj _#4 (eqtrans Heql (eqsymm Heqr))).
subst A'.
clear Heqr.
subst R.
clear Hl Hr.
so (Hseqhalt _#3 Hs) as (_ & _ & Hconv & _).
exists A.
do2 4 split; auto.
  {
  destruct Hm as (_ & _ & _ & _ & Hact).
  apply Hact; auto.
  }

  {
  destruct Hn as (_ & _ & _ & Hiffn & Hact).
  destruct Hmn as (_ & _ & _ & Hiffmn & _).
  apply Hact.
  tauto.
  }

  {
  destruct Hmn as (_ & _ & _ & _ & Hact).
  apply Hact; auto.
  }
Qed.


Lemma sound_partial_ext :
  forall G a m n,
    pseq G (deqtype a a)
    -> pseq G (deqtype (halts m) (halts m))
    -> pseq G (deqtype (halts n) (halts n))
    -> pseq (hyp_tm (halts m) :: G) (deq triv triv (halts (subst sh1 n)))
    -> pseq (hyp_tm (halts n) :: G) (deq triv triv (halts (subst sh1 m)))
    -> pseq (hyp_tm (halts m) :: G) (deq (subst sh1 m) (subst sh1 n) (subst sh1 a))
    -> pseq G (deq m n (partial a)).
Proof.
intros G a m n.
revert G.
refine (seq_pseq 2 [] m [] n 6 [] _ [] _ [] _ [_] _ [_] _ [_] _ _ _); cbn.
intros G Hclm Hcln Hseqa Hseqm Hseqn Hseqmn Hseqnm Hseq.
rewrite -> seq_eqtype in Hseqa, Hseqm, Hseqn.
rewrite -> seq_deq in Hseq |- *.
rewrite -> seq_halts in Hseqmn, Hseqnm.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
so (Hseqm _#3 Hs) as (R & Hl & Hr & Hm & _).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_halts Hl).
intros _ Heql.
invert (basic_value_inv _#6 value_halts Hr).
intros _ Heqr.
so (property_urel_eq_invert _#6 (f_equal den (eqtrans Heql (eqsymm Heqr)))) as H.
so (H _ (le_refl _)) as Hiffm.
clear R Hl Hr Hm Heql Heqr H.
so (Hseqn _#3 Hs) as (R & Hl & Hr & Hm & _).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_halts Hl).
intros _ Heql.
invert (basic_value_inv _#6 value_halts Hr).
intros _ Heqr.
so (property_urel_eq_invert _#6 (f_equal den (eqtrans Heql (eqsymm Heqr)))) as H.
so (H _ (le_refl _)) as Hiffn.
clear R Hl Hr Hm Heql Heqr H.
assert (converges (subst s m) -> pwctx i (dot triv s) (dot triv s') (hyp_tm (halts m) :: G)) as Hssm.
  {
  intros Hconvm.
  apply pwctx_cons_tm_seq; auto.
    {
    simpsub.
    apply (seqhyp_tm _#5 (iubase (halts_urel stop i (subst s m)))).
      {
      apply interp_eval_refl; apply interp_halts.
      prove_hygiene.
      }

      {
      replace (halts_urel stop i (subst s m)) with (halts_urel stop i (subst s' m)).
        {
        apply interp_eval_refl; apply interp_halts.
        prove_hygiene.
        }
      apply property_urel_extensionality; auto.
      intros j Hj.
      split; auto.
      apply Hiffm.
      }

      {
      cbn.
      apply property_action_triv; auto.
      }
    }

    {
    intros j t t' Ht.
    so (Hseqm _#3 Ht) as (R & Hl & Hr & _).
    exists toppg, R.
    auto.
    }
  }
assert (converges (subst s n) -> pwctx i (dot triv s) (dot triv s') (hyp_tm (halts n) :: G)) as Hssn.
  {
  intros Hconvn.
  apply pwctx_cons_tm_seq; auto.
    {
    simpsub.
    apply (seqhyp_tm _#5 (iubase (halts_urel stop i (subst s n)))).
      {
      apply interp_eval_refl; apply interp_halts.
      prove_hygiene.
      }

      {
      replace (halts_urel stop i (subst s n)) with (halts_urel stop i (subst s' n)).
        {
        apply interp_eval_refl; apply interp_halts.
        prove_hygiene.
        }
      apply property_urel_extensionality; auto.
      intros j Hj.
      split; auto.
      apply Hiffn.
      }

      {
      cbn.
      apply property_action_triv; auto.
      }
    }

    {
    intros j t t' Ht.
    so (Hseqn _#3 Ht) as (R & Hl & Hr & _).
    exists toppg, R.
    auto.
    }
  }
assert (converges (subst s m) <-> converges (subst s' n)) as Hiffmn.
  {
  split.
    {
    intro Hconvm.
    so (Hseqmn _#3 (Hssm Hconvm)) as (_ & _ & _ & Hconvn').
    simpsubin Hconvn'.
    exact Hconvn'.
    }

    {
    intros Hconvn'.
    so (Hseqnm _#3 (Hssn (Hiffn ander Hconvn'))) as (_ & _ & Hconvm & _).
    simpsubin Hconvm.
    exact Hconvm.
    }
  }
exists (iupartial stop i A).
simpsub.
do2 4 split.
  {
  apply interp_eval_refl; apply interp_partial; auto.
  }

  {
  apply interp_eval_refl; apply interp_partial; auto.
  }

  {
  do2 4 split; auto; try prove_hygiene.
  intro Hconv.
  so (Hseq _#3 (Hssm Hconv)) as (A' & Hal' & _ & Hm & _).
  simpsubin Hal'.
  simpsubin Hm.
  so (basic_fun _#7 Hal Hal').
  subst A'.
  exact Hm.
  }

  {
  do2 4 split; auto; try prove_hygiene.
  intro Hconvn.
  so (Hiffn andel Hconvn) as Hconvn'.
  so (Hiffmn ander Hconvn') as Hconvm.
  so (Hseq _#3 (Hssm Hconvm)) as (A' & Hal' & _ & _ & Hn & _).
  simpsubin Hal'.
  simpsubin Hn.
  so (basic_fun _#7 Hal Hal').
  subst A'.
  exact Hn.
  }

  {
  do2 4 split; auto; try prove_hygiene.
  intro Hconv.
  so (Hseq _#3 (Hssm Hconv)) as (A' & Hal' & _ & _ & _ & Hmn).
  simpsubin Hal'.
  simpsubin Hmn.
  so (basic_fun _#7 Hal Hal').
  subst A'.
  exact Hmn.
  }
Qed.


Lemma sound_halts_eta :
  forall G m p,
    pseq G (deq p p (halts m))
    -> pseq G (deq p triv (halts m)).
Proof.
intros G a p.
revert G.
refine (seq_pseq 1 [] p 1 [] _ _ _); cbn.
intros G Hclp Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq _#3 Hs) as (R & Hrobl & Hrobr & Htrue & _).
exists R.
do2 2 split; auto.
simpsubin Hrobl; clear Hrobr.
invert (basic_value_inv _#6 value_halts Hrobl).
intros _ <-.
destruct Htrue as (Hhalts & _ & Hclsp & Hclsp' & Hp & Hp').
do2 2 split.
  {
  do2 5 split; auto.
  }

  {
  do2 5 split; auto using star_refl; simpsub; apply hygiene_auto; cbn; auto.
  }

  {
  do2 5 split; auto using star_refl; simpsub; apply hygiene_auto; cbn; auto.
  }
Qed.


Lemma sound_halts_eta_hyp :
  forall G1 G2 p m n b,
    pseq (substctx (dot triv id) G2 ++ G1) (deq m n (subst (under (length G2) (dot triv id)) b))
    -> pseq (G2 ++ hyp_tm (halts p) :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) b).
Proof.
intros G1 G2 p m n b Hseq.
eapply sound_property_eta_hyp; eauto.
intros s pg z i R H.
simpsubin H.
invert (basic_value_inv _#6 value_halts H).
intros _ <-.
do 3 eexists.
reflexivity.
Qed.



Lemma sound_admiss_formation :
  forall G a a',
    pseq G (deqtype a a')
    -> pseq G (deqtype (admiss a) (admiss a')).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseqab.
rewrite -> seq_eqtype in Hseqab |- *.
intros i s s' Hs.
so (Hseqab i s s' Hs) as (A & Hal & Har & Hbl & Hbr).
exists (iuadmiss stop i A).
simpsub.
do2 3 split; apply interp_eval_refl; apply interp_admiss; auto.
Qed.


Lemma sound_admiss_formation_univ :
  forall G lv a a',
    pseq G (deq a a' (univ lv))
    -> pseq G (deq (admiss a) (admiss a') (univ lv)).
Proof.
intros G lv a b.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseqab.
rewrite -> seq_univ in Hseqab |- *.
intros i s s' Hs.
so (Hseqab i s s' Hs) as (pg & A & Hlvl & Hlvr & Hal & Har & Hbl & Hbr).
exists pg, (iuadmiss stop i A).
simpsub.
do2 5 split; auto; apply interp_eval_refl; apply interp_admiss; auto.
Qed.


Lemma sound_admiss_eta :
  forall G a p,
    pseq G (deq p p (admiss a))
    -> pseq G (deq p triv (admiss a)).
Proof.
intros G a p.
revert G.
refine (seq_pseq 1 [] p 1 [] _ _ _); cbn.
intros G Hclp Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq _#3 Hs) as (R & Hrobl & Hrobr & Htrue & _).
exists R.
do2 2 split; auto.
simpsubin Hrobl; clear Hrobr.
invert (basic_value_inv _#6 value_admiss Hrobl).
intros A _ <-.
destruct Htrue as (Hadmiss & _ & Hclsp & Hclsp' & Hp & Hp').
do2 2 split.
  {
  do2 5 split; auto.
  }

  {
  do2 5 split; auto using star_refl; simpsub; apply hygiene_auto; cbn; auto.
  }

  {
  do2 5 split; auto using star_refl; simpsub; apply hygiene_auto; cbn; auto.
  }
Qed.


Lemma sound_admiss_eta_hyp :
  forall G1 G2 a m n b,
    pseq (substctx (dot triv id) G2 ++ G1) (deq m n (subst (under (length G2) (dot triv id)) b))
    -> pseq (G2 ++ hyp_tm (admiss a) :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) b).
Proof.
intros G1 G2 a m n b Hseq.
eapply sound_property_eta_hyp; eauto.
intros s pg z i R H.
simpsubin H.
invert (basic_value_inv _#6 value_admiss H).
intros A _ <-.
do 3 eexists.
reflexivity.
Qed.



Lemma sound_uptype_formation :
  forall G a a',
    pseq G (deqtype a a')
    -> pseq G (deqtype (uptype a) (uptype a')).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseqab.
rewrite -> seq_eqtype in Hseqab |- *.
intros i s s' Hs.
so (Hseqab i s s' Hs) as (A & Hal & Har & Hbl & Hbr).
exists (iuuptype stop i A).
simpsub.
do2 3 split; apply interp_eval_refl; apply interp_uptype; auto.
Qed.


Lemma sound_uptype_formation_univ :
  forall G lv a a',
    pseq G (deq a a' (univ lv))
    -> pseq G (deq (uptype a) (uptype a') (univ lv)).
Proof.
intros G lv a b.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseqab.
rewrite -> seq_univ in Hseqab |- *.
intros i s s' Hs.
so (Hseqab i s s' Hs) as (pg & A & Hlvl & Hlvr & Hal & Har & Hbl & Hbr).
exists pg, (iuuptype stop i A).
simpsub.
do2 5 split; auto; apply interp_eval_refl; apply interp_uptype; auto.
Qed.


Lemma sound_uptype_eta :
  forall G a p,
    pseq G (deq p p (uptype a))
    -> pseq G (deq p triv (uptype a)).
Proof.
intros G a p.
revert G.
refine (seq_pseq 1 [] p 1 [] _ _ _); cbn.
intros G Hclp Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq _#3 Hs) as (R & Hrobl & Hrobr & Htrue & _).
exists R.
do2 2 split; auto.
simpsubin Hrobl; clear Hrobr.
invert (basic_value_inv _#6 value_uptype Hrobl).
intros A _ <-.
destruct Htrue as (Huptype & _ & Hclsp & Hclsp' & Hp & Hp').
do2 2 split.
  {
  do2 5 split; auto.
  }

  {
  do2 5 split; auto using star_refl; simpsub; apply hygiene_auto; cbn; auto.
  }

  {
  do2 5 split; auto using star_refl; simpsub; apply hygiene_auto; cbn; auto.
  }
Qed.


Lemma sound_uptype_eta_hyp :
  forall G1 G2 a m n b,
    pseq (substctx (dot triv id) G2 ++ G1) (deq m n (subst (under (length G2) (dot triv id)) b))
    -> pseq (G2 ++ hyp_tm (uptype a) :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) b).
Proof.
intros G1 G2 a m n b Hseq.
eapply sound_property_eta_hyp; eauto.
intros s pg z i R H.
simpsubin H.
invert (basic_value_inv _#6 value_uptype H).
intros A _ <-.
do 3 eexists.
reflexivity.
Qed.


Lemma sound_fixpoint_induction :
  forall G a m m',
    pseq G (deq triv triv (admiss a))
    -> pseq G (deq m m' (tarrow (partial a) (partial a)))
    -> pseq G (deq (app theta m) (app theta m') (partial a)).
Proof.
intros G a m n.
simpsub.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqadmiss Hseqmn.
rewrite -> seq_deq in Hseqmn |- *.
rewrite -> seq_admiss in Hseqadmiss.
intros i s s' Hs.
so (Hseqmn _#3 Hs) as (R & Harrl & Harrr & Hm & Hn & Hmn).
simpsubin Harrl.
simpsubin Harrr.
invert (basic_value_inv _#6 value_tarrow Harrl).
intros Q B Hql Hbl Heql.
invert (basic_value_inv _#6 value_tarrow Harrr).
intros Q' B' Hqr Hbr Heqr.
so (basic_fun _#7 Hql Hbl); subst B.
so (basic_fun _#7 Hqr Hbr); subst B'.
so (iuarrow_inj _#7 (eqtrans Heql (eqsymm Heqr))) as (<- & _).
clear Heqr.
subst R.
invert (basic_value_inv _#6 value_partial Hql).
intros A Hal Heql.
invert (basic_value_inv _#6 value_partial Hqr).
intros A' Har Heqr.
so (iupartial_inj _#4 (eqtrans Heql (eqsymm Heqr))).
subst A'.
clear Heqr.
subst Q.
clear Hbl Hbr Harrl Harrr.
so (Hseqadmiss _#3 Hs) as (A' & Hal' & _ & Hadmiss).
simpsubin Hal'.
so (basic_fun _#7 Hal Hal').
subst A'.
unfold admiss_property in Hadmiss.
exists (iupartial stop i A).
clear Hal'.
simpsub.
cut (forall p q,
       rel (den (iuarrow stop i (iupartial stop i A) (iupartial stop i A))) i p q
       -> rel (den (iupartial stop i A)) i (app theta p) (app theta q)).
  {
  intro Hfix.
  do2 4 split; auto.
  }
clear m n Hseqmn Hseqadmiss Hm Hn Hmn Hql Hqr Hal Har.
intros m n Hmn.
rewrite -> den_iupartial.
so (urel_closed _#5 Hmn) as (Hclm & Hcln).
assert (forall j, rel (partial_urel stop i (den A)) i (afix j m) (afix j n)) as Hallmn.
  {
  intro j.
  induct j.
    (* 0 *)
    {
    cbn.
    do2 4 split; auto using bottom_closed.
      {
      reflexivity.
      }

      {
      intros H.
      destruct H as (v & H).
      destruct (bottom_diverge _ v H).
      }
    }

    (* S *)
    {
    intros j IH.
    cbn [afix].
    cbn in Hmn.
    eapply arrow_action_app; eauto.
    }
  }
do2 4 split; auto; try prove_hygiene.
  {
  split.
    {
    intro Hconvm.
    exploit (compactness _ m (var 0)) as (j & Hconvmj); auto; try prove_hygiene.
      {
      simpsub.
      auto.
      }
    simpsubin Hconvmj.
    apply (approx_converges _ (afix j n)).
      {
      apply afix_fix_approx; auto.
      }
    so (Hallmn j) as (_ & _ & _ & H & _).
    tauto.
    }

    {
    intro Hconvn.
    exploit (compactness _ n (var 0)) as (j & Hconvnj); auto; try prove_hygiene.
      {
      simpsub.
      auto.
      }
    simpsubin Hconvnj.
    apply (approx_converges _ (afix j m)).
      {
      apply afix_fix_approx; auto.
      }
    so (Hallmn j) as (_ & _ & _ & H & _).
    tauto.
    }
  }
intros Hconvm.
exploit (compactness _ m (var 0)) as (j & Hconvmj); auto; try prove_hygiene.
  {
  simpsub.
  auto.
  }
simpsubin Hconvmj.
exploit (Hadmiss m n i (var 0) (var 0) j) as H; auto; try prove_hygiene.
2:{
  simpsubin H.
  destruct H as (_ & H).
  exact H.
  }
intros k Hk.
split; auto.
simpsub.
so (Hallmn k) as H.
cbn in H.
decompose H.
intros _ _ _ _ H.
apply H; clear H.
apply (approx_converges _ (afix j m)); auto.
apply afix_approx; auto.
Qed.


Lemma sound_partial_covariant :
  forall G a b,
    pseq G (dsubtype a b)
    -> pseq G (dsubtype (partial a) (partial b)).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_subtype in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (A & B & Hal & Har & Hbl & Hbr & Hsubtype).
exists (iupartial stop i A), (iupartial stop i B).
simpsub.
do2 4 split; try (apply interp_eval_refl; apply interp_partial; auto; done).
intros j m p Hj Hmp.
destruct Hmp as (_ & Hclm & Hclp & Hiff & Hact).
do2 4 split; auto.
Qed.


Lemma sound_total_strict :
  forall G a,
    pseq G (deqtype a a)
    -> pseq (cons (hyp_tm a) G) (deq triv triv (halts (var 0)))
    -> pseq G (dsubtype a (partial a)).
Proof.
intros G a.
revert G.
refine (seq_pseq 0 2 [] _ [_] _ _ _); cbn.
intros G Hseqa Hseqhalt.
rewrite -> seq_eqtype in Hseqa.
rewrite -> seq_halts in Hseqhalt.
rewrite -> seq_subtype.
intros i s s' Hs.
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
exists A, (iupartial stop i A).
simpsub.
do2 4 split; auto; try (apply interp_eval_refl; apply interp_partial; auto; done).
intros j m p Hj Hmp.
assert (pwctx j (dot m s) (dot p s') (cons (hyp_tm a) G)) as Hss.
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
      rewrite -> den_iutruncate.
      split; auto.
      }
    }

    {
    intros k t t' Ht.
    so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
    exists toppg, R.
    auto.
    }
  }
so (Hseqhalt _#3 Hss) as (Hclm & Hclp & Hconvm & Hconvp).
simpsubin Hclm.
simpsubin Hclp.
simpsubin Hconvm.
simpsubin Hconvp.
do2 4 split; auto.
split; auto.
Qed.


Lemma sound_uptype_admiss :
  forall G a,
    pseq G (deq triv triv (uptype a))
    -> pseq G (deq triv triv (admiss a)).
Proof.
intros G a.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_uptype in Hseq.
rewrite -> seq_admiss.
intros i s s' Hs.
so (Hseq _#3 Hs) as (A & Hal & Har & Hupward).
exists A.
do2 2 split; auto.
apply upward_impl_admissible; auto.
Qed.


Lemma sound_unitary_uptype :
  forall G a,
    pseq G (dsubtype a unittp)
    -> pseq G (deq triv triv (uptype a)).
Proof.
intros G a.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_subtype in Hseq.
rewrite -> seq_uptype.
intros i s s' Hs.
so (Hseq _#3 Hs) as (A & R & Hal & Har & Hl & _ & Hincl).
simpsubin Hl.
invert (basic_value_inv _#6 value_unittp Hl).
intros <-.
exists A.
do2 2 split; auto.
intros j m m' p p' Happroxm Happroxp Hmp.
destruct Hmp as (Hj & Hmp).
split; auto.
assert (j <= i) as Hj' by omega.
so (Hincl _#3 Hj' Hmp) as H.
cbn in H.
decompose H.
intros _ _ _ _ Hstepsm Hstepsp.
so (sapprox_action _#4 Happroxm (conj Hstepsm value_triv)) as (v & (Hstepsm' & _) & Hmc).
invertc_mc Hmc.
fold (@triv (Candidate.obj stop)).
intros <-.
so (sapprox_action _#4 Happroxp (conj Hstepsp value_triv)) as (v & (Hstepsp' & _) & Hmc).
invertc_mc Hmc.
fold (@triv (Candidate.obj stop)).
intros <-.
so (sapprox_closed _#3 Happroxm ander) as Hclm'.
so (sapprox_closed _#3 Happroxp ander) as Hclp'.
eapply urel_equiv; eauto.
  {
  eapply equiv_trans; eauto using steps_equiv.
  apply equiv_symm; eauto using steps_equiv.
  }

  {
  eapply equiv_trans; eauto using steps_equiv.
  apply equiv_symm; eauto using steps_equiv.
  }
Qed.


Lemma sound_uptype_eeqtp :
  forall G a b,
    pseq G (dsubtype a b)
    -> pseq G (dsubtype b a)
    -> pseq G (deq triv triv (uptype a))
    -> pseq G (deq triv triv (uptype b)).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 3 [] _ [] _ [] _ _ _); cbn.
intros G Hseqab Hseqba Hsequp.
rewrite -> seq_subtype in Hseqab, Hseqba.
rewrite -> seq_uptype in Hsequp |- *.
intros i s s' Hs.
so (Hseqab _#3 Hs) as (A & B & Hal & Har & Hbl & Hbr & Hab).
so (Hseqba _#3 Hs) as (B' & A' & Hbl' & _ & Hal' & _ & Hba).
so (basic_fun _#7 Hal Hal'); subst A'.
so (basic_fun _#7 Hbl Hbl'); subst B'.
so (Hsequp _#3 Hs) as (A' & Hal'' & _ & Hupward).
so (basic_fun _#7 Hal Hal''); subst A'.
exists B.
do2 2 split; auto.
intros j m m' p p' Happroxm Happroxp Hmp.
destruct Hmp as (Hj & Hmp).
split; auto.
apply Hab; [omega |].
exploit (Hupward j m m' p p') as H; auto.
  {
  split; auto.
  apply Hba; [omega | auto].
  }
destruct H; auto.
Qed.


Lemma sound_admiss_eeqtp :
  forall G a b,
    pseq G (dsubtype a b)
    -> pseq G (dsubtype b a)
    -> pseq G (deq triv triv (admiss a))
    -> pseq G (deq triv triv (admiss b)).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 3 [] _ [] _ [] _ _ _); cbn.
intros G Hseqab Hseqba Hseqadmiss.
rewrite -> seq_subtype in Hseqab, Hseqba.
rewrite -> seq_admiss in Hseqadmiss |- *.
intros i s s' Hs.
so (Hseqab _#3 Hs) as (A & B & Hal & Har & Hbl & Hbr & Hab).
so (Hseqba _#3 Hs) as (B' & A' & Hbl' & _ & Hal' & _ & Hba).
so (basic_fun _#7 Hal Hal'); subst A'.
so (basic_fun _#7 Hbl Hbl'); subst B'.
so (Hseqadmiss _#3 Hs) as (A' & Hal'' & _ & Hadmiss).
so (basic_fun _#7 Hal Hal''); subst A'.
exists B.
do2 2 split; auto.
intros f g i' m p j Hclf Hclfg Hclm Hclp Hact.
so (Hact _ (le_refl _)) as (Hi' & _).
split; auto.
apply Hab; [omega |].
exploit (Hadmiss f g i' m p j) as H; auto.
  {
  intros k Hk.
  split; auto.
  apply Hba; [omega |].
  exact (Hact k Hk ander).
  }
destruct H; auto.
Qed.


Lemma sound_partial_strict :
  forall G a,
    pseq G (deqtype a a)
    -> pseq G (dsubtype (partial a) (partial (partial a))).
Proof.
intros G a.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq.
rewrite -> seq_subtype.
intros i s s' Hs.
so (Hseq _#3 Hs) as (A & Hal & Har & _).
exists (iupartial stop i A), (iupartial stop i (iupartial stop i A)).
simpsub.
do2 4 split.
  {
  apply interp_eval_refl; apply interp_partial; auto.
  }

  {
  apply interp_eval_refl; apply interp_partial; auto.
  }

  {
  apply interp_eval_refl; apply interp_partial.
  apply interp_eval_refl; apply interp_partial; auto.
  }

  {
  apply interp_eval_refl; apply interp_partial.
  apply interp_eval_refl; apply interp_partial; auto.
  }

  {
  intros j m p Hj Hmp.
  cbn in Hmp |- *.
  decompose Hmp.
  intros _ Hclm Hclp Hiff Hact.
  do2 4 split; auto.
  intro Hconvm.
  do2 4 split; auto.
  }
Qed.


Lemma sound_partial_admiss :
  forall G a,
    pseq G (deq triv triv (admiss a))
    -> pseq G (deq triv triv (admiss (partial a))).
Proof.
intros G a.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_admiss in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (A & Hal & Har & Hadmiss).
exists (iupartial stop i A).
do2 2 split.
  {
  apply interp_eval_refl; apply interp_partial; auto.
  }

  {
  apply interp_eval_refl; apply interp_partial; auto.
  }
intros f g i' m p j Hclf Hclg Hclm Hclp Hact.
so (Hact _ (le_refl _)) as (Hj & _).
split; auto.
do2 4 split.
  {
  omega.
  }

  {
  apply hygiene_subst1; prove_hygiene.
  }

  {
  apply hygiene_subst1; prove_hygiene.
  }

  {
  split.
    {
    intros Hconv.
    so (compactness _#3 Hclf Hclm Hconv) as (j' & Hconvj').
    set (k := max j j').
    exploit (approx_converges _ (subst1 (afix j' f) m) (subst1 (afix k f) m)) as Hconvk; auto.
      {
      apply approx_funct1; auto.
      apply afix_approx; auto.
      apply Nat.le_max_r.
      }
    so (Hact k (Nat.le_max_l _ _)) as (_ & _ & _ & _ & Hiff & _).
    so (Hiff andel Hconvk) as Hconvk'.
    eapply approx_converges; eauto.
    apply approx_funct1; auto.
    apply afix_fix_approx; auto.
    }

    {
    intros Hconv.
    so (compactness _#3 Hclg Hclp Hconv) as (j' & Hconvj').
    set (k := max j j').
    exploit (approx_converges _ (subst1 (afix j' g) p) (subst1 (afix k g) p)) as Hconvk; auto.
      {
      apply approx_funct1; auto.
      apply afix_approx; auto.
      apply Nat.le_max_r.
      }
    so (Hact k (Nat.le_max_l _ _)) as (_ & _ & _ & _ & Hiff & _).
    so (Hiff ander Hconvk) as Hconvk'.
    eapply approx_converges; eauto.
    apply approx_funct1; auto.
    apply afix_fix_approx; auto.
    }
  }

  {
  intro Hconv.
  so (compactness _#3 Hclf Hclm Hconv) as (j' & Hconvj').
  set (k := max j j').
  apply (Hadmiss _#5 k); auto.
  intros k' Hk'.
  split; auto.
  so (Hact k' (le_trans _#3 (Nat.le_max_l _ _) Hk')) as (_ & _ & _ & _ & _ & Hmp).
  apply Hmp.
  eapply approx_converges; eauto.
  apply approx_funct1; auto.
  apply afix_approx; auto.
  so (Nat.le_max_r j j').
  omega.
  }
Qed.


Lemma sound_partial_strict_converse :
  forall G a,
    pseq G (deqtype a a)
    -> pseq G (dsubtype (partial (partial a)) (partial a)).
Proof.
intros G a.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq.
rewrite -> seq_subtype.
intros i s s' Hs.
so (Hseq _#3 Hs) as (A & Hal & Har & _).
exists (iupartial stop i (iupartial stop i A)), (iupartial stop i A).
simpsub.
do2 4 split.
  {
  apply interp_eval_refl; apply interp_partial.
  apply interp_eval_refl; apply interp_partial; auto.
  }

  {
  apply interp_eval_refl; apply interp_partial.
  apply interp_eval_refl; apply interp_partial; auto.
  }

  {
  apply interp_eval_refl; apply interp_partial; auto.
  }

  {
  apply interp_eval_refl; apply interp_partial; auto.
  }

  {
  intros j m p Hj Hmp.
  cbn in Hmp |- *.
  decompose Hmp.
  intros _ Hclm Hclp Hiff Hact.
  do2 4 split; auto.
  intro Hconvm.
  so (Hact Hconvm) as H.
  cbn in H.
  decompose H.
  auto.
  }
Qed.


Lemma sound_seq_bind :
  forall G a b m m' n n',
    pseq G (deq m m' (partial a))
    -> pseq (cons (hyp_tm a) G) (deq n n' (subst sh1 (partial b)))
    -> pseq G (deqtype b b)
    -> pseq G (deq (Syntax.seq m n) (Syntax.seq m' n') (partial b)).
Proof.
intros G a b m p n q.
simpsub.
revert G.
refine (seq_pseq 4 [] m [] p [hyp_tm a] n [hyp_tm a] q 3 [] _ [_] _ [] _ _ _); cbn.
intros G Hclm Hclp Hcln Hclq Hseqmp Hseqnq Hseqb.
rewrite -> seq_deq in Hseqmp, Hseqnq |- *.
rewrite -> seq_eqtype in Hseqb.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmp _#3 Hs) as (R & Hpal & Hpar & Hm & Hp & Hmp).
simpsubin Hpal.
simpsubin Hpar.
invert (basic_value_inv _#6 value_partial Hpal).
intros A Hal Heql.
invert (basic_value_inv _#6 value_partial Hpar).
intros A' Har Heqr.
so (iupartial_inj _#4 (eqtrans Heql (eqsymm Heqr))).
subst A'.
clear Heqr.
subst R.
so (Hseqb _#3 Hs) as (B & Hbl & Hbr & _).
exists (iupartial stop i B).
simpsub.
assert (forall r t, rel (den A) i r t -> pwctx i (dot r s) (dot t s') (cons (hyp_tm a) G)) as Hss.
  {
  intros r t Hrt.
  apply pwctx_cons_tm_seq; auto.
    {
    apply (seqhyp_tm _#5 A); auto.
    }
    
    {
    intros j u u' Hu.
    so (Hseqmp _#3 Hu) as (R & Hl & Hr & _).
    simpsubin Hl.
    simpsubin Hr.
    invert (basic_value_inv _#6 value_partial Hl).
    intros Q Hql Heql.
    invert (basic_value_inv _#6 value_partial Hr).
    intros Q' Hqr Heqr.
    so (iupartial_inj _#4 (eqtrans Heql (eqsymm Heqr))).
    subst Q'.
    clear Heqr.
    subst R.
    exists toppg, Q.
    auto.
    }
  }
assert (forall m n p q,
          hygiene (permit clo) n
          -> hygiene (permit clo) q
          -> rel (den (iupartial stop i A)) i m p
          -> (converges m -> rel (den (iupartial stop i B)) i (subst1 m n) (subst1 p q))
          -> rel (den (iupartial stop i B)) i (Syntax.seq m n) (Syntax.seq p q)) as Hmem.
  {
  clear m n p q Hclm Hclp Hcln Hclq Hseqmp Hseqnq Hseqb Hm Hp Hmp.
  intros m n p q Hcln Hclq Hmp Hnq.
  destruct Hmp as (_ & Hclm & Hclp & Hiffmp & Hmp).
  do2 4 split; auto; try prove_hygiene.
    {
    split.
      {
      intro Hconvmn.
      so (converges_seq_invert _ _ Hconvmn) as Hconvm.
      apply (equiv_converges (subst1 p q)).
        {
        apply equiv_symm.
        apply equiv_seq_converges.
        tauto.
        }
      so (Hnq Hconvm) as (_ & _ & _ & Hiff & _).
      apply Hiff.
      apply (equiv_converges (Syntax.seq m n)); auto.
      apply equiv_seq_converges.
      tauto.
      }

      {
      intro Hconvpq.
      so (converges_seq_invert _ _ Hconvpq) as Hconvp.
      apply (equiv_converges (subst1 m n)).
        {
        apply equiv_symm.
        apply equiv_seq_converges.
        tauto.
        }
      so (Hiffmp ander Hconvp) as Hconvm.
      so (Hnq Hconvm) as (_ & _ & _ & Hiff & _).
      apply Hiff.
      apply (equiv_converges (Syntax.seq p q)); auto.
      apply equiv_seq_converges.
      tauto.
      }
    }

    {
    intro Hconvmn.
    so (converges_seq_invert _ _ Hconvmn) as Hconvm.
    so (Hiffmp andel Hconvm) as Hconvp.
    apply (urel_equiv _#3 (subst1 m n) _ (subst1 p q)); try prove_hygiene.
      {
      apply equiv_symm.
      apply equiv_seq_converges; auto.
      }

      {
      apply equiv_symm.
      apply equiv_seq_converges; auto.
      }

      {
      so (Hnq Hconvm) as (_ & _ & _ & _ & Hnq').
      apply Hnq'.
      apply (equiv_converges (Syntax.seq m n)); auto.
      apply equiv_seq_converges; auto.
      }
    }
  }
assert (interp toppg true i (partial (subst s b)) (iupartial stop i B)) as Hpbl.
  {
  apply interp_eval_refl; apply interp_partial; auto.
  }
do2 4 split; auto.
  {
  apply interp_eval_refl; apply interp_partial; auto.
  }

  {
  apply Hmem; auto; try prove_hygiene.
  intros Hconv.
  simpsub.
  destruct Hm as (_ & _ & _ & _ & Hm').
  so (Hseqnq _#3 (Hss _ _ (Hm' Hconv))) as (R & Hpbl' & _ & Hn & _).
  simpsubin Hpbl'.
  so (basic_fun _#7 Hpbl Hpbl').
  subst R.
  exact Hn.
  }

  {
  apply Hmem; auto; try prove_hygiene.
  intros Hconv.
  simpsub.
  destruct Hp as (_ & _ & _ & _ & Hp').
  so (Hseqnq _#3 (Hss _ _ (Hp' Hconv))) as (R & Hpbl' & _ & _ & Hq & _).
  simpsubin Hpbl'.
  so (basic_fun _#7 Hpbl Hpbl').
  subst R.
  exact Hq.
  }

  {
  apply Hmem; auto; try prove_hygiene.
  intros Hconv.
  simpsub.
  destruct Hmp as (_ & _ & _ & _ & Hmp').
  so (Hseqnq _#3 (Hss _ _ (Hmp' Hconv))) as (R & Hpbl' & _ & _ & _ & Hnq).
  simpsubin Hpbl'.
  so (basic_fun _#7 Hpbl Hpbl').
  subst R.
  exact Hnq.
  }
Qed.


Lemma subst_active :
  forall (s : @sub obj) m,
    active m
    -> active (subst (under 1 s) m).
Proof.
intros s m Hactive.
induct Hactive; intros; simpsub; [apply active_var | apply active_app | apply active_prev | apply active_ppi1 | apply active_ppi2 | apply active_bite | apply active_seq]; auto.
Qed.


Lemma active_converges :
  forall (m n : @term obj),
    active n
    -> converges (subst1 m n)
    -> converges m.
Proof.
intros m n Hactive.
induct Hactive.

(* var *)
{
simpsub.
auto.
}

(* app *)
{
intros n p _ IH Hconv.
simpsubin Hconv.
eauto using converges_app_invert.
}

(* prev *)
{
intros n _ IH Hconv.
simpsubin Hconv.
eauto using converges_prev_invert.
}

(* ppi1 *)
{
intros n _ IH Hconv.
simpsubin Hconv.
eauto using converges_ppi1_invert.
}

(* ppi2 *)
{
intros n _ IH Hconv.
simpsubin Hconv.
eauto using converges_ppi2_invert.
}

(* bite *)
{
intros n p q _ IH Hconv.
simpsubin Hconv.
eauto using converges_bite_invert.
}

(* seq *)
{
intros n p _ IH Hconv.
simpsubin Hconv.
eauto using converges_seq_invert.
}
Qed.


Lemma sound_seq_active :
  forall G a b m n,
    pseq G (deq m m (partial a))
    -> pseq (cons (hyp_tm a) G) (deq n n (subst sh1 (partial b)))
    -> pseq G (deqtype b b)
    -> active n
    -> pseq G (deq (Syntax.seq m n) (subst1 m n) (partial b)).
Proof.
intros G a b m n Hseqm Hseqn Hseqb Hactive.
assert (forall s, converges (subst (dot (subst s m) s) n) -> converges (subst s m)) as H.
  {
  intros s Hconv.
  assert (converges (subst1 (subst s m) (subst (under 1 s) n))) as Hconv'.
    {
    simpsub.
    auto.
    }
  exact (active_converges _ _ (subst_active s _ Hactive) Hconv').
  }
renameover H into Hactive.
revert G Hseqm Hseqn Hseqb.
simpsub.
refine (seq_pseq 2 [] m [hyp_emp] n 3 [] _ [_] _ [] _ _ _); cbn.
intros G Hclm Hcln Hseqm Hseqn Hseqb.
rewrite -> seq_deq in Hseqm, Hseqn |- *.
rewrite -> seq_eqtype in Hseqb.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqm _#3 Hs) as (R & Hpal & Hpar & Hm & _).
simpsubin Hpal.
simpsubin Hpar.
invert (basic_value_inv _#6 value_partial Hpal).
intros A Hal Heql.
invert (basic_value_inv _#6 value_partial Hpar).
intros A' Har Heqr.
so (iupartial_inj _#4 (eqtrans Heql (eqsymm Heqr))).
subst A'.
clear Heqr.
subst R.
so (Hseqb _#3 Hs) as (B & Hbl & Hbr & _).
exists (iupartial stop i B).
simpsub.
assert (forall r t, rel (den A) i r t -> pwctx i (dot r s) (dot t s') (cons (hyp_tm a) G)) as Hss.
  {
  intros r t Hrt.
  apply pwctx_cons_tm_seq; auto.
    {
    apply (seqhyp_tm _#5 A); auto.
    }
    
    {
    intros j u u' Hu.
    so (Hseqm _#3 Hu) as (R & Hl & Hr & _).
    simpsubin Hl.
    simpsubin Hr.
    invert (basic_value_inv _#6 value_partial Hl).
    intros Q Hql Heql.
    invert (basic_value_inv _#6 value_partial Hr).
    intros Q' Hqr Heqr.
    so (iupartial_inj _#4 (eqtrans Heql (eqsymm Heqr))).
    subst Q'.
    clear Heqr.
    subst R.
    exists toppg, Q.
    auto.
    }
  }
assert (interp toppg true i (partial (subst s b)) (iupartial stop i B)) as Hpbl.
  {
  apply interp_eval_refl; apply interp_partial; auto.
  }
destruct Hm as (_ & _ & _ & Hiffm & Hactm).
so (hygiene_subst1 _#4 (subst_closub _#4 Hcls Hclm) (subst_closub_under_permit _#4 Hcln Hcls)) as Hclsmn.
simpsubin Hclsmn.
so (hygiene_subst1 _#4 (subst_closub _#4 Hcls' Hclm) (subst_closub_under_permit _#4 Hcln Hcls')) as Hclsmn'.
simpsubin Hclsmn'.
do2 4 split; auto.
  {
  apply interp_eval_refl; apply interp_partial; auto.
  }

  {
  do2 4 split; auto; prove_hygiene.
    {
    split.
      {
      intro Hconvmn.
      so (converges_seq_invert _ _ Hconvmn) as Hconvm.
      apply (equiv_converges (subst (dot (subst s' m) s') n)).
        {
        apply equiv_symm.
        relquest.
          {
          apply equiv_seq_converges.
          apply Hiffm; auto.
          }
        simpsub.
        reflexivity.
        }
      so (Hseqn _#3 (Hss _ _ (Hactm Hconvm))) as (R & Hpbl' & _ & Hmn & _).
      simpsubin Hpbl'.
      so (basic_fun _#7 Hpbl Hpbl'); subst R.
      destruct Hmn as (_ & _ & _ & Hiff & _).
      apply Hiff.
      apply (equiv_converges (Syntax.seq (subst s m) (subst (under 1 s) n))); auto.
      relquest.
        {
        apply equiv_seq_converges; auto.
        }
      simpsub.
      reflexivity.
      }

      {
      intro Hconvmn'.
      so (converges_seq_invert _ _ Hconvmn') as Hconvm'.
      apply (equiv_converges (subst (dot (subst s m) s) n)).
        {
        apply equiv_symm.
        relquest.
          {
          apply equiv_seq_converges.
          apply Hiffm; auto.
          }
        simpsub.
        reflexivity.
        }
      so (Hseqn _#3 (Hss _ _ (Hactm (Hiffm ander Hconvm')))) as (R & Hpbl' & _ & Hmn & _).
      simpsubin Hpbl'.
      so (basic_fun _#7 Hpbl Hpbl'); subst R.
      destruct Hmn as (_ & _ & _ & Hiff & _).
      apply Hiff.
      apply (equiv_converges (Syntax.seq (subst s' m) (subst (under 1 s') n))); auto.
      relquest.
        {
        apply equiv_seq_converges; auto.
        }
      simpsub.
      reflexivity.
      }
    }

    {
    intro Hconvmn.
    so (converges_seq_invert _ _ Hconvmn) as Hconvm.
    so (Hseqn _#3 (Hss _ _ (Hactm Hconvm))) as (R & Hpbl' & _ & Hmn & _).
    simpsubin Hpbl'.
    so (basic_fun _#7 Hpbl Hpbl'); subst R.
    destruct Hmn as (_ & _ & _ & _ & Hactmn).
    so (Hiffm andel Hconvm) as Hconvm'.
    apply (urel_equiv _#3 (subst (dot (subst s m) s) n) _ (subst (dot (subst s' m) s') n)); try prove_hygiene.
      {
      apply equiv_symm.
      relquest.
        {
        apply equiv_seq_converges; auto.
        }
      simpsub.
      reflexivity.
      }

      {
      apply equiv_symm.
      relquest.
        {
        apply equiv_seq_converges; auto.
        }
      simpsub.
      reflexivity.
      }

      {
      apply Hactmn.
      apply (equiv_converges (Syntax.seq (subst s m) (subst (under 1 s) n))); auto.
      relquest.
        {
        apply equiv_seq_converges; auto.
        }
      simpsub.
      reflexivity.
      }
    }
  }

  {
  do2 4 split; auto.
    {
    split.
      {
      intros Hconvmn.
      so (Hactive _ Hconvmn) as Hconvm.
      so (Hactm Hconvm) as Hm'.
      so (Hseqn _#3 (Hss _ _ Hm')) as (R & Hpbl' & _ & Hmn & _).
      simpsubin Hpbl'.
      so (basic_fun _#7 Hpbl Hpbl'); subst R.
      destruct Hmn as (_ & _ & _ & Hiff & _).
      apply Hiff; auto.
      }

      {
      intros Hconvmn'.
      so (Hactive _ Hconvmn') as Hconvm'.
      so (Hactm (Hiffm ander Hconvm')) as Hm'.
      so (Hseqn _#3 (Hss _ _ Hm')) as (R & Hpbl' & _ & Hmn & _).
      simpsubin Hpbl'.
      so (basic_fun _#7 Hpbl Hpbl'); subst R.
      destruct Hmn as (_ & _ & _ & Hiff & _).
      apply Hiff; auto.
      }
    }

    {
    intros Hconvmn.
    so (Hactive _ Hconvmn) as Hconvm.
    so (Hactm Hconvm) as Hm'.
    so (Hseqn _#3 (Hss _ _ Hm')) as (R & Hpbl' & _ & Hmn & _).
    simpsubin Hpbl'.
    so (basic_fun _#7 Hpbl Hpbl'); subst R.
    destruct Hmn as (_ & _ & _ & _ & Hact).
    apply Hact; auto.
    }
  }

  {
  do2 4 split; auto; try prove_hygiene.
    {
    split.
      {
      intros Hconvmn.
      so (converges_seq_invert _ _ Hconvmn) as Hconvm.
      so (Hseqn _#3 (Hss _ _ (Hactm Hconvm))) as (R & Hpbl' & _ & Hmn & _).
      simpsubin Hpbl'.
      so (basic_fun _#7 Hpbl Hpbl'); subst R.
      destruct Hmn as (_ & _ & _ & Hiff & _).
      apply Hiff.
      apply (equiv_converges (Syntax.seq (subst s m) (subst (under 1 s) n))); auto.
      relquest.
        {
        apply equiv_seq_converges; auto.
        }
      simpsub.
      reflexivity.
      }

      {
      intros Hconvmn'.
      so (Hactive _ Hconvmn') as Hconvm'.
      apply (equiv_converges (subst (dot (subst s m) s) n)).
        {
        apply equiv_symm.
        relquest.
          {
          apply equiv_seq_converges.
          apply Hiffm; auto.
          }
        simpsub.
        reflexivity.
        }
      so (Hseqn _#3 (Hss _ _ (Hactm (Hiffm ander Hconvm')))) as (R & Hpbl' & _ & Hmn & _).
      simpsubin Hpbl'.
      so (basic_fun _#7 Hpbl Hpbl'); subst R.
      destruct Hmn as (_ & _ & _ & Hiff & _).
      apply Hiff; auto.
      }
    }

    {
    intros Hconvmn.
    so (converges_seq_invert _ _ Hconvmn) as Hconvm.
    so (Hseqn _#3 (Hss _ _ (Hactm Hconvm))) as (R & Hpbl' & _ & Hmn & _).
    simpsubin Hpbl'.
    so (basic_fun _#7 Hpbl Hpbl'); subst R.
    destruct Hmn as (_ & _ & _ & _ & Hactmn).
    so (Hiffm andel Hconvm) as Hconvm'.
    apply (urel_equiv_1 _#3 (subst (dot (subst s m) s) n)); try prove_hygiene.
      {
      apply equiv_symm.
      relquest.
        {
        apply equiv_seq_converges; auto.
        }
      simpsub.
      reflexivity.
      }

      {
      apply Hactmn.
      apply (equiv_converges (Syntax.seq (subst s m) (subst (under 1 s) n))); auto.
      relquest.
        {
        apply equiv_seq_converges; auto.
        }
      simpsub.
      reflexivity.
      }
    }
  }
Qed.


Lemma sound_active_halts_invert :
  forall G m n,
    pseq G (deq triv triv (halts (subst1 m n)))
    -> active n
    -> pseq G (deq triv triv (halts m)).
Proof.
intros G m n Hseq Hactive.
revert G Hseq.
refine (seq_pseq 1 [] m 1 [] _ _ _); cbn.
intros G Hclm Hseq.
rewrite -> seq_halts in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq i s s' Hs) as H.
simpsubin H.
destruct H as (_ & _ & Hconvmn & Hconvmn').
do2 3 split; try prove_hygiene.
  {
  apply (active_converges _ (subst (under 1 s) n)).
    {
    apply subst_active; auto.
    }

    {
    simpsub.
    auto.
    }
  }

  {
  apply (active_converges _ (subst (under 1 s') n)).
    {
    apply subst_active; auto.
    }

    {
    simpsub.
    auto.
    }
  }
Qed.


(* Redundant *)
Lemma sound_seq_halts_invert :
  forall G m n,
    pseq G (deq triv triv (halts (Syntax.seq m n)))
    -> pseq G (deq triv triv (halts m)).
Proof.
intros G m n.
revert G.
refine (seq_pseq 1 [] m 1 [] _ _ _); cbn.
intros G Hclm Hseq.
rewrite -> seq_halts in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq i s s' Hs) as H.
simpsubin H.
destruct H as (_ & _ & Hconvmn & Hconvmn').
do2 3 split; try prove_hygiene.
  {
  eapply converges_seq_invert; eauto.
  }

  {
  eapply converges_seq_invert; eauto.
  }
Qed.


(* Redundant *)
Lemma sound_seq_halts_invert2 :
  forall G m n,
    pseq G (deq triv triv (halts (Syntax.seq m n)))
    -> pseq G (deq triv triv (halts (subst1 m n))).
Proof.
intros G m n.
revert G.
refine (seq_pseq 2 [] m [hyp_emp] n 1 [] _ _ _); cbn.
intros G Hclm Hcln Hseq.
rewrite -> seq_halts in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq i s s' Hs) as H.
simpsubin H.
destruct H as (_ & _ & Hconvmn & Hconvmn').
simpsub.
do2 3 split; try prove_hygiene.
  {
  eapply hygiene_subst; eauto.
  intros j Hj.
  destruct j as [| j].
    {
    simpsub.
    prove_hygiene.
    }
  cbn in Hj.
  simpsub.
  eapply project_closub; eauto.
  }

  {
  eapply hygiene_subst; eauto.
  intros j Hj.
  destruct j as [| j].
    {
    simpsub.
    prove_hygiene.
    }
  cbn in Hj.
  simpsub.
  eapply project_closub; eauto.
  }

  {
  so (converges_seq_invert2 _ _ Hconvmn) as H.
  simpsubin H.
  exact H.
  }

  {
  so (converges_seq_invert2 _ _ Hconvmn') as H.
  simpsubin H.
  exact H.
  }
Qed.


(* Redundant *)
Lemma sound_seq_halts :
  forall G m n,
    pseq G (deq triv triv (halts m))
    -> pseq G (deq triv triv (halts (subst1 m n)))
    -> pseq G (deq triv triv (halts (Syntax.seq m n))).
Proof.
intros G m n.
revert G.
refine (seq_pseq 1 [hyp_emp] n 2 [] _ [] _ _ _); cbn.
intros G Hcln Hseqm Hseqmn.
rewrite -> seq_halts in Hseqm, Hseqmn |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
simpsub.
so (Hseqm _#3 Hs) as (Hclsm & Hclsm' & Hconvsm & Hconvsm').
so (Hseqmn _#3 Hs) as (Hclsmn & Hclsmn' & Hconvsmn & Hconvsmn').
do2 3 split.
  {
  apply hygiene_auto; cbn.
  do2 2 split; auto.
  eapply subst_closub_under_permit; eauto.
  }

  {
  apply hygiene_auto; cbn.
  do2 2 split; auto.
  eapply subst_closub_under_permit; eauto.
  }

  {
  apply converges_seq; auto.
  simpsub.
  simpsubin Hconvsmn.
  auto.
  }

  {
  apply converges_seq; auto.
  simpsub.
  simpsubin Hconvsmn'.
  auto.
  }
Qed.


Lemma sound_seq_halts_sequal :
  forall G m n,
    pseq G (deq triv triv (halts m))
    -> pseq G (deq triv triv (sequal (Syntax.seq m n) (subst1 m n))).
Proof.
intros G m n.
revert G.
refine (seq_pseq 2 [] m [hyp_emp] n 1 [] _ _ _); cbn.
intros G Hclm Hcln Hseq.
rewrite -> seq_deq.
rewrite -> seq_halts in Hseq.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq _#3 Hs) as (_ & _ & Hconv & Hconv').
exists (iubase (unit_urel stop i)).
simpsub.
assert (rel (den (iubase (unit_urel stop i))) i triv triv) as Htriv.
  {
  do2 5 split; auto using star_refl; prove_hygiene.
  }
do2 4 split; auto.
  {
  apply interp_eval_refl.
  apply interp_sequal.
    {
    prove_hygiene.
    }

    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    prove_hygiene.
    }

    {
    relquest.
      {
      apply equiv_seq_converges; auto.
      }
    simpsub.
    reflexivity.
    }
  }

  {
  apply interp_eval_refl.
  apply interp_sequal.
    {
    prove_hygiene.
    }

    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    prove_hygiene.
    }

    {
    relquest.
      {
      apply equiv_seq_converges; auto.
      }
    simpsub.
    reflexivity.
    }
  }
Qed.


Lemma sound_partial_formation_invert :
  forall G a b,
    pseq G (deqtype (partial a) (partial b))
    -> pseq G (deqtype a b).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & H).
simpsubin H.
destruct H as (Hpal & Hpar & Hpbl & Hpbr).
invert (basic_value_inv _#6 value_partial Hpal).
intros A Hal Heql.
invert (basic_value_inv _#6 value_partial Hpar).
intros A' Har Heqr.
so (iupartial_inj _#4 (eqtrans Heql (eqsymm Heqr))).
subst A'.
invert (basic_value_inv _#6 value_partial Hpbl).
intros A' Hbl Heql'.
so (iupartial_inj _#4 (eqtrans Heql (eqsymm Heql'))).
subst A'.
invert (basic_value_inv _#6 value_partial Hpbr).
intros A' Hbr Heqr'.
so (iupartial_inj _#4 (eqtrans Heql (eqsymm Heqr'))).
subst A'.
exists A.
auto.
Qed.


Lemma sound_admiss_formation_invert :
  forall G a b,
    pseq G (deqtype (admiss a) (admiss b))
    -> pseq G (deqtype a b).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & H).
simpsubin H.
destruct H as (Hpal & Hpar & Hpbl & Hpbr).
invert (basic_value_inv _#6 value_admiss Hpal).
intros A Hal Heql.
invert (basic_value_inv _#6 value_admiss Hpar).
intros A' Har Heqr.
so (iuadmiss_inj _#4 (eqtrans Heql (eqsymm Heqr))).
subst A'.
invert (basic_value_inv _#6 value_admiss Hpbl).
intros A' Hbl Heql'.
so (iuadmiss_inj _#4 (eqtrans Heql (eqsymm Heql'))).
subst A'.
invert (basic_value_inv _#6 value_admiss Hpbr).
intros A' Hbr Heqr'.
so (iuadmiss_inj _#4 (eqtrans Heql (eqsymm Heqr'))).
subst A'.
exists A.
auto.
Qed.


Lemma sound_uptype_formation_invert :
  forall G a b,
    pseq G (deqtype (uptype a) (uptype b))
    -> pseq G (deqtype a b).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & H).
simpsubin H.
destruct H as (Hpal & Hpar & Hpbl & Hpbr).
invert (basic_value_inv _#6 value_uptype Hpal).
intros A Hal Heql.
invert (basic_value_inv _#6 value_uptype Hpar).
intros A' Har Heqr.
so (iuuptype_inj _#4 (eqtrans Heql (eqsymm Heqr))).
subst A'.
invert (basic_value_inv _#6 value_uptype Hpbl).
intros A' Hbl Heql'.
so (iuuptype_inj _#4 (eqtrans Heql (eqsymm Heql'))).
subst A'.
invert (basic_value_inv _#6 value_uptype Hpbr).
intros A' Hbr Heqr'.
so (iuuptype_inj _#4 (eqtrans Heql (eqsymm Heqr'))).
subst A'.
exists A.
auto.
Qed.
