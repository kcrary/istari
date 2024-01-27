
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

Require Import SoundUtil.
Require Import Spaces.
Require Import Extend.
Require Import SemanticsPi.
Require Import ProperLevel.
Require Import Urelsp.
Require Import Ceiling.
Require Import Equivalence.
Require Import Equivalences.
Require Import Truncate.
Require Import ProperDownward.
Require Import ProperLevel.


Local Ltac prove_hygiene :=
  repeat (apply hygiene_auto; cbn; repeat2 split; auto);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1, subst_closub;
  try (apply hygiene_var; cbn; auto; done).


Lemma sound_karrow_kind_formation :
  forall G lv k k' l l',
    pseq G (deq k k' (kind lv))
    -> pseq G (deq l l' (kind lv))
    -> pseq G (deq (karrow k l) (karrow k' l') (kind lv)).
Proof.
intros G lv k k' l l'.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqk Hseql.
rewrite -> seq_eqkind in Hseqk, Hseql |- *.
intros i s s' Hs.
so (Hseqk _#3 Hs) as (pg & K & A & h & Hlvl & Hlvr & Hk1lt & Hk1rt & Hk2lt & Hk2rt & Hk1l & Hk1r & Hk2l & Hk2r).
clear Hseqk.
so (Hseql _#3 Hs) as (pg' & L & B & h' & Hlvl' & _ & Hl1lt & Hl1rt & Hl2lt & Hl2rt & Hl1l & Hl1r & Hl2l & Hl2r).
clear Hseql.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
so (proof_irrelevance _ h h'); subst h'.
exists pg, (qarrow K L), (iuarrow stop i A B), h.
simpsub.
do2 9 split; auto;
try (apply kinterp_eval_refl; apply interp_kkarrow; auto; done);
apply interp_eval_refl; apply interp_karrow; auto.
Qed.


Lemma sound_tarrow_kind_formation :
  forall G lv a b k l,
    pseq G (deq a b (univ lv))
    -> pseq G (deq k l (kind lv))
    -> pseq G (deq (tarrow a k) (tarrow b l) (kind lv)).
Proof.
intros G lv a b k l.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqab Hseqkl.
rewrite -> seq_eqkind in Hseqkl |- *.
rewrite -> seq_univ in Hseqab.
intros i s s' Hs.
so (Hseqkl _#3 Hs) as (pg & K & B & h & Hlvl & Hlvr & Hklt & Hkrt & Hllt & Hlrt & Hkl & Hkr & Hll & Hlr).
clear Hseqkl.
so (Hseqab _#3 Hs) as (pg' & R & Hlvl' & _ & Hal & Har & Hbl & Hbr).
clear Hseqab.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
so (interp_level_internal _#5 (cin_stop pg) Hal) as (A & ->).
exists pg, (qtarrow (cin pg) (den A) K).
exists (iuarrow stop i (extend_iurel (cin_stop pg) A) B), h.
simpsub.
so (lt_page_impl_le_page _ _ (lt_page_succ _ h)) as Hle.
do2 9 split; auto;
try (apply kinterp_eval_refl; apply interp_ktarrow; auto; done);
apply interp_eval_refl;
apply interp_tarrow; auto;
eapply interp_increase; eauto using toppg_max.
Qed.


Lemma sound_karrow_formation :
  forall G k k' l l',
    pseq G (deqtype k k')
    -> pseq G (deqtype l l')
    -> pseq G (deqtype (karrow k l) (karrow k' l')).
Proof.
intros G k1 k2 l1 l2.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqk Hseql.
rewrite -> seq_eqtype in Hseqk, Hseql |- *.
intros i s s' Hs.
so (Hseqk _#3 Hs) as (A & Hk1l & Hk1r & Hk2l & Hk2r).
so (Hseql _#3 Hs) as (B & Hl1l & Hl1r & Hl2l & Hl2r).
clear Hseqk Hseql.
exists (iuarrow stop i A B).
simpsub.
do2 3 split; auto;
apply interp_eval_refl;
apply interp_karrow; auto.
Qed.


Lemma sound_karrow_formation_univ :
  forall G lv k k' l l',
    pseq G (deq k k' (univ lv))
    -> pseq G (deq l l' (univ lv))
    -> pseq G (deq (karrow k l) (karrow k' l') (univ lv)).
Proof.
intros G lv k1 k2 l1 l2.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqk Hseql.
rewrite -> seq_univ in Hseqk, Hseql |- *.
intros i s s' Hs.
so (Hseqk _#3 Hs) as (pg & A & Hlvl & Hlvr & Hk1l & Hk1r & Hk2l & Hk2r).
so (Hseql _#3 Hs) as (pg' & B & Hlvl' & _ & Hl1l & Hl1r & Hl2l & Hl2r).
clear Hseqk Hseql.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
exists pg, (iuarrow stop i A B).
simpsub.
do2 5 split; auto;
apply interp_eval_refl;
apply interp_karrow; auto.
Qed.


Lemma sound_tarrow_formation :
  forall G a a' b b',
    pseq G (deqtype a a')
    -> pseq G (deqtype b b')
    -> pseq G (deqtype (tarrow a b) (tarrow a' b')).
Proof.
intros G k1 k2 l1 l2.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqk Hseql.
rewrite -> seq_eqtype in Hseqk, Hseql |- *.
intros i s s' Hs.
so (Hseqk _#3 Hs) as (A & Hk1l & Hk1r & Hk2l & Hk2r).
so (Hseql _#3 Hs) as (B & Hl1l & Hl1r & Hl2l & Hl2r).
clear Hseqk Hseql.
exists (iuarrow stop i A B).
simpsub.
do2 3 split; auto;
apply interp_eval_refl;
apply interp_tarrow; auto.
Qed.


Lemma sound_tarrow_formation_univ :
  forall G lv a a' b b',
    pseq G (deq a a' (univ lv))
    -> pseq G (deq b b' (univ lv))
    -> pseq G (deq (tarrow a b) (tarrow a' b') (univ lv)).
Proof.
intros G lv k1 k2 l1 l2.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqk Hseql.
rewrite -> seq_univ in Hseqk, Hseql |- *.
intros i s s' Hs.
so (Hseqk _#3 Hs) as (pg & A & Hlvl & Hlvr & Hk1l & Hk1r & Hk2l & Hk2r).
so (Hseql _#3 Hs) as (pg' & B & Hlvl' & _ & Hl1l & Hl1r & Hl2l & Hl2r).
clear Hseqk Hseql.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
exists pg, (iuarrow stop i A B).
simpsub.
do2 5 split; auto;
apply interp_eval_refl;
apply interp_tarrow; auto.
Qed.


Lemma sound_pi_formation :
  forall G a a' b b',
    pseq G (deqtype a a')
    -> pseq (cons (hyp_tm a) G) (deqtype b b')
    -> pseq G (deqtype (pi a b) (pi a' b')).
Proof.
intros G a b c d.
revert G.
refine (seq_pseq 4 [] a [] b [hyp_emp] c [hyp_emp] d 2 [] _ [_] _ _ _); cbn.
intros G Hcla Hclb Hclc Hcld Hseqab Hseqcd.
rewrite -> seq_eqtype in Hseqab, Hseqcd |- *.
intros i s s' Hs.
so (seqctx_impl_closub _#4 (pwctx_impl_seqctx _#4 Hs)) as (Hcls & Hcls').
so (Hseqab _#3 Hs) as (A & Hal & Har & Hbl & Hbr).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional_multi toppg i (den A) (subst (under 1 s) c) (subst (under 1 s') c) (subst (under 1 s) d) (subst (under 1 s') d)) as (C & Hcl & Hcr & Hdl & Hdr); eauto using subst_closub_under_permit.
  {
  intros j m p Hmp.
  assert (pwctx j (dot m s) (dot p s') (cons (hyp_tm a) G)) as Hss.
    {
    assert (j <= i) as Hj.
      {
      rewrite -> HeqA in Hmp.
      destruct Hmp.
      omega.
      }
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
      }

      {
      intros j' t t' Ht.
      so (Hseqab _#3 Ht) as (R & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqcd _#3 Hss) as (R & Hcl & Hcr & Hdl & Hdr).
  exists R.
  simpsub.
  auto.
  }
exists (iupi stop i A C).
simpsub.
do2 3 split; auto;
apply interp_eval_refl;
apply interp_pi; auto.
Qed.


Lemma sound_pi_formation_univ :
  forall G lv a a' b b',
    pseq G (deq a a' (univ lv))
    -> pseq (cons (hyp_tm a) G) (deq b b' (univ (subst sh1 lv)))
    -> pseq G (deq (pi a b) (pi a' b') (univ lv)).
Proof.
intros G lv a b c d.
revert G.
refine (seq_pseq 5 [] a [] b [hyp_emp] c [hyp_emp] d [] lv 2 [] _ [_] _ _ _); cbn.
intros G Hcla Hclb Hclc Hcld Hcllv Hseqab Hseqcd.
rewrite -> seq_univ in Hseqab, Hseqcd |- *.
intros i s s' Hs.
so (seqctx_impl_closub _#4 (pwctx_impl_seqctx _#4 Hs)) as (Hcls & Hcls').
so (Hseqab _#3 Hs) as (pg & A & Hlvl & Hlvr & Hal & Har & Hbl & Hbr).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional_multi pg i (den A) (subst (under 1 s) c) (subst (under 1 s') c) (subst (under 1 s) d) (subst (under 1 s') d)) as (C & Hcl & Hcr & Hdl & Hdr); eauto using subst_closub_under_permit.
  {
  intros j m p Hmp.
  assert (pwctx j (dot m s) (dot p s') (cons (hyp_tm a) G)) as Hss.
    {
    assert (j <= i) as Hj.
      {
      rewrite -> HeqA in Hmp.
      destruct Hmp.
      omega.
      }
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
      }

      {
      intros j' t t' Ht.
      so (Hseqab _#3 Ht) as (pg' & R & _ & _ & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqcd _#3 Hss) as (pg' & R & Hlvl' & _ & Hcl & Hcr & Hdl & Hdr).
  simpsubin Hlvl'.
  so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
  exists R.
  simpsub.
  auto.
  }
exists pg, (iupi stop i A C).
simpsub.
do2 5 split; auto;
apply interp_eval_refl;
apply interp_pi; auto.
Qed.


Lemma sound_karrow_pi_equal :
  forall G a b,
    pseq G (deqtype a a)
    -> pseq G (deqtype b b)
    -> pseq G (deqtype (karrow a b) (pi a (subst sh1 b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 2 [] a [] b 2 [] _ [] _ _ _); cbn.
intros G Hcla Hclb Hseqa Hseqb.
rewrite -> seq_eqtype in Hseqa, Hseqb |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
so (Hseqb _#3 Hs) as (B & Hbl & Hbr & _).
exists (iuarrow stop i A B).
simpsub.
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
do2 3 split; auto;
apply interp_eval_refl;
try (apply interp_karrow); auto.
  {
  rewrite -> iuarrow_eq_iupi.
  apply interp_pi; auto.
  apply functional_i; auto.
    {
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }
  intros j m p Hj Hmp.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  simpsub.
  eapply basic_downward; eauto.
  }

  {
  rewrite -> iuarrow_eq_iupi.
  apply interp_pi; auto.
  apply functional_i; auto.
    {
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }
  intros j m p Hj Hmp.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  simpsub.
  eapply basic_downward; eauto.
  }
Qed.


Lemma sound_karrow_pi_equal_univ :
  forall G lv a b,
    pseq G (deq a a (univ lv))
    -> pseq G (deq b b (univ lv))
    -> pseq G (deq (karrow a b) (pi a (subst sh1 b)) (univ lv)).
Proof.
intros G lv a b.
revert G.
refine (seq_pseq 3 [] a [] b [] lv 2 [] _ [] _ _ _); cbn.
intros G Hcla Hclb Hcllv Hseqa Hseqb.
rewrite -> seq_univ in Hseqa, Hseqb |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (pg & A & Hlvl & Hlvr & Hal & Har & _).
so (Hseqb _#3 Hs) as (pg' & B & Hlvl' & _ & Hbl & Hbr & _).
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
exists pg, (iuarrow stop i A B).
simpsub.
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
do2 5 split; auto;
apply interp_eval_refl;
try (apply interp_karrow); auto.
  {
  rewrite -> iuarrow_eq_iupi.
  apply interp_pi; auto.
  apply functional_i; auto.
    {
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }
  intros j m p Hj Hmp.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  simpsub.
  eapply basic_downward; eauto.
  }

  {
  rewrite -> iuarrow_eq_iupi.
  apply interp_pi; auto.
  apply functional_i; auto.
    {
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }
  intros j m p Hj Hmp.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  simpsub.
  eapply basic_downward; eauto.
  }
Qed.


Lemma sound_tarrow_karrow_equal :
  forall G a b,
    pseq G (deqtype a a)
    -> pseq G (deqtype b b)
    -> pseq G (deqtype (tarrow a b) (karrow a b)).
Proof.
intros G a b.
revert G.
refine (seq_pseq 2 [] a [] b 2 [] _ [] _ _ _); cbn.
intros G Hcla Hclb Hseqa Hseqb.
rewrite -> seq_eqtype in Hseqa, Hseqb |- *.
intros i s s' Hs.
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
so (Hseqb _#3 Hs) as (B & Hbl & Hbr & _).
exists (iuarrow stop i A B).
simpsub.
do2 3 split; auto;
apply interp_eval_refl;
first [apply interp_karrow | apply interp_tarrow]; auto.
Qed.


Lemma sound_tarrow_karrow_equal_univ :
  forall G lv a b,
    pseq G (deq a a (univ lv))
    -> pseq G (deq b b (univ lv))
    -> pseq G (deq (tarrow a b) (karrow a b) (univ lv)).
Proof.
intros G lv a b.
revert G.
refine (seq_pseq 3 [] a [] b [] lv 2 [] _ [] _ _ _); cbn.
intros G Hcla Hclb Hcllv Hseqa Hseqb.
rewrite -> seq_univ in Hseqa, Hseqb |- *.
intros i s s' Hs.
so (Hseqa _#3 Hs) as (pg & A & Hlvl & Hlvr & Hal & Har & _).
so (Hseqb _#3 Hs) as (pg' & B & Hlvl' & _ & Hbl & Hbr & _).
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
exists pg, (iuarrow stop i A B).
simpsub.
do2 5 split; auto;
apply interp_eval_refl;
first [apply interp_karrow | apply interp_tarrow]; auto.
Qed.


Lemma sound_tarrow_pi_equal :
  forall G a b,
    pseq G (deqtype a a)
    -> pseq G (deqtype b b)
    -> pseq G (deqtype (tarrow a b) (pi a (subst sh1 b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 2 [] a [] b 2 [] _ [] _ _ _); cbn.
intros G Hcla Hclb Hseqa Hseqb.
rewrite -> seq_eqtype in Hseqa, Hseqb |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
so (Hseqb _#3 Hs) as (B & Hbl & Hbr & _).
exists (iuarrow stop i A B).
simpsub.
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
do2 3 split; auto;
apply interp_eval_refl;
try (apply interp_tarrow); auto.
  {
  rewrite -> iuarrow_eq_iupi.
  apply interp_pi; auto.
  apply functional_i; auto.
    {
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }
  intros j m p Hj Hmp.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  simpsub.
  eapply basic_downward; eauto.
  }

  {
  rewrite -> iuarrow_eq_iupi.
  apply interp_pi; auto.
  apply functional_i; auto.
    {
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }
  intros j m p Hj Hmp.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  simpsub.
  eapply basic_downward; eauto.
  }
Qed.


Lemma sound_tarrow_pi_equal_univ :
  forall G lv a b,
    pseq G (deq a a (univ lv))
    -> pseq G (deq b b (univ lv))
    -> pseq G (deq (tarrow a b) (pi a (subst sh1 b)) (univ lv)).
Proof.
intros G lv a b.
revert G.
refine (seq_pseq 3 [] a [] b [] lv 2 [] _ [] _ _ _); cbn.
intros G Hcla Hclb Hcllv Hseqa Hseqb.
rewrite -> seq_univ in Hseqa, Hseqb |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (pg & A & Hlvl & Hlvr & Hal & Har & _).
so (Hseqb _#3 Hs) as (pg' & B & Hlvl' & _ & Hbl & Hbr & _).
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
exists pg, (iuarrow stop i A B).
simpsub.
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
do2 5 split; auto;
apply interp_eval_refl;
try (apply interp_tarrow); auto.
  {
  rewrite -> iuarrow_eq_iupi.
  apply interp_pi; auto.
  apply functional_i; auto.
    {
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }
  intros j m p Hj Hmp.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  simpsub.
  eapply basic_downward; eauto.
  }

  {
  rewrite -> iuarrow_eq_iupi.
  apply interp_pi; auto.
  apply functional_i; auto.
    {
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }
  intros j m p Hj Hmp.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  simpsub.
  eapply basic_downward; eauto.
  }
Qed.


Lemma sound_pi_intro :
  forall G a b m n,
    pseq G (deqtype a a)
    -> pseq (cons (hyp_tm a) G) (deq m n b)
    -> pseq G (deq (lam m) (lam n) (pi a b)).
Proof.
intros G a b m n.
revert G.
refine (seq_pseq 4 [] a [hyp_emp] b [hyp_emp] m [hyp_emp] n 2 [] _ [_] _ _ _); cbn.
intros G Hcla Hclb Hclm Hcln Hseqa Hseqmn.
rewrite -> seq_eqtype in Hseqa.
rewrite -> seq_deq in Hseqmn |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
assert (forall j p q,
          rel (den A) j p q
          -> pwctx j (dot p s) (dot q s') (cons (hyp_tm a) G)) as Hss.
  {
  intros j p q Hpq.
  assert (j <= i) as Hj.
    {
    rewrite -> HeqA in Hpq.
    destruct Hpq.
    omega.
    }
  apply pwctx_cons_tm_seq; eauto using pwctx_downward.
    {
    eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
    }

    {
    intros j' t t' Ht.
    so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
    eauto.
    }
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as H; eauto using subst_closub_under_permit.
  {
  intros j p q Hpq.
  so (Hseqmn _#3 (Hss j p q Hpq)) as (R & Hbl & Hbr & _).
  exists R.
  simpsub.
  auto.
  }
destruct H as (B & Hbl & Hbr).
exists (iupi stop i A B).
simpsub.
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_pi; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_pi; auto.
  }

  {
  do 2 eexists.
  do2 5 split; eauto using star_refl.
    {
    apply hygiene_auto; cbn.
    split; auto.
    eapply subst_closub_under_permit; eauto.
    }

    {
    apply hygiene_auto; cbn.
    split; auto.
    eapply subst_closub_under_permit; eauto.
    }
  intros j p q Hj Hpq.
  simpsub.
  so (Hseqmn _#3 (Hss _#3 Hpq)) as (R & Hpb & _ & Hm & _).
  invert Hbl.
  intros _ _ Hbact.
  so (Hbact _#3 Hj Hpq) as H.
  simpsubin H.
  so (basic_fun _#7 Hpb H); subst R; clear H.
  exact Hm.
  }

  {
  do 2 eexists.
  do2 5 split; eauto using star_refl.
    {
    apply hygiene_auto; cbn.
    split; auto.
    eapply subst_closub_under_permit; eauto.
    }

    {
    apply hygiene_auto; cbn.
    split; auto.
    eapply subst_closub_under_permit; eauto.
    }
  intros j p q Hj Hpq.
  simpsub.
  so (Hseqmn _#3 (Hss _#3 Hpq)) as (R & Hpb & _ & _ & Hn & _).
  invert Hbl.
  intros _ _ Hbact.
  so (Hbact _#3 Hj Hpq) as H.
  simpsubin H.
  so (basic_fun _#7 Hpb H); subst R; clear H.
  exact Hn.
  }

  {
  do 2 eexists.
  do2 5 split; eauto using star_refl.
    {
    apply hygiene_auto; cbn.
    split; auto.
    eapply subst_closub_under_permit; eauto.
    }

    {
    apply hygiene_auto; cbn.
    split; auto.
    eapply subst_closub_under_permit; eauto.
    }
  intros j p q Hj Hpq.
  simpsub.
  so (Hseqmn _#3 (Hss _#3 Hpq)) as (R & Hpb & _ & _ & _ & Hmn).
  invert Hbl.
  intros _ _ Hbact.
  so (Hbact _#3 Hj Hpq) as H.
  simpsubin H.
  so (basic_fun _#7 Hpb H); subst R; clear H.
  exact Hmn.
  }
Qed.


Lemma sound_pi_elim :
  forall G a b m n p q,
    pseq G (deq m n (pi a b))
    -> pseq G (deq p q a)
    -> pseq G (deq (app m p) (app n q) (subst1 p b)).
Proof.
intros G a b m n p q.
revert G.
refine (seq_pseq 6 [] a [hyp_emp] b [] m [] n [] p [] q 2 [] _ [] _ _ _); cbn.
intros G Hcla Hclb Hclm Hcln Hclp Hclq Hseqmn Hseqpq.
rewrite -> seq_deq in Hseqmn, Hseqpq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmn _#3 Hs) as (R & Hpil & Hpir & Hm & Hn & Hmn).
clear Hseqmn.
so (Hseqpq _#3 Hs) as (A & Hal & Har & Hp & Hq & Hpq).
clear Hseqpq.
simpsubin Hpil.
simpsubin Hpir.
invert (basic_value_inv _#6 value_pi Hpil).
intros A' B Hal' Hbl Heql.
so (basic_fun _#7 Hal Hal'); subst A'.
invert (basic_value_inv _#6 value_pi Hpir).
intros A' B' Har' Hbr Heqr.
so (basic_fun _#7 Har Har'); subst A'.
so (eqtrans Heql (eqsymm Heqr)) as Heq.
clear Heqr.
subst R.
so (eq_dep_impl_eq_snd _#5 (iupi_inj _#7 Heq)); subst B'.
exists (pi1 B (urelspinj _#4 Hp)).
simpsub.
do2 4 split.
  {
  invert Hbl.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hp) as H.
  simpsubin H.
  exact H.
  }

  {
  invert Hbr.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hp) as H.
  simpsubin H.
  exact H.
  }

  {
  cbn in Hm.
  decompose Hm.
  intros l l' _ _ _ Hsteps Hsteps' Hact.
  so (Hact _#3 (le_refl _) Hp) as Hpl.
  eapply urel_equiv; eauto; try prove_hygiene.
    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_app; [| apply equiv_refl].
      apply steps_equiv; eauto.
      }
    eapply steps_equiv.
    apply star_one.
    apply step_app2.
    }

    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_app; [| apply equiv_refl].
      apply steps_equiv; eauto.
      }
    eapply steps_equiv.
    apply star_one.
    apply step_app2.
    }
  }

  {
  cbn in Hn.
  decompose Hn.
  intros l l' _ _ _ Hsteps Hsteps' Hact.
  so (Hact _#3 (le_refl _) Hq) as Hpl.
  rewrite -> (urelspinj_equal _#7 Hp Hq Hpq).
  eapply urel_equiv; eauto; try prove_hygiene.
    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_app; [| apply equiv_refl].
      apply steps_equiv; eauto.
      }
    eapply steps_equiv.
    apply star_one.
    apply step_app2.
    }

    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_app; [| apply equiv_refl].
      apply steps_equiv; eauto.
      }
    eapply steps_equiv.
    apply star_one.
    apply step_app2.
    }
  }

  {
  cbn in Hmn.
  decompose Hmn.
  intros l l' _ _ _ Hsteps Hsteps' Hact.
  assert (rel (den A) i (subst s q) (subst s' p)) as Hqp.
    {
    eapply urel_zigzag; eauto.
    }
  so (Hact _#3 (le_refl _) Hpq) as Hpl.
  rewrite -> (urelspinj_equal _#7 Hp Hpq Hpq).
  eapply urel_equiv; eauto; try prove_hygiene.
    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_app; [| apply equiv_refl].
      apply steps_equiv; eauto.
      }
    eapply steps_equiv.
    apply star_one.
    apply step_app2.
    }

    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_app; [| apply equiv_refl].
      apply steps_equiv; eauto.
      }
    eapply steps_equiv.
    apply star_one.
    apply step_app2.
    }
  }
Qed.


Lemma sound_pi_eta :
  forall G a b m,
    pseq G (deq m m (pi a b))
    -> pseq G (deq m (lam (app (subst sh1 m) (var 0))) (pi a b)).
Proof.
intros G a b m.
revert G.
refine (seq_pseq 1 [] m 1 [] _ _ _); cbn.
intros G Hclm Hseqm.
rewrite -> seq_deq in Hseqm |- *.
intros i s s' Hs.
so (Hseqm _#3 Hs) as (R & Hpil & Hpir & Hm & _).
exists R.
do2 2 split; auto.
simpsubin Hpil.
invert (basic_value_inv _#6 value_pi Hpil).
intros A B Hal Hbl <-.
assert (exists l l', equiv (subst s m) (lam l) /\ equiv (subst s' m) (lam l')) as (l & l' & Hl & Hl').
  {
  cbn in Hm.
  decompose Hm.
  intros l l' _ _ _ Hl Hl' _.
  exists l, l'; eauto using steps_equiv.
  }
so (urel_closed _#5 Hm) as (Hclsm & Hclsm').
do2 2 split; auto.
  {
  simpsub.
  refine (urel_equiv _#7 _ _ _ _ Hm).
    {
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit; auto.
    }

    {
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit; auto.
    }

    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_lam.
      eapply equiv_trans.
        {
        apply equiv_app; [| apply equiv_refl].
        rewrite -> subst_compose.
        apply equiv_subst; eauto.
        }
      simpsub.
      apply steps_equiv.
      apply star_one.
      apply step_app2.
      }
    simpsub.
    apply equiv_symm.
    rewrite <- (subst_eqsub _#4 (eqsub_expand_id _)).
    simpsub; auto.
    }

    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_lam.
      eapply equiv_trans.
        {
        apply equiv_app; [| apply equiv_refl].
        rewrite -> subst_compose.
        apply equiv_subst; eauto.
        }
      simpsub.
      apply steps_equiv.
      apply star_one.
      apply step_app2.
      }
    simpsub.
    apply equiv_symm.
    rewrite <- (subst_eqsub _#4 (eqsub_expand_id _)).
    simpsub; auto.
    }
  }

  {
  simpsub.
  refine (urel_equiv _#7 _ _ _ _ Hm); auto using equiv_refl.
    {
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit; auto.
    }

    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_lam.
      eapply equiv_trans.
        {
        apply equiv_app; [| apply equiv_refl].
        rewrite -> subst_compose.
        apply equiv_subst; eauto.
        }
      simpsub.
      apply steps_equiv.
      apply star_one.
      apply step_app2.
      }
    simpsub.
    apply equiv_symm.
    rewrite <- (subst_eqsub _#4 (eqsub_expand_id _)).
    simpsub; auto.
    }
  }
Qed.


Lemma sound_tarrow_eta :
  forall G a b m,
    pseq G (deq m m (tarrow a b))
    -> pseq G (deq m (lam (app (subst sh1 m) (var 0))) (tarrow a b)).
Proof.
intros G a b m.
revert G.
refine (seq_pseq 1 [] m 1 [] _ _ _); cbn.
intros G Hclm Hseqm.
rewrite -> seq_deq in Hseqm |- *.
intros i s s' Hs.
so (Hseqm _#3 Hs) as (R & Hpil & Hpir & Hm & _).
exists R.
do2 2 split; auto.
simpsubin Hpil.
invert (basic_value_inv _#6 value_tarrow Hpil).
intros A B Hal Hbl <-.
assert (exists l l', equiv (subst s m) (lam l) /\ equiv (subst s' m) (lam l')) as (l & l' & Hl & Hl').
  {
  cbn in Hm.
  decompose Hm.
  intros l l' _ _ _ Hl Hl' _.
  exists l, l'; eauto using steps_equiv.
  }
so (urel_closed _#5 Hm) as (Hclsm & Hclsm').
do2 2 split; auto.
  {
  simpsub.
  refine (urel_equiv _#7 _ _ _ _ Hm).
    {
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit; auto.
    }

    {
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit; auto.
    }

    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_lam.
      eapply equiv_trans.
        {
        apply equiv_app; [| apply equiv_refl].
        rewrite -> subst_compose.
        apply equiv_subst; eauto.
        }
      simpsub.
      apply steps_equiv.
      apply star_one.
      apply step_app2.
      }
    simpsub.
    apply equiv_symm.
    rewrite <- (subst_eqsub _#4 (eqsub_expand_id _)).
    simpsub; auto.
    }

    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_lam.
      eapply equiv_trans.
        {
        apply equiv_app; [| apply equiv_refl].
        rewrite -> subst_compose.
        apply equiv_subst; eauto.
        }
      simpsub.
      apply steps_equiv.
      apply star_one.
      apply step_app2.
      }
    simpsub.
    apply equiv_symm.
    rewrite <- (subst_eqsub _#4 (eqsub_expand_id _)).
    simpsub; auto.
    }
  }

  {
  simpsub.
  refine (urel_equiv _#7 _ _ _ _ Hm); auto using equiv_refl.
    {
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit; auto.
    }

    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_lam.
      eapply equiv_trans.
        {
        apply equiv_app; [| apply equiv_refl].
        rewrite -> subst_compose.
        apply equiv_subst; eauto.
        }
      simpsub.
      apply steps_equiv.
      apply star_one.
      apply step_app2.
      }
    simpsub.
    apply equiv_symm.
    rewrite <- (subst_eqsub _#4 (eqsub_expand_id _)).
    simpsub; auto.
    }
  }
Qed.


Lemma sound_karrow_eta :
  forall G a b m,
    pseq G (deq m m (karrow a b))
    -> pseq G (deq m (lam (app (subst sh1 m) (var 0))) (karrow a b)).
Proof.
intros G a b m.
revert G.
refine (seq_pseq 1 [] m 1 [] _ _ _); cbn.
intros G Hclm Hseqm.
rewrite -> seq_deq in Hseqm |- *.
intros i s s' Hs.
so (Hseqm _#3 Hs) as (R & Hpil & Hpir & Hm & _).
exists R.
do2 2 split; auto.
simpsubin Hpil.
invert (basic_value_inv _#6 value_karrow Hpil).
intros A B Hal Hbl <-.
assert (exists l l', equiv (subst s m) (lam l) /\ equiv (subst s' m) (lam l')) as (l & l' & Hl & Hl').
  {
  cbn in Hm.
  decompose Hm.
  intros l l' _ _ _ Hl Hl' _.
  exists l, l'; eauto using steps_equiv.
  }
so (urel_closed _#5 Hm) as (Hclsm & Hclsm').
do2 2 split; auto.
  {
  simpsub.
  refine (urel_equiv _#7 _ _ _ _ Hm).
    {
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit; auto.
    }

    {
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit; auto.
    }

    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_lam.
      eapply equiv_trans.
        {
        apply equiv_app; [| apply equiv_refl].
        rewrite -> subst_compose.
        apply equiv_subst; eauto.
        }
      simpsub.
      apply steps_equiv.
      apply star_one.
      apply step_app2.
      }
    simpsub.
    apply equiv_symm.
    rewrite <- (subst_eqsub _#4 (eqsub_expand_id _)).
    simpsub; auto.
    }

    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_lam.
      eapply equiv_trans.
        {
        apply equiv_app; [| apply equiv_refl].
        rewrite -> subst_compose.
        apply equiv_subst; eauto.
        }
      simpsub.
      apply steps_equiv.
      apply star_one.
      apply step_app2.
      }
    simpsub.
    apply equiv_symm.
    rewrite <- (subst_eqsub _#4 (eqsub_expand_id _)).
    simpsub; auto.
    }
  }

  {
  simpsub.
  refine (urel_equiv _#7 _ _ _ _ Hm); auto using equiv_refl.
    {
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit; auto.
    }

    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_lam.
      eapply equiv_trans.
        {
        apply equiv_app; [| apply equiv_refl].
        rewrite -> subst_compose.
        apply equiv_subst; eauto.
        }
      simpsub.
      apply steps_equiv.
      apply star_one.
      apply step_app2.
      }
    simpsub.
    apply equiv_symm.
    rewrite <- (subst_eqsub _#4 (eqsub_expand_id _)).
    simpsub; auto.
    }
  }
Qed.


Lemma sound_tarrow_formation_invert1 :
  forall G a a' b b',
    pseq G (deqtype (tarrow a b) (tarrow a' b'))
    -> pseq G (deqtype a a').
Proof.
intros G a b c d.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hpil & Hpir & Hpil' & Hpir').
simpsubin Hpil.
simpsubin Hpir.
simpsubin Hpil'.
simpsubin Hpir'.
invert (basic_value_inv _#6 value_tarrow Hpil).
intros A B Hal Hbl Heql.
invert (basic_value_inv _#6 value_tarrow Hpir).
intros A' B' Har Hbr Heqr.
so (iuarrow_inj _#7 (eqtrans Heql (eqsymm Heqr))) as (<- & _).
invert (basic_value_inv _#6 value_tarrow Hpil').
intros A' B'' Hal' Hbl' Heql'.
so (iuarrow_inj _#7 (eqtrans Heql (eqsymm Heql'))) as (<- & _).
invert (basic_value_inv _#6 value_tarrow Hpir').
intros A' B''' Har' Hbr' Heqr'.
so (iuarrow_inj _#7 (eqtrans Heql (eqsymm Heqr'))) as (<- & _).
exists A.
auto.
Qed.


Lemma sound_tarrow_formation_invert2 :
  forall G a a' b b',
    pseq G (deqtype (tarrow a b) (tarrow a' b'))
    -> pseq (cons (hyp_tm a) G) (deqtype (subst sh1 b) (subst sh1 b')).
Proof.
intros G a b c d.
revert G.
refine (seq_pseq_hyp 4 [] a [] b [] c [] d 1 [] [] _ [] [_] _ _); cbn.
intros G Hcla Hclb Hclc Hcld Hseq _.
rewrite -> seq_eqtype in Hseq |- *.
intros i ss ss' Hss.
so (pwctx_cons_invert_simple _#5 Hss) as H; clear Hss.
destruct H as (m & p & s & s' & Hs & Hmp & -> & ->).
simpsubin Hmp.
invertc Hmp.
intros A Hal Har Hmp.
so (Hseq i s s' Hs) as (R & Hpil & Hpir & Hpil' & Hpir').
simpsubin Hpil.
simpsubin Hpir.
simpsubin Hpil'.
simpsubin Hpir'.
invert (basic_value_inv _#6 value_tarrow Hpil).
intros A' B Hal' Hcl Heqacl.
so (basic_fun _#7 Hal Hal'); subst A'.
invert (basic_value_inv _#6 value_tarrow Hpir).
intros A' B' Har' Hcr Heqacr.
so (eqtrans Heqacl (eqsymm Heqacr)) as Heq.
clear Heqacr.
invert (basic_value_inv _#6 value_tarrow Hpil').
intros A'' B'' Hbl Hdl Heqbdl.
so (eqtrans Heqacl (eqsymm Heqbdl)) as Heq'.
clear Heqbdl.
invert (basic_value_inv _#6 value_tarrow Hpir').
intros A''' B''' Hbr Hdr Heqbdr.
so (eqtrans Heqacl (eqsymm Heqbdr)) as Heq''.
clear Heqbdr.
subst R.
so (iuarrow_inj _#7 Heq) as (<- & H).
so (H _#3 Hmp) as HeqB; clear H.
rewrite <- (basic_impl_iutruncate _#6 Hcl) in HeqB.
rewrite <- (basic_impl_iutruncate _#6 Hcr) in HeqB.
subst B'.
so (iuarrow_inj _#7 Heq') as (<- & H).
so (H _#3 Hmp) as HeqB; clear H.
rewrite <- (basic_impl_iutruncate _#6 Hcl) in HeqB.
rewrite <- (basic_impl_iutruncate _#6 Hdl) in HeqB.
subst B''.
so (iuarrow_inj _#7 Heq'') as (<- & H).
so (H _#3 Hmp) as HeqB; clear H.
rewrite <- (basic_impl_iutruncate _#6 Hcl) in HeqB.
rewrite <- (basic_impl_iutruncate _#6 Hdr) in HeqB.
subst B'''.
exists B.
simpsub.
do2 3 split; auto.
Qed.


Lemma sound_karrow_formation_invert1 :
  forall G a a' b b',
    pseq G (deqtype (karrow a b) (karrow a' b'))
    -> pseq G (deqtype a a').
Proof.
intros G a b c d.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hpil & Hpir & Hpil' & Hpir').
simpsubin Hpil.
simpsubin Hpir.
simpsubin Hpil'.
simpsubin Hpir'.
invert (basic_value_inv _#6 value_karrow Hpil).
intros A B Hal Hbl Heql.
invert (basic_value_inv _#6 value_karrow Hpir).
intros A' B' Har Hbr Heqr.
so (iuarrow_inj _#7 (eqtrans Heql (eqsymm Heqr))) as (<- & _).
invert (basic_value_inv _#6 value_karrow Hpil').
intros A' B'' Hal' Hbl' Heql'.
so (iuarrow_inj _#7 (eqtrans Heql (eqsymm Heql'))) as (<- & _).
invert (basic_value_inv _#6 value_karrow Hpir').
intros A' B''' Har' Hbr' Heqr'.
so (iuarrow_inj _#7 (eqtrans Heql (eqsymm Heqr'))) as (<- & _).
exists A.
auto.
Qed.


Lemma sound_karrow_formation_invert2 :
  forall G a a' b b',
    pseq G (deqtype (karrow a b) (karrow a' b'))
    -> pseq (cons (hyp_tm a) G) (deqtype (subst sh1 b) (subst sh1 b')).
Proof.
intros G a b c d.
revert G.
refine (seq_pseq_hyp 4 [] a [] b [] c [] d 1 [] [] _ [] [_] _ _); cbn.
intros G Hcla Hclb Hclc Hcld Hseq _.
rewrite -> seq_eqtype in Hseq |- *.
intros i ss ss' Hss.
so (pwctx_cons_invert_simple _#5 Hss) as H; clear Hss.
destruct H as (m & p & s & s' & Hs & Hmp & -> & ->).
simpsubin Hmp.
invertc Hmp.
intros A Hal Har Hmp.
so (Hseq i s s' Hs) as (R & Hpil & Hpir & Hpil' & Hpir').
simpsubin Hpil.
simpsubin Hpir.
simpsubin Hpil'.
simpsubin Hpir'.
invert (basic_value_inv _#6 value_karrow Hpil).
intros A' B Hal' Hcl Heqacl.
so (basic_fun _#7 Hal Hal'); subst A'.
invert (basic_value_inv _#6 value_karrow Hpir).
intros A' B' Har' Hcr Heqacr.
so (eqtrans Heqacl (eqsymm Heqacr)) as Heq.
clear Heqacr.
invert (basic_value_inv _#6 value_karrow Hpil').
intros A'' B'' Hbl Hdl Heqbdl.
so (eqtrans Heqacl (eqsymm Heqbdl)) as Heq'.
clear Heqbdl.
invert (basic_value_inv _#6 value_karrow Hpir').
intros A''' B''' Hbr Hdr Heqbdr.
so (eqtrans Heqacl (eqsymm Heqbdr)) as Heq''.
clear Heqbdr.
subst R.
so (iuarrow_inj _#7 Heq) as (<- & H).
so (H _#3 Hmp) as HeqB; clear H.
rewrite <- (basic_impl_iutruncate _#6 Hcl) in HeqB.
rewrite <- (basic_impl_iutruncate _#6 Hcr) in HeqB.
subst B'.
so (iuarrow_inj _#7 Heq') as (<- & H).
so (H _#3 Hmp) as HeqB; clear H.
rewrite <- (basic_impl_iutruncate _#6 Hcl) in HeqB.
rewrite <- (basic_impl_iutruncate _#6 Hdl) in HeqB.
subst B''.
so (iuarrow_inj _#7 Heq'') as (<- & H).
so (H _#3 Hmp) as HeqB; clear H.
rewrite <- (basic_impl_iutruncate _#6 Hcl) in HeqB.
rewrite <- (basic_impl_iutruncate _#6 Hdr) in HeqB.
subst B'''.
exists B.
simpsub.
do2 3 split; auto.
Qed.


Lemma sound_pi_formation_invert1 :
  forall G a a' b b',
    pseq G (deqtype (pi a b) (pi a' b'))
    -> pseq G (deqtype a a').
Proof.
intros G a b c d.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hpil & Hpir & Hpil' & Hpir').
simpsubin Hpil.
simpsubin Hpir.
simpsubin Hpil'.
simpsubin Hpir'.
invert (basic_value_inv _#6 value_pi Hpil).
intros A B Hal Hbl Heql.
invert (basic_value_inv _#6 value_pi Hpir).
intros A' B' Har Hbr Heqr.
so (iupi_inj _#7 (eqtrans Heql (eqsymm Heqr))) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
invert (basic_value_inv _#6 value_pi Hpil').
intros A' B' Hal' Hbl' Heql'.
so (iupi_inj _#7 (eqtrans Heql (eqsymm Heql'))) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
invert (basic_value_inv _#6 value_pi Hpir').
intros A' B' Har' Hbr' Heqr'.
so (iupi_inj _#7 (eqtrans Heql (eqsymm Heqr'))) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
exists A.
auto.
Qed.


(* Not included in Rules. *)
Lemma sound_pi_formation_invert1_univ :
  forall G lv a a' b b',
    pseq G (deq (pi a b) (pi a' b') (univ lv))
    -> pseq G (deq a a' (univ lv)).
Proof.
intros G lv a b c d.
revert G.
refine (seq_pseq 4 [] a [] b [hyp_emp] c [hyp_emp] d 1 [] _ _ _); cbn.
intros G Hcla Hclb Hclc Hcld Hseq.
rewrite -> seq_univ in Hseq |- *.
intros i s s' Hs.
so (Hseq i s s' Hs) as (pg & R & Hlvl & Hlvr & Hpil & Hpir & Hpil' & Hpir').
simpsubin Hpil.
simpsubin Hpir.
simpsubin Hpil'.
simpsubin Hpir'.
invert (basic_value_inv _#6 value_pi Hpil).
intros A B Hal Hcl Heqacl.
invert (basic_value_inv _#6 value_pi Hpir).
intros A' B' Har Hcr Heqacr.
so (eqtrans Heqacl (eqsymm Heqacr)) as Heq.
clear Heqacr.
invert (basic_value_inv _#6 value_pi Hpil').
intros A'' B'' Hbl Hdl Heqbdl.
so (eqtrans Heqacl (eqsymm Heqbdl)) as Heq'.
clear Heqbdl.
invert (basic_value_inv _#6 value_pi Hpir').
intros A''' B''' Hbr Hdr Heqbdr.
so (eqtrans Heqacl (eqsymm Heqbdr)) as Heq''.
clear Heqbdr.
subst R.
so (iupi_inj _#7 Heq) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
so (iupi_inj _#7 Heq') as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
so (iupi_inj _#7 Heq'') as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
clear Heq Heq' Heq''.
exists pg, A.
do2 5 split; auto.
Qed.


Lemma sound_pi_formation_invert2 :
  forall G a a' b b',
    pseq G (deqtype (pi a b) (pi a' b'))
    -> pseq (cons (hyp_tm a) G) (deqtype b b').
Proof.
intros G a b c d.
revert G.
refine (seq_pseq_hyp 4 [] a [] b [hyp_emp] c [hyp_emp] d 1 [] [] _ [] [_] _ _); cbn.
intros G Hcla Hclb Hclc Hcld Hseq _.
rewrite -> seq_eqtype in Hseq |- *.
intros i ss ss' Hss.
so (pwctx_cons_invert_simple _#5 Hss) as H; clear Hss.
destruct H as (m & p & s & s' & Hs & Hmp & -> & ->).
so (Hseq i s s' Hs) as (R & Hpil & Hpir & Hpil' & Hpir').
simpsubin Hpil.
simpsubin Hpir.
simpsubin Hpil'.
simpsubin Hpir'.
invert (basic_value_inv _#6 value_pi Hpil).
intros A B Hal Hcl Heqacl.
invert (basic_value_inv _#6 value_pi Hpir).
intros A' B' Har Hcr Heqacr.
so (eqtrans Heqacl (eqsymm Heqacr)) as Heq.
clear Heqacr.
invert (basic_value_inv _#6 value_pi Hpil').
intros A'' B'' Hbl Hdl Heqbdl.
so (eqtrans Heqacl (eqsymm Heqbdl)) as Heq'.
clear Heqbdl.
invert (basic_value_inv _#6 value_pi Hpir').
intros A''' B''' Hbr Hdr Heqbdr.
so (eqtrans Heqacl (eqsymm Heqbdr)) as Heq''.
clear Heqbdr.
subst R.
so (iupi_inj _#7 Heq) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
so (iupi_inj _#7 Heq') as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
so (iupi_inj _#7 Heq'') as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
clear Heq Heq' Heq''.
invertc Hmp.
intros A' Hal' _ Hmp.
so (basic_fun _#7 (interp_increase _#6 (toppg_max _) Hal) Hal'); subst A'.
exists (pi1 B (urelspinj (den A) i m p Hmp)).
simpsub.
do2 3 split.
  {
  invert Hcl.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hmp) as H.
  simpsubin H.
  exact H.
  }

  {
  invert Hcr.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hmp) as H.
  simpsubin H.
  exact H.
  }

  {
  invert Hdl.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hmp) as H.
  simpsubin H.
  exact H.
  }

  {
  invert Hdr.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hmp) as H.
  simpsubin H.
  exact H.
  }
Qed.


(* Not included in Rules. *)
Lemma sound_pi_formation_invert2_univ :
  forall G lv a a' b b',
    pseq G (deq (pi a b) (pi a' b') (univ lv))
    -> pseq (cons (hyp_tm a) G) (deq b b' (univ (subst sh1 lv))).
Proof.
intros G lv a b c d.
revert G.
refine (seq_pseq_hyp 4 [] a [] b [hyp_emp] c [hyp_emp] d 1 [] [] _ [] [_] _ _); cbn.
intros G Hcla Hclb Hclc Hcld Hseq _.
rewrite -> seq_univ in Hseq |- *.
intros i ss ss' Hss.
so (pwctx_cons_invert_simple _#5 Hss) as H; clear Hss.
destruct H as (m & p & s & s' & Hs & Hmp & -> & ->).
so (Hseq i s s' Hs) as (pg & R & Hlvl & Hlvr & Hpil & Hpir & Hpil' & Hpir').
simpsubin Hpil.
simpsubin Hpir.
simpsubin Hpil'.
simpsubin Hpir'.
invert (basic_value_inv _#6 value_pi Hpil).
intros A B Hal Hcl Heqacl.
invert (basic_value_inv _#6 value_pi Hpir).
intros A' B' Har Hcr Heqacr.
so (eqtrans Heqacl (eqsymm Heqacr)) as Heq.
clear Heqacr.
invert (basic_value_inv _#6 value_pi Hpil').
intros A'' B'' Hbl Hdl Heqbdl.
so (eqtrans Heqacl (eqsymm Heqbdl)) as Heq'.
clear Heqbdl.
invert (basic_value_inv _#6 value_pi Hpir').
intros A''' B''' Hbr Hdr Heqbdr.
so (eqtrans Heqacl (eqsymm Heqbdr)) as Heq''.
clear Heqbdr.
subst R.
so (iupi_inj _#7 Heq) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
so (iupi_inj _#7 Heq') as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
so (iupi_inj _#7 Heq'') as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
clear Heq Heq' Heq''.
invertc Hmp.
intros A' Hal' _ Hmp.
so (basic_fun _#7 (interp_increase _#6 (toppg_max _) Hal) Hal'); subst A'.
exists pg, (pi1 B (urelspinj (den A) i m p Hmp)).
simpsub.
do2 5 split; auto.
  {
  invert Hcl.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hmp) as H.
  simpsubin H.
  exact H.
  }

  {
  invert Hcr.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hmp) as H.
  simpsubin H.
  exact H.
  }

  {
  invert Hdl.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hmp) as H.
  simpsubin H.
  exact H.
  }

  {
  invert Hdr.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hmp) as H.
  simpsubin H.
  exact H.
  }
Qed.


Lemma sound_pi_ext :
  forall G a b m n a' a'' b' b'',
    pseq G (deqtype a a)
    -> pseq (cons (hyp_tm a) G) 
         (deq 
            (app (subst sh1 m) (var 0))
            (app (subst sh1 n) (var 0))
            b)
    -> pseq G (deq m m (pi a' b'))
    -> pseq G (deq n n (pi a'' b''))
    -> pseq G (deq m n (pi a b)).
Proof.
intros G a b m n a' a'' b' b''.
revert G.
refine (seq_pseq 4 [] a [hyp_emp] b [] m [] n 4 [] _ [_] _ [] _ [] _ _ _); cbn.
intros G Hcla Hclb Hclm Hcln Hseqa Hseq Hseqm Hseqn.
rewrite -> seq_eqtype in Hseqa.
rewrite -> seq_deq in Hseq, Hseqm, Hseqn |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
assert (forall j p q,
          rel (den A) j p q
          -> pwctx j (dot p s) (dot q s') (cons (hyp_tm a) G)) as Hss.
  {
  intros j p q Hpq.
  assert (j <= i) as Hj.
    {
    rewrite -> HeqA in Hpq.
    destruct Hpq.
    omega.
    }
  apply pwctx_cons_tm_seq; eauto using pwctx_downward.
    {
    eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
    }

    {
    intros j' t t' Ht.
    so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
    eauto.
    }
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as H; eauto using subst_closub_under_permit.
  {
  intros j p q Hpq.
  so (Hseq _#3 (Hss j p q Hpq)) as (R & Hbl & Hbr & _).
  exists R.
  simpsub.
  auto.
  }
destruct H as (B & Hbl & Hbr).
so (Hseqm _#3 Hs) as (R & Hl & _ & Hm & _).
simpsubin Hl.
invert (basic_value_inv _#6 value_pi Hl).
intros C D _ _ <-.
so (urel_closed _#5 Hm) as (Hcl & Hcl').
cbn in Hm.
destruct Hm as (ml & ml' & _ & _ & _ & Hstepml & Hstepmr & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepml Hcl)) as H; cbn in H.
destruct H as (Hclml & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepmr Hcl')) as H; cbn in H.
destruct H as (Hclmr & _).
clear C D Hl Hseqm Hcl Hcl'.
so (Hseqn _#3 Hs) as (R & Hl & _ & Hn & _).
simpsubin Hl.
invert (basic_value_inv _#6 value_pi Hl).
intros C D _ _ <-.
so (urel_closed _#5 Hn) as (Hcl & Hcl').
cbn in Hn.
destruct Hn as (nl & nl' & _ & _ & _ & Hstepnl & Hstepnr & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepnl Hcl)) as H; cbn in H.
destruct H as (Hclnl & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepnr Hcl')) as H; cbn in H.
destruct H as (Hclnr & _).
clear C D Hl Hseqn Hcl Hcl'.
exists (iupi stop i A B).
simpsub.
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_pi; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_pi; auto.
  }

  {
  exists ml, ml'.
  do2 5 split; auto; try prove_hygiene.
  intros j p q Hj Hpq.
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  so (Hseq _#3 (Hss _#3 Hpq)) as (R & Hpb & _ & Hm & _).
  simpsubin Hm.
  invert Hbl.
  intros _ _ Hbact.
  so (Hbact _#3 Hj Hpq) as H; clear Hbact.
  simpsubin H.
  so (basic_fun _#7 Hpb H); subst R; clear H.
  eapply urel_equiv; eauto; try prove_hygiene.
    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun x => app x _)); eauto using step_app1.
      }
    apply star_one.
    apply step_app2.
    }

    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun x => app x _)); eauto using step_app1.
      }
    apply star_one.
    apply step_app2.
    }
  }

  {
  exists nl, nl'.
  do2 5 split; auto; try prove_hygiene.
  intros j p q Hj Hpq.
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  so (Hseq _#3 (Hss _#3 Hpq)) as (R & Hpb & _ & _ & Hn & _).
  simpsubin Hn.
  invert Hbl.
  intros _ _ Hbact.
  so (Hbact _#3 Hj Hpq) as H; clear Hbact.
  simpsubin H.
  so (basic_fun _#7 Hpb H); subst R; clear H.
  eapply urel_equiv; eauto; try prove_hygiene.
    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun x => app x _)); eauto using step_app1.
      }
    apply star_one.
    apply step_app2.
    }

    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun x => app x _)); eauto using step_app1.
      }
    apply star_one.
    apply step_app2.
    }
  }

  {
  exists ml, nl'.
  do2 5 split; auto; try prove_hygiene.
  intros j p q Hj Hpq.
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  so (Hseq _#3 (Hss _#3 Hpq)) as (R & Hpb & _ & _ & _ & Hmn).
  simpsubin Hmn.
  invert Hbl.
  intros _ _ Hbact.
  so (Hbact _#3 Hj Hpq) as H; clear Hbact.
  simpsubin H.
  so (basic_fun _#7 Hpb H); subst R; clear H.
  eapply urel_equiv; eauto; try prove_hygiene.
    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun x => app x _)); eauto using step_app1.
      }
    apply star_one.
    apply step_app2.
    }

    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun x => app x _)); eauto using step_app1.
      }
    apply star_one.
    apply step_app2.
    }
  }
Qed.


Lemma sound_intersect_formation :
  forall G a a' b b',
    pseq G (deqtype a a')
    -> pseq (cons (hyp_tm a) G) (deqtype b b')
    -> pseq G (deqtype (intersect a b) (intersect a' b')).
Proof.
intros G a b c d.
revert G.
refine (seq_pseq 4 [] a [] b [hyp_emp] c [hyp_emp] d 2 [] _ [_] _ _ _); cbn.
intros G Hcla Hclb Hclc Hcld Hseqab Hseqcd.
rewrite -> seq_eqtype in Hseqab, Hseqcd |- *.
intros i s s' Hs.
so (seqctx_impl_closub _#4 (pwctx_impl_seqctx _#4 Hs)) as (Hcls & Hcls').
so (Hseqab _#3 Hs) as (A & Hal & Har & Hbl & Hbr).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional_multi toppg i (den A) (subst (under 1 s) c) (subst (under 1 s') c) (subst (under 1 s) d) (subst (under 1 s') d)) as (C & Hcl & Hcr & Hdl & Hdr); eauto using subst_closub_under_permit.
  {
  intros j m p Hmp.
  assert (pwctx j (dot m s) (dot p s') (cons (hyp_tm a) G)) as Hss.
    {
    assert (j <= i) as Hj.
      {
      rewrite -> HeqA in Hmp.
      destruct Hmp.
      omega.
      }
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
      }

      {
      intros j' t t' Ht.
      so (Hseqab _#3 Ht) as (R & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqcd _#3 Hss) as (R & Hcl & Hcr & Hdl & Hdr).
  exists R.
  simpsub.
  auto.
  }
exists (iuintersect stop i A C).
simpsub.
do2 3 split; auto;
apply interp_eval_refl;
apply interp_intersect; auto.
Qed.


Lemma sound_intersect_formation_univ :
  forall G lv a a' b b',
    pseq G (deq a a' (univ lv))
    -> pseq (cons (hyp_tm a) G) (deq b b' (univ (subst sh1 lv)))
    -> pseq G (deq (intersect a b) (intersect a' b') (univ lv)).
Proof.
intros G lv a b c d.
revert G.
refine (seq_pseq 5 [] a [] b [hyp_emp] c [hyp_emp] d [] lv 2 [] _ [_] _ _ _); cbn.
intros G Hcla Hclb Hclc Hcld Hcllv Hseqab Hseqcd.
rewrite -> seq_univ in Hseqab, Hseqcd |- *.
intros i s s' Hs.
so (seqctx_impl_closub _#4 (pwctx_impl_seqctx _#4 Hs)) as (Hcls & Hcls').
so (Hseqab _#3 Hs) as (pg & A & Hlvl & Hlvr & Hal & Har & Hbl & Hbr).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional_multi pg i (den A) (subst (under 1 s) c) (subst (under 1 s') c) (subst (under 1 s) d) (subst (under 1 s') d)) as (C & Hcl & Hcr & Hdl & Hdr); eauto using subst_closub_under_permit.
  {
  intros j m p Hmp.
  assert (pwctx j (dot m s) (dot p s') (cons (hyp_tm a) G)) as Hss.
    {
    assert (j <= i) as Hj.
      {
      rewrite -> HeqA in Hmp.
      destruct Hmp.
      omega.
      }
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
      }

      {
      intros j' t t' Ht.
      so (Hseqab _#3 Ht) as (pg' & R & _ & _ & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqcd _#3 Hss) as (pg' & R & Hlvl' & _ & Hcl & Hcr & Hdl & Hdr).
  simpsubin Hlvl'.
  so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
  exists R.
  simpsub.
  auto.
  }
exists pg, (iuintersect stop i A C).
simpsub.
do2 5 split; auto;
apply interp_eval_refl;
apply interp_intersect; auto.
Qed.


Lemma sound_intersect_intro :
  forall G a b m n,
    pseq G (deqtype a a)
    -> pseq (cons (hyp_tm a) G) (deq (subst sh1 m) (subst sh1 n) b)
    -> pseq G (deq m n (intersect a b)).
Proof.
intros G a b m n.
revert G.
refine (seq_pseq 4 [] a [hyp_emp] b [] m [] n 2 [] _ [_] _ _ _); cbn.
intros G Hcla Hclb Hclm Hcln Hseqa Hseqmn.
rewrite -> seq_eqtype in Hseqa.
rewrite -> seq_deq in Hseqmn |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
assert (forall j p q,
          rel (den A) j p q
          -> pwctx j (dot p s) (dot q s') (cons (hyp_tm a) G)) as Hss.
  {
  intros j p q Hpq.
  assert (j <= i) as Hj.
    {
    rewrite -> HeqA in Hpq.
    destruct Hpq.
    omega.
    }
  apply pwctx_cons_tm_seq; eauto using pwctx_downward.
    {
    eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
    }

    {
    intros j' t t' Ht.
    so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
    eauto.
    }
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as H; eauto using subst_closub_under_permit.
  {
  intros j p q Hpq.
  so (Hseqmn _#3 (Hss j p q Hpq)) as (R & Hbl & Hbr & _).
  exists R.
  simpsub.
  auto.
  }
destruct H as (B & Hbl & Hbr).
exists (iuintersect stop i A B).
simpsub.
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_intersect; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_intersect; auto.
  }

  {
  do2 3 split; auto.
    {
    eapply subst_closub; eauto.
    }

    {
    eapply subst_closub; eauto.
    }
  intros j p q Hj Hpq.
  so (Hseqmn _#3 (Hss _#3 Hpq)) as (R & Hpb & _ & Hm & _).
  invert Hbl.
  intros _ _ Hbact.
  so (Hbact _#3 Hj Hpq) as H.
  simpsubin H.
  so (basic_fun _#7 Hpb H); subst R; clear H.
  simpsubin Hm.
  exact Hm.
  }

  {
  do2 3 split; auto.
    {
    eapply subst_closub; eauto.
    }

    {
    eapply subst_closub; eauto.
    }
  intros j p q Hj Hpq.
  so (Hseqmn _#3 (Hss _#3 Hpq)) as (R & Hpb & _ & _ & Hn & _).
  invert Hbl.
  intros _ _ Hbact.
  so (Hbact _#3 Hj Hpq) as H.
  simpsubin H.
  so (basic_fun _#7 Hpb H); subst R; clear H.
  simpsubin Hn.
  exact Hn.
  }

  {
  do2 3 split; auto.
    {
    eapply subst_closub; eauto.
    }

    {
    eapply subst_closub; eauto.
    }
  intros j p q Hj Hpq.
  so (Hseqmn _#3 (Hss _#3 Hpq)) as (R & Hpb & _ & _ & _ & Hmn).
  invert Hbl.
  intros _ _ Hbact.
  so (Hbact _#3 Hj Hpq) as H.
  simpsubin H.
  so (basic_fun _#7 Hpb H); subst R; clear H.
  simpsubin Hmn.
  exact Hmn.
  }
Qed.


Lemma sound_intersect_elim :
  forall G a b m n p q,
    pseq G (deq m n (intersect a b))
    -> pseq G (deq p q a)
    -> pseq G (deq m n (subst1 p b)).
Proof.
intros G a b m n p q.
revert G.
refine (seq_pseq 4 [] a [hyp_emp] b [] m [] n 2 [] _ [] _ _ _); cbn.
intros G Hcla Hclb Hclm Hcln Hseqmn Hseqpq.
rewrite -> seq_deq in Hseqmn, Hseqpq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmn _#3 Hs) as (R & Hpil & Hpir & Hm & Hn & Hmn).
clear Hseqmn.
so (Hseqpq _#3 Hs) as (A & Hal & Har & Hp & Hq & Hpq).
clear Hseqpq.
simpsubin Hpil.
simpsubin Hpir.
invert (basic_value_inv _#6 value_intersect Hpil).
intros A' B Hal' Hbl Heql.
so (basic_fun _#7 Hal Hal'); subst A'.
invert (basic_value_inv _#6 value_intersect Hpir).
intros A' B' Har' Hbr Heqr.
so (basic_fun _#7 Har Har'); subst A'.
so (eqtrans Heql (eqsymm Heqr)) as Heq.
clear Heqr.
subst R.
so (eq_dep_impl_eq_snd _#5 (iuintersect_inj _#7 Heq)); subst B'.
exists (pi1 B (urelspinj _#4 Hp)).
simpsub.
do2 4 split.
  {
  invert Hbl.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hp) as H.
  simpsubin H.
  exact H.
  }

  {
  invert Hbr.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hp) as H.
  simpsubin H.
  exact H.
  }

  {
  cbn in Hm.
  decompose Hm.
  intros _ _ _ Hact.
  apply Hact; auto.
  }

  {
  cbn in Hn.
  decompose Hn.
  intros _ _ _ Hact.
  apply Hact; auto.
  }

  {
  cbn in Hmn.
  decompose Hmn.
  intros _ _ _ Hact.
  apply Hact; auto.
  }
Qed.


Lemma sound_intersect_formation_invert1 :
  forall G a a' b b',
    pseq G (deqtype (intersect a b) (intersect a' b'))
    -> pseq G (deqtype a a').
Proof.
intros G a b c d.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hpil & Hpir & Hpil' & Hpir').
simpsubin Hpil.
simpsubin Hpir.
simpsubin Hpil'.
simpsubin Hpir'.
invert (basic_value_inv _#6 value_intersect Hpil).
intros A B Hal Hbl Heql.
invert (basic_value_inv _#6 value_intersect Hpir).
intros A' B' Har Hbr Heqr.
so (iuintersect_inj _#7 (eqtrans Heql (eqsymm Heqr))) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
invert (basic_value_inv _#6 value_intersect Hpil').
intros A' B' Hal' Hbl' Heql'.
so (iuintersect_inj _#7 (eqtrans Heql (eqsymm Heql'))) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
invert (basic_value_inv _#6 value_intersect Hpir').
intros A' B' Har' Hbr' Heqr'.
so (iuintersect_inj _#7 (eqtrans Heql (eqsymm Heqr'))) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
exists A.
auto.
Qed.


Lemma sound_intersect_formation_invert2 :
  forall G a a' b b',
    pseq G (deqtype (intersect a b) (intersect a' b'))
    -> pseq (cons (hyp_tm a) G) (deqtype b b').
Proof.
intros G a b c d.
revert G.
refine (seq_pseq_hyp 4 [] a [] b [hyp_emp] c [hyp_emp] d 1 [] [] _ [] [_] _ _); cbn.
intros G Hcla Hclb Hclc Hcld Hseq _.
rewrite -> seq_eqtype in Hseq |- *.
intros i ss ss' Hss.
so (pwctx_cons_invert_simple _#5 Hss) as H; clear Hss.
destruct H as (m & p & s & s' & Hs & Hmp & -> & ->).
so (Hseq i s s' Hs) as (R & Hpil & Hpir & Hpil' & Hpir').
simpsubin Hpil.
simpsubin Hpir.
simpsubin Hpil'.
simpsubin Hpir'.
invert (basic_value_inv _#6 value_intersect Hpil).
intros A B Hal Hcl Heqacl.
invert (basic_value_inv _#6 value_intersect Hpir).
intros A' B' Har Hcr Heqacr.
so (eqtrans Heqacl (eqsymm Heqacr)) as Heq.
clear Heqacr.
invert (basic_value_inv _#6 value_intersect Hpil').
intros A'' B'' Hbl Hdl Heqbdl.
so (eqtrans Heqacl (eqsymm Heqbdl)) as Heq'.
clear Heqbdl.
invert (basic_value_inv _#6 value_intersect Hpir').
intros A''' B''' Hbr Hdr Heqbdr.
so (eqtrans Heqacl (eqsymm Heqbdr)) as Heq''.
clear Heqbdr.
subst R.
so (iuintersect_inj _#7 Heq) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
so (iuintersect_inj _#7 Heq') as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
so (iuintersect_inj _#7 Heq'') as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
clear Heq Heq' Heq''.
invertc Hmp.
intros A' Hal' _ Hmp.
so (basic_fun _#7 (interp_increase _#6 (toppg_max _) Hal) Hal'); subst A'.
exists (pi1 B (urelspinj (den A) i m p Hmp)).
simpsub.
do2 3 split.
  {
  invert Hcl.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hmp) as H.
  simpsubin H.
  exact H.
  }

  {
  invert Hcr.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hmp) as H.
  simpsubin H.
  exact H.
  }

  {
  invert Hdl.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hmp) as H.
  simpsubin H.
  exact H.
  }

  {
  invert Hdr.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hmp) as H.
  simpsubin H.
  exact H.
  }
Qed.
