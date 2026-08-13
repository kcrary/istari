
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
Require Import PageType.
Require Import SemanticsPi.
Require Import SemanticsQuotient.
Require Import SemanticsSymmetrical.
Require Import Urelsp.
Require Import SemanticsSigma.
Require Import SoundQuotient.
Require Import SoundUtil.
Require Import Ceiling.
Require Import Truncate.
Require Import ProperFun.
Require Import ProperDownward.
Require Import ProperEquiv.
Require Import Equivalence.
Require Import Equivalences.
Require Import SoundSequal.
Require Import SemanticsNative.
Require Import SemanticsEqual.
Require Import SemanticsSet.
Require Import SemanticsEqual.
Require Import SemanticsPartial.
Require Import Subsumption.


Local Ltac prove_hygiene :=
  repeat (first [ eapply subst_closub; eauto
                | apply closub_dot
                | apply hygiene_auto; cbn; repeat2 split; auto
                ]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1;
  try (apply hygiene_var; cbn; auto; done).


Lemma rel_from_ceiling :
  forall w (A B : @wurel w) i m n,
    ceiling (S i) A = ceiling (S i) B
    -> rel A i m n
    -> rel B i m n.
Proof.
intros w A B i m n Heq Hmn.
cut (rel (ceiling (S i) B) i m n).
  {
  intro H.
  destruct H; auto.
  }
rewrite <- Heq.
split; auto.
Qed.


Lemma seq_symmetrical :
  forall G a,
    seq G (deq triv triv (symmetrical a))
    <-> forall i s s',
          pwctx i s s' G
          -> exists R,
               interp toppg true i (subst s a) R
               /\ interp toppg false i (subst s' a) R
               /\ (forall j m p,
                     j <= i
                     -> rel (den R) j m p
                     -> rel (den R) j m m /\ rel (den R) j p p).
Proof.
intros G a.
split.

(* out *)
{
intros Hseq.
rewrite -> seq_deq in Hseq.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hl & Hr & Hsat & _).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_symmetrical Hl).
intros A Hal Heql.
invert (basic_value_inv _#6 value_symmetrical Hr).
intros A' Har Heqr.
so (iusymmetrical_inj _#4 (eqtrans Heql (eqsymm Heqr))).
subst A'.
clear Heqr.
subst R.
exists A.
do2 2 split; auto.
simpsubin Hsat.
cbn in Hsat.
decompose Hsat.
intros Hprop _ _ _ _ _.
intros j m p Hj Hmp.
assert (j < S i) as Hj' by omega.
so (Hprop i (le_refl _) j m p (conj Hj' Hmp)) as ((_ & Hm) & (_ & Hp)).
auto.
}

{
intro Hseq.
rewrite -> seq_deq.
intros i s s' Hs.
so (Hseq _#3 Hs) as (A & Hal & Har & Hmet).
exists (iusymmetrical stop i A).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl.
  apply interp_symmetrical; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_symmetrical; auto.
  }
cut (rel (den (iusymmetrical stop i A)) i triv triv).
  {
  auto.
  }
cbn.
do2 5 split; auto using star_refl; prove_hygiene.
intros j Hj k m p (Hk & Hmp).
assert (k <= i) as Hki by omega.
so (Hmet k m p Hki Hmp) as (Hm & Hp).
split; split; auto.
}
Qed.


Lemma sound_symmetrical_formation :
  forall G a a',
    pseq G (deqtype a a')
    -> pseq G (deqtype (symmetrical a) (symmetrical a')).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseqab.
rewrite -> seq_eqtype in Hseqab |- *.
intros i s s' Hs.
so (Hseqab i s s' Hs) as (A & Hal & Har & Hbl & Hbr).
exists (iusymmetrical stop i A).
simpsub.
do2 3 split; apply interp_eval_refl; apply interp_symmetrical; auto.
Qed.


Lemma sound_symmetrical_formation_univ :
  forall G lv a a',
    pseq G (deq a a' (univ lv))
    -> pseq G (deq (symmetrical a) (symmetrical a') (univ lv)).
Proof.
intros G lv a b.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseqab.
rewrite -> seq_univ in Hseqab |- *.
intros i s s' Hs.
so (Hseqab i s s' Hs) as (pg & A & Hlvl & Hlvr & Hal & Har & Hbl & Hbr).
exists pg, (iusymmetrical stop i A).
simpsub.
do2 5 split; auto; apply interp_eval_refl; apply interp_symmetrical; auto.
Qed.


Lemma sound_symmetrical_formation_invert :
  forall G a b,
    pseq G (deqtype (symmetrical a) (symmetrical b))
    -> pseq G (deqtype a b).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hmet.
rewrite -> seq_eqtype in Hmet |- *.
intros i s s' Hs.
so (Hmet _#3 Hs) as (R & Hmetal & Hmetar & Hmetbl & Hmetbr).
simpsubin Hmetal.
simpsubin Hmetar.
simpsubin Hmetbl.
simpsubin Hmetbr.
invert (basic_value_inv _#6 value_symmetrical Hmetal).
intros A Hal Heql.
invert (basic_value_inv _#6 value_symmetrical Hmetar).
intros A' Har Heqr.
so (iusymmetrical_inj _#4 (eqtrans Heql (eqsymm Heqr))).
subst A'.
clear Heqr.
invert (basic_value_inv _#6 value_symmetrical Hmetbl).
intros A' Hbl Heq.
so (iusymmetrical_inj _#4 (eqtrans Heql (eqsymm Heq))).
subst A'.
clear Heq.
invert (basic_value_inv _#6 value_symmetrical Hmetbr).
intros A' Hbr Heq.
so (iusymmetrical_inj _#4 (eqtrans Heql (eqsymm Heq))).
subst A'.
clear Heq.
exists A.
do2 3 split; auto.
Qed.


Lemma sound_symmetrical_eta :
  forall G a p,
    pseq G (deq p p (symmetrical a))
    -> pseq G (deq p triv (symmetrical a)).
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
invert (basic_value_inv _#6 value_symmetrical Hrobl).
intros A _ <-.
destruct Htrue as (Hsymmetrical & _ & Hclsp & Hclsp' & Hp & Hp').
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


Lemma sound_symmetrical_eta_hyp :
  forall G1 G2 a m n b,
    pseq (substctx (dot triv id) G2 ++ G1) (deq m n (subst (under (length G2) (dot triv id)) b))
    -> pseq (G2 ++ hyp_tm (symmetrical a) :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) b).
Proof.
intros G1 G2 a m n b Hseq.
eapply sound_property_eta_hyp; eauto.
intros s pg z i R H.
simpsubin H.
invert (basic_value_inv _#6 value_symmetrical H).
intros A _ <-.
do 3 eexists.
reflexivity.
Qed.


Lemma sound_flat_symmetrical :
  forall G a,
    flat a
    -> pseq G (deqtype a a)
    -> pseq G (deq triv triv (symmetrical a)).
Proof.
intros G a Hflat.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq.
rewrite -> seq_deq.
intros i s s' Hs.
so (Hseq _#3 Hs) as (A & Hal & Har & _).
exists (iusymmetrical stop i A).
simpsub.
assert (symmetrical_property stop (den A) i) as Hmet.
  {
  intros j Hj.
  intros k m p Hmp.
  destruct Hmp as (Hk & Hmp).
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  so (Hflat _#6 Hal Hmp) as (th & _ & Hm & Hp).
  set (q := oper [] th rw_nil) in Hm, Hp.
  split.
    {
    split; auto.
    refine (urel_equiv_2 _#6 Hclm _ Hmp).
    apply (equiv_trans _ _ q).
      {
      apply steps_equiv; auto.
      }

      {
      apply equiv_symm.
      apply steps_equiv; auto.
      }
    }

    {
    split; auto.
    refine (urel_equiv_1 _#6 Hclp _ Hmp).
    apply (equiv_trans _ _ q).
      {
      apply steps_equiv; auto.
      }

      {
      apply equiv_symm.
      apply steps_equiv; auto.
      }
    }
  }
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_symmetrical; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_symmetrical; auto.
  }

  {
  do2 4 split; auto using star_refl; try prove_hygiene.
  }

  {
  do2 4 split; auto using star_refl; try prove_hygiene.
  }

  {
  do2 4 split; auto using star_refl; try prove_hygiene.
  }
Qed.


Lemma sound_unitary_symmetrical :
  forall G a,
    pseq G (dsubtype a unittp)
    -> pseq G (deq triv triv (symmetrical a)).
Proof.
intros G a.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_subtype in Hseq.
rewrite -> seq_symmetrical.
intros i s s' Hs.
so (Hseq _#3 Hs) as (A & R & Hal & Har & Hunitl & _ & Hcont).
simpsubin Hunitl.
so (basic_fun _#7 Hunitl (interp_eval_refl _#6 (interp_unit _#4))).
subst R.
exists A.
do2 2 split; auto.
intros j m p Hj Hmp.
so (Hcont _#3 Hj Hmp) as Hmp'.
cbn in Hmp'.
decompose Hmp'.
intros _ _ Hclm Hclp Hsteps Hsteps'.
split.
  {
  refine (urel_equiv_2 _#6 Hclm _ Hmp).
  apply (equiv_trans _ _ triv).
    {
    apply steps_equiv; auto.
    }

    {
    apply equiv_symm.
    apply steps_equiv; auto.
    }
  }

  {
  refine (urel_equiv_1 _#6 Hclp _ Hmp).
  apply (equiv_trans _ _ triv).
    {
    apply steps_equiv; auto.
    }

    {
    apply equiv_symm.
    apply steps_equiv; auto.
    }
  }
Qed.



Lemma sound_booltp_symmetrical :
  forall G,
    pseq G (deq triv triv (symmetrical booltp)).
Proof.
intros G.
apply sound_flat_symmetrical.
  {
  intros i j s A m p Hal Hmp.
  simpsubin Hal.
  so (basic_fun _#7 Hal (interp_eval_refl _#6 (interp_bool _#4))).
  subst A.
  cbn in Hmp.
  decompose Hmp.
  intros _ _ _ Hsteps.
  destruct Hsteps as [(Hstepsm & Hstepsp) | (Hstepsm & Hstepsp)].
    {
    exists (oper_native_elem _ (Native.native_bool true)).
    do2 2 split; auto.
    apply canon_native_elem.
    }

    {
    exists (oper_native_elem _ (Native.native_bool false)).
    do2 2 split; auto.
    apply canon_native_elem.
    }
  }

  {
  revert G.
  refine (seq_pseq 0 0 _ _); cbn.
  intro G.
  rewrite -> seq_eqtype.
  intros i s s' Hs.
  exists (iubase (SemanticsSimple.bool_urel stop i)).
  simpsub.
  do2 3 split; apply interp_eval_refl; apply interp_bool.
  }
Qed.


Lemma sound_nativetp_symmetrical :
  forall A f G,
    pseq G (deq triv triv (symmetrical (nativetp A f))).
Proof.
intros A f G.
apply sound_flat_symmetrical.
  {
  intros i j s B m p Hb Hmp.
  simpsubin Hb.
  invert (basic_value_inv _#6 (value_nativetp _ _) Hb).
  intros <-.
  cbn in Hmp.
  decompose Hmp.
  intros Hj Hclm Hclp x Hstepsm Hstepsp.
  exists (oper_native_elem _ (f x)).
  do2 2 split; auto.
  apply canon_native_elem.
  }
  
  {
  revert G.
  refine (seq_pseq 0 0 _ _); cbn.
  intro G.
  rewrite -> seq_eqtype.
  intros i s s' Hs.
  exists (iubase (native_urel A f stop i)).
  simpsub.
  do2 3 split; apply interp_eval_refl; apply interp_native.
  }
Qed.


Lemma sound_nattp_symmetrical :
  forall G,
    pseq G (deq triv triv (symmetrical nattp)).
Proof.
refine (seq_pseq 0 0 _ _); cbn.
intro G.
rewrite -> seq_symmetrical.
intros i s s' Hs.
exists (nattp_def top i).
simpsub.
assert (top <<= stop) as Htopstop.
  {
  apply succ_nodecrease.
  }
do2 2 split.
  {
  apply interp_nattp.
  }

  {
  apply interp_nattp.
  }

  {
  intros j m p Hj Hmp.
  rewrite -> nattp_nat_urel in Hmp |- *; auto.
  destruct Hmp as (n & Hki & Hm & Hp).
  split.
    {
    exists n.
    auto.
    }

    {
    exists n.
    auto.
    }
  }
Qed.


Lemma sound_tarrow_symmetrical :
  forall G a b,
    pseq G (deq triv triv (symmetrical a))
    -> pseq G (deq triv triv (symmetrical b))
    -> pseq G (deq triv triv (symmetrical (tarrow a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqa Hseqb.
rewrite -> seq_symmetrical in Hseqa, Hseqb |- *.
intros i s s' Hs.
so (Hseqa _#3 Hs) as (A & Hal & Har & Hmeta).
so (Hseqb _#3 Hs) as (B & Hbl & Hbr & Hmetb).
exists (iuarrow stop i A B).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl.
  apply interp_tarrow; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_tarrow; auto.
  }
intros j m p Hj Hmp.
  cbn in Hmp.
  decompose Hmp.
  intros l l' Hki Hclm Hclp Hsteps Hsteps' Hact.
  split.
    {
    exists l, l.
    do2 5 split; auto.
    intros k n q Hk Hnq.
    so (Hmeta k n q (le_trans _#3 Hk Hj) Hnq) as (Hn & Hq).
    so (urel_zigzag _#7 Hq Hnq Hn) as Hqn.
    so (Hact _#3 Hk Hn) as Hnl_nl'.
    so (Hact _#3 Hk Hqn) as Hql_nl'.
    so (Hmetb k (subst1 q l) (subst1 n l') (le_trans _#3 Hk Hj) Hql_nl') as (Hql_ql & _).
    eapply urel_zigzag; eauto.
    }

    {
    exists l', l'.
    do2 5 split; auto.
    intros k n q Hk Hnq.
    so (Hmeta k n q (le_trans _#3 Hk Hj) Hnq) as (Hn & Hq).
    so (urel_zigzag _#7 Hq Hnq Hn) as Hqn.
    so (Hact _#3 Hk Hq) as Hql_ql'.
    so (Hact _#3 Hk Hqn) as Hql_nl'.
    so (Hmetb k (subst1 q l) (subst1 n l') (le_trans _#3 Hk Hj) Hql_nl') as (_ & Hnl'_nl').
    apply (urel_zigzag _ _ _ _ (subst1 n l') (subst1 q l)); auto.
    }
Qed.


Lemma sound_pi_symmetrical :
  forall G a b,
    pseq G (deq triv triv (symmetrical a))
    -> pseq (hyp_tm a :: G) (deq triv triv (symmetrical b))
    -> pseq G (deq triv triv (symmetrical (pi a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 1 [hyp_emp] b 2 [] _ [_] _ _ _); cbn.
intros G Hclb Hseqa Hseqb.
rewrite -> seq_symmetrical in Hseqa, Hseqb |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & Hmeta).
assert (forall j m p,
          rel (den A) j m p
          -> pwctx j (dot m s) (dot p s') (hyp_tm a :: G)) as Hextend.
  {
  intros j m p Hmp.
  so (basic_member_index _#9 Hal Hmp) as Hj.
  apply pwctx_cons_tm_seq.
    {
    eapply pwctx_downward; eauto.
    }

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
    intros k t t' Ht.
    so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
    eauto.
    }
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr).
  {
  setoid_rewrite -> (basic_impl_iutruncate _#6 Hal) at 1.
  reflexivity.
  }

  {
  eapply subst_closub_under_permit; eauto.
  }

  {
  eapply subst_closub_under_permit; eauto.
  }

  {
  intros j m p Hmp.
  so (Hextend _#3 Hmp) as Hs'.
  so (Hseqb _#3 Hs') as (B & Hbl & Hbr & _).
  exists B.
  simpsub.
  auto.
  }
exists (iupi stop i A B).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl.
  apply interp_pi; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_pi; auto.
  }
intros j m p Hj Hmp.
cbn in Hmp.
decompose Hmp.
intros l l' _ Hclm Hclp Hstepsm Hstepsp Hact.
split; auto.
  {
  exists l, l.
  do2 5 split; auto.
  intros k n q Hk Hnq.
  invert Hbl.
  intros _ _ Hbact.
  so (le_trans _#3 Hk Hj) as Hki.
  so (Hbact _#3 Hki Hnq) as Hinterp.
  simpsubin Hinterp.
  so (Hseqb _#3 (Hextend _#3 Hnq)) as (Bn & Hbnl & _ & Hmetbn).
  so (basic_fun _#7 Hinterp Hbnl).
  subst Bn.
  clear Hbnl.
  so (Hmeta _#3 Hki Hnq) as (Hn & Hq).
  so (urel_zigzag _#7 Hq Hnq Hn) as Hqn.
  so (Hact k n n Hk Hn) as Hnlnl'.
  so (Hact k q n Hk Hqn) as Hqlnl'.
  exploit (Hmetbn k (subst1 q l) (subst1 n l')) as (Hql & _); auto.
    {
    force_exact Hqlnl'.
    f_equal.
    f_equal.
    f_equal.
    apply urelspinj_equal; auto.
    }
  refine (urel_zigzag _ _ _ _ (subst1 n l') (subst1 q l) _ _ _ _).
    {
    force_exact Hnlnl'.
    f_equal.
    f_equal.
    f_equal.
    apply urelspinj_equal; auto.
    }

    {
    force_exact Hqlnl'.
    f_equal.
    f_equal.
    f_equal.
    apply urelspinj_equal; auto.
    }

    {
    exact Hql.
    }
  }

  {
  exists l', l'.
  do2 5 split; auto.
  intros k n q Hk Hnq.
  invert Hbl.
  intros _ _ Hbact.
  so (le_trans _#3 Hk Hj) as Hki.
  so (Hbact _#3 Hki Hnq) as Hinterp.
  simpsubin Hinterp.
  so (Hseqb _#3 (Hextend _#3 Hnq)) as (Bn & Hbnl & _ & Hmetbn).
  so (basic_fun _#7 Hinterp Hbnl).
  subst Bn.
  clear Hbnl.
  so (Hmeta _#3 Hki Hnq) as (Hn & Hq).
  so (urel_zigzag _#7 Hq Hnq Hn) as Hqn.
  so (Hact k n n Hk Hn) as Hnlnl'.
  so (Hact k n q Hk Hnq) as Hnlql'.
  exploit (Hmetbn k (subst1 n l) (subst1 n l')) as (_ & Hnl'); auto.
    {
    force_exact Hnlnl'.
    f_equal.
    f_equal.
    f_equal.
    apply urelspinj_equal; auto.
    }
  refine (urel_zigzag _ _ _ _ (subst1 n l') (subst1 n l) _ _ _ _).
    {
    exact Hnl'.
    }

    {
    force_exact Hnlnl'.
    f_equal.
    f_equal.
    f_equal.
    apply urelspinj_equal; auto.
    }

    {
    exact Hnlql'.
    }
  }
Qed.


Lemma sound_intersect_symmetrical :
  forall G a b,
    pseq G (deqtype a a)
    -> pseq (hyp_tm a :: G) (deq triv triv (symmetrical b))
    -> pseq G (deq triv triv (symmetrical (intersect a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 1 [hyp_emp] b 2 [] _ [_] _ _ _); cbn.
intros G Hclb Hseqa Hseqb.
rewrite -> seq_symmetrical in Hseqb |- *.
rewrite -> seq_eqtype in Hseqa.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
assert (forall j m p,
          rel (den A) j m p
          -> pwctx j (dot m s) (dot p s') (hyp_tm a :: G)) as Hextend.
  {
  intros j m p Hmp.
  so (basic_member_index _#9 Hal Hmp) as Hj.
  apply pwctx_cons_tm_seq.
    {
    eapply pwctx_downward; eauto.
    }

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
    intros k t t' Ht.
    so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
    eauto.
    }
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr).
  {
  setoid_rewrite -> (basic_impl_iutruncate _#6 Hal) at 1.
  reflexivity.
  }

  {
  eapply subst_closub_under_permit; eauto.
  }

  {
  eapply subst_closub_under_permit; eauto.
  }

  {
  intros j m p Hmp.
  so (Hextend _#3 Hmp) as Hs'.
  so (Hseqb _#3 Hs') as (B & Hbl & Hbr & _).
  exists B.
  simpsub.
  auto.
  }
exists (iuintersect stop i A B).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl.
  apply interp_intersect; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_intersect; auto.
  }
intros j m p Hj Hmp.
cbn in Hmp.
decompose Hmp.
intros _ Hclm Hclp Hact.
split.
  {
  do2 3 split; auto.
  intros k n q Hk Hnq.
  invert Hbl.
  intros _ _ Hbact.
  so (le_trans _#3 Hk Hj) as Hki.
  so (Hbact _#3 Hki Hnq) as Hinterp.
  simpsubin Hinterp.
  so (Hseqb _#3 (Hextend _#3 Hnq)) as (Bn & Hbnl & _ & Hmetbn).
  so (basic_fun _#7 Hinterp Hbnl).
  subst Bn.
  clear Hbnl.
  so (Hact k n q Hk Hnq) as Hmp.
  exploit (Hmetbn k m p (le_refl _) Hmp) as (Hm & Hp).
  exact Hm.
  }

  {
  do2 3 split; auto.
  intros k n q Hk Hnq.
  invert Hbr.
  intros _ _ Hbact.
  so (le_trans _#3 Hk Hj) as Hki.
  so (Hbact _#3 Hki Hnq) as Hinterp.
  simpsubin Hinterp.
  so (Hseqb _#3 (Hextend _#3 Hnq)) as (Bn & _ & Hbnr & Hmetbn).
  so (basic_fun _#7 Hinterp Hbnr).
  subst Bn.
  clear Hbnr.
  so (Hact k n q Hk Hnq) as Hmp.
  exploit (Hmetbn k m p (le_refl _) Hmp) as (Hm & Hp).
  exact Hp.
  }
Qed.



Lemma sound_prod_symmetrical :
  forall G a b,
    pseq G (deq triv triv (symmetrical a))
    -> pseq G (deq triv triv (symmetrical b))
    -> pseq G (deq triv triv (symmetrical (prod a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqa Hseqb.
rewrite -> seq_deq in Hseqa, Hseqb |- *.
intros i s s' Hs.
so (Hseqa _#3 Hs) as (R & Hl & Hr & Hsata & _).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_symmetrical Hl).
intros A Hal Heql.
invert (basic_value_inv _#6 value_symmetrical Hr).
intros A' Har Heqr.
so (iusymmetrical_inj _#4 (eqtrans Heql (eqsymm Heqr))).
subst A'.
clear Heqr Hl Hr.
subst R.
simpsubin Hsata.
so (Hseqb _#3 Hs) as (R & Hl & Hr & Hsatb & _).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_symmetrical Hl).
intros B Hbl Heql.
invert (basic_value_inv _#6 value_symmetrical Hr).
intros B' Hbr Heqr.
so (iusymmetrical_inj _#4 (eqtrans Heql (eqsymm Heqr))).
subst B'.
clear Heqr Hl Hr.
subst R.
simpsubin Hsatb.
cbn in Hsata, Hsatb.
decompose Hsata.
intros Hmeta _ _ _ _ _.
decompose Hsatb.
intros Hmetb _ _ _ _ _.
exists (iusymmetrical stop i (iuprod stop A B)).
simpsub.
assert (symmetrical_property stop (prod_urel stop (den A) (den B)) i) as Hprop.
  {
  intros j Hj.
  intros k m p Hmp.
  destruct Hmp as (Hk & Hmp).
  cbn in Hmp.
  decompose Hmp.
  intros m1 p1 m2 p2 Hclm Hclp Hstepsm Hstepsp Hmp1 Hmp2.
  so (Hmeta j Hj k m1 p1 (conj Hk Hmp1)) as ((_ & Hmm1) & (_ & Hpp1)).
  so (Hmetb j Hj k m2 p2 (conj Hk Hmp2)) as ((_ & Hmm2) & (_ & Hpp2)).
  split.
    {
    split; auto.
    exists m1, m1, m2, m2.
    do2 5 split; auto.
    }

    {
    split; auto.
    exists p1, p1, p2, p2.
    do2 5 split; auto.
    }
  }
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_symmetrical.
  apply interp_eval_refl.
  apply interp_prod; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_symmetrical.
  apply interp_eval_refl.
  apply interp_prod; auto.
  }

  {
  cbn.
  do2 4 split; auto using star_refl; try prove_hygiene.
  }

  {
  cbn.
  do2 4 split; auto using star_refl; try prove_hygiene.
  }

  {
  cbn.
  do2 4 split; auto using star_refl; try prove_hygiene.
  }
Qed.


Lemma sound_sigma_symmetrical :
  forall G a b,
    pseq G (deq triv triv (symmetrical a))
    -> pseq (hyp_tm a :: G) (deq triv triv (symmetrical b))
    -> pseq G (deq triv triv (symmetrical (sigma a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 1 [hyp_emp] b 2 [] _ [_] _ _ _); cbn.
intros G Hclb Hseqa Hseqb.
rewrite -> seq_symmetrical in Hseqa, Hseqb |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & Hmeta).
assert (forall j m p,
          rel (den A) j m p
          -> pwctx j (dot m s) (dot p s') (hyp_tm a :: G)) as Hextend.
  {
  intros j m p Hmp.
  so (basic_member_index _#9 Hal Hmp) as Hj.
  apply pwctx_cons_tm_seq.
    {
    eapply pwctx_downward; eauto.
    }

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
    intros k t t' Ht.
    so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
    eauto.
    }
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr).
  {
  setoid_rewrite -> (basic_impl_iutruncate _#6 Hal) at 1.
  reflexivity.
  }

  {
  eapply subst_closub_under_permit; eauto.
  }

  {
  eapply subst_closub_under_permit; eauto.
  }

  {
  intros j m p Hmp.
  so (Hextend _#3 Hmp) as Hs'.
  so (Hseqb _#3 Hs') as (B & Hbl & Hbr & _).
  exists B.
  simpsub.
  auto.
  }
exists (iusigma stop A B).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl.
  apply interp_sigma; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_sigma; auto.
  }
intros j m p Hj Hmp.
cbn in Hmp.
decompose Hmp.
intros m1 p1 m2 p2 Hm1p1 Hclm Hclp Hstepsm Hstepsp Hm2p2.
so (Hmeta _#3 Hj Hm1p1) as (Hm1 & Hp1).
so (Hseqb _#3 (Hextend _#3 Hm1p1)) as (Bn & Hbnl & _ & Hmetbn).
invert Hbl.
intros _ _ Hbact.
so (Hbact _#3 Hj Hm1p1) as Hinterp.
simpsubin Hinterp.
so (basic_fun _#7 Hinterp Hbnl).
subst Bn.
so (Hmetbn _#3 (le_refl _) Hm2p2) as (Hm2 & Hp2).
split.
  {
  exists m1, m1, m2, m2, Hm1.
  do2 4 split; auto.
  cbn.
  force_exact Hm2.
  f_equal.
  f_equal.
  f_equal.
  apply urelspinj_equal; auto.
  }

  {
  exists p1, p1, p2, p2, Hp1.
  do2 4 split; auto.
  cbn.
  force_exact Hp2.
  f_equal.
  f_equal.
  f_equal.
  apply urelspinj_equal; auto.
  }
Qed.


Lemma sound_set_symmetrical :
  forall G a b,
    pseq G (deq triv triv (symmetrical a))
    -> pseq (hyp_tm a :: G) (deqtype b b)
    -> pseq G (deq triv triv (symmetrical (set a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 1 [hyp_emp] b 2 [] _ [_] _ _ _); cbn.
intros G Hclb Hseqa Hseqb.
rewrite -> seq_symmetrical in Hseqa |- *.
rewrite -> seq_eqtype in Hseqb.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & Hmeta).
assert (forall j m p,
          rel (den A) j m p
          -> pwctx j (dot m s) (dot p s') (hyp_tm a :: G)) as Hextend.
  {
  intros j m p Hmp.
  so (basic_member_index _#9 Hal Hmp) as Hj.
  apply pwctx_cons_tm_seq.
    {
    eapply pwctx_downward; eauto.
    }

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
    intros k t t' Ht.
    so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
    eauto.
    }
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr).
  {
  setoid_rewrite -> (basic_impl_iutruncate _#6 Hal) at 1.
  reflexivity.
  }

  {
  eapply subst_closub_under_permit; eauto.
  }

  {
  eapply subst_closub_under_permit; eauto.
  }

  {
  intros j m p Hmp.
  so (Hextend _#3 Hmp) as Hs'.
  so (Hseqb _#3 Hs') as (B & Hbl & Hbr & _).
  exists B.
  simpsub.
  auto.
  }
exists (iuset stop A B).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl.
  apply interp_set; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_set; auto.
  }
intros j m p Hj Hmp.
cbn in Hmp.
decompose Hmp.
intros n q Hmp Hnq.
so (Hmeta _#3 Hj Hmp) as (Hm & Hp).
so (Hseqb _#3 (Hextend _#3 Hmp)) as (Bn & Hbnl & _ & Hmetbn).
invert Hbl.
intros _ _ Hbact.
so (Hbact _#3 Hj Hmp) as Hinterp.
simpsubin Hinterp.
so (basic_fun _#7 Hinterp Hbnl).
subst Bn.
split.
  {
  exists n, q, Hm.
  cbn.
  force_exact Hnq.
  f_equal.
  f_equal.
  f_equal.
  apply urelspinj_equal; auto.
  }

  {
  exists n, q, Hp.
  cbn.
  force_exact Hnq.
  f_equal.
  f_equal.
  f_equal.
  apply urelspinj_equal; auto.
  }
Qed.


Lemma sound_quotient_symmetrical :
  forall G a b,
    pseq G (deqtype (quotient a b) (quotient a b))
    -> pseq G (deq triv triv (symmetrical a))
    -> pseq G (deq triv triv (symmetrical (quotient a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqquot Hseqmet.
rewrite -> seq_eqtype in Hseqquot.
rewrite -> seq_deq in Hseqmet |- *.
intros i s s' Hs.
so (Hseqquot _#3 Hs) as (R & Hl & Hr & _).
simpsubin Hl.
simpsubin Hr.
cbn [Nat.add] in Hl.
cbn [Nat.add] in Hr.
invert (basic_value_inv _#6 value_quotient Hl).
intros A B hs ht Hal Hbl Heql.
invert (basic_value_inv _#6 value_quotient Hr).
intros A' B' hs' ht' Har Hbr Heqr.
so (iuquotient_inj _#9 (eqtrans Heql (eqsymm Heqr))).
subst A'.
clear Heqr.
subst R.
exists (iusymmetrical stop i (iuquotient stop A B hs ht)).
simpsub.
cbn [Nat.add].
assert (symmetrical_property stop (den (iuquotient stop A B hs ht)) i) as Hprop.
  {
  intros j Hj.
  so (Hseqmet _#3 Hs) as (R & Hmetl & _ & Hsat & _).
  simpsubin Hmetl.
  invert (basic_value_inv _#6 value_symmetrical Hmetl).
  intros A' Hal' <-.
  so (basic_fun _#7 Hal Hal').
  subst A'.
  simpsubin Hsat.
  cbn in Hsat.
  decompose Hsat.
  intros Hprop _ _ _ _ _.
  intros k m p Hmp.
  destruct Hmp as (Hk & Hmp).
  cbn in Hmp.
  decompose Hmp.
  intros n q u v Hmq Hnp Huv.
  so (Hprop j Hj k m q (conj Hk Hmq)) as ((_ & Hmm) & _).
  so (Hprop j Hj k n p (conj Hk Hnp)) as (_ & (_ & Hpp)).
  so (hs _#7 Hmq Hnp Huv) as (u1 & v1 & Huv1).
  split.
    {
    so (ht _#11 Hmq Hnp Hmq Huv Huv1) as (u2 & v2 & Huv2).
    split; auto.
    exists m, m.
    exists u2, v2.
    exists Hmm, Hmm.
    cbn.
    force_exact Huv2.
    f_equal.
    f_equal.
    f_equal.
    apply urelspinj_equal.
    apply prod_action_ppair; auto.
    }

    {
    so (ht _#11 Hnp Hmq Hnp Huv1 Huv) as (u2 & v2 & Huv2).
    split; auto.
    exists p, p.
    exists u2, v2.
    exists Hpp, Hpp.
    cbn.
    force_exact Huv2.
    f_equal.
    f_equal.
    f_equal.
    apply urelspinj_equal.
    apply prod_action_ppair; auto.
    }
  }
do2 4 split; auto.
  {
  apply interp_eval_refl.
  apply interp_symmetrical; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_symmetrical; auto.
  }

  {
  do2 5 split; auto using star_refl; try prove_hygiene.
  }

  {
  do2 5 split; auto using star_refl; try prove_hygiene.
  }

  {
  do2 5 split; auto using star_refl; try prove_hygiene.
  }
Qed.


Lemma sound_partial_symmetrical :
  forall G a,
    pseq G (deq triv triv (symmetrical a))
    -> pseq G (deq triv triv (symmetrical (partial a))).
Proof.
intros G a.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseqa.
rewrite -> seq_symmetrical in Hseqa |- *.
intros i s s' Hs.
so (Hseqa _#3 Hs) as (A & Hal & Har & Hmet).
exists (iupartial stop i A).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl.
  apply interp_partial; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_partial; auto.
  }
intros j m p Hj Hmp.
cbn in Hmp.
decompose Hmp.
intros _ Hclm Hclp Hconviff Hmp.
split.
  {
  do2 4 split; auto.
    {
    split; auto.
    }

    {
    intros Hconv.
    so (Hmet _#3 Hj (Hmp Hconv)) as (Hm & Hp).
    exact Hm.
    }
  }

  {
  do2 4 split; auto.
    {
    split; auto.
    }

    {
    intros Hconv.
    so (Hmet _#3 Hj (Hmp (Hconviff ander Hconv))) as (Hm & Hp).
    exact Hp.
    }
  }
Qed.


Lemma sound_arrow_quotient_commute :
  forall G a b c m n ms mt,
    pseq G (deq triv triv (symmetrical a))
    -> pseq G (deq triv triv (symmetrical b))
    -> pseq (hyp_tm (subst sh1 b) :: hyp_tm b :: G) (deqtype c c)
    (* symmetry *)
    -> pseq (hyp_tm c ::
            hyp_tm (subst sh1 b) ::
            hyp_tm b :: 
            G) 
         (deq ms ms (subst (dot (var 2) (dot (var 1) (sh 3))) c))
    (* transitivity *)
    -> pseq (hyp_tm (subst (dot (var 1) (dot (var 2) (sh 4))) c) :: 
            hyp_tm (subst sh1 c) ::
            hyp_tm (subst (sh 2) b) :: 
            hyp_tm (subst sh1 b) :: 
            hyp_tm b :: 
            G)
         (deq mt mt (subst (dot (var 2) (dot (var 4) (sh 5))) c))
    -> pseq (hyp_tm c :: hyp_tm (subst sh1 b) :: hyp_tm b :: G) (deq triv triv (subst sh1 c))
    -> pseq (hyp_tm (equal (subst (sh 2) a) (var 1) (var 0)) :: hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deq triv triv (sequal (var 2) (var 1)))
    -> pseq G (deq m n (tarrow a (quotient b c)))
    -> pseq G (deq m n (quotient (tarrow a b) 
                          (pi (subst (sh 2) a)
                             (subst (dot (app (var 1) (var 0)) (dot (app (var 2) (var 0)) (sh 3))) c)))).
Proof.
intros G dom a b m n ms mt.
revert G.
refine (seq_pseq 3 [] dom [] a [hyp_emp; hyp_emp] b 8 [] _ [] _ [_; _] _ [_; _; _] _ [_; _; _; _; _] _ [_; _; _] _ [_; _; _] _ [] _ _ _); cbn.
intros G Hcldom Hcla Hclb Hseqdom Hseqa Hseqb Hseqsymm Hseqtrans Hseqtriv Hseqelem Hseqmn.
rewrite -> seq_symmetrical in Hseqdom, Hseqa.
rewrite -> seq_eqtype in Hseqb.
rewrite -> seq_deq in Hseqsymm, Hseqtrans, Hseqtriv, Hseqelem, Hseqmn |- *.
assert (top <<= stop) as Htopstop.
  {
  apply succ_nodecrease.
  }
assert (forall i s s' A u v x y,
          pwctx i s s' G
          -> interp toppg true i (subst s a) A
          -> interp toppg false i (subst s' a) A
          -> rel (den A) i u v
          -> rel (den A) i x y
          -> pwctx i (dot x (dot u s)) (dot y (dot v s')) (hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hextends.
  {
  intros i s s' A u v x y Hs Hal Har Huv Hxy.
  so (basic_member_index _#9 Hal Huv) as Hj.
  apply pwctx_cons_tm_seq.
    {
    apply pwctx_cons_tm_seq.
      {
      apply (pwctx_downward i); auto.
      }

      {
      apply (seqhyp_tm _#5 A); auto.
      }
    
      {
      intros k t t' Ht.
      so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
      eauto.
      }
    }

    {
    simpsub.
    apply (seqhyp_tm _#5 A); auto.
    }

    {
    intros k tt tt' Htt.
    invertc Htt.
    intros p q t t' Ht _ _ _ <- <-.
    so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
    exists toppg, R.
    simpsub.
    auto.
    }
  }
assert (forall i s s' Dom A u v x y,
          pwctx i s s' G
          -> interp toppg true i (subst s dom) Dom
          -> interp toppg false i (subst s' dom) Dom
          -> interp toppg true i (subst s a) A
          -> interp toppg false i (subst s' a) A
          -> rel (arrow_urel stop i (den Dom) (den A)) i u v
          -> rel (arrow_urel stop i (den Dom) (den A)) i x y
          -> exists F,
               functional the_system toppg true i (den Dom) (subst (dot (app x (var 0)) (dot (app u (var 0)) (compose s sh1))) b) F
               /\ functional the_system toppg false i (den Dom) (subst (dot (app y (var 0)) (dot (app v (var 0)) (compose s' sh1))) b) F) as Hfnify.
  {
  clear m n Hseqmn.
  intros i s s' Dom A u v x y Hs Hdoml Hdomr Hal Har Huv Hxy.
  so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
  so (urel_closed _#5 Huv) as (Hclu & Hclv).
  so (urel_closed _#5 Hxy) as (Hclx & Hcly).
  apply (extract_functional toppg i (den Dom)
             (subst (dot (app x (var 0)) (dot (app u (var 0)) (compose s sh1))) b)
             (subst (dot (app y (var 0)) (dot (app v (var 0)) (compose s' sh1))) b)).
    {
    exact (f_equal den (basic_impl_iutruncate _#6 Hdoml)).
    }

    {
    eapply hygiene_subst; eauto.
    intros k Hk.
    destruct k as [|[|k]].
      {
      simpsub.
      prove_hygiene.
      }

      {
      simpsub.
      prove_hygiene.
      }

      {
      simpsub.
      apply hygiene_shift_permit.
      prove_hygiene.
      }
    }

    {
    eapply hygiene_subst; eauto.
    intros k Hk.
    destruct k as [|[|k]].
      {
      simpsub.
      prove_hygiene.
      }

      {
      simpsub.
      prove_hygiene.
      }

      {
      simpsub.
      apply hygiene_shift_permit.
      prove_hygiene.
      }
    }

    {
    intros j m p Hmp.
    simpsub.
    unfold subst1.
    rewrite -> (subst_into_closed _ _ x); auto.
    rewrite -> (subst_into_closed _ _ y); auto.
    rewrite -> (subst_into_closed _ _ u); auto.
    rewrite -> (subst_into_closed _ _ v); auto.
    so (basic_member_index _#9 Hdoml Hmp) as Hj.
    exploit (Hextends j s s' (iutruncate (S j) A) (app u m) (app v p) (app x m) (app y p)) as Hs'; auto.
      {
      eapply pwctx_downward; eauto.
      }

      {
      eapply basic_downward; eauto.
      }

      {
      eapply basic_downward; eauto.
      }

      {
      split.
        {
        omega.
        }
      eapply (arrow_action_app _ j); eauto.
      so (urel_downward_leq _#6 Hj Huv) as (l & l' & _ & Hl).
      exists l, l'.
      split; auto.
      }

      {
      split.
        {
        omega.
        }
      eapply (arrow_action_app _ j); eauto.
      so (urel_downward_leq _#6 Hj Hxy) as (l & l' & _ & Hl).
      exists l, l'.
      split; auto.
      }
    so (Hseqb _#3 Hs') as (B & Hbl & Hbr & _).
    exists B.
    simpsub.
    unfold subst1.
    auto.
    }
  }
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqdom _#3 Hs) as (Dom & Hdoml & Hdomr & _).
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
exploit (extract_functional_dual toppg 
           (iuarrow stop i Dom A)
           G
           (tarrow dom a)
           (pi (subst (sh 2) dom)
              (subst (dot (app (var 1) (var 0)) (dot (app (var 2) (var 0)) (sh 3))) b))
           i s s') as H.
  {
  prove_hygiene.
  eapply hygiene_subst; eauto.
  intros k Hk.
  destruct k as [|[|k]].
    {
    simpsub.
    prove_hygiene.
    }

    {
    simpsub.
    prove_hygiene.
    }

    {
    simpsub.
    apply hygiene_var.
    cbn.
    prove_hygiene.
    }
  }

  {
  exact Hs.
  }

  {
  simpsub.
  apply interp_eval_refl.
  apply interp_tarrow; auto.
  }

  {
  simpsub.
  apply interp_eval_refl.
  apply interp_tarrow; auto.
  }

  {
  intros j t Hj Hst.
  simpsub.
  apply (relhyp_tm _#4 (iuarrow stop j (iutruncate (S j) Dom) (iutruncate (S j) A))).
    {
    apply interp_eval_refl.
    apply interp_tarrow.
      {
      apply (basic_downward _#3 i); auto.
      }

      {
      apply (basic_downward _#3 i); auto.
      }
    }

    {
    apply interp_eval_refl.
    apply interp_tarrow.
      {
      so (Hseqdom _#3 Hst) as (Dom' & Hdoml' & Hdomt & _).
      so (basic_fun _#7 (basic_downward _#7 Hj Hdoml) Hdoml').
      subst Dom'.
      exact Hdomt.
      }

      {
      so (Hseqa _#3 Hst) as (R' & Hal' & Hat & _).
      so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal').
      subst R'.
      exact Hat.
      }
    }
  }

  {
  intros j t Hj Hst.
  simpsub.
  apply (relhyp_tm _#4 (iuarrow stop j (iutruncate (S j) Dom) (iutruncate (S j) A))).
    {
    apply interp_eval_refl.
    apply interp_tarrow.
      {
      apply (basic_downward _#3 i); auto.
      }

      {
      apply (basic_downward _#3 i); auto.
      }
    }

    {
    apply interp_eval_refl.
    apply interp_tarrow.
      {
      so (Hseqdom _#3 Hst) as (Dom' & Hdomt & Hdomr' & _).
      so (basic_fun _#7 (basic_downward _#7 Hj Hdomr) Hdomr').
      subst Dom'.
      exact Hdomt.
      }

      {
      so (Hseqa _#3 Hst) as (R' & Hat & Har' & _).
      so (basic_fun _#7 (basic_downward _#7 Hj Har) Har').
      subst R'.
      exact Hat.
      }
    }
  }

  {
  clear m n ms mt Hseqsymm Hseqtrans Hseqmn i s s' Hs Hcls Hcls' Dom A Hdoml Hdomr Hal Har.
  intros i ss ss' Hss.
  simpsubin Hss.
  invertc Hss.
  intros x y s1 s1' Hs1 Hxy _ _ <- <-.
  invertc Hs1.
  intros u v s s' Hs Huv _ _ <- <-.
  so (Hseqa _#3 Hs) as (A & Hal & Har & _).
  so (Hseqdom _#3 Hs) as (Dom & Hdoml & Hdomr & _).
  simpsubin Huv.
  invertc Huv.
  intros Q Harrl _ Huv.
  so (basic_fun _#7 Harrl (interp_eval_refl _#6 (interp_tarrow _#8 Hdoml Hal))).
  subst Q.
  clear Harrl.
  simpsubin Hxy.
  invertc Hxy.
  intros Q Harrl _ Hxy.
  so (basic_fun _#7 Harrl (interp_eval_refl _#6 (interp_tarrow _#8 Hdoml Hal))).
  subst Q.
  clear Harrl.
  so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
  so (urel_closed _#5 Huv) as (Hclu & Hclv).
  so (urel_closed _#5 Hxy) as (Hclx & Hcly).
  simpsub.
  exploit (Hfnify i s s' Dom A u v x y) as (B & Hbl & Hbr); auto.
  exists (iupi stop i Dom B).
  split.
    {
    rewrite -> (subst_into_closed _ _ u); auto.
    rewrite -> (subst_into_closed _ _ x); auto.
    apply interp_eval_refl.
    apply interp_pi; auto.
    }

    {
    rewrite -> (subst_into_closed _ _ v); auto.
    rewrite -> (subst_into_closed _ _ y); auto.
    apply interp_eval_refl.
    apply interp_pi; auto.
    }
  }
destruct H as (C & Hcl & Hcr).
exploit (extract_functional_dual toppg A G a b i s s') as H; auto.
  {
  intros j t Hj Hst.
  so (Hseqa _#3 Hst) as (A' & Hl & Ht & _).
  so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hl).
  subst A'.
  apply (relhyp_tm _#4 (iutruncate (S j) A)); auto.
  apply (basic_downward _#3 i); auto.
  }

  {
  intros j t Hj Hst.
  so (Hseqa _#3 Hst) as (A' & Ht & Hr & _).
  so (basic_fun _#7 (basic_downward _#7 Hj Har) Hr).
  subst A'.
  apply (relhyp_tm _#4 (iutruncate (S j) A)); auto.
  apply (basic_downward _#3 i); auto.
  }

  {
  intros j t t' Ht.
  so (Hseqb _#3 Ht) as (R & Hl & Hr & _).
  eauto.
  }
destruct H as (D & Hdl & Hdr).
assert (symmish stop (den A) (fun X => den (pi1 D X))) as hsold.
  {
  clear C Hcl Hcr m n Hseqmn.
  intros j m n p q u v Hmn Hpq Huv.
  so (urel_closed _#5 Hmn) as (Hclm & Hcln).
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  so (basic_member_index _#9 Hal Hmn) as Hj.
  exploit (Hextends j s s' (iutruncate (S j) A) m n p q) as Hs'; auto.
    {
    eapply pwctx_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    split; auto.
    }

    {
    split; auto.
    }
  exploit (pwctx_cons_tm_seq j u v (dot p (dot m s)) (dot q (dot n s')) b (hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hs''; auto.
    {
    eapply seqhyp_tm; eauto.
      {
      invert Hdl.
      intros _ _ Hdact.
      so (Hdact j (ppair m p) (ppair n q) Hj (prod_action_ppair _#8 Hmn Hpq)) as H.
      simpsubin H.
      refine (basic_equiv _#7 _ _ H).
        {
        prove_hygiene.
        }

        {
        apply equiv_funct; auto using equiv_refl.
        apply equivsub_dot.
          {
          apply equiv_beta2.
          }
        apply equivsub_dot.
          {
          apply equiv_beta1.
          }
        apply equivsub_refl.
        }
      }

      {
      invert Hdr.
      intros _ _ Hdact.
      so (Hdact j (ppair m p) (ppair n q) Hj (prod_action_ppair _#8 Hmn Hpq)) as H.
      simpsubin H.
      refine (basic_equiv _#7 _ _ H).
        {
        prove_hygiene.
        }

        {
        apply equiv_funct; auto using equiv_refl.
        apply equivsub_dot.
          {
          apply equiv_beta2.
          }
        apply equivsub_dot.
          {
          apply equiv_beta1.
          }
        apply equivsub_refl.
        }
      }
    }

    {
    intros k t t' Ht.
    so (Hseqb _#3 Ht) as (R & Hl & Hr & _).
    eauto.
    }
  so (Hseqsymm _#3 Hs'') as (R & Hl & _ & Hsat & _).
  simpsubin Hl.
  exists (subst (dot u (dot p (dot m s))) ms).
  exists (subst (dot v (dot q (dot n s'))) ms).
  force_exact Hsat.
  f_equal.
  f_equal.
  clear Hsat.
  invert Hdl.
  intros _ _ Hdact.
  so (Hdact j (ppair p m) (ppair q n) Hj (prod_action_ppair _#8 Hpq Hmn)) as H.
  simpsubin H.
  refine (basic_fun _#7 _ H).
  refine (basic_equiv _#7 _ _ Hl).
    {
    prove_hygiene.
    }

    {
    apply equiv_symm.
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot.
      {
      apply equiv_beta2.
      }
    apply equivsub_dot.
      {
      apply equiv_beta1.
      }
    apply equivsub_refl.
    }
  }
assert (transish stop (den A) (fun X => den (pi1 D X))) as htold.
  {
  clear C Hcl Hcr m n Hseqmn.
  intros j m n p q r t u1 v1 u2 v2 Hmn Hpq Hrt Huv1 Huv2.
  so (urel_closed _#5 Hmn) as (Hclm & Hcln).
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  so (urel_closed _#5 Hrt) as (Hclr & Hclt).
  so (basic_member_index _#9 Hal Hmn) as Hj.
  assert (pwctx j (dot u2 (dot u1 (dot r (dot p (dot m s))))) (dot v2 (dot v1 (dot t (dot q (dot n s'))))) (hyp_tm (subst (dot (var 1) (dot (var 2) (sh 4))) b) :: hyp_tm (subst (sh 1) b) :: hyp_tm (subst (sh 2) a) :: hyp_tm (subst (sh 1) a) :: hyp_tm a :: G)) as Hs'.
    {
    apply pwctx_cons_tm_seq.
      {
      apply pwctx_cons_tm_seq.
        {
        apply pwctx_cons_tm_seq.
          {
          eapply (Hextends _#3 (iutruncate (S j) A)).
            {
            eapply pwctx_downward; eauto.
            }
        
            {
            eapply basic_downward; eauto.
            }
        
            {
            eapply basic_downward; eauto.
            }
        
            {
            split; auto.
            }
        
            {
            split; auto.
            }
          }
        
          {
          apply (seqhyp_tm _#5 (iutruncate (S j) A)).
            {
            simpsub.
            eapply basic_downward; eauto.
            }

            {
            simpsub.
            eapply basic_downward; eauto.
            }
            
            {
            split; auto.
            }
          }
          
          {
          intros k zz zz' Hzz.
          invertc Hzz.
          intros x1 y1 zz1 zz1' Hzz _ _ _ <- <-.
          invertc Hzz.
          intros x2 y2 z z' Hz _ _ _ <- <-.
          so (Hseqa _#3 Hz) as (R & Hl & Hr & _).
          exists toppg, R.
          simpsub.
          auto.
          }
        }

        {
        simpsub.
        eapply seqhyp_tm; eauto.
          {
          invert Hdl.
          intros _ _ Hdact.
          so (Hdact j (ppair m p) (ppair n q) Hj (prod_action_ppair _#8 Hmn Hpq)) as H.
          simpsubin H.
          clear Hdact.
          refine (basic_equiv _#7 _ _ H); clear H.
            {
            prove_hygiene.
            }

            {
            apply equiv_funct; auto using equiv_refl.
            apply equivsub_dot.
              {
              apply equiv_beta2.
              }
            apply equivsub_dot.
              {
              apply equiv_beta1.
              }
            apply equivsub_refl.
            }
          }

          {
          invert Hdr.
          intros _ _ Hdact.
          so (Hdact j (ppair m p) (ppair n q) Hj (prod_action_ppair _#8 Hmn Hpq)) as H.
          simpsubin H.
          clear Hdact.
          refine (basic_equiv _#7 _ _ H); clear H.
            {
            prove_hygiene.
            }

            {
            apply equiv_funct; auto using equiv_refl.
            apply equivsub_dot.
              {
              apply equiv_beta2.
              }
            apply equivsub_dot.
              {
              apply equiv_beta1.
              }
            apply equivsub_refl.
            }
          }
        }

        {
        intros k zz zz' Hzz.
        invertc Hzz.
        intros x y z z' Hz _ _ _ <- <-.
        so (Hseqb _#3 Hz) as (R & Hl & Hr & _).
        exists toppg, R.
        simpsub.
        auto.
        }
      }

      {
      simpsub.
      eapply seqhyp_tm; eauto.
        {
        invert Hdl.
        intros _ _ Hdact.
        so (Hdact j (ppair p r) (ppair q t) Hj (prod_action_ppair _#8 Hpq Hrt)) as H.
        simpsubin H.
        clear Hdact.
        refine (basic_equiv _#7 _ _ H); clear H.
          {
          prove_hygiene.
          }

          {
          apply equiv_funct; auto using equiv_refl.
          apply equivsub_dot.
            {
            apply equiv_beta2.
            }
          apply equivsub_dot.
            {
            apply equiv_beta1.
            }
          apply equivsub_refl.
          }
        }

        {
        invert Hdr.
        intros _ _ Hdact.
        so (Hdact j (ppair p r) (ppair q t) Hj (prod_action_ppair _#8 Hpq Hrt)) as H.
        simpsubin H.
        clear Hdact.
        refine (basic_equiv _#7 _ _ H); clear H.
          {
          prove_hygiene.
          }

          {
          apply equiv_funct; auto using equiv_refl.
          apply equivsub_dot.
            {
            apply equiv_beta2.
            }
          apply equivsub_dot.
            {
            apply equiv_beta1.
            }
          apply equivsub_refl.
          }
        }
      }

      {
      intros k zz zz' Hzz.
      invertc Hzz.
      intros x1 y1 zz1 zz1' Hzz _ _ _ <- <-.
      invertc Hzz.
      intros x2 y2 zz2 zz2' Hzz Hxy2 _ _ <- <-.
      invertc Hzz.
      intros x3 y3 zz3 zz3' Hzz Hxy3 _ _ <- <-.
      invertc Hzz.
      intros x4 y4 z z' Hz _ _ _ <- <-.
      simpsubin Hxy2.
      simpsubin Hxy3.
      simpsub.
      invertc Hxy2.
      intros R Hl Hr Hxy2.
      invertc Hxy3.
      intros R' Hl' _ Hxy3.
      so (basic_fun _#7 Hl Hl').
      subst R'.
      so (Hextends _#8 Hz Hl Hr Hxy3 Hxy2) as Hz'.
      so (Hseqb _#3 Hz') as (Q & Hql & Hqr & _).
      eauto.
      }
    }
  so (Hseqtrans _#3 Hs') as (R & Hl & Hr & Hsat & _).
  simpsubin Hl.
  simpsubin Hr.
  exists (subst (dot u2 (dot u1 (dot r (dot p (dot m s))))) mt).
  exists (subst (dot v2 (dot v1 (dot t (dot q (dot n s'))))) mt).
  force_exact Hsat.
  clear Hsat.
  f_equal.
  f_equal.
  invert Hdl.
  intros _ _ Hdact.
  so (Hdact j (ppair m r) (ppair n t) Hj (prod_action_ppair _#8 Hmn Hrt)) as H.
  simpsubin H.
  refine (basic_fun _#7 _ H).
  refine (basic_equiv _#7 _ _ Hl).
    {
    prove_hygiene.
    }

    {
    apply equiv_symm.
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot.
      {
      apply equiv_beta2.
      }
    apply equivsub_dot.
      {
      apply equiv_beta1.
      }
    apply equivsub_refl.
    }
  }
assert (symmish stop (arrow_urel stop i (den Dom) (den A)) (fun X => den (pi1 C X))) as hsnew.
  {
  clear m n Hseqmn Hseqtrans.
  clear D Hdl Hdr hsold htold.
  intros j m n p q u v Hmn Hpq Huv.
  so (urel_closed _#5 Hmn) as (Hclm & Hcln).
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  so (urel_closed _#5 Huv) as (Hclu & Hclv).
  exploit (basic_member_index the_system toppg true i (tarrow (subst s dom) (subst s a)) (iuarrow stop i Dom A) j m n) as Hj; auto.
    {
    apply interp_eval_refl.
    apply interp_tarrow; auto.
    }
  exists (lam triv), (lam triv).
  so (Hfnify j s s' (iutruncate (S j) Dom) (iutruncate (S j) A) (ppi1 (ppair p m)) (ppi1 (ppair q n)) (ppi2 (ppair p m)) (ppi2 (ppair q n))) as (F & Hfl & Hfr).
    {
    eapply pwctx_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eassert _ as Hpq'; [refine (urel_equiv _#4 (ppi1 (ppair p m)) _ (ppi1 (ppair q n)) _ _ _ _ Hpq) |].
      {
      prove_hygiene.
      }

      {
      prove_hygiene.
      }

      {
      apply equiv_symm.
      apply equiv_beta1.
      }

      {
      apply equiv_symm.
      apply equiv_beta1.
      }
    refine (rel_from_ceiling _#6 _ Hpq').
    rewrite -> !ceiling_arrow.
    rewrite -> !Nat.min_r; auto.
    f_equal.
      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }

      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }
    }

    {
    eassert _ as Hmn'; [refine (urel_equiv _#4 (ppi2 (ppair p m)) _ (ppi2 (ppair q n)) _ _ _ _ Hmn) |].
      {
      prove_hygiene.
      }

      {
      prove_hygiene.
      }

      {
      apply equiv_symm.
      apply equiv_beta2.
      }

      {
      apply equiv_symm.
      apply equiv_beta2.
      }
    refine (rel_from_ceiling _#6 _ Hmn').
    rewrite -> !ceiling_arrow.
    rewrite -> !Nat.min_r; auto.
    f_equal.
      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }

      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }
    }
  so (Hfnify j s s' (iutruncate (S j) Dom) (iutruncate (S j) A) (ppi1 (ppair m p)) (ppi1 (ppair n q)) (ppi2 (ppair m p)) (ppi2 (ppair n q))) as (I & Hil & Hir).
    {
    eapply pwctx_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eassert _ as Hmn'; [refine (urel_equiv _#4 (ppi1 (ppair m p)) _ (ppi1 (ppair n q)) _ _ _ _ Hmn) |].
      {
      prove_hygiene.
      }

      {
      prove_hygiene.
      }

      {
      apply equiv_symm.
      apply equiv_beta1.
      }

      {
      apply equiv_symm.
      apply equiv_beta1.
      }
    refine (rel_from_ceiling _#6 _ Hmn').
    rewrite -> !ceiling_arrow.
    rewrite -> !Nat.min_r; auto.
    f_equal.
      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }

      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }
    }

    {
    eassert _ as Hpq'; [refine (urel_equiv _#4 (ppi2 (ppair m p)) _ (ppi2 (ppair n q)) _ _ _ _ Hpq) |].
      {
      prove_hygiene.
      }

      {
      prove_hygiene.
      }

      {
      apply equiv_symm.
      apply equiv_beta2.
      }

      {
      apply equiv_symm.
      apply equiv_beta2.
      }
    refine (rel_from_ceiling _#6 _ Hpq').
    rewrite -> !ceiling_arrow.
    rewrite -> !Nat.min_r; auto.
    f_equal.
      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }

      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }
    }
  invert Hcl.
  intros _ _ Hcact.
  so (Hcact _#3 Hj (prod_action_ppair stop _ _ j p m q n Hpq Hmn)) as H.
  clear Hcact.
  simpsubin H.
  rewrite -> (subst_into_closed _ _ p) in H; auto.
  rewrite -> (subst_into_closed _ _ m) in H; auto.
  assert (interp toppg true j (pi (subst s dom) (subst (dot (app (ppi2 (ppair p m)) (var 0)) (dot (app (ppi1 (ppair p m)) (var 0)) (compose s sh1))) b)) (iupi stop j (iutruncate (S j) Dom) F)) as H'.
    {
    apply interp_eval_refl.
    apply interp_pi; auto.
    eapply basic_downward; eauto.
    }
  so (basic_fun _#7 H H') as Heq.
  clear H H'.
  cbn in Heq.
  cut (rel (den (iupi stop j (iutruncate (S j) Dom) F)) j (lam triv) (lam triv)).
    {
    intro H.
    force_exact H.
    f_equal.
    f_equal.
    symmetry.
    exact Heq.
    }
  clear Heq.
  exists triv, triv.
  do2 5 split; auto using star_refl; try prove_hygiene.
  intros j' r t Hj' Hrt.
  so (urel_closed _#5 Hrt) as (Hclr & Hclt).
  simpsub.
  invert Hfl.
  intros _ _ Hfact.
  so (Hfact j' r t Hj' Hrt) as H.
  clear Hfact.
  simpsubin H.
  unfold subst1 in H.
  rewrite -> (subst_into_closed _ _ p) in H; auto.
  rewrite -> (subst_into_closed _ _ m) in H; auto.
  eassert _ as Hinterp; [refine (basic_equiv _#5 (subst (dot (app m r) (dot (app p r) s)) b) _ _ _ H) |].
    {
    prove_hygiene.
    }

    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot.
      {
      apply equiv_app; auto using equiv_refl.
      apply equiv_beta2.
      }
    apply equivsub_dot.
      {
      apply equiv_app; auto using equiv_refl.
      apply equiv_beta1.
      }
    apply equivsub_refl.
    }
  clear H.
  exploit (Hextends j' s s' (iutruncate (S j') A) (app p r) (app q t) (app m r) (app n t)) as Hs'.
    {
    apply (pwctx_downward i); auto.
    omega.
    }

    {
    apply (basic_downward _#3 i); auto.
    omega.
    }

    {
    apply (basic_downward _#3 i); auto.
    omega.
    }

    {
    apply (arrow_action_app _ j' (den (iutruncate (S j') Dom)) (den (iutruncate (S j') A))).
      {
      cut (rel (ceiling (S j') (arrow_urel stop i (den Dom) (den A))) j' p q).
        {
        intro H.
        rewrite -> ceiling_arrow in H.
        rewrite -> Nat.min_r in H; auto.
        omega.
        }
      split; auto.
      eapply urel_downward_leq; eauto.
      }

      {
      clear Hinterp.
      destruct Hrt as (_ & Hrt).
      split; auto.
      }
    }

    {
    apply (arrow_action_app _ j' (den (iutruncate (S j') Dom)) (den (iutruncate (S j') A))).
      {
      cut (rel (ceiling (S j') (arrow_urel stop i (den Dom) (den A))) j' m n).
        {
        intro H.
        rewrite -> ceiling_arrow in H.
        rewrite -> Nat.min_r in H; auto.
        omega.
        }
      split; auto.
      eapply urel_downward_leq; eauto.
      }

      {
      clear Hinterp.
      destruct Hrt as (_ & Hrt).
      split; auto.
      }
    }
  so (Hseqb _#3 Hs') as (R & Hl & Hr & _).
  so (basic_fun _#7 Hl Hinterp) as HeqR.
  assert (exists x y,
            rel (den R) j' x y) as (x & y & Hxy).
    {
    subst R.
    clear Hs' Hl Hr.
    assert (rel (den A) j' (app m r) (app n t)) as Hmrnt.
      {
      apply (arrow_action_app _ j' (den (iutruncate (S j') Dom)) (den (iutruncate (S j') A))).
        {
        cut (rel (ceiling (S j') (arrow_urel stop i (den Dom) (den A))) j' m n).
          {
          intro H.
          rewrite -> ceiling_arrow in H.
          rewrite -> Nat.min_r in H; auto.
          omega.
          }
        split; auto.
        eapply urel_downward_leq; eauto.
        }
  
        {
        clear Hinterp.
        destruct Hrt as (_ & Hrt).
        split; auto.
        }
      }
    assert (rel (den A) j' (app p r) (app q t)) as Hprqt.
      {
      apply (arrow_action_app _ j' (den (iutruncate (S j') Dom)) (den (iutruncate (S j') A))).
        {
        cut (rel (ceiling (S j') (arrow_urel stop i (den Dom) (den A))) j' p q).
          {
          intro H.
          rewrite -> ceiling_arrow in H.
          rewrite -> Nat.min_r in H; auto.
          omega.
          }
        split; auto.
        eapply urel_downward_leq; eauto.
        }
  
        {
        clear Hinterp.
        destruct Hrt as (_ & Hrt).
        split; auto.
        }
      }
    assert (pwctx j' (dot (app p r) (dot (app m r) s)) (dot (app q t) (dot (app n t) s')) (hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hs'.
      {
      eapply (Hextends _#3 (iutruncate (S j') A)).
        {
        apply (pwctx_downward i); auto.
        omega.
        }

        {
        apply (basic_downward _#3 i); auto.
        omega.
        }

        {
        apply (basic_downward _#3 i); auto.
        omega.
        }
        
        {
        split; auto.
        }

        {
        split; auto.
        }
      }
    assert (pwctx j' (dot (app u r) (dot (app p r) (dot (app m r) s))) (dot (app v t) (dot (app q t) (dot (app n t) s'))) (hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hs''.
      {
      apply pwctx_cons_tm_seq.
        {
        auto.
        }

        {
        invert Hcl.
        intros _ _ Hcact.
        so (Hcact _#3 Hj (prod_action_ppair _#8 Hmn Hpq)) as Hl.
        clear Hcact.
        simpsubin Hl.
        rewrite -> (subst_into_closed _ _ m) in Hl; auto.
        rewrite -> (subst_into_closed _ _ p) in Hl; auto.
        so (interp_eval_refl _#6 (interp_pi _#8 (basic_downward _#7 Hj Hdoml) Hil)) as H.
        so (basic_fun _#7 H Hl) as Heq.
        clear H Hl.
        assert (rel (den (iupi stop j (iutruncate (S j) Dom) I)) j u v) as Huv'.
          {
          rewrite -> Heq.
          exact Huv.
          }
        clear Huv Heq.
        so (pi_action_app _#10 Hrt Hj' Huv') as Hinh.
        cbn -[iutruncate] in Hinh.
        invert Hil.
        intros _ _ Hiact.
        so (Hiact j' r t Hj' Hrt) as Hl.
        clear Hiact.
        simpsubin Hl.
        unfold subst1 in Hl.
        rewrite -> (subst_into_closed _ _ m) in Hl; auto.
        rewrite -> (subst_into_closed _ _ p) in Hl; auto.
        invert Hir.
        intros _ _ Hiact.
        so (Hiact j' r t Hj' Hrt) as Hr.
        clear Hiact.
        simpsubin Hr.
        unfold subst1 in Hr.
        rewrite -> (subst_into_closed _ _ n) in Hr; auto.
        rewrite -> (subst_into_closed _ _ q) in Hr; auto.
        apply (seqhyp_tm _#5 (pi1 I (urelspinj _ _ _ _ Hrt))); auto.
          {
          refine (basic_equiv _#7 _ _ Hl).
            {
            prove_hygiene.
            }

            {
            apply equiv_funct; auto using equiv_refl.
            apply equivsub_dot.
              {
              apply equiv_app; auto using equiv_refl.
              apply equiv_beta2.
              }
            apply equivsub_dot.
              {
              apply equiv_app; auto using equiv_refl.
              apply equiv_beta1.
              }
            apply equivsub_refl.
            }
          }

          {
          refine (basic_equiv _#7 _ _ Hr).
            {
            prove_hygiene.
            }

            {
            apply equiv_funct; auto using equiv_refl.
            apply equivsub_dot.
              {
              apply equiv_app; auto using equiv_refl.
              apply equiv_beta2.
              }
            apply equivsub_dot.
              {
              apply equiv_app; auto using equiv_refl.
              apply equiv_beta1.
              }
            apply equivsub_refl.
            }
          }
        }

        {
        intros k z z' Hz.
        so (Hseqb _#3 Hz) as (R & Hl & Hr & _).
        eauto.
        }
      }
    so (Hseqsymm _#3 Hs'') as (R & Hl & _ & Hsat & _).
    simpsubin Hl.
    so (basic_fun _#7 Hinterp Hl).
    subst R.
    exists (subst (dot (app u r) (dot (app p r) (dot (app m r) s))) ms).
    exists (subst (dot (app v t) (dot (app q t) (dot (app n t) s'))) ms).
    exact Hsat.
    }
  assert (pwctx j'
            (dot x (dot (app m r) (dot (app p r) s)))
            (dot y (dot (app n t) (dot (app q t) s')))
            (hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hs''.
    {
    apply pwctx_cons_tm_seq; auto.
      {
      apply (seqhyp_tm _#5 R); auto.
      }

      {
      intros k z z' Hz.
      so (Hseqb _#3 Hz) as (Q & Hql & Hqr & _).
      eauto.
      }
    }
  so (Hseqtriv _#3 Hs'') as (R' & Hl' & _ & Hrtriv & _).
  simpsubin Hl'.
  so (basic_fun _#7 Hl Hl').
  subst R'.
  subst R.
  exact Hrtriv.
  }
assert (transish stop (arrow_urel stop i (den Dom) (den A)) (fun X => den (pi1 C X))) as htnew.
  {
  clear m n Hseqmn Hseqsymm.
  clear D Hdl Hdr hsold htold.
  intros j m n p q x y u1 v1 u2 v2 Hmn Hpq Hxy Huv1 Huv2.
  so (urel_closed _#5 Hmn) as (Hclm & Hcln).
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  so (urel_closed _#5 Hxy) as (Hclx & Hcly).
  so (urel_closed _#5 Huv1) as (Hclu1 & Hclv1).
  so (urel_closed _#5 Huv2) as (Hclu2 & Hclv2).
  exploit (basic_member_index the_system toppg true i (tarrow (subst s dom) (subst s a)) (iuarrow stop i Dom A) j m n) as Hj; auto.
    {
    apply interp_eval_refl.
    apply interp_tarrow; auto.
    }
  exists (lam triv), (lam triv).
  so (Hfnify j s s' (iutruncate (S j) Dom) (iutruncate (S j) A) (ppi1 (ppair m x)) (ppi1 (ppair n y)) (ppi2 (ppair m x)) (ppi2 (ppair n y))) as (F & Hfl & Hfr).
    {
    eapply pwctx_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eassert _ as Hmn'; [refine (urel_equiv _#4 (ppi1 (ppair m x)) _ (ppi1 (ppair n y)) _ _ _ _ Hmn) |].
      {
      prove_hygiene.
      }

      {
      prove_hygiene.
      }

      {
      apply equiv_symm.
      apply equiv_beta1.
      }

      {
      apply equiv_symm.
      apply equiv_beta1.
      }
    refine (rel_from_ceiling _#6 _ Hmn').
    rewrite -> !ceiling_arrow.
    rewrite -> !Nat.min_r; auto.
    f_equal.
      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }

      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }
    }

    {
    eassert _ as Hxy'; [refine (urel_equiv _#4 (ppi2 (ppair m x)) _ (ppi2 (ppair n y)) _ _ _ _ Hxy) |].
      {
      prove_hygiene.
      }

      {
      prove_hygiene.
      }

      {
      apply equiv_symm.
      apply equiv_beta2.
      }

      {
      apply equiv_symm.
      apply equiv_beta2.
      }
    refine (rel_from_ceiling _#6 _ Hxy').
    rewrite -> !ceiling_arrow.
    rewrite -> !Nat.min_r; auto.
    f_equal.
      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }

      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }
    }
  so (Hfnify j s s' (iutruncate (S j) Dom) (iutruncate (S j) A) (ppi1 (ppair m p)) (ppi1 (ppair n q)) (ppi2 (ppair m p)) (ppi2 (ppair n q))) as (I & Hil & Hir).
    {
    eapply pwctx_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eassert _ as Hmn'; [refine (urel_equiv _#4 (ppi1 (ppair m p)) _ (ppi1 (ppair n q)) _ _ _ _ Hmn) |].
      {
      prove_hygiene.
      }

      {
      prove_hygiene.
      }

      {
      apply equiv_symm.
      apply equiv_beta1.
      }

      {
      apply equiv_symm.
      apply equiv_beta1.
      }
    refine (rel_from_ceiling _#6 _ Hmn').
    rewrite -> !ceiling_arrow.
    rewrite -> !Nat.min_r; auto.
    f_equal.
      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }

      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }
    }

    {
    eassert _ as Hpq'; [refine (urel_equiv _#4 (ppi2 (ppair m p)) _ (ppi2 (ppair n q)) _ _ _ _ Hpq) |].
      {
      prove_hygiene.
      }

      {
      prove_hygiene.
      }

      {
      apply equiv_symm.
      apply equiv_beta2.
      }

      {
      apply equiv_symm.
      apply equiv_beta2.
      }
    refine (rel_from_ceiling _#6 _ Hpq').
    rewrite -> !ceiling_arrow.
    rewrite -> !Nat.min_r; auto.
    f_equal.
      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }

      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }
    }
  so (Hfnify j s s' (iutruncate (S j) Dom) (iutruncate (S j) A) (ppi1 (ppair p x)) (ppi1 (ppair q y)) (ppi2 (ppair p x)) (ppi2 (ppair q y))) as (J & Hjl & Hjr).
    {
    eapply pwctx_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eapply basic_downward; eauto.
    }

    {
    eassert _ as Hpq'; [refine (urel_equiv _#4 (ppi1 (ppair p x)) _ (ppi1 (ppair q y)) _ _ _ _ Hpq) |].
      {
      prove_hygiene.
      }

      {
      prove_hygiene.
      }

      {
      apply equiv_symm.
      apply equiv_beta1.
      }

      {
      apply equiv_symm.
      apply equiv_beta1.
      }
    refine (rel_from_ceiling _#6 _ Hpq').
    rewrite -> !ceiling_arrow.
    rewrite -> !Nat.min_r; auto.
    f_equal.
      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }

      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }
    }

    {
    eassert _ as Hxy'; [refine (urel_equiv _#4 (ppi2 (ppair p x)) _ (ppi2 (ppair q y)) _ _ _ _ Hxy) |].
      {
      prove_hygiene.
      }

      {
      prove_hygiene.
      }

      {
      apply equiv_symm.
      apply equiv_beta2.
      }

      {
      apply equiv_symm.
      apply equiv_beta2.
      }
    refine (rel_from_ceiling _#6 _ Hxy').
    rewrite -> !ceiling_arrow.
    rewrite -> !Nat.min_r; auto.
    f_equal.
      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }

      {
      rewrite -> den_iutruncate.
      rewrite -> ceiling_idem.
      auto.
      }
    }
  invert Hcl.
  intros _ _ Hcact.
  so (Hcact _#3 Hj (prod_action_ppair stop _ _ j m x n y Hmn Hxy)) as H.
  clear Hcact.
  simpsubin H.
  rewrite -> (subst_into_closed _ _ m) in H; auto.
  rewrite -> (subst_into_closed _ _ x) in H; auto.
  assert (interp toppg true j (pi (subst s dom) (subst (dot (app (ppi2 (ppair m x)) (var 0)) (dot (app (ppi1 (ppair m x)) (var 0)) (compose s sh1))) b)) (iupi stop j (iutruncate (S j) Dom) F)) as H'.
    {
    apply interp_eval_refl.
    apply interp_pi; auto.
    eapply basic_downward; eauto.
    }
  so (basic_fun _#7 H H') as Heq.
  clear H H'.
  cbn in Heq.
  cut (rel (den (iupi stop j (iutruncate (S j) Dom) F)) j (lam triv) (lam triv)).
    {
    intro H.
    force_exact H.
    f_equal.
    f_equal.
    symmetry.
    exact Heq.
    }
  clear Heq.
  exists triv, triv.
  do2 5 split; auto using star_refl; try prove_hygiene.
  intros j' r t Hj' Hrt.
  so (urel_closed _#5 Hrt) as (Hclr & Hclt).
  simpsub.
  invert Hfl.
  intros _ _ Hfact.
  so (Hfact j' r t Hj' Hrt) as H.
  clear Hfact.
  simpsubin H.
  unfold subst1 in H.
  rewrite -> (subst_into_closed _ _ m) in H; auto.
  rewrite -> (subst_into_closed _ _ x) in H; auto.
  eassert _ as Hinterp; [refine (basic_equiv _#5 (subst (dot (app x r) (dot (app m r) s)) b) _ _ _ H) |].
    {
    prove_hygiene.
    }

    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot.
      {
      apply equiv_app; auto using equiv_refl.
      apply equiv_beta2.
      }
    apply equivsub_dot.
      {
      apply equiv_app; auto using equiv_refl.
      apply equiv_beta1.
      }
    apply equivsub_refl.
    }
  clear H.
  exploit (Hextends j' s s' (iutruncate (S j') A) (app m r) (app n t) (app x r) (app y t)) as Hs'.
    {
    apply (pwctx_downward i); auto.
    omega.
    }

    {
    apply (basic_downward _#3 i); auto.
    omega.
    }

    {
    apply (basic_downward _#3 i); auto.
    omega.
    }

    {
    apply (arrow_action_app _ j' (den (iutruncate (S j') Dom)) (den (iutruncate (S j') A))).
      {
      cut (rel (ceiling (S j') (arrow_urel stop i (den Dom) (den A))) j' m n).
        {
        intro H.
        rewrite -> ceiling_arrow in H.
        rewrite -> Nat.min_r in H; auto.
        omega.
        }
      split; auto.
      eapply urel_downward_leq; eauto.
      }

      {
      clear Hinterp.
      destruct Hrt as (_ & Hrt).
      split; auto.
      }
    }

    {
    apply (arrow_action_app _ j' (den (iutruncate (S j') Dom)) (den (iutruncate (S j') A))).
      {
      cut (rel (ceiling (S j') (arrow_urel stop i (den Dom) (den A))) j' x y).
        {
        intro H.
        rewrite -> ceiling_arrow in H.
        rewrite -> Nat.min_r in H; auto.
        omega.
        }
      split; auto.
      eapply urel_downward_leq; eauto.
      }

      {
      clear Hinterp.
      destruct Hrt as (_ & Hrt).
      split; auto.
      }
    }
  so (Hseqb _#3 Hs') as (R & Hl & Hr & _).
  so (basic_fun _#7 Hl Hinterp) as HeqR.
  assert (exists z w,
            rel (den R) j' z w) as (z & w & Hzw).
    {
    subst R.
    clear Hs' Hl Hr.
    assert (rel (den A) j' (app m r) (app n t)) as Hmrnt.
      {
      apply (arrow_action_app _ j' (den (iutruncate (S j') Dom)) (den (iutruncate (S j') A))).
        {
        cut (rel (ceiling (S j') (arrow_urel stop i (den Dom) (den A))) j' m n).
          {
          intro H.
          rewrite -> ceiling_arrow in H.
          rewrite -> Nat.min_r in H; auto.
          omega.
          }
        split; auto.
        eapply urel_downward_leq; eauto.
        }
  
        {
        clear Hinterp.
        destruct Hrt as (_ & Hrt).
        split; auto.
        }
      }
    assert (rel (den A) j' (app p r) (app q t)) as Hprqt.
      {
      apply (arrow_action_app _ j' (den (iutruncate (S j') Dom)) (den (iutruncate (S j') A))).
        {
        cut (rel (ceiling (S j') (arrow_urel stop i (den Dom) (den A))) j' p q).
          {
          intro H.
          rewrite -> ceiling_arrow in H.
          rewrite -> Nat.min_r in H; auto.
          omega.
          }
        split; auto.
        eapply urel_downward_leq; eauto.
        }
  
        {
        clear Hinterp.
        destruct Hrt as (_ & Hrt).
        split; auto.
        }
      }
    assert (rel (den A) j' (app x r) (app y t)) as Hxryt.
      {
      apply (arrow_action_app _ j' (den (iutruncate (S j') Dom)) (den (iutruncate (S j') A))).
        {
        cut (rel (ceiling (S j') (arrow_urel stop i (den Dom) (den A))) j' x y).
          {
          intro H.
          rewrite -> ceiling_arrow in H.
          rewrite -> Nat.min_r in H; auto.
          omega.
          }
        split; auto.
        eapply urel_downward_leq; eauto.
        }
  
        {
        clear Hinterp.
        destruct Hrt as (_ & Hrt).
        split; auto.
        }
      }
    assert (pwctx j' (dot (app u2 r) (dot (app u1 r) (dot (app x r) (dot (app p r) (dot (app m r) s))))) (dot (app v2 t) (dot (app v1 t) (dot (app y t) (dot (app q t) (dot (app n t) s'))))) (hyp_tm (subst (dot (var 1) (dot (var 2) (sh 4))) b) :: hyp_tm (subst sh1 b) :: hyp_tm (subst (sh 2) a) :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hs''.
      {
      apply pwctx_cons_tm_seq.
        {
        apply pwctx_cons_tm_seq.
          {
          apply pwctx_cons_tm_seq.
            {
            apply (Hextends _#3 (iutruncate (S j') A)).
              {
              apply (pwctx_downward i); auto.
              omega.
              }
      
              {
              apply (basic_downward _#3 i); auto.
              omega.
              }
      
              {
              apply (basic_downward _#3 i); auto.
              omega.
              }
              
              {
              split; auto.
              }
      
              {
              split; auto.
              }
            }

            {
            apply (seqhyp_tm _#5 (iutruncate (S j') A)).
              {
              simpsub.
              apply (basic_downward _#3 i); auto.
              omega.
              }

              {
              simpsub.
              apply (basic_downward _#3 i); auto.
              omega.
              }

              {
              split; auto.
              }
            }

            {
            intros k z z' Hz.
            invertc Hz.
            intros c d z1 z1' Hz _ _ _ <- <-.
            invertc Hz.
            intros e f z z' Hz _ _ _ <- <-.
            so (Hseqa _#3 Hz) as (R & Hl & Hr & _).
            exists toppg, R.
            simpsub.
            auto.
            }
          }

          {
          simpsub.
          invert Hcl.
          intros _ _ Hcact.
          so (Hcact _#3 Hj (prod_action_ppair _#8 Hmn Hpq)) as Hl.
          clear Hcact.
          simpsubin Hl.
          rewrite -> (subst_into_closed _ _ m) in Hl; auto.
          rewrite -> (subst_into_closed _ _ p) in Hl; auto.
          so (interp_eval_refl _#6 (interp_pi _#8 (basic_downward _#7 Hj Hdoml) Hil)) as H.
          so (basic_fun _#7 H Hl) as Heq.
          clear H Hl.
          assert (rel (den (iupi stop j (iutruncate (S j) Dom) I)) j u1 v1) as Huv1'.
            {
            rewrite -> Heq.
            exact Huv1.
            }
          clear Huv1 Heq.
          so (pi_action_app _#10 Hrt Hj' Huv1') as Hinh.
          cbn -[iutruncate] in Hinh.
          invert Hil.
          intros _ _ Hiact.
          so (Hiact j' r t Hj' Hrt) as Hl.
          clear Hiact.
          simpsubin Hl.
          unfold subst1 in Hl.
          rewrite -> (subst_into_closed _ _ m) in Hl; auto.
          rewrite -> (subst_into_closed _ _ p) in Hl; auto.
          invert Hir.
          intros _ _ Hiact.
          so (Hiact j' r t Hj' Hrt) as Hr.
          clear Hiact.
          simpsubin Hr.
          unfold subst1 in Hr.
          rewrite -> (subst_into_closed _ _ n) in Hr; auto.
          rewrite -> (subst_into_closed _ _ q) in Hr; auto.
          apply (seqhyp_tm _#5 (pi1 I (urelspinj _ _ _ _ Hrt))); auto.
            {
            refine (basic_equiv _#7 _ _ Hl).
              {
              prove_hygiene.
              }
  
              {
              apply equiv_funct; auto using equiv_refl.
              apply equivsub_dot.
                {
                apply equiv_app; auto using equiv_refl.
                apply equiv_beta2.
                }
              apply equivsub_dot.
                {
                apply equiv_app; auto using equiv_refl.
                apply equiv_beta1.
                }
              apply equivsub_refl.
              }
            }
  
            {
            refine (basic_equiv _#7 _ _ Hr).
              {
              prove_hygiene.
              }
  
              {
              apply equiv_funct; auto using equiv_refl.
              apply equivsub_dot.
                {
                apply equiv_app; auto using equiv_refl.
                apply equiv_beta2.
                }
              apply equivsub_dot.
                {
                apply equiv_app; auto using equiv_refl.
                apply equiv_beta1.
                }
              apply equivsub_refl.
              }
            }
          }

          {
          intros k zz zz' Hz.
          invertc Hz.
          intros c d z z' Hz _ _ _ <- <-.
          so (Hseqb _#3 Hz) as (R & Hl & Hr & _).
          exists toppg, R.
          simpsub.
          auto.
          }
        }

        {
        simpsub.
        invert Hcl.
        intros _ _ Hcact.
        so (Hcact _#3 Hj (prod_action_ppair _#8 Hpq Hxy)) as Hl.
        clear Hcact.
        simpsubin Hl.
        rewrite -> (subst_into_closed _ _ p) in Hl; auto.
        rewrite -> (subst_into_closed _ _ x) in Hl; auto.
        so (interp_eval_refl _#6 (interp_pi _#8 (basic_downward _#7 Hj Hdoml) Hjl)) as H.
        so (basic_fun _#7 H Hl) as Heq.
        clear H Hl.
        assert (rel (den (iupi stop j (iutruncate (S j) Dom) J)) j u2 v2) as Huv2'.
          {
          rewrite -> Heq.
          exact Huv2.
          }
        clear Huv2 Heq.
        so (pi_action_app _#10 Hrt Hj' Huv2') as Hinh.
        cbn -[iutruncate] in Hinh.
        invert Hjl.
        intros _ _ Hjact.
        so (Hjact j' r t Hj' Hrt) as Hl.
        clear Hjact.
        simpsubin Hl.
        unfold subst1 in Hl.
        rewrite -> (subst_into_closed _ _ p) in Hl; auto.
        rewrite -> (subst_into_closed _ _ x) in Hl; auto.
        invert Hjr.
        intros _ _ Hjact.
        so (Hjact j' r t Hj' Hrt) as Hr.
        clear Hjact.
        simpsubin Hr.
        unfold subst1 in Hr.
        rewrite -> (subst_into_closed _ _ q) in Hr; auto.
        rewrite -> (subst_into_closed _ _ y) in Hr; auto.
        apply (seqhyp_tm _#5 (pi1 J (urelspinj _ _ _ _ Hrt))); auto.
          {
          refine (basic_equiv _#7 _ _ Hl).
            {
            prove_hygiene.
            }

            {
            apply equiv_funct; auto using equiv_refl.
            apply equivsub_dot.
              {
              apply equiv_app; auto using equiv_refl.
              apply equiv_beta2.
              }
            apply equivsub_dot.
              {
              apply equiv_app; auto using equiv_refl.
              apply equiv_beta1.
              }
            apply equivsub_refl.
            }
          }

          {
          refine (basic_equiv _#7 _ _ Hr).
            {
            prove_hygiene.
            }

            {
            apply equiv_funct; auto using equiv_refl.
            apply equivsub_dot.
              {
              apply equiv_app; auto using equiv_refl.
              apply equiv_beta2.
              }
            apply equivsub_dot.
              {
              apply equiv_app; auto using equiv_refl.
              apply equiv_beta1.
              }
            apply equivsub_refl.
            }
          }
        }

        {
        intros k zz zz' Hz.
        invertc Hz.
        intros e f ze zf Hz _ _ _ <- <-.
        invertc Hz.
        intros c3 d3 z3 z3' Hz Hcd3 _ _ <- <-.
        invertc Hz.
        intros c2 d2 z2 z2' Hz Hcd2 _ _ <- <-.
        invertc Hz.
        intros c1 d1 z z' Hz _ _ _ <- <-.
        invertc Hcd2.
        intros Az Hazl Hazr Hcd2.
        simpsubin Hazl.
        simpsubin Hazr.
        invertc Hcd3.
        intros Az' Hazl' _ Hcd3.
        simpsubin Hazl'.
        so (basic_fun _#7 Hazl Hazl').
        subst Az'.
        exploit (Hextends k z z' Az c2 d2 c3 d3) as Hz'; auto.
        so (Hseqb _#3 Hz') as (R & Hl & Hr & _).
        exists toppg, R.
        simpsub.
        auto.
        }
      }
    so (Hseqtrans _#3 Hs'') as (R & Hl & _ & Hsat & _).
    simpsubin Hl.
    so (basic_fun _#7 Hinterp Hl).
    subst R.
    exists (subst (dot (app u2 r) (dot (app u1 r) (dot (app x r) (dot (app p r) (dot (app m r) s))))) mt).
    exists (subst (dot (app v2 t) (dot (app v1 t) (dot (app y t) (dot (app q t) (dot (app n t) s'))))) mt).
    exact Hsat.
    }
  assert (pwctx j'
            (dot z (dot (app x r) (dot (app m r) s)))
            (dot w (dot (app y t) (dot (app n t) s')))
            (hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hs''.
    {
    apply pwctx_cons_tm_seq; auto.
      {
      apply (seqhyp_tm _#5 R); auto.
      }

      {
      intros k zz zz' Hzz.
      so (Hseqb _#3 Hzz) as (Q & Hql & Hqr & _).
      eauto.
      }
    }
  so (Hseqtriv _#3 Hs'') as (R' & Hl' & _ & Hrtriv & _).
  simpsubin Hl'.
  so (basic_fun _#7 Hl Hl').
  subst R'.
  subst R.
  exact Hrtriv.
  }
exists (iuquotient stop (iuarrow stop i Dom A) C hsnew htnew).
simpsub.
cbn [Nat.add].
do2 2 split.
  {
  apply interp_eval_refl.
  apply interp_quotient.
    {
    apply interp_eval_refl.
    apply interp_tarrow; auto.
    }

    {
    force_exact Hcl.
    f_equal.
    simpsub.
    cbn [Nat.add].
    reflexivity.
    }
  }

  {
  apply interp_eval_refl.
  apply interp_quotient.
    {
    apply interp_eval_refl.
    apply interp_tarrow; auto.
    }

    {
    force_exact Hcr.
    f_equal.
    simpsub.
    reflexivity.
    }
  }
so (Hseqmn _#3 Hs) as (R & Hl & _ & Hm & Hn & Hmn).
simpsubin Hl.
cbn [Nat.add] in Hl.
assert (interp toppg true i 
          (tarrow (subst s dom) (quotient (subst s a) (subst (dot (var 0) (dot (var 1) (compose s (sh 2)))) b)))
          (iuarrow stop i Dom (iuquotient stop A D hsold htold))) as Harrquot.
  {
  apply interp_eval_refl.
  apply interp_tarrow; auto.
  apply interp_eval_refl.
  apply interp_quotient; auto.
  force_exact Hdl.
  f_equal.
  simpsub.
  reflexivity.
  }
so (basic_fun _#7 Hl Harrquot).
subst R.
clear Hl Harrquot.
assert (forall j x y, rel (den Dom) j x y -> equiv x y) as Hdiagonal.
  {
  clear m n A Hal Har C Hcl Hcr D Hdl Hdr hsold htold hsnew htnew Hmn Hm Hn Hextends Hfnify Hseqa Hseqb Hseqsymm Hseqtrans Hseqtriv Hseqmn.
  intros j x y Hxy.
  so (basic_member_index _#9 Hdoml Hxy) as Hj.
  so (Hseqdom _#3 Hs) as (Dom' & Hdoml' & _ & Hmetdom).
  so (basic_fun _#7 Hdoml Hdoml').
  subst Dom'.
  clear Hdoml'.
  so (Hmetdom j x y Hj Hxy) as (Hxx & Hyy).
  so (urel_zigzag _#7 Hyy Hxy Hxx) as Hyx.
  assert (pwctx j (dot triv (dot y (dot x s))) (dot triv (dot y (dot x s'))) (hyp_tm (equal (subst (sh 2) dom) (var 1) (var 0)) :: hyp_tm (subst sh1 dom) :: hyp_tm dom :: G)) as Hs'.
    {
    apply pwctx_cons_tm_seq.
      {
      apply pwctx_cons_tm_seq.
        {
        apply pwctx_cons_tm_seq.
          {
          eapply pwctx_downward; eauto.
          }

          {
          apply (seqhyp_tm _#5 (iutruncate (S j) Dom)).
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
          intros k t t' Ht.
          so (Hseqdom _#3 Ht) as (R & Hl & Hr & _).
          eauto.
          }
        }

        {
        simpsub.
        apply (seqhyp_tm _#5 (iutruncate (S j) Dom)).
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
        intros k tt tt' Htt.
        invertc Htt.
        intros p q t t' Ht _ _ _ <- <-.
        so (Hseqdom _#3 Ht) as (R & Hl & Hr & _).
        simpsub.
        eauto.
        }
      }

      {
      simpsub.
      assert (j < S j) as Hjj by omega.
      apply (seqhyp_tm _#5 (iuequal stop true j (iutruncate (S j) Dom) x y x y (conj Hjj Hxx) (conj Hjj Hyy))).
        {
        apply interp_eval_refl.
        apply interp_equal.
        eapply basic_downward; eauto.
        }

        {
        rewrite -> iuequal_swap.
        cbn.
        apply interp_eval_refl.
        apply interp_equal.
        eapply basic_downward; eauto.
        }

        {
        do2 5 split; auto using star_refl; try prove_hygiene.
        exists x.
        split.
          {
          cbn.
          auto.
          }

          {
          split; auto.
          }
        }
      }

      {
      clear Dom Hdoml Hdomr Hxy Hxx Hyx Hyy Hmetdom.
      intros k tt tt' Htt.
      invertc Htt.
      intros p q t1 t1' Ht1 Hpq _ _ <- <-.
      invertc Ht1.
      intros m n t t' Ht Hmn _ _ <- <-.
      simpsub.
      invertc Hmn.
      intros Dom Hdoml Hdomr Hmn.
      invertc Hpq.
      intros Dom' Hdoml' _ Hpq.
      simpsubin Hdoml'.
      so (basic_fun _#7 Hdoml Hdoml').
      subst Dom'.
      exists toppg.
      exists (iuequal stop true k Dom m p n q Hmn Hpq).
      split.
        {
        apply interp_eval_refl.
        apply interp_equal; auto.
        }

        {
        rewrite -> iuequal_swap.
        apply interp_eval_refl.
        apply interp_equal; auto.
        }
      }
    }
  so (Hseqelem _#3 Hs') as (R & Hl & _).
  simpsubin Hl.
  invert (basic_value_inv _#6 value_sequal Hl).
  intros _ _ Hequiv _.
  exact Hequiv.
  }
assert (forall m n,
          rel (den (iuarrow stop i Dom (iuquotient stop A D hsold htold))) i (subst s m) (subst s' n)
          -> rel (den (iuquotient stop (iuarrow stop i Dom A) C hsnew htnew)) i (subst s m) (subst s' n)) as Hprop.
  {
  clear m n Hseqmn Hm Hn Hmn.
  intros m n Hmn.
  so (urel_closed _#5 Hmn) as (Hclm & Hcln').
  exists (subst s' n).
  exists (subst s m).
  exists (lam triv).
  exists (lam triv).
  so (Hseqa _#3 Hs) as (A' & Hal' & _ & Hmet).
  so (basic_fun _#7 Hal Hal').
  subst A'.
  clear Hal'.
  assert (rel (den (iuarrow stop i Dom A)) i (subst s m) (subst s m)) as Hml.
    {
    cbn in Hmn |- *.
    decompose Hmn.
    intros l l' _ _ _ Hsteps Hsteps' Hact.
    exists l, l.
    do2 5 split; auto.
    intros j p q Hj Hpq.
    so (urel_closed _#5 Hpq) as (Hclp & Hclq).
    so (Hact _#3 Hj Hpq) as H.
    cbn in H.
    decompose H.
    intros r t hrel hrel' Hl Hr _.
    (* Right here is the interesting part. *)
    exploit (Hmet j (subst1 p l) t) as (Hll & _); auto.
    refine (urel_equiv _#7 _ _ (equiv_refl _ _) _ Hll).
      {
      so (steps_hygiene _#4 Hsteps Hclm) as H.
      so (hygiene_invert_auto _#5 H) as (Hcll & _).
      cbn in Hcll.
      apply hygiene_subst1; auto.
      }

      {
      so (steps_hygiene _#4 Hsteps Hclm) as H.
      so (hygiene_invert_auto _#5 H) as (Hcll & _).
      cbn in Hcll.
      apply hygiene_subst1; auto.
      }
    unfold subst1.
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    eapply Hdiagonal; eauto.
    }
  assert (rel (den (iuarrow stop i Dom A)) i (subst s' n) (subst s' n)) as Hnr.
    {
    cbn in Hmn |- *.
    decompose Hmn.
    intros l l' _ _ _ Hsteps Hsteps' Hact.
    exists l', l'.
    do2 5 split; auto.
    intros j p q Hj Hpq.
    so (urel_closed _#5 Hpq) as (Hclp & Hclq).
    so (Hact _#3 Hj Hpq) as H.
    cbn in H.
    decompose H.
    intros r t hrel hrel' Hl Hr _.
    (* The interesting part, repeated. *)
    exploit (Hmet j r (subst1 q l')) as (_ & Hrr); auto.
    refine (urel_equiv _#7 _ _ _ (equiv_refl _ _) Hrr).
      {
      so (steps_hygiene _#4 Hsteps' Hcln') as H.
      so (hygiene_invert_auto _#5 H) as (Hcll & _).
      cbn in Hcll.
      apply hygiene_subst1; auto.
      }

      {
      so (steps_hygiene _#4 Hsteps' Hcln') as H.
      so (hygiene_invert_auto _#5 H) as (Hcll & _).
      cbn in Hcll.
      apply hygiene_subst1; auto.
      }
    unfold subst1.
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm.
    eapply Hdiagonal; eauto.
    }
  exists Hml, Hnr.
  cbn [pi1 nearrow_compose den_ne].
  invert Hcl.
  intros _ _ Hactc.
  so (Hactc _#3 (le_refl _) (prod_action_ppair stop (den (iuarrow stop i Dom A)) (den (iuarrow stop i Dom A)) i (subst s m) (subst s' n) (subst s m) (subst s' n) Hml Hnr)) as H.
  simpsubin H.
  eassert _ as H'; [refine (basic_equiv _#5 (pi (subst s dom) (subst (dot (app (subst (compose s' sh1) n) (var 0)) (dot (app (subst (compose s sh1) m) (var 0)) (compose s sh1))) b)) _ _ _ H) |].
    {
    prove_hygiene.
    eapply hygiene_subst; eauto.
    intros k Hk.
    destruct k as [|[|k]]; simpsub.
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
      apply hygiene_shift_permit; auto.
      }
    }

    {
    apply equiv_pi; auto using equiv_refl.
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot.
      {
      apply equiv_app; auto using equiv_refl.
      apply equiv_beta2.
      }
    apply equivsub_dot.
      {
      apply equiv_app; auto using equiv_refl.
      apply equiv_beta1.
      }
    apply equivsub_refl.
    }
  clear H.
  exploit (extract_functional toppg i (den Dom)
             (subst (dot 
                       (app (subst (compose s' sh1) n) (var 0))
                       (dot 
                          (app (subst (compose s sh1) m) (var 0))
                          (compose s sh1))) b)
             (subst (dot 
                       (app (subst (compose s' sh1) n) (var 0))
                       (dot 
                          (app (subst (compose s sh1) m) (var 0))
                          (compose s' sh1))) b))
             as H.
    {
    exact (f_equal den (basic_impl_iutruncate _#6 Hdoml)).
    }

    {
    eapply hygiene_subst; eauto.
    intros k Hk.
    destruct k as [|[|k]]; simpsub.
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
      apply hygiene_shift_permit; auto.
      }
    }

    {
    eapply hygiene_subst; eauto.
    intros k Hk.
    destruct k as [|[|k]]; simpsub.
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
      apply hygiene_shift_permit; auto.
      }
    }

    {
    clear H'.
    intros j p q Hpq.
    so (basic_member_index _#9 Hdoml Hpq) as Hj.
    simpsub.
    exploit (Hextends j s s' (iutruncate (S j) A) (app (subst s m) p) (app (subst s m) q) (app (subst s' n) p) (app (subst s' n) q)) as Hs'.
      {
      eapply pwctx_downward; eauto.
      }

      {
      eapply basic_downward; eauto.
      }

      {
      eapply basic_downward; eauto.
      }

      {
      split.
        {
        omega.
        }
      eapply (arrow_action_app _ j); eauto.
      so (urel_downward_leq _#6 Hj Hml) as (l & l' & _ & Hl).
      exists l, l'.
      split; auto.
      }

      {
      split.
        {
        omega.
        }
      eapply (arrow_action_app _ j); eauto.
      so (urel_downward_leq _#6 Hj Hnr) as (l & l' & _ & Hl).
      exists l, l'.
      split; auto.
      }
    so (Hseqb _#3 Hs') as (R & Hl & Hr & _).
    eauto.
    }
  destruct H as (E & Hel & Her).
  assert (interp toppg true i 
            (pi (subst s dom)
               (subst (dot 
                         (app (subst (compose s' sh1) n) (var 0))
                         (dot (app (subst (compose s sh1) m) (var 0)) (compose s sh1))) b))
            (iupi stop i Dom E)) as Hinterp.
    {
    apply interp_eval_refl.
    apply interp_pi; auto.
    }
  so (basic_fun _#7 H' Hinterp) as Heq.
  clear H'.
  assert (rel (den (iupi stop i Dom E)) i (lam triv) (lam triv)) as Hrel.
    {
    clear Hinterp Heq.
    cbn in Hmn |- *.
    decompose Hmn.
    intros l l' _ _ _ Hsteps Hsteps' Hact.
    exists triv, triv.
    do2 5 split; auto using star_refl.
      {
      prove_hygiene.
      }

      {
      prove_hygiene.
      }
    intros j p q Hj Hpq.
    so (urel_closed _#5 Hpq) as (Hclp & Hclq).
    simpsub.
    so (Hact _#3 Hj Hpq) as Hrel.
    cbn in Hrel.
    decompose Hrel.
    intros r t hrel hrel' Hmpt Hrnq Hacross.
    invert Hel.
    intros _ _ Heact.
    so (Heact _ _ _ Hj Hpq) as H.
    clear Heact.
    simpsubin H.
    exploit (Hextends j s s' (iutruncate (S j) A) (app (subst s m) p) (app (subst s m) q) (app (subst s' n) p) (app (subst s' n) q)) as Hs'.
      {
      eapply pwctx_downward; eauto.
      }

      {
      eapply basic_downward; eauto.
      }

      {
      eapply basic_downward; eauto.
      }

      {
      split.
        {
        omega.
        }
      eapply (arrow_action_app _ j); eauto.
      so (urel_downward_leq _#6 Hj Hml) as (z & z' & _ & Hz).
      exists z, z'.
      split; auto.
      }

      {
      split.
        {
        omega.
        }
      eapply (arrow_action_app _ j); eauto.
      so (urel_downward_leq _#6 Hj Hnr) as (z & z' & _ & Hz).
      exists z, z'.
      split; auto.
      }
    so (Hseqb _#3 Hs') as (R & Hl & Hr & _).
    so (basic_fun _#7 H Hl) as Heq.
    cut (rel (den R) j triv triv).
      {
      intro Hrel.
      force_exact Hrel.
      f_equal.
      f_equal.
      symmetry; auto.
      }
    clear H Heq.
    assert (exists x y, rel (den R) j x y) as H.
      {
      exists hrel, hrel'.
      force_exact Hacross.
      f_equal.
      f_equal.
      assert (rel (prod_urel stop (den A) (den A)) j (ppair (app (subst s m) p) (app (subst s' n) p)) (ppair (app (subst s m) q) (app (subst s' n) q))) as Hmpnp.
        {
        apply prod_action_ppair.
          {
          eapply (arrow_action_app _ i _ _ j); eauto.
          change (rel (den (iuarrow stop i Dom A)) j (subst s m) (subst s m)).
          apply (urel_downward_leq _ _ _ i); auto.
          }

          {
          eapply (arrow_action_app _ i _ _ j); eauto.
          change (rel (den (iuarrow stop i Dom A)) j (subst s' n) (subst s' n)).
          apply (urel_downward_leq _ _ _ i); auto.
          }
        }
      invert Hdl.
      intros _ _ Hdact.
      so (Hdact _#3 Hj Hmpnp) as H.
      simpsubin H.
      eassert _ as H'; [refine (basic_equiv _#5 (subst (dot (app (subst s' n) p) (dot (app (subst s m) p) s)) b) _ _ _ H) |].
        {
        prove_hygiene.
        }
    
        {
        apply equiv_funct; auto using equiv_refl.
        apply equivsub_dot.
          {
          apply equiv_beta2.
          }
        apply equivsub_dot.
          {
          apply equiv_beta1.
          }
        apply equivsub_refl.
        }
      clear H.
      so (basic_fun _#7 Hl H').
      subst R.
      clear H'.
      f_equal.
      (* The final interesting part. *)
      apply urelspinj_equal.
      apply prod_action_ppair.
        {
        apply (urel_equiv_1 _#3 (app (subst s m) p)).
          {
          so (steps_hygiene _#4 Hsteps Hclm) as H.
          so (hygiene_invert_auto _#5 H) as (Hcll & _).
          cbn in Hcll.
          apply hygiene_subst1; auto.
          }

          {
          apply (equiv_trans _ _ (app (lam l) p)).
            {
            apply equiv_app; auto using equiv_refl.
            apply steps_equiv; auto.
            }

            {
            apply equiv_beta.
            }
          }

          {
          eapply (arrow_action_app _ i _ _ j); eauto.
          change (rel (den (iuarrow stop i Dom A)) j (subst s m) (subst s m)).
          apply (urel_downward_leq _ _ _ i); auto.
          }
        }

        {
        apply (urel_equiv_2 _#4 (subst1 q l')).
          {
          prove_hygiene.
          }

          {
          apply equiv_symm.
          apply (equiv_trans _ _ (app (lam l') q)).
            {
            apply equiv_app; auto using equiv_refl.
            apply steps_equiv; auto.
            }

            {
            apply equiv_beta.
            }
          }

          {
          exact Hrnq.
          }
        }
      }
    destruct H as (x & y & Hxy).
    assert (pwctx j 
              (dot x (dot (app (subst s' n) p) (dot (app (subst s m) p) s)))
              (dot y (dot (app (subst s' n) q) (dot (app (subst s m) q) s')))
              (hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hs''.
      {
      apply pwctx_cons_tm_seq; auto.
        {
        apply (seqhyp_tm _#5 R); auto.
        }

        {
        intros k u u' Hu.
        so (Hseqb _#3 Hu) as (Q & Hql & Hqr & _).
        eauto.
        }
      }
    so (Hseqtriv _#3 Hs'') as (R' & Hl' & _ & Hrtriv & _).
    simpsubin Hl'.
    so (basic_fun _#7 Hl Hl').
    subst R'.
    clear Hl'.
    simpsubin Hrtriv.
    exact Hrtriv.
    }
  rewrite <- Heq in Hrel.
  exact Hrel.
  }
do2 2 split.
  {
  apply Hprop; auto.
  }

  {
  apply Hprop; auto.
  }

  {
  apply Hprop; auto.
  }
Qed.
