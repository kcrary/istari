
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


Lemma sound_pi_quotient_commute :
  forall G a b c m n,
    pseq G (deq triv triv (symmetrical a))
    -> pseq (hyp_tm a :: G) (deq triv triv (symmetrical b))
    -> pseq (hyp_tm (subst sh1 b) :: hyp_tm b :: hyp_tm a :: G) (deqtype c c)
    -> pseq (hyp_tm a :: G) (deqtype (quotient b c) (quotient b c))
    -> pseq G (deqtype (quotient (pi a b) (pi (subst (sh 2) a) (subst (dot (app (var 1) (var 0)) (dot (app (var 2) (var 0)) (dot (var 0) (sh 3)))) c))) (quotient (pi a b) (pi (subst (sh 2) a) (subst (dot (app (var 1) (var 0)) (dot (app (var 2) (var 0)) (dot (var 0) (sh 3)))) c))))
    -> pseq (hyp_tm c :: hyp_tm (subst sh1 b) :: hyp_tm b :: hyp_tm a :: G) (deq triv triv (subst sh1 c))
    -> pseq (hyp_tm (equal (subst (sh 2) a) (var 1) (var 0)) :: hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deq triv triv (sequal (var 2) (var 1)))
    -> pseq G (deq m n (pi a (quotient b c)))
    -> pseq G (deq m n (quotient (pi a b) 
                          (pi (subst (sh 2) a)
                             (subst (dot (app (var 1) (var 0)) (dot (app (var 2) (var 0)) (dot (var 0) (sh 3)))) c)))).
Proof.
intros G a b c m n.
revert G.
refine (seq_pseq 3 [] a [hyp_emp] b [hyp_emp; hyp_emp; hyp_emp] c 8 [] _ [_] _ [_; _; _] _ [_] _ [] _ [_; _; _; _] _ [_; _; _] _ [] _ _ _); cbn.
intros G Hcla Hclb Hclc Hseqa Hseqb Hseqc Hseqquotbc Hseqquotabc Hseqtriv Hseqelem Hseqmn.
rewrite -> seq_symmetrical in Hseqa, Hseqb.
rewrite -> seq_eqtype in Hseqc, Hseqquotbc, Hseqquotabc.
rewrite -> seq_deq in Hseqtriv, Hseqelem, Hseqmn |- *.
assert (top <<= stop) as Htopstop.
  {
  apply succ_nodecrease.
  }
assert (forall i s s' A j x y,
          pwctx i s s' G
          -> interp toppg true i (subst s a) A
          -> interp toppg false i (subst s' a) A
          -> rel (den A) j x y
          -> pwctx j (dot x s) (dot y s') (hyp_tm a :: G)) as HctxA.
  {
  intros i s s' A j x y Hs Hal Har Hxy.
  so (basic_member_index _#9 Hal Hxy) as Hj.
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
assert (forall i s s' A B j x y k m n p q,
          pwctx i s s' G
          -> interp toppg true i (subst s a) A
          -> interp toppg false i (subst s' a) A
          -> functional the_system toppg true i (den A) (subst (under 1 s) b) B
          -> functional the_system toppg false i (den A) (subst (under 1 s') b) B
          -> forall (hxy : rel (den A) j x y),
               rel (den (pi1 B (urelspinj (den A) j x y hxy))) k m p
               -> rel (den (pi1 B (urelspinj (den A) j x y hxy))) k n q
               -> pwctx k (dot n (dot m (dot x s))) (dot q (dot p (dot y s'))) (hyp_tm (subst sh1 b) :: hyp_tm b :: hyp_tm a :: G)) as HctxB.
  {
  clear m n Hseqmn.
  intros i s s' A B j x y k m n p q Hs Hal Har Hbl Hbr Hxy Hmp Hnq.
  so (basic_member_index _#9 Hal Hxy) as Hj.
  invert Hbl.
  intros _ _ Hactb.
  so (Hactb _#3 Hj Hxy) as Hbxl.
  simpsubin Hbxl.
  so (basic_member_index _#9 Hbxl Hmp) as Hk.
  clear Hbxl.
  so (le_trans _#3 Hk Hj) as Hki.
  apply pwctx_cons_tm_seq.
    {
    apply pwctx_cons_tm_seq.
      {
      eapply HctxA; eauto.
      eapply (urel_downward_leq _ _ _ j); eauto.
      }

      {
      apply (seqhyp_tm _#5 (iutruncate (S k) (pi1 B (urelspinj _#4 Hxy)))); auto.
        {
        apply (basic_downward _ _ _ j); auto.
        invert Hbl.
        intros _ _ Hact.
        so (Hact _#3 Hj Hxy) as H.
        simpsubin H.
        exact H.
        }

        {
        apply (basic_downward _ _ _ j); auto.
        invert Hbr.
        intros _ _ Hact.
        so (Hact _#3 Hj Hxy) as H.
        simpsubin H.
        exact H.
        }

        {
        split; auto.
        }
      }
      
      {
      intros l t t' Ht.
      so (Hseqb _#3 Ht) as (R & Hl & Hr & _).
      eauto.
      }
    }

    {
    apply (seqhyp_tm _#5 (iutruncate (S k) (pi1 B (urelspinj _#4 Hxy)))); auto.
      {
      apply (basic_downward _ _ _ j); auto.
      invert Hbl.
      intros _ _ Hact.
      so (Hact _#3 Hj Hxy) as H.
      simpsubin H.
      simpsub.
      exact H.
      }

      {
      apply (basic_downward _ _ _ j); auto.
      invert Hbr.
      intros _ _ Hact.
      so (Hact _#3 Hj Hxy) as H.
      simpsubin H.
      simpsub.
      exact H.
      }

      {
      split; auto.
      }
    }
    
    {
    intros l tt tt' Htt.
    invert Htt.
    intros r u t t' Ht _ _ _ <- <-.
    so (Hseqb _#3 Ht) as (R & Hl & Hr & _).
    exists toppg, R.
    simpsub.
    auto.
    }
  }
assert (forall i s s' A B j x y k m n p q C u v,
          pwctx i s s' G
          -> interp toppg true i (subst s a) A
          -> interp toppg false i (subst s' a) A
          -> functional the_system toppg true i (den A) (subst (under 1 s) b) B
          -> functional the_system toppg false i (den A) (subst (under 1 s') b) B
          -> forall 
               (hxy : rel (den A) j x y)
               (hmp : rel (den (pi1 B (urelspinj (den A) j x y hxy))) k m p)
               (hnq : rel (den (pi1 B (urelspinj (den A) j x y hxy))) k n q),
                 interp toppg true k (subst (dot n (dot m (dot x s))) c) C
                 -> interp toppg false k (subst (dot q (dot p (dot y s'))) c) C
                 -> rel (den C) k u v
                 -> pwctx k (dot u (dot n (dot m (dot x s)))) (dot v (dot q (dot p (dot y s')))) (hyp_tm c :: hyp_tm (subst sh1 b) :: hyp_tm b :: hyp_tm a :: G)) as HctxC.
  {
  clear m n Hseqmn.
  intros i s s' A B j x y k m n p q C u v Hs Hal Har Hbl Hbr Hxy Hmp Hnq Hcl Hcr Huv.
  apply pwctx_cons_tm_seq.
    {
    eapply HctxB; eauto.
    }

    {
    apply (seqhyp_tm _#5 C); auto.
    }

    {
    intros l t t' Ht.
    so (Hseqc _#3 Ht) as (R & Hct & Hct' & _).
    eauto.
    }
  }
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & Hmeta).
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as H.
  {
  exact (f_equal den (basic_impl_iutruncate _#6 Hal)).
  }

  {
  eapply subst_closub_under_permit; eauto.
  }

  {
  eapply subst_closub_under_permit; eauto.
  }

  {
  intros j x y Hxy.
  so (Hseqb _#3 (HctxA _#7 Hs Hal Har Hxy)) as (B & Hbl & Hbr & _).
  exists B.
  simpsub.
  auto.
  }
destruct H as (B & Hbl & Hbr).
so (Hseqquotabc _#3 Hs) as (Q2 & Hq2l & Hq2r & _).
simpsubin Hq2l.
simpsubin Hq2r.
cbn [Nat.add] in Hq2l, Hq2r.
exists Q2.
simpsub.
cbn [Nat.add].
do2 2 split; auto.
exploit (extract_functional toppg i (den A) (subst (under 1 s) (quotient b c)) (subst (under 1 s') (quotient b c))) as H.
  {
  exact (f_equal den (basic_impl_iutruncate _#6 Hal)).
  }

  {
  eapply subst_closub_under_permit; eauto.
  prove_hygiene.
  }

  {
  eapply subst_closub_under_permit; eauto.
  prove_hygiene.
  }

  {
  intros j x y Hxy.
  so (Hseqquotbc _#3 (HctxA _#7 Hs Hal Har Hxy)) as (R & Hl & Hr & _).
  exists R.
  simpsub.
  simpsubin Hl.
  simpsubin Hr.
  cbn [Nat.add] in Hl, Hr |- *.
  auto.
  }
destruct H as (Q1 & Hq1l & Hq1r).
simpsubin Hq1l.
simpsubin Hq1r.
cbn [Nat.add] in Hq1l, Hq1r.
assert (forall m n,
          rel (den (iupi stop i A Q1)) i (subst s m) (subst s' n)
          -> rel (den Q2) i (subst s m) (subst s' n)) as Hprop.
2:{
  so (Hseqmn _#3 Hs) as (R & Hl & _ & Hm & Hn & Hmn).
  simpsubin Hl.
  assert (interp toppg true i (subst s (pi a (quotient b c))) (iupi stop i A Q1)) as Haq1l.
    {
    simpsub.
    cbn [Nat.add].
    apply interp_eval_refl.
    apply interp_pi; auto.
    }
  simpsubin Haq1l.
  so (basic_fun _#7 Hl Haq1l).
  subst R.
  do2 2 split; apply Hprop; auto.
  }
clear m n Hseqmn.
assert (forall j x y, rel (den A) j x y -> equiv x y) as Hdiagonal.
  {
  intros j x y Hxy.
  so (basic_member_index _#9 Hal Hxy) as Hj.
  so (Hmeta j x y Hj Hxy) as (Hxx & Hyy).
  so (urel_zigzag _#7 Hyy Hxy Hxx) as Hyx.
  assert (pwctx j (dot triv (dot y (dot x s))) (dot triv (dot y (dot x s'))) (hyp_tm (equal (subst (sh 2) a) (var 1) (var 0)) :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hs'.
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

        {
        simpsub.
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
        intros k tt tt' Htt.
        invertc Htt.
        intros p q t t' Ht _ _ _ <- <-.
        so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
        simpsub.
        eauto.
        }
      }

      {
      simpsub.
      assert (j < S j) as Hjj by omega.
      apply (seqhyp_tm _#5 (iuequal stop true j (iutruncate (S j) A) x y x y (conj Hjj Hxx) (conj Hjj Hyy))).
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
invert (basic_value_inv _#6 value_quotient Hq2l).
intros AB AC hs ht Habl Hacl Heq1.
so (basic_fun _#7 Habl (interp_eval_refl _#6 (interp_pi _#8 Hal Hbl))).
subst AB.
clear Habl.
subst Q2.
assert (forall j x y (hxy : rel (den A) j x y),
          exists C hs' ht',
            functional the_system toppg true j (prod_urel stop (den (pi1 B (urelspinj _#4 hxy))) (den (pi1 B (urelspinj _#4 hxy)))) (subst (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) (dot x (compose s sh1)))) c) C
            /\ pi1 Q1 (urelspinj _#4 hxy) = iuquotient stop (pi1 B (urelspinj _#4 hxy)) C hs' ht') as Hatoc.
  {
  intros j x y Hxy.
  so (basic_member_index _#9 Hal Hxy) as Hj.
  so (urel_closed _#5 Hxy) as (Hclx & Hcly).
  exploit (extract_functional toppg j (prod_urel stop (den (pi1 B (urelspinj _#4 Hxy))) (den (pi1 B (urelspinj _#4 Hxy)))) (subst (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) (dot x (compose s sh1)))) c) (subst (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) (dot y (compose s' sh1)))) c)) as (C & Hcl & _).
    {
    rewrite -> ceiling_prod.
    invert Hbl.
    intros _ _ Hactb.
    so (Hactb _#3 Hj Hxy) as Hl.
    simpsubin Hl.
    so (f_equal den (basic_impl_iutruncate _#6 Hl)) as Heq.
    f_equal; auto.
    }

    {
    eapply hygiene_subst; eauto.
    intros k Hk.
    destruct k as [|[|[|k]]]; simpsub; prove_hygiene.
    }

    {
    eapply hygiene_subst; eauto.
    intros k Hk.
    destruct k as [|[|[|k]]]; simpsub; prove_hygiene.
    }
  
    {
    intros k m p Hmp.
    so (urel_closed _#5 Hmp) as (Hclm & Hclp).
    cbn in Hmp.
    decompose Hmp.
    intros m1 p1 m2 p2 _ _ Hstepsm Hstepsp Hmp1 Hmp2.
    so (Hseqc _#3 (HctxB _#13 Hs Hal Har Hbl Hbr Hxy Hmp1 Hmp2)) as (R & Hl & Hr & _).
    exists R.
    simpsub.
    unfold subst1.
    rewrite -> (subst_into_closed _ _ x); auto.
    rewrite -> (subst_into_closed _ _ y); auto.
    split.
      {
      apply (basic_equiv _ _ _ _ (subst (dot m2 (dot m1 (dot x s))) c)); auto.
        {
        prove_hygiene.
        }

        {
        apply equiv_funct; auto using equiv_refl.
        apply equivsub_dot.
          {
          apply equiv_symm.
          apply steps_equiv.
          eapply star_trans.
            {
            apply (star_map' _ _ ppi2); eauto using step_ppi21.
            }
          apply star_one.
          apply step_ppi22.
          }
        apply equivsub_dot.
          {
          apply equiv_symm.
          apply steps_equiv.
          eapply star_trans.
            {
            apply (star_map' _ _ ppi1); eauto using step_ppi11.
            }
          apply star_one.
          apply step_ppi12.
          }
        apply equivsub_refl.
        }
      }

      {
      apply (basic_equiv _ _ _ _ (subst (dot p2 (dot p1 (dot y s'))) c)); auto.
        {
        prove_hygiene.
        }

        {
        apply equiv_funct; auto using equiv_refl.
        apply equivsub_dot.
          {
          apply equiv_symm.
          apply steps_equiv.
          eapply star_trans.
            {
            apply (star_map' _ _ ppi2); eauto using step_ppi21.
            }
          apply star_one.
          apply step_ppi22.
          }
        apply equivsub_dot.
          {
          apply equiv_symm.
          apply steps_equiv.
          eapply star_trans.
            {
            apply (star_map' _ _ ppi1); eauto using step_ppi11.
            }
          apply star_one.
          apply step_ppi12.
          }
        apply equivsub_refl.
        }
      }
    }
  exists C.
  invert Hq1l.
  intros _ _ Hact.
  so (Hact _#3 Hj Hxy) as Hq1xl.
  simpsubin Hq1xl.
  cbn [Nat.add] in Hq1xl.
  invert (basic_value_inv _#6 value_quotient Hq1xl).
  intros B' C' hs'' ht'' Hbxl Hcxl Heq.
  invert Hbl.
  intros _ _ Hbact.
  so (Hbact _#3 Hj Hxy) as Hbxl'.
  simpsubin Hbxl'.
  so (basic_fun _#7 Hbxl Hbxl').
  subst B'.
  clear Hbxl'.
  simpsubin Hcxl.
  rewrite -> (subst_into_closed _ _ x) in Hcxl; auto.
  so (functional_fun _#8 Hcl Hcxl).
  subst C'.
  exists hs'', ht''.
  split; auto.
  }
intros m n Hmn.
so (urel_closed _#5 Hmn) as (Hclsm & Hclsn).
cbn in Hmn.
decompose Hmn.
intros l l' _ _ _ Hsteps Hsteps' Hactmn.
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hsteps Hclsm)) as H; cbn in H.
destruct H as (Hcll & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hsteps' Hclsn)) as H; cbn in H.
destruct H as (Hcll' & _).
assert (rel (den (iupi stop i A B)) i (subst s m) (subst s m)) as Hm.
  {
  cbn.
  exists l, l.
  do2 5 split; auto.
  intros j x y Hj Hxy.
  so (urel_closed _#5 Hxy) as (Hclx & Hcly).
  so (Hatoc _#3 Hxy) as (C & hs'' & ht'' & Hcxl & Heq).
  so (Hactmn _#3 Hj Hxy) as Hlxy.
  assert (rel (den (iuquotient stop (pi1 B (urelspinj _#4 Hxy)) C hs'' ht'')) j (subst1 x l) (subst1 y l')) as Hlxy'.
    {
    force_exact Hlxy.
    f_equal.
    f_equal.
    exact Heq.
    }
  clear Hlxy.
  rename Hlxy' into Hlxy.
  cbn in Hlxy.
  decompose Hlxy.
  intros m3 p3 u v Hm Hn Huv.
  so (Hdiagonal _#3 Hxy) as Hequivxy.
  so (Hseqb _#3 (HctxA _#7 Hs Hal Har Hxy)) as (B' & Hl & _ & Hmetb).
  invert Hbl.
  intros _ _ Hactb.
  so (Hactb _#3 Hj Hxy) as Hl'.
  simpsubin Hl'.
  so (basic_fun _#7 Hl Hl').
  subst B'.
  clear Hl Hl'.
  so (Hmetb _#3 (le_refl _) Hm) as (H & _).
  apply (urel_equiv_2 _#4 (subst1 x l)).
    {
    apply hygiene_subst1; auto.
    }

    {
    unfold subst1.
    apply equiv_funct1; auto using equiv_refl.
    }
  exact H.
  }
assert (rel (den (iupi stop i A B)) i (subst s' n) (subst s' n)) as Hn.
  {
  clear Hm.
  cbn.
  exists l', l'.
  do2 5 split; auto.
  intros j x y Hj Hxy.
  so (urel_closed _#5 Hxy) as (Hclx & Hcly).
  so (Hatoc _#3 Hxy) as (C & hs'' & ht'' & Hcxl & Heq).
  so (Hactmn _#3 Hj Hxy) as Hlxy.
  assert (rel (den (iuquotient stop (pi1 B (urelspinj _#4 Hxy)) C hs'' ht'')) j (subst1 x l) (subst1 y l')) as Hlxy'.
    {
    force_exact Hlxy.
    f_equal.
    f_equal.
    exact Heq.
    }
  clear Hlxy.
  rename Hlxy' into Hlxy.
  cbn in Hlxy.
  decompose Hlxy.
  intros m3 p3 u v Hm Hn Huv.
  so (Hdiagonal _#3 Hxy) as Hequivxy.
  so (Hseqb _#3 (HctxA _#7 Hs Hal Har Hxy)) as (B' & Hl & _ & Hmetb).
  invert Hbl.
  intros _ _ Hactb.
  so (Hactb _#3 Hj Hxy) as Hl'.
  simpsubin Hl'.
  so (basic_fun _#7 Hl Hl').
  subst B'.
  clear Hl Hl'.
  so (Hmetb _#3 (le_refl _) Hn) as (_ & H).
  apply (urel_equiv_1 _#3 (subst1 y l')).
    {
    apply hygiene_subst1; auto.
    }

    {
    unfold subst1.
    apply equiv_funct1; auto using equiv_refl, equiv_symm.
    }
  exact H.
  }
exists (subst s' n), (subst s m), (lam triv), (lam triv).
exists Hm, Hn.
cbn.
invert Hacl.
intros _ _ Hactac.
so (Hactac _#3 (le_refl _) (prod_action_ppair stop (den (iupi stop i A B)) (den (iupi stop i A B)) i _ _ _ _ Hm Hn)) as Hacml.
simpsubin Hacml.
invert (basic_value_inv _#6 value_pi Hacml).
clear Hactac Hacml.
intros A' C Hal' Hcl Heq.
so (basic_fun _#7 Hal Hal').
subst A'.
clear Hal'.
cut (rel (den (iupi stop i A C)) i (lam triv) (lam triv)).
  {
  intro H.
  force_exact H.
  f_equal.
  f_equal.
  exact Heq.
  }
clear Heq.
exists triv, triv.
do2 5 split; auto using star_refl; try prove_hygiene.
intros j x y Hj Hxy.
so (urel_closed _#5 Hxy) as (Hclx & Hcly).
simpsub.
invert Hcl.
intros _ _ Hactc.
so (Hactc _#3 Hj Hxy) as Hcmxl.
clear Hactc.
simpsubin Hcmxl.
eassert _ as Hcmxl'; [refine (basic_equiv _#5 (subst (dot (subst1 x l') (dot (subst1 x l) (dot x s))) c) _ _ _ Hcmxl)|].
  {
  eapply hygiene_subst; eauto.
  intros k Hk.
  destruct k as [|[|[|k]]]; simpsub; auto.
    {
    apply hygiene_subst1; auto.
    }

    {
    apply hygiene_subst1; auto.
    }
  }

  {
  apply equiv_funct; auto using equiv_refl.
  apply equivsub_dot.
    {
    eapply equiv_trans.
      {
      apply equiv_app.
        {
        eapply equiv_trans.
          {
          apply equiv_beta2.
          }
        apply steps_equiv; eauto.
        }
      apply equiv_refl.
      }
    eapply equiv_beta.
    }
  apply equivsub_dot.
    {
    eapply equiv_trans.
      {
      apply equiv_app.
        {
        eapply equiv_trans.
          {
          apply equiv_beta1.
          }
        apply steps_equiv; eauto.
        }
      apply equiv_refl.
      }
    eapply equiv_beta.
    }
  apply equivsub_refl.
  }
clear Hcmxl.
rename Hcmxl' into Hcmxl.
assert (rel (den (pi1 B (urelspinj _#4 Hxy))) j (subst1 x l) (subst1 y l)) as Hxyl.
  {
  cbn in Hm.
  decompose Hm.
  intros l'' l''' _ _ _ Hsteps'' Hsteps''' Hact.
  so (equiv_value _ _ _ value_lam value_lam (equiv_trans _#4 (equiv_symm _#3 (steps_equiv _#3 Hsteps)) (steps_equiv _#3 Hsteps''))) as H.
  invertc H.
  intros H _.
  invertc H.
  intros Hequiv _.
  so (equiv_value _ _ _ value_lam value_lam (equiv_trans _#4 (equiv_symm _#3 (steps_equiv _#3 Hsteps)) (steps_equiv _#3 Hsteps'''))) as H.
  invertc H.
  intros H _.
  invertc H.
  intros Hequiv' _.
  apply (urel_equiv _#3 (subst1 x l'') _ (subst1 y l''')).
    {
    apply hygiene_subst1; auto.
    }

    {
    apply hygiene_subst1; auto.
    }

    {
    apply equiv_subst1.
    apply equiv_symm; auto.
    }

    {
    apply equiv_subst1.
    apply equiv_symm; auto.
    }
  apply Hact; auto.
  }
assert (rel (den (pi1 B (urelspinj _#4 Hxy))) j (subst1 x l') (subst1 y l')) as Hxyl'.
  {
  cbn in Hn.
  decompose Hn.
  intros l'' l''' _ _ _ Hsteps'' Hsteps''' Hact.
  so (equiv_value _ _ _ value_lam value_lam (equiv_trans _#4 (equiv_symm _#3 (steps_equiv _#3 Hsteps')) (steps_equiv _#3 Hsteps''))) as H.
  invertc H.
  intros H _.
  invertc H.
  intros Hequiv _.
  so (equiv_value _ _ _ value_lam value_lam (equiv_trans _#4 (equiv_symm _#3 (steps_equiv _#3 Hsteps')) (steps_equiv _#3 Hsteps'''))) as H.
  invertc H.
  intros H _.
  invertc H.
  intros Hequiv' _.
  apply (urel_equiv _#3 (subst1 x l'') _ (subst1 y l''')).
    {
    apply hygiene_subst1; auto.
    }

    {
    apply hygiene_subst1; auto.
    }

    {
    apply equiv_subst1.
    apply equiv_symm; auto.
    }

    {
    apply equiv_subst1.
    apply equiv_symm; auto.
    }
  apply Hact; auto.
  }
so (Hseqc _#3 (HctxB _#13 Hs Hal Har Hbl Hbr Hxy Hxyl Hxyl')) as (Cmx & Hcmxl' & Hcmxr & _).
so (basic_fun _#7 Hcmxl Hcmxl').
clear Hcmxl'.
subst Cmx.
cut (exists u v, rel (den (pi1 C (urelspinj _#4 Hxy))) j u v).
  {
  intros (u & v & Huv).
  so (Hseqtriv _#3 (HctxC _#16 Hs Hal Har Hbl Hbr Hxy Hxyl Hxyl' Hcmxl Hcmxr Huv)) as (Cmx & Hcmxl' & _ & Htriv & _).
  simpsubin Hcmxl'.
  so (basic_fun _#7 Hcmxl Hcmxl').
  clear Hcmxl'.
  subst Cmx.
  simpsubin Htriv.
  exact Htriv.
  }
so (Hactmn _#3 Hj Hxy) as Hxyll.
so (Hatoc _#3 Hxy) as (Cx & hs' & ht' & Hcxl & Heq).
assert (rel (den (iuquotient stop (pi1 B (urelspinj _#4 Hxy)) Cx hs' ht')) j (subst1 x l) (subst1 y l')) as Hxyll'.
  {
  force_exact Hxyll.
  f_equal.
  f_equal.
  exact Heq.
  }
clear Hxyll.
rename Hxyll' into Hxyll.
clear Heq.
cbn in Hxyll.
decompose Hxyll.
intros m3 n3 u v Hm3 Hn3 Huv.
exists u, v.
invert Hcxl.
intros _ _ Hact.
so (Hact _#3 (le_refl _) (prod_action_ppair stop (den (pi1 B (urelspinj (den A) j x y Hxy))) (den (pi1 B (urelspinj (den A) j x y Hxy))) j (subst1 x l) (subst1 x l') (subst1 y l) (subst1 y l') Hxyl Hxyl')) as Hcmxl'.
simpsubin Hcmxl'.
eassert _ as Hcmxl''; [refine (basic_equiv _#5 (subst (dot (subst1 x l') (dot (subst1 x l) (dot x s))) c) _ _ _ Hcmxl')|].
  {
  eapply hygiene_subst; eauto.
  intros k Hk.
  destruct k as [|[|[|k]]]; simpsub; auto.
    {
    apply hygiene_subst1; auto.
    }

    {
    apply hygiene_subst1; auto.
    }
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
  rewrite -> (subst_into_closed _ _ x); auto.
  apply equivsub_refl.
  }
so (basic_fun _#7 Hcmxl Hcmxl'') as Heq.
clear Hcmxl' Hcmxl''.
rewrite -> Heq.
clear Heq.
force_exact Huv.
f_equal.
f_equal.
f_equal.
apply urelspinj_equal.
apply prod_action_ppair; auto.
Qed.
