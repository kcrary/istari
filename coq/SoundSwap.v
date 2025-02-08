
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
Require Import SemanticsSet.
Require Import SemanticsSimple.
Require Import SemanticsPi.
Require Import SoundFut.
Require Import Urelsp.
Require Import ProperDownward.
Require Import ProperLevel.



Local Ltac prove_hygiene :=
  repeat (apply hygiene_auto; cbn; repeat2 split; auto);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1, subst_closub;
  try (apply hygiene_var; cbn; auto; done).


Lemma sound_future_squash_swap :
  forall G m a,
    pseq (promote G) (deqtype a a)
    -> pseq G (deq m m (set unittp (fut (subst sh1 a))))
    -> pseq G (deq (next triv) (next triv) (fut (set unittp (subst sh1 a)))).
Proof.
intros G m a.
revert G.
refine (seq_pseq_promote 1 [] a 2 true [] _ false [] _ _ _); cbn.
intros G Hcla Hseqa Hseq.
rewrite -> seq_deq in Hseq |- *.
rewrite -> seq_eqtype in Hseqa.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq _ _ _ Hs) as (R & Hl & Hr & Hm & _).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_set Hl).
intros C F Hcl Hf Heql.
invert (basic_value_inv _#6 value_set Hr).
intros C' F' Hcr Hf' Heqr.
so (iuset_inj _#5 (eqtrans Heql (eqsymm Heqr))).
subst C'.
clear Heqr.
subst R.
invert Hf.
intros _ _ Hact.
destruct i as [| i].
  {
  exists (iufut0 stop).
  simpsub.
  do2 4 split.
    {
    apply interp_eval_refl.
    apply interp_fut_zero.
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }

    {
    apply interp_eval_refl.
    apply interp_fut_zero.
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }

    {
    cbn.
    exists triv, triv.
    do2 5 split; auto using star_refl; try prove_hygiene.
    intro H.
    omega.
    }

    {
    cbn.
    exists triv, triv.
    do2 5 split; auto using star_refl; try prove_hygiene.
    intro H.
    omega.
    }

    {
    cbn.
    exists triv, triv.
    do2 5 split; auto using star_refl; try prove_hygiene.
    intro H.
    omega.
    }
  }
invert (basic_value_inv _#6 value_unittp Hcl).
intros <-.
so (Hseqa _ _ _ (pwctx_promote _#4 Hs)) as (A & Hal & Har & _).
so (interp_eval_refl _#6 (interp_fut _#6 Hal)) as Hfal.
cbn in Hm.
decompose Hm.
intros p q Hm' Hpq.
so (Hact (S i) (subst s m) (subst s' m) (le_refl _) Hm') as Hfal'.
simpsubin Hfal'.
so (interp_fun _#7 Hfal Hfal') as Heqf.
cbn in Heqf.
unfold wiurel_ofe in Heqf.
rewrite <- Heqf in Hpq.
cbn in Hpq.
decompose Hpq.
intros r t _ Hclr Hclt _ _ Hrtif.
cbn in Hrtif.
assert (S i > 0) as Hpos by omega.
so (Hrtif Hpos) as Hrt.
exists (iufut stop (S i) (iuset stop (iubase (unit_urel stop i)) (semiconst_ne _ A))).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl.
  apply interp_fut.
  apply interp_eval_refl.
  apply interp_set.
    {
    apply interp_eval_refl.
    apply interp_unit.
    }
  apply functional_i.
    {
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }

    {
    rewrite -> den_iubase.
    rewrite -> ceiling_unit.
    f_equal.
    rewrite -> Nat.min_id.
    reflexivity.
    }
  intros j n n' Hj Hn.
  simpsub.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  eapply basic_downward; eauto.
  }

  {
  apply interp_eval_refl.
  apply interp_fut.
  apply interp_eval_refl.
  apply interp_set.
    {
    apply interp_eval_refl.
    apply interp_unit.
    }
  apply functional_i.
    {
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }

    {
    rewrite -> den_iubase.
    rewrite -> ceiling_unit.
    f_equal.
    rewrite -> Nat.min_id.
    reflexivity.
    }
  intros j n n' Hj Hn.
  simpsub.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  eapply basic_downward; eauto.
  }
assert (rel (den (iufut stop (S i) (iuset stop (iubase (unit_urel stop i)) (semiconst_ne (den (iubase (unit_urel stop i))) A)))) (S i) (next triv) (next triv)) as H.
  {
  cbn.
  exists triv, triv.
  do2 5 split; auto using star_refl; try prove_hygiene.
  intros _.
  cbn.
  assert (rel (unit_urel stop i) i triv triv) as Hrel.
    {
    do2 5 split; auto using star_refl; prove_hygiene.
    }
  exists r, t, Hrel.
  rewrite -> urelsp_index_inj.
  split; [omega | auto].
  }
do2 2 split; auto.
Qed.


Lemma sound_future_isquash_swap :
  forall G m a,
    pseq (promote G) (deqtype a a)
    -> pseq G (deq m m (iset unittp (fut (subst sh1 a))))
    -> pseq G (deq (next triv) (next triv) (fut (iset unittp (subst sh1 a)))).
Proof.
intros G m a.
revert G.
refine (seq_pseq_promote 1 [] a 2 true [] _ false [] _ _ _); cbn.
intros G Hcla Hseqa Hseq.
rewrite -> seq_deq in Hseq |- *.
rewrite -> seq_eqtype in Hseqa.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq _ _ _ Hs) as (R & Hl & Hr & Hm & _).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_iset Hl).
intros C F Hcl Hf Heql.
invert (basic_value_inv _#6 value_iset Hr).
intros C' F' Hcr Hf' Heqr.
so (iuiset_inj _#5 (eqtrans Heql (eqsymm Heqr))) as Heq.
injectionT Heq.
intros <-.
clear Heq Heqr.
subst R.
invert Hf.
intros _ _ Hact.
destruct i as [| i].
  {
  exists (iufut0 stop).
  simpsub.
  do2 4 split.
    {
    apply interp_eval_refl.
    apply interp_fut_zero.
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }

    {
    apply interp_eval_refl.
    apply interp_fut_zero.
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }

    {
    cbn.
    exists triv, triv.
    do2 5 split; auto using star_refl; try prove_hygiene.
    intro H.
    omega.
    }

    {
    cbn.
    exists triv, triv.
    do2 5 split; auto using star_refl; try prove_hygiene.
    intro H.
    omega.
    }

    {
    cbn.
    exists triv, triv.
    do2 5 split; auto using star_refl; try prove_hygiene.
    intro H.
    omega.
    }
  }
invert (basic_value_inv _#6 value_unittp Hcl).
intros <-.
so (Hseqa _ _ _ (pwctx_promote _#4 Hs)) as (A & Hal & Har & _).
so (interp_eval_refl _#6 (interp_fut _#6 Hal)) as Hfal.
cbn in Hm.
decompose Hm.
intros p q Hm' Hpq.
so (Hact (S i) (subst s m) (subst s' m) (le_refl _) Hm') as Hfal'.
simpsubin Hfal'.
so (interp_fun _#7 Hfal Hfal') as Heqf.
cbn in Heqf.
unfold wiurel_ofe in Heqf.
rewrite <- Heqf in Hpq.
cbn in Hpq.
decompose Hpq.
intros r t _ Hclr Hclt _ _ Hrtif.
cbn in Hrtif.
assert (S i > 0) as Hpos by omega.
so (Hrtif Hpos) as Hrt.
exists (iufut stop (S i) (iuiset stop (iubase (unit_urel stop i)) (semiconst_ne _ A))).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl.
  apply interp_fut.
  apply interp_eval_refl.
  apply interp_iset.
    {
    apply interp_eval_refl.
    apply interp_unit.
    }
  apply functional_i.
    {
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }

    {
    rewrite -> den_iubase.
    rewrite -> ceiling_unit.
    f_equal.
    rewrite -> Nat.min_id.
    reflexivity.
    }
  intros j n n' Hj Hn.
  simpsub.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  eapply basic_downward; eauto.
  }

  {
  apply interp_eval_refl.
  apply interp_fut.
  apply interp_eval_refl.
  apply interp_iset.
    {
    apply interp_eval_refl.
    apply interp_unit.
    }
  apply functional_i.
    {
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }

    {
    rewrite -> den_iubase.
    rewrite -> ceiling_unit.
    f_equal.
    rewrite -> Nat.min_id.
    reflexivity.
    }
  intros j n n' Hj Hn.
  simpsub.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  eapply basic_downward; eauto.
  }
assert (rel (den (iufut stop (S i) (iuiset stop (iubase (unit_urel stop i)) (semiconst_ne (den (iubase (unit_urel stop i))) A)))) (S i) (next triv) (next triv)) as H.
  {
  cbn.
  exists triv, triv.
  do2 5 split; auto using star_refl; try prove_hygiene.
  intros _.
  cbn.
  assert (rel (unit_urel stop i) i triv triv) as Hrel.
    {
    do2 5 split; auto using star_refl; prove_hygiene.
    }
  exists r, t, Hrel.
  rewrite -> urelsp_index_inj.
  split; [omega | auto].
  }
do2 2 split; auto.
Qed.


Lemma sound_squash_future_swap :
  forall G m a,
    pseq (promote G) (deqtype a a)
    -> pseq G (deq m m (fut (set unittp (subst sh1 a))))
    -> pseq G (deq triv triv (set unittp (fut (subst sh1 a)))).
Proof.
intros G m a.
revert G.
refine (seq_pseq_promote 1 [] a 2 true [] _ false [] _ _ _); cbn.
intros G Hcla Hseqa Hseq.
rewrite -> seq_deq in Hseq |- *.
rewrite -> seq_eqtype in Hseqa.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq _ _ _ Hs) as (R & Hl & Hr & Hm & _).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_fut Hl).
  {
  intros _ <- <-.
  exists (iuset stop (iubase (unit_urel stop 0)) (nearrow_const _ (wiurel_ofe stop) (iufut0 stop))).
  simpsub.
  do2 2 split.
    {
    apply interp_eval_refl.
    apply interp_set.
      {
      apply interp_eval_refl.
      apply interp_unit.
      }
    apply functional_i.
      {
      prove_hygiene.
      rewrite -> subst_compose.
      apply hygiene_shift_permit.
      eapply subst_closub; eauto.
      }

      {
      rewrite -> den_iubase.
      rewrite -> ceiling_unit.
      reflexivity.
      }
    intros j n p Hj Hnp.
    simpsub.
    cbn.
    apply interp_eval_refl.
    replace j with 0 by omega.
    apply interp_fut_zero.
    eapply subst_closub; eauto.
    }

    {
    apply interp_eval_refl.
    apply interp_set.
      {
      apply interp_eval_refl.
      apply interp_unit.
      }
    apply functional_i.
      {
      prove_hygiene.
      rewrite -> subst_compose.
      apply hygiene_shift_permit.
      eapply subst_closub; eauto.
      }

      {
      rewrite -> den_iubase.
      rewrite -> ceiling_unit.
      reflexivity.
      }
    intros j n p Hj Hnp.
    simpsub.
    cbn.
    apply interp_eval_refl.
    replace j with 0 by omega.
    apply interp_fut_zero.
    eapply subst_closub; eauto.
    }
  assert (rel (den (iuiset stop (iubase (unit_urel stop 0)) (nearrow_const _ (wiurel_ofe stop) (iufut0 stop)))) 0 triv triv) as H.
    {
    cbn.
    assert (rel (unit_urel stop 0) 0 triv triv) as H.
      {
      do2 5 split; auto using star_refl; prove_hygiene.
      }
    exists (next triv), (next triv), H.
    exists triv, triv.
    do2 5 split; auto using star_refl; try prove_hygiene.
    intro Hnope.
    omega.
    }
  do2 2 split; auto.
  }
intros i' B Hbl <- Heql.
invert (basic_value_inv _#6 value_fut Hr).
intros B' Hbr Heqr.
so (iufut_inj _#5 (eqtrans Heql (eqsymm Heqr))).
subst B'.
subst R.
clear Heqr.
invert (basic_value_inv _#6 value_set Hbl).
intros C F Hcl Hf <-.
invert Hf.
intros _ _ Hact.
invert (basic_value_inv _#6 value_unittp Hcl).
intros <-.
so (Hseqa _ _ _ (pwctx_promote _#4 Hs)) as (A & Hal & Har & _).
exists (iuset stop (iubase (unit_urel stop (S i'))) (semiconst_ne _ (iufut stop (S i') A))).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl.
  apply interp_set.
    {
    apply interp_eval_refl.
    apply interp_unit.
    }
  apply functional_i.
    {
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }

    {
    rewrite -> den_iubase.
    rewrite -> ceiling_unit.
    f_equal.
    rewrite -> Nat.min_id.
    reflexivity.
    }
  intros j n p Hj Hnp.
  simpsub.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  destruct j as [| j].
    {
    rewrite -> iutruncate_iufut_one.
    apply interp_eval_refl.
    apply interp_fut_zero.
    eapply subst_closub; eauto.
    }

    {
    rewrite -> iutruncate_iufut; [| omega].
    cbn.
    rewrite -> Nat.min_r; [| omega].
    apply interp_eval_refl.
    apply interp_fut.
    apply (basic_downward _ _ _ i'); [omega | auto].
    }
  }

  {
  apply interp_eval_refl.
  apply interp_set.
    {
    apply interp_eval_refl.
    apply interp_unit.
    }
  apply functional_i.
    {
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }

    {
    rewrite -> den_iubase.
    rewrite -> ceiling_unit.
    f_equal.
    rewrite -> Nat.min_id.
    reflexivity.
    }
  intros j n p Hj Hnp.
  simpsub.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  destruct j as [| j].
    {
    rewrite -> iutruncate_iufut_one.
    apply interp_eval_refl.
    apply interp_fut_zero.
    eapply subst_closub; eauto.
    }

    {
    rewrite -> iutruncate_iufut; [| omega].
    cbn.
    rewrite -> Nat.min_r; [| omega].
    apply interp_eval_refl.
    apply interp_fut.
    apply (basic_downward _ _ _ i'); [omega | auto].
    }
  }
assert (rel (den (iuset stop (iubase (unit_urel stop (S i'))) (semiconst_ne (den (iubase (unit_urel stop (S i')))) (iufut stop (S i') A)))) (S i') triv triv) as H.
  {
  cbn.
  so (basic_value_inv _#6 value_set Hbl) as H.
  remember (iuset stop (iubase (unit_urel stop i')) F) as X eqn:HeqX.
  invert H.
  intros C F' Hc Hf' HeqX'.
  clear H.
  so (iuset_inj _#5 (eqtrans HeqX' HeqX)) as Heq.
  subst C.
  subst X.
  clear HeqX'.
  cbn in Hm.
  decompose Hm.
  intros n n' _ _ _ _ _ Hnif.
  assert (S i' > 0) as Hgt by omega.
  so (Hnif Hgt) as Hn.
  cbn in Hn.
  decompose Hn.
  intros p q Hn' Hpq.
  so (Hact i' n n' (le_refl _) Hn') as Hal'.
  simpsubin Hal'.
  so (interp_fun _#7 Hal Hal') as HeqA.
  cbn in HeqA.
  unfold wiurel_ofe in HeqA.
  cbn in Hpq.
  rewrite <- HeqA in Hpq.
  assert (rel (unit_urel stop (S i')) (S i') triv triv) as Hrel.
    {
    do2 5 split; auto using star_refl; prove_hygiene.
    }
  exists (next p), (next q), Hrel.
  rewrite -> urelsp_index_inj.
  cbn.
  split; [omega |].
  exists p, q.
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  do2 5 split; auto using star_refl; prove_hygiene.
  }
do2 2 split; auto.
Qed.


Lemma sound_isquash_future_swap :
  forall G m a,
    pseq (promote G) (deqtype a a)
    -> pseq G (deq m m (fut (iset unittp (subst sh1 a))))
    -> pseq G (deq triv triv (iset unittp (fut (subst sh1 a)))).
Proof.
intros G m a.
revert G.
refine (seq_pseq_promote 1 [] a 2 true [] _ false [] _ _ _); cbn.
intros G Hcla Hseqa Hseq.
rewrite -> seq_deq in Hseq |- *.
rewrite -> seq_eqtype in Hseqa.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq _ _ _ Hs) as (R & Hl & Hr & Hm & _).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_fut Hl).
  {
  intros _ <- <-.
  exists (iuiset stop (iubase (unit_urel stop 0)) (nearrow_const _ (wiurel_ofe stop) (iufut0 stop))).
  simpsub.
  do2 2 split.
    {
    apply interp_eval_refl.
    apply interp_iset.
      {
      apply interp_eval_refl.
      apply interp_unit.
      }
    apply functional_i.
      {
      prove_hygiene.
      rewrite -> subst_compose.
      apply hygiene_shift_permit.
      eapply subst_closub; eauto.
      }

      {
      rewrite -> den_iubase.
      rewrite -> ceiling_unit.
      reflexivity.
      }
    intros j n p Hj Hnp.
    simpsub.
    cbn.
    apply interp_eval_refl.
    replace j with 0 by omega.
    apply interp_fut_zero.
    eapply subst_closub; eauto.
    }

    {
    apply interp_eval_refl.
    apply interp_iset.
      {
      apply interp_eval_refl.
      apply interp_unit.
      }
    apply functional_i.
      {
      prove_hygiene.
      rewrite -> subst_compose.
      apply hygiene_shift_permit.
      eapply subst_closub; eauto.
      }

      {
      rewrite -> den_iubase.
      rewrite -> ceiling_unit.
      reflexivity.
      }
    intros j n p Hj Hnp.
    simpsub.
    cbn.
    apply interp_eval_refl.
    replace j with 0 by omega.
    apply interp_fut_zero.
    eapply subst_closub; eauto.
    }
  assert (rel (den (iuiset stop (iubase (unit_urel stop 0)) (nearrow_const _ (wiurel_ofe stop) (iufut0 stop)))) 0 triv triv) as H.
    {
    cbn.
    assert (rel (unit_urel stop 0) 0 triv triv) as H.
      {
      do2 5 split; auto using star_refl; prove_hygiene.
      }
    exists (next triv), (next triv), H.
    exists triv, triv.
    do2 5 split; auto using star_refl; try prove_hygiene.
    intro Hnope.
    omega.
    }
  do2 2 split; auto.
  }
intros i' B Hbl <- Heql.
invert (basic_value_inv _#6 value_fut Hr).
intros B' Hbr Heqr.
so (iufut_inj _#5 (eqtrans Heql (eqsymm Heqr))).
subst B'.
subst R.
clear Heqr.
invert (basic_value_inv _#6 value_iset Hbl).
intros C F Hcl Hf <-.
invert Hf.
intros _ _ Hact.
invert (basic_value_inv _#6 value_unittp Hcl).
intros <-.
so (Hseqa _ _ _ (pwctx_promote _#4 Hs)) as (A & Hal & Har & _).
exists (iuiset stop (iubase (unit_urel stop (S i'))) (semiconst_ne _ (iufut stop (S i') A))).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl.
  apply interp_iset.
    {
    apply interp_eval_refl.
    apply interp_unit.
    }
  apply functional_i.
    {
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }

    {
    rewrite -> den_iubase.
    rewrite -> ceiling_unit.
    f_equal.
    rewrite -> Nat.min_id.
    reflexivity.
    }
  intros j n p Hj Hnp.
  simpsub.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  destruct j as [| j].
    {
    rewrite -> iutruncate_iufut_one.
    apply interp_eval_refl.
    apply interp_fut_zero.
    eapply subst_closub; eauto.
    }

    {
    rewrite -> iutruncate_iufut; [| omega].
    cbn.
    rewrite -> Nat.min_r; [| omega].
    apply interp_eval_refl.
    apply interp_fut.
    apply (basic_downward _ _ _ i'); [omega | auto].
    }
  }

  {
  apply interp_eval_refl.
  apply interp_iset.
    {
    apply interp_eval_refl.
    apply interp_unit.
    }
  apply functional_i.
    {
    prove_hygiene.
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }

    {
    rewrite -> den_iubase.
    rewrite -> ceiling_unit.
    f_equal.
    rewrite -> Nat.min_id.
    reflexivity.
    }
  intros j n p Hj Hnp.
  simpsub.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  destruct j as [| j].
    {
    rewrite -> iutruncate_iufut_one.
    apply interp_eval_refl.
    apply interp_fut_zero.
    eapply subst_closub; eauto.
    }

    {
    rewrite -> iutruncate_iufut; [| omega].
    cbn.
    rewrite -> Nat.min_r; [| omega].
    apply interp_eval_refl.
    apply interp_fut.
    apply (basic_downward _ _ _ i'); [omega | auto].
    }
  }
assert (rel (den (iuiset stop (iubase (unit_urel stop (S i'))) (semiconst_ne (den (iubase (unit_urel stop (S i')))) (iufut stop (S i') A)))) (S i') triv triv) as H.
  {
  cbn.
  so (basic_value_inv _#6 value_iset Hbl) as H.
  remember (iuiset stop (iubase (unit_urel stop i')) F) as X eqn:HeqX.
  invert H.
  intros C F' Hc Hf' HeqX'.
  clear H.
  so (iuiset_inj _#5 (eqtrans HeqX' HeqX)) as Heq.
  injectionT Heq.
  intros ->.
  clear Heq.
  subst X.
  clear HeqX'.
  cbn in Hm.
  decompose Hm.
  intros n n' _ _ _ _ _ Hnif.
  assert (S i' > 0) as Hgt by omega.
  so (Hnif Hgt) as Hn.
  cbn in Hn.
  decompose Hn.
  intros p q Hn' Hpq.
  so (Hact i' n n' (le_refl _) Hn') as Hal'.
  simpsubin Hal'.
  so (interp_fun _#7 Hal Hal') as HeqA.
  cbn in HeqA.
  unfold wiurel_ofe in HeqA.
  cbn in Hpq.
  rewrite <- HeqA in Hpq.
  assert (rel (unit_urel stop (S i')) (S i') triv triv) as Hrel.
    {
    do2 5 split; auto using star_refl; prove_hygiene.
    }
  exists (next p), (next q), Hrel.
  rewrite -> urelsp_index_inj.
  cbn.
  split; [omega |].
  exists p, q.
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  do2 5 split; auto using star_refl; prove_hygiene.
  }
do2 2 split; auto.
Qed.
