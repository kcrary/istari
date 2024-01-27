
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

Require Import Spaces.
Require Import Extend.
Require Import ProperLevel.
Require Import Urelsp.
Require Import Ceiling.
Require Import Equivalence.
Require Import Equivalences.
Require Import Truncate.
Require Import ProperDownward.
Require Import ProperLevel.
Require Import ProperEquiv.
Require Import Subsumption.
Require Import SemanticsPi.
Require Import SemanticsSigma.
Require Import ContextHygiene.
Require Import SoundUtil.


Lemma sound_sigma_formation :
  forall G a a' b b',
    pseq G (deqtype a a')
    -> pseq (cons (hyp_tm a) G) (deqtype b b')
    -> pseq G (deqtype (sigma a b) (sigma a' b')).
Proof.
intros G a b c d.
revert G.
refine (seq_pseq 2 [hyp_emp] c [hyp_emp] d 2 [] _ [_] _ _ _); cbn.
intros G Hclc Hcld Hseqab Hseqcd.
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
exists (iusigma stop A C).
simpsub.
do2 3 split; auto;
apply interp_eval_refl;
apply interp_sigma; auto.
Qed.


Lemma sound_sigma_formation_univ :
  forall G lv a a' b b',
    pseq G (deq a a' (univ lv))
    -> pseq (cons (hyp_tm a) G) (deq b b' (univ (subst sh1 lv)))
    -> pseq G (deq (sigma a b) (sigma a' b') (univ lv)).
Proof.
intros G lv a b c d.
revert G.
refine (seq_pseq 2 [hyp_emp] c [hyp_emp] d 2 [] _ [_] _ _ _); cbn.
intros G Hclc Hcld Hseqab Hseqcd.
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
exists pg, (iusigma stop A C).
simpsub.
do2 5 split; auto;
apply interp_eval_refl;
apply interp_sigma; auto.
Qed.


Local Ltac prove_hygiene :=
  repeat (first [ eapply subst_closub; eauto
                | apply closub_dot
                | apply hygiene_auto; cbn; repeat2 split; auto
                ]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1;
  try (apply hygiene_var; cbn; auto; done).


Lemma sound_sigma_intro :
  forall G a b m m' n n',
    pseq G (deq m m' a)
    -> pseq G (deq n n' (subst1 m b))
    -> pseq (cons (hyp_tm a) G) (deqtype b b)
    -> pseq G (deq (ppair m n) (ppair m' n') (sigma a b)).
Proof.
intros G a b m n p q.
revert G.
refine (seq_pseq 5 [hyp_emp] b [] m [] p [] n [] q 3 [] _ [] _ [_] _ _ _); cbn.
intros G Hclb Hclm Hclp Hcln Hclq Hseqmn Hseqpq Hseqb.
rewrite -> seq_eqtype in Hseqb.
rewrite -> seq_deq in Hseqmn, Hseqpq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmn _#3 Hs) as (A & Hal & Har & Hm & Hn & Hmn).
so (Hseqpq _#3 Hs) as (R & Hmbl & Hmbr & Hp & Hq & Hpq); clear Hseqpq.
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as H; eauto using subst_closub_under_permit.
  { 
 exact (f_equal den (basic_impl_iutruncate _#6 Hal)).
  }

  {
  intros j r t Hrt.
  so (basic_member_index _#9 Hal Hrt) as Hj.
  assert (pwctx j (dot r s) (dot t s') (cons (hyp_tm a) G)) as Hs'.
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
      intros j' u u' Hu.
      so (Hseqmn _#3 Hu) as (Q & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hs') as (Q & Hl & Hr & _).
  exists Q.
  simpsub.
  auto.
  }
destruct H as (B & Hbl & Hbr).
exists (iusigma stop A B).
simpsub.
invert Hbl.
intros _ _ Hact.
so (Hact _#3 (le_refl _) Hm) as H.
simpsubin H.
simpsubin Hmbl.
so (basic_fun _#7 H Hmbl); clear H; subst R.
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_sigma; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_sigma; auto.
  }

  {
  exists (subst s m), (subst s' m), (subst s p), (subst s' p), Hm.
  do2 4 split; auto using star_refl; try prove_hygiene.
  }

  {
  exists (subst s n), (subst s' n), (subst s q), (subst s' q), Hn.
  do2 4 split; auto using star_refl; try prove_hygiene.
  cbn.
  force_exact Hq.
  f_equal; f_equal; f_equal.
  apply urelspinj_equal; auto.
  }

  {
  exists (subst s m), (subst s' n), (subst s p), (subst s' q), Hmn.
  do2 4 split; auto using star_refl; try prove_hygiene.
  cbn.
  force_exact Hpq.
  f_equal; f_equal; f_equal.
  apply urelspinj_equal; auto.
  }
Qed.
           

Lemma sound_sigma_elim1 :
  forall G a b m n,
    pseq G (deq m n (sigma a b))
    -> pseq G (deq (ppi1 m) (ppi1 n) a).
Proof.
intros G a b m n.
revert G.
refine (seq_pseq 2 [] m [] n 1 [] _ _ _); cbn.
intros G Hclm Hcln Hseqmn.
rewrite -> seq_deq in Hseqmn |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmn _#3 Hs) as (R & Hl & Hr & Hm & Hn & Hmn).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_sigma Hl).
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_sigma Hr).
intros A' B' Har Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iusigma_inj _#5 Heq) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
exists A.
simpsub.
do2 4 split; auto.
  {
  destruct Hm as (p & q & r & t & Hpq & _ & _ & Hsteps & Hsteps' & Hrt).
  apply (urel_equiv _#3 p _ q); auto; prove_hygiene.
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi1); auto using step_ppi11.
      exact Hsteps.
      }
    apply star_one; apply step_ppi12.
    }

    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi1); auto using step_ppi11.
      exact Hsteps'.
      }
    apply star_one; apply step_ppi12.
    }
  }

  {
  destruct Hn as (p & q & r & t & Hpq & _ & _ & Hsteps & Hsteps' & Hrt).
  apply (urel_equiv _#3 p _ q); auto; prove_hygiene.
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi1); auto using step_ppi11.
      exact Hsteps.
      }
    apply star_one; apply step_ppi12.
    }

    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi1); auto using step_ppi11.
      exact Hsteps'.
      }
    apply star_one; apply step_ppi12.
    }
  }

  {
  destruct Hmn as (p & q & r & t & Hpq & _ & _ & Hsteps & Hsteps' & Hrt).
  apply (urel_equiv _#3 p _ q); auto; prove_hygiene.
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi1); auto using step_ppi11.
      exact Hsteps.
      }
    apply star_one; apply step_ppi12.
    }

    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi1); auto using step_ppi11.
      exact Hsteps'.
      }
    apply star_one; apply step_ppi12.
    }
  }
Qed.


Lemma sound_sigma_elim2 :
  forall G a b m n,
    pseq G (deq m n (sigma a b))
    -> pseq G (deq (ppi2 m) (ppi2 n) (subst1 (ppi1 m) b)).
Proof.
intros G a b m n.
revert G.
refine (seq_pseq 3 [hyp_emp] b [] m [] n 1 [] _ _ _); cbn.
intros G Hclb Hclm Hlcn Hseqmn.
rewrite -> seq_deq in Hseqmn |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmn _#3 Hs) as (R & Hl & Hr & Hm & Hn & Hmn).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_sigma Hl).
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_sigma Hr).
intros A' B' Har Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iusigma_inj _#5 Heq) as H; clear Heq.
injectionT H.
intros <-.
injectionT H.
intros <-.
destruct Hm as (p1 & q1 & p2 & q2 & Hpq1 & _ & _ & Hstepsm & Hstepsm' & Hpq2).
cbn in Hpq2.
destruct Hn as (r1 & t1 & r2 & t2 & Hrt1 & _ & _ & Hstepsn & Hstepsn' & Hrt2).
cbn in Hrt2.
destruct Hmn as (p1' & q1' & r2' & t2' & Hpt1 & _ & _ & Hstepsma & Hstepsna' & Hpt2).
cbn in Hpt2.
injection (determinism_eval _#4 (conj Hstepsm value_ppair) (conj Hstepsma value_ppair)).
intros <- <-.
injection (determinism_eval _#4 (conj Hstepsn' value_ppair) (conj Hstepsna' value_ppair)).
intros <- <-.
exists (pi1 B (urelspinj (den A) _#3 Hpq1)).
simpsub.
do2 4 split.
  {
  invert Hbl.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hpq1) as H.
  simpsubin H.
  refine (basic_equiv _#7 _ _ H); clear H; try prove_hygiene.
  apply equiv_symm.
  apply equiv_funct; auto using equiv_refl.
  apply equivsub_dot; auto using equivsub_refl.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi1); auto using step_ppi11.
    exact Hstepsm.
    }
  apply star_one; apply step_ppi12.
  }

  {
  invert Hbr.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hpq1) as H.
  simpsubin H.
  refine (basic_equiv _#7 _ _ H); clear H; try prove_hygiene.
  apply equiv_symm.
  apply equiv_funct; auto using equiv_refl.
  apply equivsub_dot; auto using equivsub_refl.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi1); auto using step_ppi11.
    exact Hstepsm'.
    }
  apply star_one; apply step_ppi12.
  }

  {
  refine (urel_equiv _#7 _#4 Hpq2); try prove_hygiene.
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi2); auto using step_ppi21.
      exact Hstepsm.
      }
    apply star_one; apply step_ppi22.
    }

    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi2); auto using step_ppi21.
      exact Hstepsm'.
      }
    apply star_one; apply step_ppi22.
    }
  }

  {
  refine (rel_from_dist _#6 _ (urel_equiv _#7 _#4 Hrt2)); try prove_hygiene.
    {
    apply dist_refl'.
    f_equal; f_equal.
    apply urelspinj_equal; auto.
    apply (urel_zigzag _#4 t1 p1); auto.
    }

    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi2); auto using step_ppi21.
      exact Hstepsn.
      }
    apply star_one; apply step_ppi22.
    }

    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi2); auto using step_ppi21.
      exact Hstepsn'.
      }
    apply star_one; apply step_ppi22.
    }
  }

  {
  refine (rel_from_dist _#6 _ (urel_equiv _#7 _#4 Hpt2)); try prove_hygiene.
    {
    apply dist_refl'.
    f_equal; f_equal.
    apply urelspinj_equal; auto.
    }

    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi2); auto using step_ppi21.
      exact Hstepsm.
      }
    apply star_one; apply step_ppi22.
    }

    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi2); auto using step_ppi21.
      exact Hstepsn'.
      }
    apply star_one; apply step_ppi22.
    }
  }
Qed.


Lemma sound_sigma_eta :
  forall G a b m,
    pseq G (deq m m (sigma a b))
    -> pseq G (deq m (ppair (ppi1 m) (ppi2 m)) (sigma a b)).
Proof.
intros G a b m.
revert G.
refine (seq_pseq 2 [hyp_emp] b [] m 1 [] _ _ _); cbn.
intros G Hclb Hclm Hseqm.
rewrite -> seq_deq in Hseqm |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqm _#3 Hs) as (R & Habl & Habr & Hm & _).
exists R.
do2 2 split; auto.
simpsub.
split; auto.
simpsubin Habl.
invert (basic_value_inv _#6 value_sigma Habl).
intros A B Ha Hb <-.
cbn in Hm.
decompose Hm.
intros n n' p p' Hn _ _ Hsteps Hsteps' Hp.
split.
  {
  assert (rel (den A) i (ppi1 (subst s m)) (ppi1 (subst s' m))) as Hn'.
    {
    eapply urel_equiv; eauto; try prove_hygiene.
      {
      apply equiv_symm.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1); auto using step_ppi11.
        exact Hsteps.
        }
      apply star_one; apply step_ppi12.
      }

      {
      apply equiv_symm.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1); auto using step_ppi11.
        exact Hsteps'.
        }
      apply star_one; apply step_ppi12.
      }
    }
  exists (ppi1 (subst s m)), (ppi1 (subst s' m)), (ppi2 (subst s m)), (ppi2 (subst s' m)), Hn'.
  do2 4 split; auto using star_refl; try prove_hygiene.
  cbn.
  refine (rel_from_dist _#6 _ (urel_equiv _#7 _#4 Hp)); try prove_hygiene.
    {
    apply dist_refl'.
    f_equal; f_equal.
    apply urelspinj_equal.
    apply (urel_zigzag _#4 n' (ppi1 (subst s m))); auto.
    eapply urel_equiv_1; eauto; try prove_hygiene.
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi1); auto using step_ppi11.
      exact Hsteps.
      }
    apply star_one; apply step_ppi12.
    }

    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi2); auto using step_ppi21.
      exact Hsteps.
      }
    apply star_one; apply step_ppi22.
    }

    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi2); auto using step_ppi21.
      exact Hsteps'.
      }
    apply star_one; apply step_ppi22.
    }
  }

  {
  assert (rel (den A) i n (ppi1 (subst s' m))) as Hn'.
    {
    eapply urel_equiv_2; eauto; try prove_hygiene.
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi1); auto using step_ppi11.
      exact Hsteps'.
      }
    apply star_one; apply step_ppi12.
    }
  exists n, (ppi1 (subst s' m)), p, (ppi2 (subst s' m)), Hn'.
  do2 4 split; auto using star_refl; try prove_hygiene.
  cbn.
  refine (rel_from_dist _#6 _ (urel_equiv_2 _#6 _ _ Hp)); try prove_hygiene.
    {
    apply dist_refl'.
    f_equal; f_equal.
    apply urelspinj_equal.
    apply (urel_zigzag _#4 n' (ppi1 (subst s m))); auto.
      {
      eapply urel_equiv_1; eauto; try prove_hygiene.
      apply equiv_symm.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1); auto using step_ppi11.
        exact Hsteps.
        }
      apply star_one; apply step_ppi12.
      }

      {
      refine (urel_equiv _#7 _ _ _ _ Hn); try prove_hygiene.
        {
        apply equiv_symm.
        apply steps_equiv.
        eapply star_trans.
          {
          apply (star_map' _ _ ppi1); auto using step_ppi11.
          exact Hsteps.
          }
        apply star_one; apply step_ppi12.
        }
  
        {
        apply equiv_symm.
        apply steps_equiv.
        eapply star_trans.
          {
          apply (star_map' _ _ ppi1); auto using step_ppi11.
          exact Hsteps'.
          }
        apply star_one; apply step_ppi12.
        }
      }
    }

    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi2); auto using step_ppi21.
      exact Hsteps'.
      }
    apply star_one; apply step_ppi22.
    }
  }
Qed.


Lemma sound_sigma_eta_hyp :
  forall G1 G2 a b m n c,
    pseq (substctx (dot (ppair (var 1) (var 0)) (sh 2)) G2 ++ cons (hyp_tm b) (cons (hyp_tm a) G1)) (deq m n (subst (under (length G2) (dot (ppair (var 1) (var 0)) (sh 2))) c))
    -> pseq (G2 ++ cons (hyp_tm (sigma a b)) G1) (deq (subst (under (length G2) (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) sh1))) m) (subst (under (length G2) (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) sh1))) n) c).
Proof.
intros G1 G2 a b m n c.
revert G1.
refine (seq_pseq_hyp 2 [hyp_emp] b (G2 ++ [hyp_tm (sigma a b)]) c 1 _ [_; _] _ _ [_] _ _); cbn.
intros G1 Hclb Hclc Hseq _.
eapply subsume_seq_extract; eauto; clear Hseq.
  {
  autorewrite with canonlist in Hclc.
  auto.
  }
apply subsume_under.
do2 2 split.
  {
  intros j.
  split.
    {
    intro Hj.
    destruct j as [| [| j]]; simpsub; prove_hygiene.
    }

    {
    intro Hj.
    rewrite -> ctxpred_length.
    cbn.
    destruct j as [| j]; try omega.
    simpsubin Hj.
    rewrite -> ctxpred_length in Hj.
    cbn in Hj.
    invert Hj; intro; omega.
    }
  }

  {
  intros j.
  split.
    {
    intro Hj.
    destruct j as [| [| j]]; simpsub; prove_hygiene.
    }

    {
    intro Hj.
    rewrite -> ctxpred_length.
    cbn.
    destruct j as [| [| j]]; try omega.
    simpsubin Hj.
    rewrite -> ctxpred_length in Hj.
    cbn in Hj.
    invert Hj; intro; omega.
    }
  }
intros i ss ss' Hss.
invertc Hss.
intros p q s s' Hs Hpq Hleft Hright <- <-.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
simpsubin Hpq.
invertc Hpq.
intros R Habl Habr Hpq.
invert (basic_value_inv _#6 value_sigma Habl).
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_sigma Habr).
intros A' B' Har Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iusigma_inj _#5 Heq) as H; clear Heq.
injectionT H.
intros <-.
injectionT H.
intros <-.
destruct Hpq as (p1 & q1 & p2 & q2 & Hpq1 & Hclp & Hclq & Hstepsp & Hstepsq & Hpq2).
do2 4 split.
  {
  simpsub.
  apply pwctx_cons_tm.
    {
    apply pwctx_cons_tm; auto.
      {
      apply (seqhyp_tm _#5 A); auto.
      eapply urel_equiv; eauto; try prove_hygiene.
        {
        apply equiv_symm.
        apply steps_equiv.
        eapply star_trans.
          {
          apply (star_map' _ _ ppi1); auto using step_ppi11.
          exact Hstepsp.
          }
        apply star_one; apply step_ppi12.
        }

        {
        apply equiv_symm.
        apply steps_equiv.
        eapply star_trans.
          {
          apply (star_map' _ _ ppi1); auto using step_ppi11.
          exact Hstepsq.
          }
        apply star_one; apply step_ppi12.
        }
      }

      {
      intros j u Hj Hu.
      exploit (Hleft j false u) as H; auto using smaller_le, pwctx_impl_seqctx.
      rewrite -> qpromote_hyp_tm in H.
      simpsubin H.
      invertc H.
      intros R Hl Hr.
      invert (basic_value_inv _#6 value_sigma Hl); clear Hl.
      intros A' B' Har' _ Heq1.
      invert (basic_value_inv _#6 value_sigma Hr); clear Hr.
      intros A'' B'' Har'' _ Heq2.
      so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
      clear Heq2.
      subst R.
      so (basic_fun _#7 (basic_downward _#7 Hj Har) Har'); subst A'.
      so (iusigma_inj _#5 Heq) as H; clear Heq.
      injectionT H.
      intros <-.
      clear H.
      apply (relhyp_tm _#4 (iutruncate (S j) A)); auto.
      }

      {
      intros j u Hj Hu.
      exploit (Hright j false u) as H; auto using smaller_le, pwctx_impl_seqctx.
      rewrite -> qpromote_hyp_tm in H.
      simpsubin H.
      invertc H.
      intros R Hl Hr.
      invert (basic_value_inv _#6 value_sigma Hl); clear Hl.
      intros A' B' Hal' _ Heq1.
      invert (basic_value_inv _#6 value_sigma Hr); clear Hr.
      intros A'' B'' Hal'' _ Heq2.
      so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
      clear Heq2.
      subst R.
      so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst A'.
      so (iusigma_inj _#5 Heq) as H; clear Heq.
      injectionT H.
      intros <-.
      clear H.
      apply (relhyp_tm _#4 (iutruncate (S j) A)); auto.
      }
    }

    {
    apply (seqhyp_tm _#5 (pi1 B (urelspinj (den A) _#3 Hpq1))).
      {
      invert Hbl.
      intros _ _ Hact.
      so (Hact _#3 (le_refl _) Hpq1) as H.
      simpsubin H.
      eapply basic_equiv; eauto; clear H; try prove_hygiene.
      apply equiv_symm.
      apply equiv_funct; auto using equiv_refl.
      apply equivsub_dot; auto using equivsub_refl.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1); auto using step_ppi11.
        exact Hstepsp.
        }
      apply star_one; apply step_ppi12.
      }

      {
      invert Hbr.
      intros _ _ Hact.
      so (Hact _#3 (le_refl _) Hpq1) as H.
      simpsubin H.
      eapply basic_equiv; eauto; clear H; try prove_hygiene.
      apply equiv_symm.
      apply equiv_funct; auto using equiv_refl.
      apply equivsub_dot; auto using equivsub_refl.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1); auto using step_ppi11.
        exact Hstepsq.
        }
      apply star_one; apply step_ppi12.
      }

      {
      eapply urel_equiv; eauto; try prove_hygiene.
        {
        apply equiv_symm.
        apply steps_equiv.
        eapply star_trans.
          {
          apply (star_map' _ _ ppi2); auto using step_ppi21.
          exact Hstepsp.
          }
        apply star_one; apply step_ppi22.
        }
      
        {
        apply equiv_symm.
        apply steps_equiv.
        eapply star_trans.
          {
          apply (star_map' _ _ ppi2); auto using step_ppi21.
          exact Hstepsq.
          }
        apply star_one; apply step_ppi22.
        }
      }
    }

    {
    intros j uu Hj Huu.
    invertc Huu.
    intros r u Hu Hr _ _ <-.
    so (pwctx_impl_closub _#4 Hu) as (_ & Hclu).
    simpsubin Hr.
    invertc Hr.
    intros A' Hal' Hau Hr.
    so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst A'.
    clear Hal'.
    so (urel_closed _#5 Hr) as (_ & Hclr).
    exploit (Hleft j false u) as H; auto using smaller_le, pwctx_impl_seqctx.
    rewrite -> qpromote_hyp_tm in H.
    simpsubin H.
    invertc H.
    intros R H1 H2.
    invert (basic_value_inv _#6 value_sigma H1); clear H1.
    intros A' B' Har' Hbr' Heq1.
    invert (basic_value_inv _#6 value_sigma H2); clear H2.
    intros A'' B'' Har'' Hbr'' Heq2.
    so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
    clear Heq2.
    subst R.
    so (iusigma_inj _#5 Heq) as H; clear Heq.
    injectionT H.
    intros <-.
    injectionT H.
    intros <-.
    so (basic_fun _#7 (basic_downward _#7 Hj Har) Har'); subst A'.
    so (functional_fun _#8 (functional_downward _#8 Hj Hbr) Hbr'); subst B'.
    apply (relhyp_tm _#4 (iutruncate (S j) (pi1 B (embed_ceiling _ _ (urelspinj (ceiling (S j) (den A)) _#3 (conj (Nat.lt_succ_diag_r j) (urel_downward_leq _#6 Hj Hpq1))))))).
      {
      invert Hbr'.
      intros B' _ _ Hact Heq.
      so (eq_dep_impl_eq_snd _#5 Heq); subst B'; clear Heq.
      so (Hact _#3 (le_refl _) (conj (Nat.lt_succ_diag_r j) (urel_downward_leq _#6 Hj Hpq1))) as H.
      cbn in H.
      eapply basic_equiv; eauto; clear H; try prove_hygiene.
      simpsub.
      apply equiv_symm.
      apply equiv_funct; auto using equiv_refl.
      apply equivsub_dot; auto using equivsub_refl.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1); auto using step_ppi11.
        exact Hstepsq.
        }
      apply star_one; apply step_ppi12.
      }

      {
      invert Hbr''.
      intros B' _ _ Hact Heq.
      so (eq_dep_impl_eq_snd _#5 Heq); subst B'; clear Heq.
      so (Hact _#3 (le_refl _) Hr) as H.
      cbn in H.
      rewrite -> embed_ceiling_urelspinj.
      destruct Hr as (Hj' & Hr).
      rewrite -> embed_ceiling_urelspinj in H.
      simpsubin H.
      force_exact H.
      unfold interp.
      f_equal.
      f_equal; f_equal.
      apply urelspinj_equal.
      refine (urel_equiv_1 _#6 _ _ (urel_downward_leq _#6 Hj Hpq1)); try prove_hygiene.
      apply equiv_symm.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1); auto using step_ppi11.
        exact Hstepsp.
        }
      apply star_one; apply step_ppi12.
      }
    }

    {
    intros j uu Hj Huu.
    invertc Huu.
    intros r u Hu Hr _ _ <-.
    so (pwctx_impl_closub _#4 Hu) as (Hclu & _).
    simpsubin Hr.
    invertc Hr.
    intros A' Hau Har' Hr.
    so (basic_fun _#7 (basic_downward _#7 Hj Har) Har'); subst A'.
    clear Har'.
    so (urel_closed _#5 Hr) as (Hclr & _).
    exploit (Hright j false u) as H; auto using smaller_le, pwctx_impl_seqctx.
    rewrite -> qpromote_hyp_tm in H.
    simpsubin H.
    invertc H.
    intros R H1 H2.
    invert (basic_value_inv _#6 value_sigma H1); clear H1.
    intros A' B' Hal' Hbl' Heq1.
    invert (basic_value_inv _#6 value_sigma H2); clear H2.
    intros A'' B'' Hal'' Hbl'' Heq2.
    so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
    clear Heq2.
    subst R.
    so (iusigma_inj _#5 Heq) as H; clear Heq.
    injectionT H.
    intros <-.
    injectionT H.
    intros <-.
    so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst A'.
    so (functional_fun _#8 (functional_downward _#8 Hj Hbl) Hbl'); subst B'.
    apply (relhyp_tm _#4 (iutruncate (S j) (pi1 B (embed_ceiling _ _ (urelspinj (ceiling (S j) (den A)) _#3 (conj (Nat.lt_succ_diag_r j) (urel_downward_leq _#6 Hj Hpq1))))))).
      {
      invert Hbl'.
      intros B' _ _ Hact Heq.
      so (eq_dep_impl_eq_snd _#5 Heq); subst B'; clear Heq.
      so (Hact _#3 (le_refl _) (conj (Nat.lt_succ_diag_r j) (urel_downward_leq _#6 Hj Hpq1))) as H.
      cbn in H.
      eapply basic_equiv; eauto; clear H; try prove_hygiene.
      simpsub.
      apply equiv_symm.
      apply equiv_funct; auto using equiv_refl.
      apply equivsub_dot; auto using equivsub_refl.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1); auto using step_ppi11.
        exact Hstepsp.
        }
      apply star_one; apply step_ppi12.
      }

      {
      invert Hbl''.
      intros B' _ _ Hact Heq.
      so (eq_dep_impl_eq_snd _#5 Heq); subst B'; clear Heq.
      so (Hact _#3 (le_refl _) Hr) as H.
      cbn in H.
      rewrite -> embed_ceiling_urelspinj.
      destruct Hr as (Hj' & Hr).
      rewrite -> embed_ceiling_urelspinj in H.
      simpsubin H.
      force_exact H.
      unfold interp.
      f_equal.
      f_equal; f_equal.
      apply urelspinj_equal.
      refine (urel_equiv_2 _#6 _ _ Hr).
        {
        exact (urel_closed _#5 Hpq1 ander).
        }
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1); auto using step_ppi11.
        exact Hstepsq.
        }
      apply star_one; apply step_ppi12.
      }
    }
  }

  {
  simpsub.
  apply equivsub_dot; auto using equivsub_refl.
  apply (equiv_trans _ _ (ppair p1 p2)).
    {
    apply equiv_ppair.
      {
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1); auto using step_ppi11.
        exact Hstepsp.
        }
      apply star_one; apply step_ppi12.
      }

      {
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi2); auto using step_ppi21.
        exact Hstepsp.
        }
      apply star_one; apply step_ppi22.
      }
    }

    {
    apply equiv_symm.
    apply steps_equiv; eauto.
    }
  }

  {
  simpsub.
  apply equivsub_dot; auto using equivsub_refl.
  apply (equiv_trans _ _ (ppair q1 q2)).
    {
    apply equiv_ppair.
      {
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1); auto using step_ppi11.
        exact Hstepsq.
        }
      apply star_one; apply step_ppi12.
      }

      {
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi2); auto using step_ppi21.
        exact Hstepsq.
        }
      apply star_one; apply step_ppi22.
      }
    }

    {
    apply equiv_symm.
    apply steps_equiv; eauto.
    }
  }

  {
  intros j d uu Hji Huu.
  so (smaller_impl_le _#3 Hji) as Hj.
  rewrite -> !qpromote_cons in Huu.
  rewrite -> !qpromote_hyp_tm in Huu.
  simpsubin Huu.
  invertc Huu.
  intros r2 uu' Huu' Hr2 <-.
  invertc Huu'.
  intros r1 u Hu Hr1 <-.
  simpsub.
  rewrite -> qpromote_cons.
  rewrite -> qpromote_hyp_tm.
  apply seqctx_cons; auto.
  simpsub.
  invertc Hr1.
  intros A' Hal' Har' Hr1.
  so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst A'.
  invertc Hr2.
  intros R Hbpl Hbrr Hr2.
  so (urel_closed _#5 Hr1 ander) as Hclr1.
  so (urel_closed _#5 Hr2 ander) as Hclr2.
  so (urel_closed _#5 Hpq1 andel) as Hclp1.
  so (urel_closed _#5 Hpq2 andel) as Hclp2.
  apply (seqhyp_relhyp_2 _#4 (hyp_tm (subst s' (sigma a b)))).
    {
    exploit (Hleft _#3 Hji Hu) as H.
    rewrite -> qpromote_hyp_tm in H.
    simpsubin H.
    simpsub.
    exact H.
    }
  apply (seqhyp_tm _#5 (iutruncate (S j) (iusigma stop A B))).
    {
    exact (basic_downward _#7 Hj Habl).
    }

    {
    simpsub.
    exact (basic_downward _#7 Hj Habr).
    }

    {
    destruct Hr1 as (Hjs & Hr1).
    split; auto.
    assert (rel (den A) j p1 r1) as Hpr1.
      {
      eapply urel_equiv_1; eauto; try prove_hygiene.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1); auto using step_ppi11.
        exact Hstepsp.
        }
      apply star_one; apply step_ppi12.
      }
    exists p1, r1, p2, r2, Hpr1.
    do2 4 split; auto using star_refl; try prove_hygiene.
    cbn.
    invert Hbl.
    intros _ _ Hact.
    so (Hact _#3 (le_refl _) Hpq1) as H; clear Hact.
    simpsubin H.
    eassert _; [refine (basic_fun _#7 (basic_equiv _#7 _ _ Hbpl) (basic_downward _#7 Hj H)) |]; clear H; try prove_hygiene.
      {
      apply equiv_funct; auto using equiv_refl.
      apply equivsub_dot; auto using equivsub_refl.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1); auto using step_ppi11.
        exact Hstepsp.
        }
      apply star_one; apply step_ppi12.
      }
    subst R.
    destruct Hr2 as (_ & Hr2).
    refine (rel_from_dist _#6 _ (urel_equiv_1 _#6 _ _ Hr2)); auto.
      {
      apply den_nonexpansive.
      apply (pi2 B).
      apply urelspinj_dist_diff; auto.
      }
      
      {
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi2); auto using step_ppi21.
        exact Hstepsp.
        }
      apply star_one; apply step_ppi22.
      }
    }
  }

  {
  intros j d uu Hji Huu.
  so (smaller_impl_le _#3 Hji) as Hj.
  rewrite -> !qpromote_cons in Huu.
  rewrite -> !qpromote_hyp_tm in Huu.
  simpsubin Huu.
  invertc Huu.
  intros r2 uu' Huu' Hr2 <-.
  invertc Huu'.
  intros r1 u Hu Hr1 <-.
  simpsub.
  rewrite -> qpromote_cons.
  rewrite -> qpromote_hyp_tm.
  apply seqctx_cons; auto.
  simpsub.
  invertc Hr1.
  intros A' Hal' Har' Hr1.
  so (basic_fun _#7 (basic_downward _#7 Hj Har) Har'); subst A'.
  invertc Hr2.
  intros R Hbrl Hbpr Hr2.
  so (urel_closed _#5 Hr1 andel) as Hclr1.
  so (urel_closed _#5 Hr2 andel) as Hclr2.
  so (urel_closed _#5 Hpq1 ander) as Hclq1.
  so (urel_closed _#5 Hpq2 ander) as Hclq2.
  apply (seqhyp_relhyp_1 _#3 (hyp_tm (subst s (sigma a b)))).
    {
    exploit (Hright _#3 Hji Hu) as H.
    rewrite -> qpromote_hyp_tm in H.
    simpsubin H.
    simpsub.
    exact H.
    }
  apply (seqhyp_tm _#5 (iutruncate (S j) (iusigma stop A B))).
    {
    simpsub.
    exact (basic_downward _#7 Hj Habl).
    }

    {
    simpsub.
    exact (basic_downward _#7 Hj Habr).
    }

    {
    destruct Hr1 as (Hjs & Hr1).
    split; auto.
    assert (rel (den A) j r1 q1) as Hrq1.
      {
      eapply urel_equiv_2; eauto; try prove_hygiene.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1); auto using step_ppi11.
        exact Hstepsq.
        }
      apply star_one; apply step_ppi12.
      }
    exists r1, q1, r2, q2, Hrq1.
    do2 4 split; auto using star_refl; try prove_hygiene.
    cbn.
    invert Hbr.
    intros _ _ Hact.
    so (Hact _#3 (le_refl _) Hpq1) as H; clear Hact.
    simpsubin H.
    eassert _; [refine (basic_fun _#7 (basic_equiv _#7 _ _ Hbpr) (basic_downward _#7 Hj H)) |]; clear H; try prove_hygiene.
      {
      apply equiv_funct; auto using equiv_refl.
      apply equivsub_dot; auto using equivsub_refl.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1); auto using step_ppi11.
        exact Hstepsq.
        }
      apply star_one; apply step_ppi12.
      }
    subst R.
    destruct Hr2 as (_ & Hr2).
    refine (rel_from_dist _#6 _ (urel_equiv_2 _#6 _ _ Hr2)); auto.
      {
      apply den_nonexpansive.
      apply (pi2 B).
      apply urelspinj_dist_diff; auto.
      eapply urel_downward_leq; eauto.
      }
      
      {
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi2); auto using step_ppi21.
        exact Hstepsq.
        }
      apply star_one; apply step_ppi22.
      }
    }
  }
Qed.


Lemma sound_sigma_ext :
  forall G a b m n a' a'' b' b'',
    pseq G (deq (ppi1 m) (ppi1 n) a)
    -> pseq G (deq (ppi2 m) (ppi2 n) (subst1 (ppi1 m) b))
    -> pseq (cons (hyp_tm a) G) (deqtype b b)
    -> pseq G (deq m m (sigma a' b'))
    -> pseq G (deq n n (sigma a'' b''))
    -> pseq G (deq m n (sigma a b)).
Proof.
intros G a b m n a' a'' b' b''.
revert G.
refine (seq_pseq 3 [hyp_emp] b [] m [] n 5 [] _ [] _ [_] _ [] _ [] _ _ _); cbn.
intros G Hclb Hclm Hcln Hseq1 Hseq2 Hseqb Hseqm Hseqn.
rewrite -> seq_deq in Hseq1, Hseq2, Hseqm, Hseqn |- *.
rewrite -> seq_eqtype in Hseqb.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq1 _#3 Hs) as (A & Hal & Har & Hm1 & Hn1 & Hmn1).
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as H; eauto using subst_closub_under_permit.
  { 
  exact (f_equal den (basic_impl_iutruncate _#6 Hal)).
  }

  {
  intros j r t Hrt.
  so (basic_member_index _#9 Hal Hrt) as Hj.
  assert (pwctx j (dot r s) (dot t s') (cons (hyp_tm a) G)) as Hs'.
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
      intros j' u u' Hu.
      so (Hseq1 _#3 Hu) as (Q & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hs') as (Q & Hl & Hr & _).
  exists Q.
  simpsub.
  auto.
  }
destruct H as (B & Hbl & Hbr).
so (Hseq2 _#3 Hs) as (Bx & Hbxl & _ & Hm2 & Hn2 & Hmn2).
invert Hbl.
intros _ _ Hact.
so (Hact _ _ _ (le_refl _) Hm1) as Hbxl'; clear Hact.
simpsubin Hbxl.
simpsubin Hbxl'.
so (basic_fun _#7 Hbxl Hbxl'); subst Bx.
clear Hbxl Hbxl'.
so (Hseqm _#3 Hs) as (R & Hsigl & _ & Hm & _).
simpsubin Hsigl.
invert (basic_value_inv _#6 value_sigma Hsigl).
intros A' B' _ _ <-.
cbn in Hm.
decompose Hm.
intros m1 m1' m2 m2' _ _ _ Hstepsm Hstepsm' _.
clear A' B' Hsigl.
so (Hseqn _#3 Hs) as (R & Hsigl & _ & Hn & _).
simpsubin Hsigl.
invert (basic_value_inv _#6 value_sigma Hsigl).
intros A' B' _ _ <-.
cbn in Hn.
decompose Hn.
intros n1 n1' n2 n2' _ _ _ Hstepsn Hstepsn' _.
clear A' B' Hsigl.
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsm (subst_closub _#4 Hcls Hclm))) as H; cbn in H.
destruct H as (Hclm1 & Hclm2 & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsm' (subst_closub _#4 Hcls' Hclm))) as H; cbn in H.
destruct H as (Hclm1' & Hclm2' & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsn (subst_closub _#4 Hcls Hcln))) as H; cbn in H.
destruct H as (Hcln1 & Hcln2 & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsn' (subst_closub _#4 Hcls' Hcln))) as H; cbn in H.
destruct H as (Hcln1' & Hcln2' & _).
assert (equiv (ppi1 (subst s m)) m1) as Hequivm1.
  {
  simpsub.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi1); eauto using step_ppi11.
    }
  apply star_one.
  apply step_ppi12.
  }
assert (equiv (ppi1 (subst s' m)) m1') as Hequivm1'.
  {
  simpsub.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi1); eauto using step_ppi11.
    }
  apply star_one.
  apply step_ppi12.
  }
assert (equiv (ppi2 (subst s m)) m2) as Hequivm2.
  {
  simpsub.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi2); eauto using step_ppi21.
    }
  apply star_one.
  apply step_ppi22.
  }
assert (equiv (ppi2 (subst s' m)) m2') as Hequivm2'.
  {
  simpsub.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi2); eauto using step_ppi21.
    }
  apply star_one.
  apply step_ppi22.
  }
assert (equiv (ppi1 (subst s n)) n1) as Hequivn1.
  {
  simpsub.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi1); eauto using step_ppi11.
    }
  apply star_one.
  apply step_ppi12.
  }
assert (equiv (ppi1 (subst s' n)) n1') as Hequivn1'.
  {
  simpsub.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi1); eauto using step_ppi11.
    }
  apply star_one.
  apply step_ppi12.
  }
assert (equiv (ppi2 (subst s n)) n2) as Hequivn2.
  {
  simpsub.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi2); eauto using step_ppi21.
    }
  apply star_one.
  apply step_ppi22.
  }
assert (equiv (ppi2 (subst s' n)) n2') as Hequivn2'.
  {
  simpsub.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi2); eauto using step_ppi21.
    }
  apply star_one.
  apply step_ppi22.
  }
exists (iusigma stop A B).
simpsub.
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_sigma; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_sigma; auto.
  }

  {
  assert (rel (den A) i m1 m1') as Hrel.
    {
    refine (urel_equiv _#7 _ _ _ _ Hm1); auto.
    }
  exists m1, m1', m2, m2', Hrel.
  do2 4 split; eauto using subst_closub.
  cbn.
  eassert _ as H; [refine (urel_equiv _#4 m2 _ m2' _#4 Hm2) |]; auto.
  force_exact H; clear H.
  do 3 f_equal.
  apply urelspinj_equal.
  refine (urel_equiv_2 _#6 _ _ Hm1); auto.
  }

  {
  assert (rel (den A) i n1 n1') as Hrel.
    {
    refine (urel_equiv _#7 _ _ _ _ Hn1); auto.
    }
  exists n1, n1', n2, n2', Hrel.
  do2 4 split; eauto using subst_closub.
  cbn.
  eassert _ as H; [refine (urel_equiv _#4 n2 _ n2' _#4 Hn2) |]; auto.
  force_exact H; clear H.
  do 3 f_equal.
  apply urelspinj_equal.
  refine (urel_equiv_2 _#6 _ _ Hmn1); auto.
  }

  {
  assert (rel (den A) i m1 n1') as Hrel.
    {
    refine (urel_equiv _#7 _ _ _ _ Hmn1); auto.
    }
  exists m1, n1', m2, n2', Hrel.
  do2 4 split; eauto using subst_closub.
  cbn.
  eassert _ as H; [refine (urel_equiv _#4 m2 _ n2' _#4 Hmn2) |]; auto.
  force_exact H; clear H.
  do 3 f_equal.
  apply urelspinj_equal.
  refine (urel_equiv_2 _#6 _ _ Hmn1); auto.
  }
Qed.


Lemma sound_prod_kind_formation :
  forall G lv k k' l l',
    pseq G (deq k k' (kind lv))
    -> pseq G (deq l l' (kind lv))
    -> pseq G (deq (prod k l) (prod k' l') (kind lv)).
Proof.
intros G lv k1 k2 l1 l2.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqk Hseql.
rewrite -> seq_eqkind in Hseqk, Hseql |- *.
intros i s s' Hs.
so (Hseqk _#3 Hs) as (pg & K & A & hl & Hlvl & Hlvr & Hk1lt & Hk1rt & Hk2lt & Hk2rt & Hk1l & Hk1r & Hk2l & Hk2r).
clear Hseqk.
so (Hseql _#3 Hs) as (pg' & L & B & hl' & Hlvl' & _ & Hl1lt & Hl1rt & Hl2lt & Hl2rt & Hl1l & Hl1r & Hl2l & Hl2r).
clear Hseql.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
so (proof_irrelevance _ hl hl'); subst hl'.
exists pg, (qprod K L), (iuprod stop A B), hl.
simpsub.
do2 9 split; auto;
try (apply kinterp_eval_refl; apply interp_kprod; auto; done);
apply interp_eval_refl; apply interp_prod; auto.
Qed.


Lemma sound_prod_formation :
  forall G k k' l l',
    pseq G (deqtype k k')
    -> pseq G (deqtype l l')
    -> pseq G (deqtype (prod k l) (prod k' l')).
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
exists (iuprod stop A B).
simpsub.
do2 3 split; auto;
apply interp_eval_refl;
apply interp_prod; auto.
Qed.


Lemma sound_prod_formation_univ :
  forall G lv k k' l l',
    pseq G (deq k k' (univ lv))
    -> pseq G (deq l l' (univ lv))
    -> pseq G (deq (prod k l) (prod k' l') (univ lv)).
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
exists pg, (iuprod stop A B).
simpsub.
do2 5 split; auto;
apply interp_eval_refl;
apply interp_prod; auto.
Qed.


Lemma sound_prod_sigma_equal :
  forall G a b,
    pseq G (deqtype a a)
    -> pseq G (deqtype b b)
    -> pseq G (deqtype (prod a b) (sigma a (subst sh1 b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 1 [] b 2 [] _ [] _ _ _); cbn.
intros G Hclb Hseqa Hseqb.
rewrite -> seq_eqtype in Hseqa, Hseqb |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
so (Hseqb _#3 Hs) as (B & Hbl & Hbr & _).
exists (iuprod stop A B).
simpsub.
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
do2 3 split; auto;
apply interp_eval_refl;
try (apply interp_prod); auto.
  {
  rewrite -> iuprod_eq_iusigma.
  apply interp_sigma; auto.
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
  rewrite -> iuprod_eq_iusigma.
  apply interp_sigma; auto.
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


Lemma sound_prod_sigma_equal_univ :
  forall G lv a b,
    pseq G (deq a a (univ lv))
    -> pseq G (deq b b (univ lv))
    -> pseq G (deq (prod a b) (sigma a (subst sh1 b)) (univ lv)).
Proof.
intros G lv a b.
revert G.
refine (seq_pseq 1 [] b 2 [] _ [] _ _ _); cbn.
intros G Hclb Hseqa Hseqb.
rewrite -> seq_univ in Hseqa, Hseqb |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (pg & A & Hlvl & Hlvr & Hal & Har & _).
so (Hseqb _#3 Hs) as (pg' & B & Hlvl' & _ & Hbl & Hbr & _).
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
exists pg, (iuprod stop A B).
simpsub.
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
do2 5 split; auto;
apply interp_eval_refl;
try (apply interp_prod); auto.
  {
  rewrite -> iuprod_eq_iusigma.
  apply interp_sigma; auto.
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
  rewrite -> iuprod_eq_iusigma.
  apply interp_sigma; auto.
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


Lemma sound_prod_elim1 :
  forall G a b m n,
    pseq G (deq m n (prod a b))
    -> pseq G (deq (ppi1 m) (ppi1 n) a).
Proof.
intros G a b m n.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hl & Hr & Hm & Hn & Hmn).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_prod Hl).
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_prod Hr).
intros A' B' Har Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iuprod_inj _#5 Heq) as (<- & _); clear Heq.
exists A.
do2 2 split; auto.
simpsub.
clear Hseq.
revert m n Hm Hn Hmn.
cut (forall m n, 
       rel (den (iuprod stop A B)) i m n
       -> rel (den A) i (ppi1 m) (ppi1 n)).
  {
  intros.
  do2 2 split; auto.
  }
intros m n Hmn.
cbn in Hmn.
decompose Hmn.
intros m1 n1 m2 n2 Hclm Hcln Hstepsm Hstepsn Hmn1 Hmn2.
refine (urel_equiv _#7 _ _ _ _ Hmn1); try prove_hygiene.
  {
  apply equiv_symm.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi1); auto using step_ppi11.
    exact Hstepsm.
    }
  apply star_one; apply step_ppi12.
  }

  {
  apply equiv_symm.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi1); auto using step_ppi11.
    exact Hstepsn.
    }
  apply star_one; apply step_ppi12.
  }
Qed.


Lemma sound_prod_elim2 :
  forall G a b m n,
    pseq G (deq m n (prod a b))
    -> pseq G (deq (ppi2 m) (ppi2 n) b).
Proof.
intros G a b m n.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hl & Hr & Hm & Hn & Hmn).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_prod Hl).
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_prod Hr).
intros A' B' Har Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iuprod_inj _#5 Heq) as (<- & Heq'); clear Heq.
assert (B = B').
  {
  cbn in Hm.
  decompose Hm.
  intros p q _ _ _ _ _ _ H _.
  so (Heq' _#3 H) as Heq.
  rewrite <- (basic_impl_iutruncate _#6 Hbl) in Heq.
  rewrite <- (basic_impl_iutruncate _#6 Hbr) in Heq.
  exact Heq.
  }
subst B'.
clear Heq'.
exists B.
do2 2 split; auto.
simpsub.
clear Hseq.
revert m n Hm Hn Hmn.
cut (forall m n, 
       rel (den (iuprod stop A B)) i m n
       -> rel (den B) i (ppi2 m) (ppi2 n)).
  {
  intros.
  do2 2 split; auto.
  }
intros m n Hmn.
cbn in Hmn.
decompose Hmn.
intros m1 n1 m2 n2 Hclm Hcln Hstepsm Hstepsn Hmn1 Hmn2.
refine (urel_equiv _#7 _ _ _ _ Hmn2); try prove_hygiene.
  {
  apply equiv_symm.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi2); auto using step_ppi21.
    exact Hstepsm.
    }
  apply star_one; apply step_ppi22.
  }

  {
  apply equiv_symm.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi2); auto using step_ppi21.
    exact Hstepsn.
    }
  apply star_one; apply step_ppi22.
  }
Qed.


Lemma sound_sigma_formation_invert1 :
  forall G a a' b b',
    pseq G (deqtype (sigma a b) (sigma a' b'))
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
invert (basic_value_inv _#6 value_sigma Hpil).
intros A B Hal Hbl Heql.
invert (basic_value_inv _#6 value_sigma Hpir).
intros A' B' Har Hbr Heqr.
so (iusigma_inj _#5 (eqtrans Heql (eqsymm Heqr))) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
invert (basic_value_inv _#6 value_sigma Hpil').
intros A' B' Hal' Hbl' Heql'.
so (iusigma_inj _#5 (eqtrans Heql (eqsymm Heql'))) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
invert (basic_value_inv _#6 value_sigma Hpir').
intros A' B' Har' Hbr' Heqr'.
so (iusigma_inj _#5 (eqtrans Heql (eqsymm Heqr'))) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
exists A.
auto.
Qed.


Lemma sound_sigma_formation_invert2 :
  forall G a a' b b',
    pseq G (deqtype (sigma a b) (sigma a' b'))
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
invert (basic_value_inv _#6 value_sigma Hpil).
intros A B Hal Hcl Heqacl.
invert (basic_value_inv _#6 value_sigma Hpir).
intros A' B' Har Hcr Heqacr.
so (eqtrans Heqacl (eqsymm Heqacr)) as Heq.
clear Heqacr.
invert (basic_value_inv _#6 value_sigma Hpil').
intros A'' B'' Hbl Hdl Heqbdl.
so (eqtrans Heqacl (eqsymm Heqbdl)) as Heq'.
clear Heqbdl.
invert (basic_value_inv _#6 value_sigma Hpir').
intros A''' B''' Hbr Hdr Heqbdr.
so (eqtrans Heqacl (eqsymm Heqbdr)) as Heq''.
clear Heqbdr.
subst R.
so (iusigma_inj _#5 Heq) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
so (iusigma_inj _#5 Heq') as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
so (iusigma_inj _#5 Heq'') as H.
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


Lemma sound_prod_formation_invert1 :
  forall G a a' b b',
    pseq G (deqtype (prod a b) (prod a' b'))
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
invert (basic_value_inv _#6 value_prod Hpil).
intros A B Hal Hbl Heql.
invert (basic_value_inv _#6 value_prod Hpir).
intros A' B' Har Hbr Heqr.
so (iuprod_inj _#5 (eqtrans Heql (eqsymm Heqr))) as (<- & _).
invert (basic_value_inv _#6 value_prod Hpil').
intros A' B'' Hal' Hbl' Heql'.
so (iuprod_inj _#5 (eqtrans Heql (eqsymm Heql'))) as (<- & _).
invert (basic_value_inv _#6 value_prod Hpir').
intros A' B''' Har' Hbr' Heqr'.
so (iuprod_inj _#5 (eqtrans Heql (eqsymm Heqr'))) as (<- & _).
exists A.
auto.
Qed.


Lemma sound_prod_formation_invert2 :
  forall G a a' b b',
    pseq G (deqtype (prod a b) (prod a' b'))
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
invert (basic_value_inv _#6 value_prod Hpil).
intros A' B Hal' Hcl Heqacl.
so (basic_fun _#7 Hal Hal'); subst A'.
invert (basic_value_inv _#6 value_prod Hpir).
intros A' B' Har' Hcr Heqacr.
so (eqtrans Heqacl (eqsymm Heqacr)) as Heq.
clear Heqacr.
invert (basic_value_inv _#6 value_prod Hpil').
intros A'' B'' Hbl Hdl Heqbdl.
so (eqtrans Heqacl (eqsymm Heqbdl)) as Heq'.
clear Heqbdl.
invert (basic_value_inv _#6 value_prod Hpir').
intros A''' B''' Hbr Hdr Heqbdr.
so (eqtrans Heqacl (eqsymm Heqbdr)) as Heq''.
clear Heqbdr.
subst R.
so (iuprod_inj _#5 Heq) as (<- & H).
so (H _#3 Hmp) as HeqB; clear H.
rewrite <- (basic_impl_iutruncate _#6 Hcl) in HeqB.
rewrite <- (basic_impl_iutruncate _#6 Hcr) in HeqB.
subst B'.
so (iuprod_inj _#5 Heq') as (<- & H).
so (H _#3 Hmp) as HeqB; clear H.
rewrite <- (basic_impl_iutruncate _#6 Hcl) in HeqB.
rewrite <- (basic_impl_iutruncate _#6 Hdl) in HeqB.
subst B''.
so (iuprod_inj _#5 Heq'') as (<- & H).
so (H _#3 Hmp) as HeqB; clear H.
rewrite <- (basic_impl_iutruncate _#6 Hcl) in HeqB.
rewrite <- (basic_impl_iutruncate _#6 Hdr) in HeqB.
subst B'''.
exists B.
simpsub.
do2 3 split; auto.
Qed.
