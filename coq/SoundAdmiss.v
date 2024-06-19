
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
Require Import Ceiling.
Require Import SoundSimple.
Require Import Equivalence.
Require Import Truncate.
Require Import ProperDownward.
Require Import MapTerm.
Require Import SoundUtil.
Require Import SoundPartialUtil.
Require Import Urelsp.

Require Import SemanticsSimple.
Require Import SemanticsPi.
Require Import SemanticsSigma.
Require Import SemanticsFut.
Require Import SemanticsSet.
Require Import SoundSequal.

Local Ltac prove_hygiene :=
  repeat (apply hygiene_auto; cbn; repeat2 split; auto);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1, subst_closub;
  try (eapply subst_closub_under_permit; eauto; done);
  try (apply hygiene_var; cbn; auto; done).


Lemma sound_total_stuff :
  forall G a m,
    pseq G (deq m m a)
    -> (forall i s A n q,
          interp toppg true i (subst s a) A
          -> rel (den A) i n q
          -> converges n /\ converges q)
    -> pseq G (deq triv triv (halts m)).
Proof.
intros G a m Hseq Hstuff.
revert G Hseq.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_deq in Hseq.
rewrite -> seq_halts.
intros i s s' Hs.
so (Hseq _#3 Hs) as (A & Hal & _ & Hm & _).
so (urel_closed _#5 Hm) as (Hcl & Hcl').
so (Hstuff _#5 Hal Hm) as (Hconv & Hconv').
auto.
Qed.


Theorem sound_total_flat :
  forall G a m,
    flat a
    -> pseq G (deq m m a)
    -> pseq G (deq triv triv (halts m)).
Proof.
intros G a m Hflat Hpseq.
eapply sound_total_stuff; eauto.
intros i s A p q Ha Hpq.
so (Hflat _#6 Ha Hpq) as (th & Hcanon & Hp & Hq).
split.
  {
  exists (oper [] th rw_nil).
  split; auto.
  apply value_i; auto.
  }

  {
  exists (oper [] th rw_nil).
  split; auto.
  apply value_i; auto.
  }
Qed.


Lemma flat_impl_upward :
  forall w A,
    (forall i m p, 
       rel A i m p 
       -> exists th, 
            canon _ th
            /\ star step m (oper [] th rw_nil) 
            /\ star step p (oper [] th rw_nil))
    -> upward w A.
Proof.
intros w A Hflat.
intros i m m' p p' Happroxm Happroxp Hmp.
so (Hflat _#3 Hmp) as (th & Hcanon & Hstepsm & Hstepsp).
so (sapprox_action _#4 Happroxm (conj Hstepsm (value_i _#4 Hcanon))) as (v & (Hstepsm' & _) & Hmc).
invertc_mc Hmc.
intros <-.
so (sapprox_action _#4 Happroxp (conj Hstepsp (value_i _#4 Hcanon))) as (v & (Hstepsp' & _) & Hmc).
invertc_mc Hmc.
intros <-.
refine (urel_equiv _#7 _ _ _ _ Hmp).
  {
  exact (sapprox_closed _#3 Happroxm ander).
  }

  {
  exact (sapprox_closed _#3 Happroxp ander).
  }

  {
  eapply (equiv_trans _ _ (oper [] th rw_nil)).
    {
    apply steps_equiv; auto.
    }

    {
    apply equiv_symm.
    apply steps_equiv; auto.
    }
  }

  {
  eapply (equiv_trans _ _ (oper [] th rw_nil)).
    {
    apply steps_equiv; auto.
    }

    {
    apply equiv_symm.
    apply steps_equiv; auto.
    }
  }
Qed.


Lemma sound_flat_upward :
  forall G a,
    flat a
    -> pseq G (deqtype a a)
    -> pseq G (deq triv triv (uptype a)).
Proof.
intros G a Hflat.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq.
rewrite -> seq_uptype.
intros i s s' Hs.
so (Hseq _#3 Hs) as (A & Hal & Har & _).
exists A.
do2 2 split; auto.
apply flat_impl_upward.
intros j m p Hmp.
destruct Hmp as (Hj & Hmp).
eapply Hflat; eauto.
Qed.


(* Redundant *)
Lemma sound_voidtp_uptype :
  forall G,
    pseq G (deq triv triv (uptype voidtp)).
Proof.
intro G.
apply sound_flat_upward.
2:{
  revert G.
  refine (seq_pseq 0 0 _ _); cbn.
  intro G.
  rewrite -> seq_eqtype.
  intros i s s' Hs.
  exists (iubase (void_urel stop)).
  simpsub.
  do2 3 split.
    {
    apply interp_eval_refl; apply interp_void.
    }
  
    {
    apply interp_eval_refl; apply interp_void.
    }

    {
    apply interp_eval_refl; apply interp_void.
    }
  
    {
    apply interp_eval_refl; apply interp_void.
    }
  }
intros i j s A m p Ha Hmp.
simpsubin Ha.
invert (basic_value_inv _#6 value_voidtp Ha).
intros <-.
destruct Hmp.
Qed.


Lemma sound_unittp_total :
  forall G m,
    pseq G (deq m m unittp)
    -> pseq G (deq triv triv (halts m)).
Proof.
intros G m Hseq.
eapply sound_total_stuff; eauto.
intros i s R n q Hl Hnq.
simpsubin Hl.
invert (basic_value_inv _#6 value_unittp Hl).
intros <-.
cbn in Hnq.
decompose Hnq.
intros _ _ _ _ Hsteps Hsteps'.
split; exists triv; split; auto using value_triv.
Qed.    


(* Redundant *)
Lemma sound_unittp_uptype :
  forall G,
    pseq G (deq triv triv (uptype unittp)).
Proof.
intro G.
apply sound_flat_upward.
2:{
  revert G.
  refine (seq_pseq 0 0 _ _); cbn.
  intro G.
  rewrite -> seq_eqtype.
  intros i s s' Hs.
  exists (iubase (unit_urel stop i)).
  simpsub.
  do2 3 split.
    {
    apply interp_eval_refl; apply interp_unit.
    }
  
    {
    apply interp_eval_refl; apply interp_unit.
    }

    {
    apply interp_eval_refl; apply interp_unit.
    }
  
    {
    apply interp_eval_refl; apply interp_unit.
    }
  }
intros i j s A m p Ha Hmp.
simpsubin Ha.
invert (basic_value_inv _#6 value_unittp Ha).
intros <-.
cbn in Hmp.
decompose Hmp.
intros _ _ _ _ Hm Hp.
exists (oper_triv _).
do2 2 split; auto.
apply canon_triv.
Qed.


Lemma sound_booltp_total :
  forall G m,
    pseq G (deq m m booltp)
    -> pseq G (deq triv triv (halts m)).
Proof.
intros G m Hseq.
eapply sound_total_stuff; eauto.
intros i s R n q Hl Hnq.
simpsubin Hl.
invert (basic_value_inv _#6 value_booltp Hl).
intros <-.
cbn in Hnq.
decompose Hnq.
intros _ _ _ H.
destruct H as [(Hsteps & Hsteps') | (Hsteps & Hsteps')].
  {
  split; exists btrue; split; auto using value_btrue.
  }

  {
  split; exists bfalse; split; auto using value_bfalse.
  }
Qed.    


Lemma sound_booltp_uptype :
  forall G,
    pseq G (deq triv triv (uptype booltp)).
Proof.
intro G.
apply sound_flat_upward.
2:{
  revert G.
  refine (seq_pseq 0 0 _ _); cbn.
  intro G.
  rewrite -> seq_eqtype.
  intros i s s' Hs.
  exists (iubase (bool_urel stop i)).
  simpsub.
  do2 3 split.
    {
    apply interp_eval_refl; apply interp_bool.
    }
  
    {
    apply interp_eval_refl; apply interp_bool.
    }

    {
    apply interp_eval_refl; apply interp_bool.
    }
  
    {
    apply interp_eval_refl; apply interp_bool.
    }
  }
intros i j s A m p Ha Hmp.
simpsubin Ha.
invert (basic_value_inv _#6 value_booltp Ha).
intros <-.
cbn in Hmp.
decompose Hmp.
intros _ _ _ H.
destruct H as [(Hsteps & Hsteps') | (Hsteps & Hsteps')].
  {
  exists (oper_btrue _).
  do2 2 split; auto.
  apply canon_btrue.
  }

  {
  exists (oper_bfalse _).
  do2 2 split; auto.
  apply canon_bfalse.
  }
Qed.


Lemma sound_pi_total :
  forall G a b m,
    pseq G (deq m m (pi a b))
    -> pseq G (deq triv triv (halts m)).
Proof.
intros G a b m Hseq.
eapply sound_total_stuff; eauto.
intros i s R n q Hl Hnq.
simpsubin Hl.
invert (basic_value_inv _#6 value_pi Hl).
intros A B _ _ <-.
cbn in Hnq.
decompose Hnq.
intros n' q' _ _ _ Hsteps Hsteps' _.
split.
  {
  exists (lam n').
  split; auto using value_lam.
  }

  {
  exists (lam q').
  split; auto using value_lam.
  }
Qed.


Lemma sound_pi_uptype :
  forall G a b,
    pseq G (deqtype a a)
    -> pseq (cons (hyp_tm a) G) (deq triv triv (uptype b))
    -> pseq G (deq triv triv (uptype (pi a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 2 [] a [hyp_emp] b 2 [] _ [_] _ _ _); cbn.
intros G Hcla Hclb Hseqa Hseqb.
rewrite -> seq_eqtype in Hseqa.
rewrite -> seq_uptype in Hseqb |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr); eauto using subst_closub_under_permit.
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
      so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hss) as (R & Hbl & Hbr & _).
  exists R.
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
intros j m m' p p' Happroxm Happroxp Hmp.
destruct Hmp as (Hj & Hmp).
split; auto.
cbn in Hmp |- *.
decompose Hmp.
clear Hj.
intros r t Hj _ _ Hstepsm Hstepsp Hact.
so (sapprox_closed _#3 Happroxm) as (Hclm & Hclm').
so (sapprox_closed _#3 Happroxp) as (Hclp & Hclp').
so (sapprox_action _#4 Happroxm (conj Hstepsm value_lam)) as (x & (Hstepsm' & _) & H).
invertc_mc H.
intros r' Hr.
fold (lam r').
intros <-.
so (sapprox_action _#4 Happroxp (conj Hstepsp value_lam)) as (x & (Hstepsp' & _) & H).
invertc_mc H.
intros t' Ht.
fold (lam t').
intros <-.
exists r', t'.
do2 5 split; auto.
intros j' n q Hj' Hnq.
so (urel_closed _#5 Hnq) as (Hcln & Hclq).
so (Hact _ _ _ Hj' Hnq) as Hnrqt.
assert (pwctx j' (dot n s) (dot q s') (cons (hyp_tm a) G)) as Hss.
  {
  apply pwctx_cons_tm_seq.
    {
    apply (pwctx_downward i); auto.
    omega.
    }

    {
    apply (seqhyp_tm _#5 (iutruncate (S j') A)).
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
    }

    {
    intros k u u' Hu.
    so (Hseqa _#3 Hu) as (R & H & H' & _).
    eauto.
    }
  }
so (Hseqb _#3 Hss) as (R & H & _ & Hupward).
so (f_equal den (basic_impl_iutruncate _#6 H)) as Heq.
rewrite -> den_iutruncate in Heq.
rewrite <- Heq in Hupward.
invert Hbl.
intros _ _ Hactb.
so (Hactb _ _ _ (le_trans _#3 Hj' Hj) Hnq) as H'.
simpsubin H'.
so (basic_fun _#7 H H').
subst R.
clear H H'.
eapply Hupward; eauto.
  {
  apply Hr.
    {
    so (steps_hygiene _#4 Hstepsm Hclm) as H.
    so (hygiene_invert_auto _#5 H) as H'; cbn in H'; clear H.
    destruct H' as (H & _).
    apply hygiene_subst1; auto.
    }

    {
    so (steps_hygiene _#4 Hstepsm' Hclm') as H.
    so (hygiene_invert_auto _#5 H) as H'; cbn in H'; clear H.
    destruct H' as (H & _).
    apply hygiene_subst1; auto.
    }
  }

  {
  apply Ht.
    {
    so (steps_hygiene _#4 Hstepsp Hclp) as H.
    so (hygiene_invert_auto _#5 H) as H'; cbn in H'; clear H.
    destruct H' as (H & _).
    apply hygiene_subst1; auto.
    }

    {
    so (steps_hygiene _#4 Hstepsp' Hclp') as H.
    so (hygiene_invert_auto _#5 H) as H'; cbn in H'; clear H.
    destruct H' as (H & _).
    apply hygiene_subst1; auto.
    }
  }
Qed.


Lemma sound_pi_admiss :
  forall G a b,
    pseq G (deqtype a a)
    -> pseq (cons (hyp_tm a) G) (deq triv triv (admiss b))
    -> pseq G (deq triv triv (admiss (pi a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 2 [] a [hyp_emp] b 2 [] _ [_] _ _ _); cbn.
intros G Hcla Hclb Hseqa Hseqb.
rewrite -> seq_eqtype in Hseqa.
rewrite -> seq_admiss in Hseqb |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr); eauto using subst_closub_under_permit.
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
      so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hss) as (R & Hbl & Hbr & _).
  exists R.
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
intros f g i' m p j Hclf Hclg Hclm Hclp Hmp.
so (Hmp j (le_refl _)) as (Hi' & Hmpj).
split; auto.
cbn in Hmpj.
decompose Hmpj.
intros x y _ _ _ Hstepsx Hstepsy _.
so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _ f j Hclf) Hclm) (conj Hstepsx value_lam)) as (w & (Hstepsm1 & _) & Hmc).
invertc_mc Hmc.
intros m1 _.
fold (lam m1).
intros <-.
so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _ g j Hclg) Hclp) (conj Hstepsy value_lam)) as (w & (Hstepsp1 & _) & Hmc).
invertc_mc Hmc.
intros p1 _.
fold (lam p1).
intros <-.
clear x y Hstepsx Hstepsy.
exists m1, p1.
do2 5 split; auto.
  {
  omega.
  }

  {
  apply hygiene_subst1; auto; prove_hygiene.
  }

  {
  apply hygiene_subst1; auto; prove_hygiene.
  }
intros i'' n q Hi'' Hnq.
so (urel_closed _#5 Hnq) as (Hcln & Hclq).
assert (i'' <= i) as Hi''_i by omega.
assert (pwctx i'' (dot n s) (dot q s') (cons (hyp_tm a) G)) as Hss.
  {
  apply pwctx_cons_tm_seq.
    {
    apply (pwctx_downward i); auto.
    }

    {
    apply (seqhyp_tm _#5 (iutruncate (S i'') A)).
      {
      apply (basic_downward _#3 i); auto.
      }

      {
      apply (basic_downward _#3 i); auto.
      }

      {
      split; auto.
      }
    }

    {
    intros k u u' Hu.
    so (Hseqa _#3 Hu) as (R & H & H' & _).
    eauto.
    }
  }
so (Hseqb _#3 Hss) as (R & H & _ & Hadmiss).
so (f_equal den (basic_impl_iutruncate _#6 H)) as Heq.
rewrite -> den_iutruncate in Heq.
rewrite <- Heq in Hadmiss.
invert Hbl.
intros _ _ Hactb.
so (Hactb _ _ _ Hi''_i Hnq) as H'.
simpsubin H'.
so (basic_fun _#7 H H').
subst R.
clear H H'.
eassert _ as H; [refine (steps_hygiene _#4 Hstepsm1 _) |].
  {
  apply hygiene_subst1; prove_hygiene.
  }
so (hygiene_invert_auto _#5 H) as H'; cbn in H'; clear H.
destruct H' as (Hclm1 & _).
eassert _ as H; [refine (steps_hygiene _#4 Hstepsp1 _) |].
  {
  apply hygiene_subst1; prove_hygiene.
  }
so (hygiene_invert_auto _#5 H) as H'; cbn in H'; clear H.
destruct H' as (Hclp1 & _).
apply (urel_equiv _#3 (subst1 (app theta f) (app m (subst sh1 n))) _ (subst1 (app theta g) (app p (subst sh1 q)))); try prove_hygiene.
  {
  simpsub.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
    }
  apply star_one.
  apply step_app2.
  }

  {
  simpsub.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
    }
  apply star_one.
  apply step_app2.
  }
apply (Hadmiss _#5 j); auto; try prove_hygiene.
intros k Hk.
simpsub.
exact (pi_action_app _#10 Hnq Hi'' (Hmp _ Hk ander)).
Qed.


Lemma sound_intersect_strict :
  forall G a b m,
    pseq G (deq m m a)
    -> pseq (cons (hyp_tm a) G) (dsubtype b (partial b))
    -> pseq G (dsubtype (intersect a b) (partial (intersect a b))).
Proof.
intros G a b x.
revert G.
refine (seq_pseq 2 [] a [hyp_emp] b 2 [] _ [_] _ _ _); cbn.
intros G Hcla Hclb Hseqa Hseqb.
rewrite -> seq_deq in Hseqa.
rewrite -> seq_subtype in Hseqb |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & Hx & _).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr); eauto using subst_closub_under_permit.
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
      so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hss) as (R & _ & Hbl & Hbr & _).
  exists R.
  simpsub.
  auto.
  }
exists (iuintersect stop i A B), (iupartial stop i (iuintersect stop i A B)).
simpsub.
assert (forall j n q, j <= i -> rel (den A) j n q -> pwctx j (dot n s) (dot q s') (cons (hyp_tm a) G)) as Hss.
  {
  intros j n q Hj Hnq.
  apply pwctx_cons_tm_seq.
    {
    apply (pwctx_downward i); auto.
    }

    {
    apply (seqhyp_tm _#5 (iutruncate (S j) A)).
      {
      apply (basic_downward _#3 i); auto.
      }

      {
      apply (basic_downward _#3 i); auto.
      }

      {
      split; auto.
      }
    }

    {
    intros k u u' Hu.
    so (Hseqa _#3 Hu) as (R & H & H' & _).
    eauto.
    }
  }
do2 4 split.
  {
  apply interp_eval_refl; apply interp_intersect; auto.
  }

  {
  apply interp_eval_refl; apply interp_intersect; auto.
  }

  {
  apply interp_eval_refl; apply interp_partial.
  apply interp_eval_refl; apply interp_intersect; auto.
  }

  {
  apply interp_eval_refl; apply interp_partial.
  apply interp_eval_refl; apply interp_intersect; auto.
  }
intros j m p Hj Hmp.
cbn in Hmp.
decompose Hmp.
intros _ Hm Hp Hact.
do2 4 split; auto.
  {
  so (Hact _#3 (le_refl _) (urel_downward_leq _#6 Hj Hx)) as Hmp.
  invert Hbl.
  intros _ _ H.
  so (H _#3 Hj (urel_downward_leq _#6 Hj Hx)) as Hblx; clear H.
  so (Hseqb _#3 (Hss _#3 Hj (urel_downward_leq _#6 Hj Hx))) as (Bx & R & Hblx' & _ & Hl & _ & Hsubtype).
  simpsubin Hblx.
  so (basic_fun _#7 Hblx Hblx'); subst Bx.
  simpsubin Hl.
  invert (basic_value_inv _#6 value_partial Hl).
  intros Bx Hblx'' <-.
  so (basic_fun _#7 Hblx Hblx''); subst Bx.
  clear Hblx Hblx' Hl.
  so (Hsubtype _#3 (le_refl _) Hmp) as Hmp'.
  clear Hsubtype.
  destruct Hmp' as (_ & _ & _ & H & _).
  exact H.
  }

  {
  intro Hconv.
  do2 3 split; auto.
  }
Qed.
    

Lemma sound_intersect_admiss :
  forall G a b,
    pseq G (deqtype a a)
    -> pseq (cons (hyp_tm a) G) (deq triv triv (admiss b))
    -> pseq G (deq triv triv (admiss (intersect a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 2 [] a [hyp_emp] b 2 [] _ [_] _ _ _); cbn.
intros G Hcla Hclb Hseqa Hseqb.
rewrite -> seq_eqtype in Hseqa.
rewrite -> seq_admiss in Hseqb |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr); eauto using subst_closub_under_permit.
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
      so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hss) as (R & Hbl & Hbr & _).
  exists R.
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
intros f g i' m p j Hclf Hclg Hclm Hclp Hmp.
destruct (Hmp _ (le_refl _)) as (Hi' & _).
split; auto.
do2 3 split.
  {
  omega.
  }

  {
  apply hygiene_subst1; auto; prove_hygiene.
  }

  {
  apply hygiene_subst1; auto; prove_hygiene.
  }
intros i'' n q Hi'' Hnq.
so (urel_closed _#5 Hnq) as (Hcln & Hclq).
assert (i'' <= i) as Hi''_i by omega.
assert (pwctx i'' (dot n s) (dot q s') (cons (hyp_tm a) G)) as Hss.
  {
  apply pwctx_cons_tm_seq.
    {
    apply (pwctx_downward i); auto.
    }

    {
    apply (seqhyp_tm _#5 (iutruncate (S i'') A)).
      {
      apply (basic_downward _#3 i); auto.
      }

      {
      apply (basic_downward _#3 i); auto.
      }

      {
      split; auto.
      }
    }

    {
    intros k u u' Hu.
    so (Hseqa _#3 Hu) as (R & H & H' & _).
    eauto.
    }
  }
so (Hseqb _#3 Hss) as (R & H & _ & Hadmiss).
so (f_equal den (basic_impl_iutruncate _#6 H)) as Heq.
rewrite -> den_iutruncate in Heq.
rewrite <- Heq in Hadmiss.
invert Hbl.
intros _ _ Hactb.
so (Hactb _ _ _ Hi''_i Hnq) as H'.
simpsubin H'.
so (basic_fun _#7 H H').
subst R.
clear H H'.
apply (Hadmiss _#5 j); auto.
intros k Hk.
so (Hmp _ Hk) as H.
destruct H as (_ & _ & _ & _ & Hmp').
exact (Hmp' _ _ _ Hi'' Hnq).
Qed.


Lemma sound_intersect_uptype :
  forall G a b,
    pseq G (deqtype a a)
    -> pseq (cons (hyp_tm a) G) (deq triv triv (uptype b))
    -> pseq G (deq triv triv (uptype (intersect a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 2 [] a [hyp_emp] b 2 [] _ [_] _ _ _); cbn.
intros G Hcla Hclb Hseqa Hseqb.
rewrite -> seq_eqtype in Hseqa.
rewrite -> seq_uptype in Hseqb |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr); eauto using subst_closub_under_permit.
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
      so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hss) as (R & Hbl & Hbr & _).
  exists R.
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
intros j m m' p p' Happroxm Happroxp Hmp.
destruct Hmp as (Hj & Hmp).
split; auto.
so (sapprox_closed _#3 Happroxm) as (Hclm & Hclm').
so (sapprox_closed _#3 Happroxp) as (Hclp & Hclp').
do2 3 split; auto.
  {
  omega.
  }
intros j' n q Hj' Hnq.
so (urel_closed _#5 Hnq) as (Hcln & Hclq).
assert (j' <= i) as Hj'_i by omega.
assert (pwctx j' (dot n s) (dot q s') (cons (hyp_tm a) G)) as Hss.
  {
  apply pwctx_cons_tm_seq.
    {
    apply (pwctx_downward i); auto.
    }

    {
    apply (seqhyp_tm _#5 (iutruncate (S j') A)).
      {
      apply (basic_downward _#3 i); auto.
      }

      {
      apply (basic_downward _#3 i); auto.
      }

      {
      split; auto.
      }
    }

    {
    intros k u u' Hu.
    so (Hseqa _#3 Hu) as (R & H & H' & _).
    eauto.
    }
  }
so (Hseqb _#3 Hss) as (R & H & _ & Hupward).
so (f_equal den (basic_impl_iutruncate _#6 H)) as Heq.
rewrite -> den_iutruncate in Heq.
rewrite <- Heq in Hupward.
invert Hbl.
intros _ _ Hactb.
so (Hactb _ _ _ Hj'_i Hnq) as H'.
simpsubin H'.
so (basic_fun _#7 H H').
subst R.
clear H H'.
eapply Hupward; eauto.
destruct Hmp as (_ & _ & _ & H).
apply H; auto.
Qed.


Lemma sound_sigma_total :
  forall G a b m,
    pseq G (deq m m (sigma a b))
    -> pseq G (deq triv triv (halts m)).
Proof.
intros G a b m Hseq.
eapply sound_total_stuff; eauto.
intros i s R n q Hl Hnq.
simpsubin Hl.
invert (basic_value_inv _#6 value_sigma Hl).
intros A B _ _ <-.
cbn in Hnq.
decompose Hnq.
intros n1 q1 n2 q2 _ _ _ Hsteps Hsteps' _.
split.
  {
  exists (ppair n1 n2).
  split; auto using value_ppair.
  }

  {
  exists (ppair q1 q2).
  split; auto using value_ppair.
  }
Qed.
    

Lemma sound_sigma_uptype :
  forall G a b,
    pseq G (deq triv triv (uptype a))
    -> pseq (cons (hyp_tm a) G) (deq triv triv (uptype b))
    -> pseq G (deq triv triv (uptype (sigma a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 2 [] a [hyp_emp] b 2 [] _ [_] _ _ _); cbn.
intros G Hcla Hclb Hseqa Hseqb.
rewrite -> seq_uptype in Hseqa, Hseqb |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & Hupwarda).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr); eauto using subst_closub_under_permit.
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
      so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hss) as (R & Hbl & Hbr & _).
  exists R.
  simpsub.
  auto.
  }
exists (iusigma stop A B).
simpsub.
do2 2 split; auto.
  {
  apply interp_eval_refl.
  apply interp_sigma; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_sigma; auto.
  }
intros j m m' p p' Happroxm Happroxp Hmp.
destruct Hmp as (Hj & Hmp).
split; auto.
assert (j <= i) as Hj' by omega.
cbn in Hmp |- *.
decompose Hmp.
intros m1 p1 m2 p2 Hm1p1 Hclm Hclp Hstepsm Hstepsp Hm2p2.
so (sapprox_closed _#3 Happroxm) as (_ & Hclm').
so (sapprox_closed _#3 Happroxp) as (_ & Hclp').
so (sapprox_action _#4 Happroxm (conj Hstepsm value_ppair)) as (x & (Hstepsm' & _) & H).
invertc_mc H.
intros m1' Hm1 m2' Hm2.
fold (ppair m1' m2').
intros <-.
so (sapprox_action _#4 Happroxp (conj Hstepsp value_ppair)) as (x & (Hstepsp' & _) & H).
invertc_mc H.
intros p1' Hp1 p2' Hp2.
fold (ppair p1' p2').
intros <-.
exists m1', p1', m2', p2'.
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsm Hclm)) as H; cbn in H.
destruct H as (Hclm1 & Hclm2 & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsp Hclp)) as H; cbn in H.
destruct H as (Hclp1 & Hclp2 & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsm' Hclm')) as H; cbn in H.
destruct H as (Hclm1' & Hclm2' & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsp' Hclp')) as H; cbn in H.
destruct H as (Hclp1' & Hclp2' & _).
so (closed_ci _#4 Hclm1 Hclm1' Hm1) as H; renameover H into Hm1.
so (closed_ci _#4 Hclm2 Hclm2' Hm2) as H; renameover H into Hm2.
so (closed_ci _#4 Hclp1 Hclp1' Hp1) as H; renameover H into Hp1.
so (closed_ci _#4 Hclp2 Hclp2' Hp2) as H; renameover H into Hp2.
exploit (Hupwarda j m1 m1' p1 p1') as H; auto.
  {
  split; auto.
  }
destruct H as (_ & Hm1p1').
exists Hm1p1'.
do2 4 split; auto.
assert (pwctx j (dot m1' s) (dot p1' s') (cons (hyp_tm a) G)) as Hss.
  {
  apply pwctx_cons_tm_seq.
    {
    apply (pwctx_downward i); auto.
    }

    {
    apply (seqhyp_tm _#5 (iutruncate (S j) A)).
      {
      apply (basic_downward _#3 i); auto.
      }

      {
      apply (basic_downward _#3 i); auto.
      }

      {
      split; auto.
      }
    }

    {
    intros k u u' Hu.
    so (Hseqa _#3 Hu) as (R & H & H' & _).
    eauto.
    }
  }
so (Hseqb _#3 Hss) as (Bx & Hbxl & _ & Hupwardb).
invert Hbl.
intros _ _ Hactb.
so (Hactb _ _ _ Hj' Hm1p1') as Hbxl'.
simpsubin Hbxl'.
so (basic_fun _#7 Hbxl Hbxl'); subst Bx.
clear Hbxl Hbxl' Hactb.
eapply Hupwardb; eauto.
split; auto.
force_exact Hm2p2.
f_equal.
f_equal.
f_equal.
apply urelspinj_equal.
exploit (Hupwarda j m1 m1 p1 p1') as H; auto using sapprox_refl.
  {
  split; auto.
  }
destruct H; auto.
Qed.


Lemma sound_prod_admiss :
  forall G a b,
    pseq G (deq triv triv (admiss a))
    -> pseq G (deq triv triv (admiss b))
    -> pseq G (deq triv triv (admiss (prod a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqa Hseqb.
rewrite -> seq_admiss in Hseqa, Hseqb |- *.
intros i s s' Hs.
so (Hseqa _#3 Hs) as (A & Hal & Har & Hadmissa).
so (Hseqb _#3 Hs) as (B & Hbl & Hbr & Hadmissb).
so (f_equal den (basic_impl_iutruncate _#6 Hal)) as Heq.
rewrite -> den_iutruncate in Heq.
rewrite <- Heq in Hadmissa; clear Heq.
so (f_equal den (basic_impl_iutruncate _#6 Hbl)) as Heq.
rewrite -> den_iutruncate in Heq.
rewrite <- Heq in Hadmissb; clear Heq.
exists (iuprod stop A B).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl; apply interp_prod; auto.
  }

  {
  apply interp_eval_refl; apply interp_prod; auto.
  }
intros f g i' m p j Hclf Hclg Hclm Hclp Hmp.
so (Hmp _ (le_refl _)) as (Hj & Hmpj).
split; auto.
cbn in Hmpj.
decompose Hmpj.
intros x1 y1 x2 y2 _ _ Hsteps1 Hsteps2 _ _.
so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _ f j Hclf) Hclm) (conj Hsteps1 value_ppair)) as (w & (Hstepsm1 & _) & Hmc).
invertc_mc Hmc.
intros m1 _ m2 _.
fold (ppair m1 m2).
intros <-.
so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _ g j Hclg) Hclp) (conj Hsteps2 value_ppair)) as (w & (Hstepsp1 & _) & Hmc).
invertc_mc Hmc.
intros p1 _ p2 _.
fold (ppair p1 p2).
intros <-.
clear x1 y1 x2 y2 Hsteps1 Hsteps2.
exists m1, p1, m2, p2.
eassert _ as H; [refine (steps_hygiene _#4 Hstepsm1 _) |].
  {
  apply hygiene_subst1; prove_hygiene.
  }
so (hygiene_invert_auto _#5 H) as H'; cbn in H'; clear H.
destruct H' as (Hclm1 & Hclm2 & _).
eassert _ as H; [refine (steps_hygiene _#4 Hstepsp1 _) |].
  {
  apply hygiene_subst1; prove_hygiene.
  }
so (hygiene_invert_auto _#5 H) as H'; cbn in H'; clear H.
destruct H' as (Hclp1 & Hclp2 & _).
do2 5 split; auto.
  {
  apply hygiene_subst1; prove_hygiene.
  }

  {
  apply hygiene_subst1; prove_hygiene.
  }

  {
  apply (urel_equiv _#3 (subst1 (app theta f) (ppi1 m)) _ (subst1 (app theta g) (ppi1 p))); auto.
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
  apply (Hadmissa _#5 j); auto; try prove_hygiene.
  intros k Hk.
  simpsub.
  so (Hmp _ Hk) as (_ & H).
  cbn in H.
  eapply prod_action_ppi1; eauto.
  }

  {
  apply (urel_equiv _#3 (subst1 (app theta f) (ppi2 m)) _ (subst1 (app theta g) (ppi2 p))); auto.
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
  apply (Hadmissb _#5 j); auto; try prove_hygiene.
  intros k Hk.
  simpsub.
  so (Hmp _ Hk) as (_ & H).
  cbn in H.
  eapply prod_action_ppi2; eauto.
  }
Qed.


Lemma sound_sigma_uptype_admiss :
  forall G a b,
    pseq G (deq triv triv (uptype a))
    -> pseq (cons (hyp_tm a) G) (deq triv triv (admiss b))
    -> pseq G (deq triv triv (admiss (sigma a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 2 [] a [hyp_emp] b 2 [] _ [_] _ _ _); cbn.
intros G Hcla Hclb Hseqa Hseqb.
rewrite -> seq_uptype in Hseqa.
rewrite -> seq_admiss in Hseqb |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & Hupward).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr); eauto using subst_closub_under_permit.
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
      so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hss) as (R & Hbl & Hbr & _).
  exists R.
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
intros f g i' m p j Hclf Hclg Hclm Hclp Hmp.
so (Hmp _ (le_refl _)) as (Hj & Hmpj).
split; auto.
cbn in Hmpj.
decompose Hmpj.
intros x1 y1 x2 y2 _ _ _ Hsteps1 Hsteps2 _.
so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _ f j Hclf) Hclm) (conj Hsteps1 value_ppair)) as (w & (Hstepsm1 & _) & Hmc).
invertc_mc Hmc.
intros m1 _ m2 _.
fold (ppair m1 m2).
intros <-.
so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _ g j Hclg) Hclp) (conj Hsteps2 value_ppair)) as (w & (Hstepsp1 & _) & Hmc).
invertc_mc Hmc.
intros p1 _ p2 _.
fold (ppair p1 p2).
intros <-.
clear x1 y1 x2 y2 Hsteps1 Hsteps2.
exists m1, p1, m2, p2.
eassert _ as H; [refine (steps_hygiene _#4 Hstepsm1 _) |].
  {
  apply hygiene_subst1; prove_hygiene.
  }
so (hygiene_invert_auto _#5 H) as H'; cbn in H'; clear H.
destruct H' as (Hclm1 & Hclm2 & _).
eassert _ as H; [refine (steps_hygiene _#4 Hstepsp1 _) |].
  {
  apply hygiene_subst1; prove_hygiene.
  }
so (hygiene_invert_auto _#5 H) as H'; cbn in H'; clear H.
destruct H' as (Hclp1 & Hclp2 & _).
assert (rel (den A) i' m1 p1) as Hm1p1.
  {
  apply (urel_equiv _#3 (subst1 (app theta f) (ppi1 m)) _ (subst1 (app theta g) (ppi1 p))); auto.
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
  apply (upward_impl_admissible _ _ Hupward _#5 j); auto; try prove_hygiene.
  intros k Hk.
  split; auto.
  so (Hmp _ Hk) as (_ & H).
  cbn in H.
  decompose H.
  intros m1' p1' m2' p2' Hm1p1' _ _ Hstepsmk Hstepspk _.
  eapply urel_equiv; eauto.
    {
    apply hygiene_subst1; prove_hygiene.
    apply afix_closed; auto.
    }

    {
    apply hygiene_subst1; prove_hygiene.
    apply afix_closed; auto.
    }

    {
    simpsub.
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi1); eauto using step_ppi11.
      }
    apply star_one.
    apply step_ppi12.
    }

    {
    simpsub.
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi1); eauto using step_ppi11.
      }
    apply star_one.
    apply step_ppi12.
    }
  }
exists Hm1p1.
do2 4 split; auto.
  {
  apply hygiene_subst1; prove_hygiene.
  }

  {
  apply hygiene_subst1; prove_hygiene.
  }
apply (urel_equiv _#3 (subst1 (app theta f) (ppi2 m)) _ (subst1 (app theta g) (ppi2 p))); auto.
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
assert (i' <= i) as Hi' by omega.
assert (pwctx i' (dot m1 s) (dot p1 s') (cons (hyp_tm a) G)) as Hss.
  {
  apply pwctx_cons_tm_seq.
    {
    apply (pwctx_downward i); auto.
    }

    {
    apply (seqhyp_tm _#5 (iutruncate (S i') A)).
      {
      apply (basic_downward _#3 i); auto.
      }

      {
      apply (basic_downward _#3 i); auto.
      }

      {
      split; auto.
      }
    }

    {
    intros k u u' Hu.
    so (Hseqa _#3 Hu) as (R & H & H' & _).
    eauto.
    }
  }
so (Hseqb _#3 Hss) as (Bx & Hbxl & _ & Hadmiss).
invert Hbl.
intros _ _ Hactb.
so (Hactb _ _ _ Hi' Hm1p1) as Hbxl'.
simpsubin Hbxl'.
so (basic_fun _#7 Hbxl Hbxl'); subst Bx.
clear Hbxl' Hactb.
so (f_equal den (basic_impl_iutruncate _#6 Hbxl)) as Heq.
rewrite -> den_iutruncate in Heq.
rewrite <- Heq in Hadmiss; clear Heq Hbxl.
cbn [pi1 nearrow_compose den_ne].
apply (Hadmiss _#5 j); auto; try prove_hygiene.
intros k Hk.
so (Hmp _ Hk) as (_ & H).
cbn in H.
decompose H.
intros m1' p1' m2' p2' Hm1p1' _ _ Hstepsmk Hstepspk Hm2p2'.
so (urel_closed _#5 Hm1p1') as (Hm1' & Hp1').
apply (urel_equiv _#3 m2' _ p2').
  {
  apply hygiene_subst1; prove_hygiene; auto using afix_closed.
  }

  {
  apply hygiene_subst1; prove_hygiene; auto using afix_closed.
  }

  {
  simpsub.
  apply equiv_symm.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi2); eauto using step_ppi21.
    }
  apply star_one.
  apply step_ppi22.
  }

  {
  simpsub.
  apply equiv_symm.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi2); eauto using step_ppi21.
    }
  apply star_one.
  apply step_ppi22.
  }
(* The key trick is right here. *)
force_exact Hm2p2'.
f_equal.
f_equal.
f_equal.
apply urelspinj_equal.
rewrite <- HeqA in Hupward.
apply (Hupward _ m1' _ p1'); auto using sapprox_refl.
apply (sapprox_trans _ _ (subst1 (afix k g) (ppi1 p))).
  {
  apply anti_steps_sapprox; auto.
    {
    apply hygiene_subst1; prove_hygiene; auto using afix_closed.
    }
  simpsub.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi1); eauto using step_ppi11.
    }
  apply star_one.
  apply step_ppi12.
  }
apply (sapprox_trans _ _ (subst1 (app theta g) (ppi1 p))).
2:{
  apply steps_sapprox; auto.
    {
    apply hygiene_subst1; prove_hygiene; auto using afix_closed.
    }
  simpsub.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi1); eauto using step_ppi11.
    }
  apply star_one.
  apply step_ppi12.
  }
apply sapprox_funct1.
  {
  intros T h.
  simpmap.
  apply afix_fix_approx.
  apply map_hygiene; auto.
  }

  {
  prove_hygiene.
  }
Qed.


Lemma sound_fut_total :
  forall G a m,
    pseq G (deq m m (fut a))
    -> pseq G (deq triv triv (halts m)).
Proof.
intros G a m Hseq.
eapply sound_total_stuff; eauto.
intros i s R n q Hl Hnq.
simpsubin Hl.
invert (basic_value_inv _#6 value_fut Hl).
  {
  intros _ <- <-.
  cbn in Hnq.
  decompose Hnq.
  intros n' q' _ _ _ Hsteps Hsteps' _.
  split.
    {
    exists (next n').
    split; auto using value_next.
    }

    {
    exists (next q').
    split; auto using value_next.
    }
  }

  {
  intros i' A _ <- <-.
  cbn in Hnq.
  decompose Hnq.
  intros n' q' _ _ _ Hsteps Hsteps' _.
  split.
    {
    exists (next n').
    split; auto using value_next.
    }

    {
    exists (next q').
    split; auto using value_next.
    }
  }
Qed.


Lemma sound_fut_uptype :
  forall G a,
    pseq (promote G) (deq triv triv (uptype a))
    -> pseq G (deq triv triv (uptype (fut a))).
Proof.
intros G a.
revert G.
refine (seq_pseq_promote 1 [] a 1 true [] _ _ _); cbn.
intros G Hcla Hseq.
rewrite -> seq_uptype in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
destruct i as [| i].
  {
  exists (iufut0 stop).
  simpsub.
  do2 2 split.
    {
    apply interp_eval_refl; apply interp_fut_zero; eapply subst_closub; eauto.
    }

    {
    apply interp_eval_refl; apply interp_fut_zero; eapply subst_closub; eauto.
    }

    {
    intros i m m' p p' Happroxm Happroxp Hmp.
    destruct Hmp as (Hi & Hmp).
    split; auto.
    cbn in Hmp.
    decompose Hmp.
    intros n q _ Hcln Hclq Hstepsm Hstepsp _.
    so (sapprox_closed _#3 Happroxm) as (Hclm & Hclm').
    so (sapprox_closed _#3 Happroxp) as (Hclp & Hclp').
    so (sapprox_action _#4 Happroxm (conj Hstepsm value_next)) as (x & (Hstepsm' & _) & H).
    invertc_mc H.
    intros n' Hn.
    fold (next n').
    intros <-.
    so (sapprox_action _#4 Happroxp (conj Hstepsp value_next)) as (x & (Hstepsp' & _) & H).
    invertc_mc H.
    intros q' Hq.
    fold (next q').
    intros <-.
    exists n', q'.
    do2 5 split; auto; omega.
    }
  }

  {
  so (pwctx_promote _#4 Hs) as Hs'.
  so (Hseq _#3 Hs') as (A & Hal & Har & Hupward).
  exists (iufut stop (S i) A).
  simpsub.
  do2 2 split.
    {
    apply interp_eval_refl; apply interp_fut; auto.
    }
  
    {
    apply interp_eval_refl; apply interp_fut; auto.
    }
  
    {
    intros j m m' p p' Happroxm Happroxp Hmp.
    destruct Hmp as (Hj & Hmp).
    split; auto.
    cbn in Hmp.
    decompose Hmp.
    intros n q Hj' _ _ Hstepsm Hstepsp Hact.
    so (sapprox_closed _#3 Happroxm) as (Hclm & Hclm').
    so (sapprox_closed _#3 Happroxp) as (Hclp & Hclp').
    so (sapprox_action _#4 Happroxm (conj Hstepsm value_next)) as (x & (Hstepsm' & _) & H).
    invertc_mc H.
    intros n' Hn.
    fold (next n').
    intros <-.
    so (sapprox_action _#4 Happroxp (conj Hstepsp value_next)) as (x & (Hstepsp' & _) & H).
    invertc_mc H.
    intros q' Hq.
    fold (next q').
    intros <-.
    so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsm Hclm)) as H; cbn in H.
    destruct H as (Hcln & _).
    so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsp Hclp)) as H; cbn in H.
    destruct H as (Hclq & _).
    so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsm' Hclm')) as H; cbn in H.
    destruct H as (Hcln' & _).
    so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsp' Hclp')) as H; cbn in H.
    destruct H as (Hclq' & _).
    exists n', q'.
    do2 5 split; auto.
    intros Hpos.
    so (closed_ci _#4 Hcln Hcln' Hn) as Happroxn.
    so (closed_ci _#4 Hclq Hclq' Hq) as Happroxq.
    eapply Hupward; eauto.
    split; auto.
    omega.
    }
  }
Qed.


Lemma sound_fut_admiss :
  forall G a,
    pseq (promote G) (deq triv triv (admiss a))
    -> pseq G (deq triv triv (admiss (fut a))).
Proof.
intros G a.
revert G.
refine (seq_pseq_promote 1 [] a 1 true [] _ _ _); cbn.
intros G Hcla Hseq.
rewrite -> seq_admiss in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
destruct i as [| i].
  {
  exists (iufut0 stop).
  simpsub.
  do2 2 split.
    {
    apply interp_eval_refl; apply interp_fut_zero; eapply subst_closub; eauto.
    }

    {
    apply interp_eval_refl; apply interp_fut_zero; eapply subst_closub; eauto.
    }

    {
    intros f g i m p j Hclf Hclg Hclm Hclp Hmpall.
    destruct (Hmpall _ (le_refl _)) as (Hi & Hmpj).
    split; auto.
    cbn in Hmpj |- *.
    decompose Hmpj.
    intros n q _ _ _ Hstepsm Hstepsp _.
    so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _#3 Hclf) Hclm) (conj Hstepsm value_next)) as (x & (Hstepsm' & _) & H).
    invertc_mc H.
    intros n' Hn.
    fold (next n').
    intros <-.
    so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _#3 Hclg) Hclp) (conj Hstepsp value_next)) as (y & (Hstepsp' & _) & H).
    invertc_mc H.
    intros q' Hq.
    fold (next q').
    intros <-.
    exists n', q'.
    do2 5 split; auto.
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
      omega.
      }
    }
  }

  {
  so (pwctx_promote _#4 Hs) as Hs'.
  so (Hseq _#3 Hs') as (A & Hal & Har & Hadmiss).
  exists (iufut stop (S i) A).
  simpsub.
  do2 2 split.
    {
    apply interp_eval_refl; apply interp_fut; auto.
    }
  
    {
    apply interp_eval_refl; apply interp_fut; auto.
    }
  
    {
    intros f g i' m p j Hclf Hclg Hclm Hclp Hmpall.
    destruct (Hmpall _ (le_refl _)) as (Hi' & Hmpj).
    split; auto.
    cbn in Hmpj |- *.
    decompose Hmpj.
    intros n q _ _ _ Hstepsm Hstepsp _.
    so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _#3 Hclf) Hclm) (conj Hstepsm value_next)) as (x & (Hstepsm' & _) & H).
    invertc_mc H.
    intros n' Hn.
    fold (next n').
    intros <-.
    so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _#3 Hclg) Hclp) (conj Hstepsp value_next)) as (y & (Hstepsp' & _) & H).
    invertc_mc H.
    intros q' Hq.
    fold (next q').
    intros <-.
    eassert _ as H; [refine (steps_hygiene _#4 Hstepsm _) |].
      {
      apply hygiene_subst1; prove_hygiene.
      apply afix_closed; auto.
      }
    so (hygiene_invert_auto _#5 H) as H'; cbn in H'; clear H.
    destruct H' as (Hcln & _).
    eassert _ as H; [refine (steps_hygiene _#4 Hstepsp _) |].
      {
      apply hygiene_subst1; prove_hygiene.
      apply afix_closed; auto.
      }
    so (hygiene_invert_auto _#5 H) as H'; cbn in H'; clear H.
    destruct H' as (Hclq & _).
    eassert _ as H; [refine (steps_hygiene _#4 Hstepsm' _) |].
      {
      apply hygiene_subst1; prove_hygiene.
      }
    so (hygiene_invert_auto _#5 H) as H'; cbn in H'; clear H.
    destruct H' as (Hcln' & _).
    eassert _ as H; [refine (steps_hygiene _#4 Hstepsp' _) |].
      {
      apply hygiene_subst1; prove_hygiene.
      }
    so (hygiene_invert_auto _#5 H) as H'; cbn in H'; clear H.
    destruct H' as (Hclq' & _).
    exists n', q'.
    do2 5 split; auto.
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
      intros Hi''.
      apply (urel_equiv _#3 (subst1 (app theta f) (prev m)) _ (subst1 (app theta g) (prev p))); auto.
        {
        simpsub.
        apply steps_equiv.
        eapply star_trans.
          {
          apply (star_map' _ _ prev); eauto using step_prev1.
          }
        apply star_one.
        apply step_prev2.
        }

        {
        simpsub.
        apply steps_equiv.
        eapply star_trans.
          {
          apply (star_map' _ _ prev); eauto using step_prev1.
          }
        apply star_one.
        apply step_prev2.
        }
      apply (Hadmiss _#5 j); auto; try prove_hygiene.
      intros k Hk.
      split; [omega |].
      so (Hmpall _ Hk) as (_ & Hmpk).
      cbn in Hmpk.
      simpsub.
      decompose Hmpk.
      intros n'' q'' _ _ _ Hstepsmk Hstepspk Hact.
      exploit Hact as Hnq; [omega |].
      refine (urel_equiv _#7 _ _ _ _ Hnq).
        {
        prove_hygiene.
        apply hygiene_subst1; auto.
        apply afix_closed; auto.
        }

        {
        prove_hygiene.
        apply hygiene_subst1; auto.
        apply afix_closed; auto.
        }
      
        {
        apply equiv_symm.
        apply steps_equiv.
        eapply star_trans.
          {
          apply (star_map' _ _ prev); eauto using step_prev1.
          }
        apply star_one.
        apply step_prev2.
        }

        {
        apply equiv_symm.
        apply steps_equiv.
        eapply star_trans.
          {
          apply (star_map' _ _ prev); eauto using step_prev1.
          }
        apply star_one.
        apply step_prev2.
        }
      }
    }
  }
Qed.


Lemma sound_set_strict :
  forall G a b,
    pseq (hyp_tm a :: G) (deqtype b b)
    -> pseq G (dsubtype a (partial a))
    -> pseq G (dsubtype (set a b) (partial (set a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 1 [hyp_emp] b 2 [_] _ [] _ _ _); cbn.
intros G Hclb Hseqb Hseqa.
rewrite -> seq_eqtype in Hseqb.
rewrite -> seq_subtype in Hseqa |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & R & Hal & Har & Hpl & _ & Hincl).
simpsubin Hpl.
invert (basic_value_inv _#6 value_partial Hpl).
intros A' Hal' <-.
so (interp_fun _#7 Hal Hal').
subst A'.
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr); eauto using subst_closub_under_permit.
  {
  intros j m p Hmp.
  assert (j <= i) as Hj.
    {
    rewrite -> HeqA in Hmp.
    destruct Hmp.
    omega.
    }
  assert (pwctx j (dot m s) (dot p s') (hyp_tm a :: G)) as Hss.
    {
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      apply (seqhyp_tm _#5 (iutruncate (S j) A)); auto.
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
      so (Hseqa _#3 Ht) as (A' & _ & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hss) as (B & Hbl & Hbr & _).
  exists B.
  simpsub.
  auto.
  }
exists (iuset stop A B), (iupartial stop i (iuset stop A B)).
simpsub.
do2 4 split.
  {
  apply interp_eval_refl; apply interp_set; auto.
  }

  {
  apply interp_eval_refl; apply interp_set; auto.
  }

  {
  apply interp_eval_refl; apply interp_partial.
  apply interp_eval_refl; apply interp_set; auto.
  }

  {
  apply interp_eval_refl; apply interp_partial.
  apply interp_eval_refl; apply interp_set; auto.
  }

  {
  intros j m p Hj Hmpset.
  so (urel_closed _#5 Hmpset) as (Hclm & Hclp).
  cbn in Hmpset.
  so Hmpset as (r & t & Hmp & Hrt).
  do2 4 split; auto.
    {
    destruct (Hincl _#3 Hj Hmp) as (_ & _ & _ & Hiff & _).
    exact Hiff.
    }
  }
Qed.


Lemma sound_set_uptype :
  forall G a b,
    pseq G (deq triv triv (uptype a))
    -> pseq (hyp_tm a :: G) (deqtype b b)
    -> pseq G (deq triv triv (uptype (set a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 1 [hyp_emp] b 2 [] _ [_] _ _ _); cbn.
intros G Hclb Hseqa Hseqb.
rewrite -> seq_uptype in Hseqa |- *.
rewrite -> seq_eqtype in Hseqb.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & HupwardA).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
rewrite <- HeqA in HupwardA.
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr); eauto using subst_closub_under_permit.
  {
  intros j m p Hmp.
  assert (j <= i) as Hj.
    {
    rewrite -> HeqA in Hmp.
    destruct Hmp.
    omega.
    }
  assert (pwctx j (dot m s) (dot p s') (hyp_tm a :: G)) as Hss.
    {
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      apply (seqhyp_tm _#5 (iutruncate (S j) A)); auto.
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
      so (Hseqa _#3 Ht) as (A' & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hss) as (B & Hbl & Hbr & _).
  exists B.
  simpsub.
  auto.
  }
exists (iuset stop A B).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl; apply interp_set; auto.
  }

  {
  apply interp_eval_refl; apply interp_set; auto.
  }

  {
  intros j m m' p p' Happroxm Happroxp Hmp.
  so (urel_closed _#5 Hmp) as (Hclm & _).
  destruct Hmp as (Hj & Hmp).
  split; auto.
  destruct Hmp as (r & t & Hmp & Hrt).
  so (HupwardA _#5 Happroxm Happroxp Hmp) as Hmp'.
  exists r, t, Hmp'.
  force_exact Hrt.
  f_equal.
  f_equal.
  apply urelspinj_equal.
  apply (HupwardA _ m _ p); auto.
  apply sapprox_refl; auto.
  }
Qed.


Lemma sound_iset_strict :
  forall G a b,
    pseq (hyp_tm a :: G) (deqtype b b)
    -> pseq G (dsubtype a (partial a))
    -> pseq G (dsubtype (iset a b) (partial (iset a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 1 [hyp_emp] b 2 [_] _ [] _ _ _); cbn.
intros G Hclb Hseqb Hseqa.
rewrite -> seq_eqtype in Hseqb.
rewrite -> seq_subtype in Hseqa |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & R & Hal & Har & Hpl & _ & Hincl).
simpsubin Hpl.
invert (basic_value_inv _#6 value_partial Hpl).
intros A' Hal' <-.
so (interp_fun _#7 Hal Hal').
subst A'.
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr); eauto using subst_closub_under_permit.
  {
  intros j m p Hmp.
  assert (j <= i) as Hj.
    {
    rewrite -> HeqA in Hmp.
    destruct Hmp.
    omega.
    }
  assert (pwctx j (dot m s) (dot p s') (hyp_tm a :: G)) as Hss.
    {
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      apply (seqhyp_tm _#5 (iutruncate (S j) A)); auto.
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
      so (Hseqa _#3 Ht) as (A' & _ & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hss) as (B & Hbl & Hbr & _).
  exists B.
  simpsub.
  auto.
  }
exists (iuiset stop A B), (iupartial stop i (iuiset stop A B)).
simpsub.
do2 4 split.
  {
  apply interp_eval_refl; apply interp_iset; auto.
  }

  {
  apply interp_eval_refl; apply interp_iset; auto.
  }

  {
  apply interp_eval_refl; apply interp_partial.
  apply interp_eval_refl; apply interp_iset; auto.
  }

  {
  apply interp_eval_refl; apply interp_partial.
  apply interp_eval_refl; apply interp_iset; auto.
  }

  {
  intros j m p Hj Hmpset.
  so (urel_closed _#5 Hmpset) as (Hclm & Hclp).
  cbn in Hmpset.
  so Hmpset as (r & t & Hmp & Hrt).
  do2 4 split; auto.
    {
    destruct (Hincl _#3 Hj Hmp) as (_ & _ & _ & Hiff & _).
    exact Hiff.
    }
  }
Qed.


Lemma sound_iset_uptype :
  forall G a b,
    pseq G (deq triv triv (uptype a))
    -> pseq (hyp_tm a :: G) (deqtype b b)
    -> pseq G (deq triv triv (uptype (iset a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 1 [hyp_emp] b 2 [] _ [_] _ _ _); cbn.
intros G Hclb Hseqa Hseqb.
rewrite -> seq_uptype in Hseqa |- *.
rewrite -> seq_eqtype in Hseqb.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & HupwardA).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
rewrite <- HeqA in HupwardA.
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr); eauto using subst_closub_under_permit.
  {
  intros j m p Hmp.
  assert (j <= i) as Hj.
    {
    rewrite -> HeqA in Hmp.
    destruct Hmp.
    omega.
    }
  assert (pwctx j (dot m s) (dot p s') (hyp_tm a :: G)) as Hss.
    {
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      apply (seqhyp_tm _#5 (iutruncate (S j) A)); auto.
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
      so (Hseqa _#3 Ht) as (A' & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hss) as (B & Hbl & Hbr & _).
  exists B.
  simpsub.
  auto.
  }
exists (iuiset stop A B).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl; apply interp_iset; auto.
  }

  {
  apply interp_eval_refl; apply interp_iset; auto.
  }

  {
  intros j m m' p p' Happroxm Happroxp Hmp.
  so (urel_closed _#5 Hmp) as (Hclm & _).
  destruct Hmp as (Hj & Hmp).
  split; auto.
  destruct Hmp as (r & t & Hmp & Hrt).
  so (HupwardA _#5 Happroxm Happroxp Hmp) as Hmp'.
  exists r, t, Hmp'.
  force_exact Hrt.
  f_equal.
  f_equal.
  apply urelspinj_equal.
  apply (HupwardA _ m _ p); auto.
  apply sapprox_refl; auto.
  }
Qed.


Lemma sound_type_halt :
  forall G a,
    pseq G (deqtype a a)
    -> pseq G (deq triv triv (halts a)).
Proof.
intros G a.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseqa.
rewrite -> seq_eqtype in Hseqa.
rewrite -> seq_halts.
intros i s s' Hs.
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
invert Hal.
intros v Hcl Hstepsl Hintl.
invert Har.
intros w Hcl' Hstepsr Hintr.
do2 3 split; auto.
  {
  exists v.
  split; auto.
  eapply basicv_value; eauto.
  }

  {
  exists w.
  split; auto.
  eapply basicv_value; eauto.
  }
Qed.
