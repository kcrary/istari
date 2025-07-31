
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
Require Import SemanticsEqual.

Local Ltac prove_hygiene :=
  repeat (apply hygiene_auto; cbn; repeat2 split; auto);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1, subst_closub, afix_closed;
  try (eapply subst_closub_under_permit; eauto; done);
  try (apply hygiene_var; cbn; auto; done).


Lemma subst_afix :
  forall object s k (m : term object),
    subst s (afix k m) = afix k (subst s m).
Proof.
intros object s k m.
induct k; auto.
intros n IH.
cbn [afix].
simpsub.
f_equal.
auto.
Qed.


Hint Rewrite subst_afix : subst.


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


Lemma sound_pi_padmiss_domain_closed :
  forall G a b c,
    pseq G (deqtype a a)
    -> pseq G (deqtype b b)
    -> pseq (hyp_tm b :: G) (deq triv triv (padmiss (subst sh1 a) (subst (dot (var 1) (dot (var 0) (sh 2))) c)))
    -> pseq G (deq triv triv (padmiss a (pi (subst sh1 b) c))).
Proof.
intros G a b c.
revert G.
refine (seq_pseq 2 [] b [hyp_emp; hyp_emp] c 3 [] _ [] _ [_] _ _ _); cbn.
intros G Hclb Hclc Hseqa Hseqb Hseq.
rewrite -> seq_padmiss in Hseq |- *.
rewrite -> seq_eqtype in Hseqa, Hseqb.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
so (Hseqb _#3 Hs) as (B & Hbl & Hbr & _).
so (f_equal den (basic_impl_iutruncate _#6 Hal)) as HeqA.
so (f_equal den (basic_impl_iutruncate _#6 Hbl)) as HeqB.
assert (forall j n q,
          rel (den B) j n q
          -> pwctx j (dot n s) (dot q s') (cons (hyp_tm b) G)) as Hss.
  {
  intros j n q Hnq.
  assert (j <= i) as Hj.
    {
    rewrite -> HeqB in Hnq.
    destruct Hnq.
    omega.
    }
  apply pwctx_cons_tm_seq; eauto using pwctx_downward.
    {
    eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
    }

    {
    intros j' t t' Ht.
    so (Hseqb _#3 Ht) as (R & Hl & Hr & _).
    eauto.
    }
  }
clear Hseqa Hseqb.
exploit (extract_functional toppg i (den A) (subst (under 1 s) (pi (subst sh1 b) c)) (subst (under 1 s') (pi (subst sh1 b) c))) as H; auto.
  {
  eapply subst_closub_under_permit; eauto.
  prove_hygiene.
  }
  
  {
  eapply subst_closub_under_permit; eauto.
  prove_hygiene.
  }

  {
  intros j m p Hmp.
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  so Hmp as H.
  rewrite -> HeqA in H.
  destruct H as (Hj_lt & _).
  assert (j <= i) as Hj by omega.
  exploit (extract_functional toppg j (ceiling (S j) (den B)) (subst (dot (var 0) (dot (subst sh1 m) (compose s sh1))) c) (subst (dot (var 0) (dot (subst sh1 p) (compose s' sh1))) c)) as H; auto.
    {
    rewrite -> ceiling_idem.
    reflexivity.
    }

    {
    eapply hygiene_subst; eauto.
    intros l Hl.
    destruct l as [|[| l]]; simpsub.
      {
      apply hygiene_var;
      auto.
      }

      {
      apply hygiene_shift_permit; auto.
      }
    
      {
      cbn in Hl.
      apply hygiene_shift_permit.
      eapply project_closub; eauto.
      }
    }

    {
    eapply hygiene_subst; eauto.
    intros l Hl.
    destruct l as [|[| l]]; simpsub.
      {
      apply hygiene_var;
      auto.
      }

      {
      apply hygiene_shift_permit; auto.
      }
    
      {
      cbn in Hl.
      apply hygiene_shift_permit.
      eapply project_closub; eauto.
      }
    }

    {
    intros k n q Hnq.
    destruct Hnq as (Hk_lt & Hnq).
    assert (k <= j) as Hk by omega.
    so (le_trans _#3 Hk Hj) as Hki.
    so (Hseq _#3 (Hss _#3 Hnq)) as (A' & C & Hal' & _ & Hcl & Hcr & Hadmiss).
    simpsubin Hal'.
    so (interp_fun _#7 (basic_downward _#7 Hki Hal) Hal').
    subst A'.
    simpsubin Hcl.
    simpsubin Hcr.
    assert (k < S k) as Hkk_lt by omega.
    so (urel_downward_leq _#6 Hk Hmp) as Hmpk.
    exists (pi1 C (urelspinj (den (iutruncate (S k) A)) _ _ _ (conj Hkk_lt Hmpk))).
    split.
      {
      invert Hcl.
      intros _ _ Hact.
      so (Hact k _ _ (le_refl _) (conj Hkk_lt Hmpk)) as H.
      simpsubin H.
      simpsub.
      exact H.
      }

      {
      invert Hcr.
      intros _ _ Hact.
      so (Hact k _ _ (le_refl _) (conj Hkk_lt Hmpk)) as H.
      simpsubin H.
      simpsub.
      exact H.
      }
    }
  destruct H as (C & Hcl & Hcr).
  exists (iupi stop j (iutruncate (S j) B) C).
  assert (j < S j) as Hjj_lt by omega.
  split.
    {
    simpsub.
    apply interp_eval_refl.
    apply interp_pi; auto.
    eapply basic_downward; eauto.
    }

    {
    simpsub.
    apply interp_eval_refl.
    apply interp_pi; auto.
    eapply basic_downward; eauto.
    }
  }
destruct H as (BC & Hbcl & Hbcr).
exists A, BC.
do2 4 split; auto.
intros f g i' m p d e j Hde Hclf Hclg Hclm Hclp Hcld Hcle Hadmact.
cbn.
destruct Hde as (Hi'_lt & Hde).
assert (i' <= i) as Hi' by omega.
split; auto.
rewrite -> embed_ceiling_urelspinj.
invert Hbcl.
intros _ _ Hbclact.
so (Hbclact _#3 Hi' Hde) as Hbclde.
simpsubin Hbclde.
invert (basic_value_inv _#6 value_pi Hbclde).
intros B' C Hbl' Hcl Heq.
so (interp_fun _#7 (basic_downward _#7 Hi' Hbl) Hbl').
subst B'.
clear Hbl'.
eassert (rel (den (iupi stop i' (iutruncate (S i') B) C)) _ _ _) as H.
2:{
  force_exact H.
  f_equal.
  f_equal.
  exact Heq.
  }
assert (exists l l', star step (subst1 (app theta f) m) (lam l) /\ star step (subst1 (app theta g) p) (lam l')) as (l & l' & Hstepsl & Hstepsl').
  {
  so (Hadmact _ (le_refl _)) as (Hdej & Hmpj).
  destruct Hdej as (Hi'_lt_alt & Hdej).
  so (proof_irrelevance _ Hi'_lt Hi'_lt_alt).
  subst Hi'_lt_alt.
  cbn in Hmpj.
  destruct Hmpj as (_ & Hmpj).
  rewrite -> embed_ceiling_urelspinj in Hmpj.
  so (Hbclact _#3 Hi' Hdej) as Hbcldej.
  simpsubin Hbcldej.
  rewrite -> (subst_into_closed _ _ f) in Hbcldej; auto.
  invert (basic_value_inv _#6 value_pi Hbcldej).
  intros B' C' Hbl' Hclj Heqj.
  eassert (rel (den (iupi stop i' B' C')) _ _ _) as H.
    {
    force_exact Hmpj.
    f_equal.
    f_equal.
    symmetry.
    exact Heqj.
    }
  renameover H into Hmpj.
  cbn in Hmpj.
  decompose Hmpj.
  intros lj lj' _ _ _ Hsteps Hsteps' _.
  so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _ f j Hclf) Hclm) (conj Hsteps value_lam)) as (w & (Hstepsm & _) & Hmc).
  invertc_mc Hmc.
  intros l _ <-.
  fold (lam l) in Hstepsm.
  so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _ g j Hclg) Hclp) (conj Hsteps' value_lam)) as (w & (Hstepsp & _) & Hmc).
  invertc_mc Hmc.
  intros l' _ <-.
  fold (lam l) in Hstepsm.
  fold (lam l') in Hstepsp.
  exists l, l'.
  auto.
  }
cbn.
exploit (steps_hygiene _ clo (subst1 (app theta f) m) (lam l)) as H; auto.
  {
  apply hygiene_subst1; auto.
  prove_hygiene.
  }
so (hygiene_invert_auto _#5 H) as H'; cbn in H'.
destruct H' as (Hcll & _).
clear H.
exploit (steps_hygiene _ clo (subst1 (app theta g) p) (lam l')) as H; auto.
  {
  apply hygiene_subst1; auto.
  prove_hygiene.
  }
so (hygiene_invert_auto _#5 H) as H'; cbn in H'.
destruct H' as (Hcll' & _).
clear H.
exists l, l'.
do2 5 split; auto.
  {
  apply hygiene_subst1; auto.
  apply hygiene_auto; cbn; auto using theta_closed.
  }

  {
  apply hygiene_subst1; auto.
  apply hygiene_auto; cbn; auto using theta_closed.
  }
intros i'' n q Hi'' Hnq.
destruct Hnq as (Hi''_lt & Hnq).
so (urel_closed _#5 Hnq) as (Hcln & Hclq).
so (Hseq _#3 (Hss i'' n q Hnq)) as (A' & Cn & Hal' & _ & Hcnl & _ & Hadmiss).
simpsubin Hal'.
assert (i'' <= i) as Hii by omega.
so (interp_fun _#7 (basic_downward _#7 Hii Hal) Hal').
subst A'.
simpsubin Hcnl.
assert (i'' < S i'') as Hirefl_lt by omega.
so (urel_downward_leq _#6 Hi'' Hde) as Hde'.
exploit (Hadmiss f g i'' (app m (subst sh1 n)) (app p (subst sh1 q)) d e j (conj Hirefl_lt (conj Hirefl_lt Hde'))) as H; auto; try prove_hygiene.
  {
  intros k Hk.
  so (Hadmact k Hk) as (Hdek & Hmpk).
  destruct Hdek as (Hi'_lt_alt & Hdek).
  so (proof_irrelevance _ Hi'_lt Hi'_lt_alt).
  subst Hi'_lt_alt.
  cbn in Hmpk.
  destruct Hmpk as (_ & Hmpk).
  rewrite -> embed_ceiling_urelspinj in Hmpk.
  so (urel_downward_leq _#6 Hi'' Hdek) as Hdek'.
  exists (conj Hirefl_lt (conj Hirefl_lt Hdek')).
  simpsub.
  cbn.
  split; auto.
  rewrite -> embed_ceiling_urelspinj.
  so (Hbclact _#3 Hi' Hdek) as Hbcldek.
  simpsubin Hbcldek.
  rewrite -> (subst_into_closed _ _ f) in Hbcldek; auto.
  invert (basic_value_inv _#6 value_pi Hbcldek).
  intros B' C' Hbl' Hclk Heqk.
  so (interp_fun _#7 (basic_downward _#7 Hi' Hbl) Hbl').
  subst B'.
  clear Hbl'.
  invertc Hclk.
  intros _ _ Hactk.
  so (Hactk _ _ _ Hi'' (conj Hi''_lt Hnq)).
  simpsubin H.
  unfold subst1 in H.
  rewrite -> (subst_into_closed _ _ f) in H; auto.
  invert Hcnl.
  intros _ _ Hactk'.
  so (Hactk' _ _ _ (le_refl _) (conj Hirefl_lt Hdek')) as H'.
  simpsubin H'.
  so (interp_fun _#7 H H') as HeqCdn.
  clear H H'.
  eassert (rel (den (pi1 C' (urelspinj (den (iutruncate (S i') B)) i'' n q (conj Hi''_lt Hnq)))) _ _ _) as H.
  2:{
    force_exact H.
    f_equal.
    f_equal.
    exact HeqCdn.
    }
  clear Hactk Hactk' HeqCdn.
  eassert (rel (den (iupi stop i' (iutruncate (S i') B) C')) _ _ _) as H.
    {
    force_exact Hmpk.
    f_equal.
    f_equal.
    symmetry.
    exact Heqk.
    }
  renameover H into Hmpk.
  cbn in Hmpk.
  decompose Hmpk.
  intros x y _ _ _ Hstepsx Hstepsy Hact.
  so (Hact _ _ _ Hi'' (conj Hi''_lt Hnq)) as H.
  cbn.
  refine (urel_equiv _#7 _ _ _ _ H); clear H; try prove_hygiene.
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun Z => app Z n)); eauto using step_app1.
      }
    apply star_one.
    apply step_app2.
    }
  
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun Z => app Z q)); eauto using step_app1.
      }
    apply star_one.
    apply step_app2.
    }
  }
simpsubin H.
cbn in H.
destruct H as (_ & Hrel).
rewrite -> embed_ceiling_urelspinj in Hrel.
so (functional_downward _#8 Hi'' Hcl) as Hcl'.
cbn in Hcl'.
invertc Hcl'.
intros _ _ Hact.
so (Hact _ _ _ (le_refl _) (conj Hirefl_lt (conj Hi''_lt Hnq))) as H1.
simpsubin H1.
invertc Hcnl.
intros _ _ Hact'.
so (Hact' _ _ _ (le_refl _) (conj Hirefl_lt Hde')) as H2.
simpsubin H2.
so (interp_fun _#7 H1 H2) as Heqf.
cbn in Heqf.
rewrite -> embed_ceiling_urelspinj in Heqf.
eassert (rel (den (iutruncate (S i'') (pi1 C (urelspinj (ceiling (S i') (fst B)) i'' n q (conj Hi''_lt Hnq))))) _ _ _) as H.
  {
  force_exact Hrel.
  f_equal.
  f_equal.
  symmetry.
  exact Heqf.
  }
renameover H into Hrel.
destruct Hrel as (_ & Hrel).
refine (urel_equiv _#7 _ _ _ _ Hrel); try prove_hygiene.
  {
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ (fun Z => app Z n)); eauto using step_app1.
    }
  apply star_one.
  apply step_app2.
  }

  {
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ (fun Z => app Z q)); eauto using step_app1.
    }
  apply star_one.
  apply step_app2.
  }
Qed.


Lemma sound_tarrow_padmiss_domain_halts :
  forall G a m b c,
    pseq G (deq triv triv (padmiss a c))
    -> pseq (hyp_tm a :: G) (deq m m (partial b))
    -> pseq G (deq triv triv (padmiss a (tarrow (halts m) c))).
Proof.
intros G a r b c.
revert G.
refine (seq_pseq 2 [hyp_emp] c [hyp_emp] r 2 [] _ [_] _ _ _); cbn.
intros G Hclc Hclr Hseqac Hseqm.
rewrite -> seq_padmiss in Hseqac |- *.
rewrite -> seq_deq in Hseqm.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqac _#3 Hs) as (A & C & Hal & Har & Hcl & Hcr & Hadmiss).
so (f_equal den (basic_impl_iutruncate _#6 Hal)) as HeqA.
assert (forall j m p,
          rel (den A) j m p
          -> pwctx j (dot m s) (dot p s') (cons (hyp_tm a) G)) as Hss.
  {
  intros j n q Hnq.
  assert (j <= i) as Hj.
    {
    rewrite -> HeqA in Hnq.
    destruct Hnq.
    omega.
    }
  apply pwctx_cons_tm_seq; eauto using pwctx_downward.
    {
    eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
    }

    {
    intros j' t t' Ht.
    so (Hseqac _#3 Ht) as (R & _ & Hl & Hr & _).
    eauto.
    }
  }
(* Adapt for other proofs *)
exploit (extract_functional toppg i (den A) (halts (subst (under 1 s) r)) (halts (subst (under 1 s') r))) as (R & Hrl & Hrr); auto; try prove_hygiene.
  {
  intros j m p Hmp.
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  exists (iubase (halts_urel stop j (subst (dot m s) r))).
  split.
    {
    simpsub.
    apply interp_eval_refl.
    apply interp_halts.
    eapply hygiene_subst; eauto.
    intros z Hz.
    destruct z as [| z]; simpsub; auto.
    }

    {
    replace (halts_urel stop j (subst (dot m s) r)) with (halts_urel stop j (subst (dot p s') r)).
      {
      simpsub.
      apply interp_eval_refl.
      apply interp_halts.
      eapply hygiene_subst; eauto.
      intros z Hz.
      destruct z as [| z]; simpsub; auto.
      }
    so (Hseqm _ _ _ (Hss _ _ _ Hmp)) as (BB & Hbl & _ & Hr & _).
    simpsubin Hbl.
    invert (basic_value_inv _#6 value_partial Hbl).
    intros B _ <-.
    cbn in Hr.
    decompose Hr.
    intros _ _ _ Hiff _.
    apply property_urel_extensionality; auto.
    intros k Hk.
    symmetry.
    auto.
    }
  }
exists A.
assert (@nonexpansive (urelsp (den A)) siurel_ofe (fun X => iuarrow stop (urelsp_index _ X) (pi1 R X) (pi1 C X))) as Hne.
  {
  intros j X Y HXY.
  destruct j as [| j].
    {
    apply dist_zero.
    }
  so (urelsp_eta _ _ X) as (k & m & p & Hmp & ->).
  so (urelsp_eta _ _ Y) as (k' & n & q & Hnq & ->).
  rewrite -> !urelsp_index_inj.
  apply iutruncate_collapse_conv.
  rewrite -> !iutruncate_iuarrow.
  f_equal.
    {
    so (urelspinj_dist_index' _#11 HXY) as [(Heq & _) | (Hle & Hle')].
      {
      subst k; auto.
      }

      {
      so (Min.min_r k j).
      so (Min.min_r k' j).
      omega.
      }
    }

    {
    apply iutruncate_collapse.
    apply (pi2 R); auto.
    }

    {
    apply iutruncate_collapse.
    apply (pi2 C); auto.
    }
  }
exists (expair _ Hne).
do2 4 split; auto.
  {
  apply functional_i; auto.
    {
    eapply subst_closub_under_permit; eauto.
    apply hygiene_auto; cbn.
    do2 2 split; auto.
    prove_hygiene.
    }
  intros j m p Hj Hmp.
  simpsub.
  cbn.
  rewrite -> urelsp_index_inj.
  apply interp_eval_refl.
  apply interp_tarrow.
    {
    invert Hrl.
    intros _ _ Hact.
    so (Hact _ _ _ Hj Hmp) as H.
    simpsubin H.
    exact H.
    }

    {
    invert Hcl.
    intros _ _ Hact.
    so (Hact _ _ _ Hj Hmp) as H.
    simpsubin H.
    exact H.
    }
  }

  {
  apply functional_i; auto.
    {
    eapply subst_closub_under_permit; eauto.
    apply hygiene_auto; cbn.
    do2 2 split; auto.
    prove_hygiene.
    }
  intros j m p Hj Hmp.
  simpsub.
  cbn.
  rewrite -> urelsp_index_inj.
  apply interp_eval_refl.
  apply interp_tarrow.
    {
    invert Hrr.
    intros _ _ Hact.
    so (Hact _ _ _ Hj Hmp) as H.
    simpsubin H.
    exact H.
    }

    {
    invert Hcr.
    intros _ _ Hact.
    so (Hact _ _ _ Hj Hmp) as H.
    simpsubin H.
    exact H.
    }
  }
intros f g i' m p d e j Hde Hclf Hclg Hclm Hclp Hcld Hcle Hadmact.
destruct Hde as (Hi'_lt & Hde).
cbn.
split; auto.
rewrite -> embed_ceiling_urelspinj.
rewrite -> urelsp_index_inj.
assert (exists l l', star step (subst1 (app theta f) m) (lam l) /\ star step (subst1 (app theta g) p) (lam l')) as (l & l' & Hstepsl & Hstepsl').
  {
  so (Hadmact _ (le_refl _)) as (Hdej & Hmpj).
  destruct Hdej as (Hi'_lt_alt & Hdej).
  so (proof_irrelevance _ Hi'_lt Hi'_lt_alt).
  subst Hi'_lt_alt.
  cbn in Hmpj.
  destruct Hmpj as (_ & Hmpj).
  rewrite -> embed_ceiling_urelspinj in Hmpj.
  decompose Hmpj.
  intros lj lj' _ _ _ Hsteps Hsteps' _.
  so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _ f j Hclf) Hclm) (conj Hsteps value_lam)) as (w & (Hstepsm & _) & Hmc).
  invertc_mc Hmc.
  intros l _ <-.
  fold (lam l) in Hstepsm.
  so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _ g j Hclg) Hclp) (conj Hsteps' value_lam)) as (w & (Hstepsp & _) & Hmc).
  invertc_mc Hmc.
  intros l' _ <-.
  fold (lam l) in Hstepsm.
  fold (lam l') in Hstepsp.
  exists l, l'.
  auto.
  }
eassert _ as H; [refine (steps_hygiene _#4 Hstepsl _) |].
  {
  apply hygiene_subst1; prove_hygiene.
  }
so (hygiene_invert_auto _#5 H) as H'; cbn in H'; clear H.
destruct H' as (Hcll & _).
eassert _ as H; [refine (steps_hygiene _#4 Hstepsl' _) |].
  {
  apply hygiene_subst1; prove_hygiene.
  }
so (hygiene_invert_auto _#5 H) as H'; cbn in H'; clear H.
destruct H' as (Hcll' & _).
exists l, l'.
do2 5 split; auto.
  {
  apply hygiene_subst1; auto.
  prove_hygiene.
  }

  {
  apply hygiene_subst1; auto.
  prove_hygiene.
  }
intros i'' n q Hi'' Hnq.
so (urel_closed _#5 Hnq) as (Hcln & Hclq).
(* Adapt for other proofs *)
assert (exists t,
          j <= t
          /\ forall k, 
               t <= k
               -> exists (Hdek : rel (den A) i'' (subst1 (afix k f) d) (subst1 (afix k g) e)),
                    rel (den (pi1 R (urelspinj (den A) _ _ _ Hdek))) i'' n q) as (t & Hjt & Hnqall).
  {
  invert Hrl.
  intros _ _ HactR.
  assert (i' <= i) as Hi' by omega.
  so (HactR _ _ _ Hi' Hde) as Hrdl.
  simpsubin Hrdl.
  invert (basic_value_inv _#6 value_halts Hrdl).
  intros _ Heq.
  eassert (rel (den (iubase (halts_urel stop i' (subst (dot (subst1 (app theta f) d) s) r)))) _ _ _) as H.
    {
    force_exact Hnq.
    f_equal.
    f_equal.
    symmetry.
    exact Heq.
    }
  renameover H into Hnq.
  clear Heq.
  cbn in Hnq.
  decompose Hnq.
  intros Hconv _ _ _ Hstepsn Hstepsq.
  exploit (compactness _ f (subst (dot d (compose s sh1)) r)) as (t & Hconvt); auto.
    {
    eapply hygiene_subst; eauto.
    intros z Hz.
    destruct z as [| z]; simpsub; auto.
    apply hygiene_shift_permit.
    cbn in Hz.
    eapply project_closub; eauto.
    }
  
    {
    simpsub.
    exact Hconv.
    }
  exists (max j t).
  so (Nat.le_max_l j t) as Hjmax.
  split; auto.
  intros k Hk.
  assert (j <= k) as Hjk by omega.
  so (Hadmact _ Hjk) as (Hdek & _).
  destruct Hdek as (_ & Hdek).
  so (urel_downward_leq _#6 Hi'' Hdek) as Hdek'.
  exists Hdek'.
  assert (i'' <= i) as Hi''_i by omega.
  so (HactR _ _ _ Hi''_i Hdek') as Hrdlk.
  simpsubin Hrdlk.
  invert (basic_value_inv _#6 value_halts Hrdlk).
  intros _ Heqk.
  eassert (rel (den (iubase (halts_urel stop i'' (subst (dot (subst1 (afix k f) d) s) r)))) _ _ _) as H.
  2:{
    force_exact H.
    f_equal.
    f_equal.
    exact Heqk.
    }
  clear Hrdlk Heqk.
  cbn.
  do2 5 split; auto.
    {
    simpsubin Hconvt.
    refine (approx_converges _#3 _ Hconvt).
    cut (approx (subst1 (afix t f) (subst (dot d (compose s sh1)) r)) (subst1 (afix k f) (subst (dot d (compose s sh1)) r))).
      {
      intro H.
      simpsubin H.
      exact H.
      }
    apply approx_funct1.
      {
      apply afix_approx; auto.
      so (Nat.le_max_r j t) as Htmax.
      omega.
      }

      {
      eapply hygiene_subst; eauto.
      intros z Hz.
      destruct z as [| z]; simpsub; auto.
      apply hygiene_shift_permit.
      cbn in Hz.
      eapply project_closub; eauto.
      }
    }
  }
assert (i'' < S i) as Hi''_i_lt by omega.
so (urel_downward_leq _#6 Hi'' Hde) as Hde'.
exploit (Hadmiss f g i'' (app m n) (app p q) d e (max j t) (conj Hi''_i_lt Hde')) as Hrel; auto; try prove_hygiene.
  {
  intros k Hjtk.
  so (Nat.max_lub_l _ _ _ Hjtk) as Hjk.
  so (Nat.max_lub_r _ _ _ Hjtk) as Htk.
  so (Hadmact k Hjk) as (Hdek & Hmpk).
  destruct Hdek as (Hi'_lt_alt & Hdek).
  so (proof_irrelevance _ Hi'_lt Hi'_lt_alt).
  subst Hi'_lt_alt.
  so (urel_downward_leq _#6 Hi'' Hdek) as Hdek'.
  exists (conj Hi''_i_lt Hdek').
  simpsub.
  cbn.
  split; auto.
  rewrite -> embed_ceiling_urelspinj.
  cbn in Hmpk.
  destruct Hmpk as (_ & Hmpk).
  rewrite -> urelsp_index_embed_ceiling in Hmpk.
  rewrite -> urelsp_index_inj in Hmpk.
  rewrite -> embed_ceiling_urelspinj in Hmpk.
  decompose Hmpk.
  intros lk lk' _ _ _ Hsteps Hsteps' Hact.
  so (Hnqall k Htk) as (Hdek'' & Hnqk).
  so (proof_irrelevance _ Hdek' Hdek'').
  subst Hdek''.
  exploit (Hact i'' n q) as H; auto.
    {
    refine (rel_from_dist _#6 _ Hnqk).
    apply den_nonexpansive.
    apply (pi2 R).
    apply urelspinj_dist; auto.
    }
  rewrite -> (subst_into_closed _ _ n Hcln).
  rewrite -> (subst_into_closed _ _ q Hclq).
  apply (urel_equiv _#3 (subst1 n lk) _ (subst1 q lk')); try prove_hygiene.
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun Z => app Z n)); eauto using step_app1.
      }
    apply star_one.
    apply step_app2.
    }
  
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun Z => app Z q)); eauto using step_app1.
      }
    apply star_one.
    apply step_app2.
    }

    {
    refine (rel_from_dist _#6 _ H).
    apply den_nonexpansive.
    apply (pi2 C).
    apply dist_symm.
    apply urelspinj_dist; auto.
    }
  }
simpsubin Hrel.
cbn in Hrel.
destruct Hrel as (_ & Hrel).
rewrite -> embed_ceiling_urelspinj in Hrel.
rewrite -> (subst_into_closed _ _ n Hcln) in Hrel.
rewrite -> (subst_into_closed _ _ q Hclq) in Hrel.
apply (urel_equiv _#3 (app (subst1 (app theta f) m) n) _ (app (subst1 (app theta g) p) q)); try prove_hygiene.
  {
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ (fun Z => app Z n)); eauto using step_app1.
    }
  apply star_one.
  apply step_app2.
  }

  {
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ (fun Z => app Z q)); eauto using step_app1.
    }
  apply star_one.
  apply step_app2.
  }

  {
  refine (rel_from_dist _#6 _ Hrel).
  apply den_nonexpansive.
  apply (pi2 C).
  apply urelspinj_dist; auto.
  }
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


Lemma sound_prod_padmiss :
  forall G a b c,
    pseq G (deq triv triv (padmiss a b))
    -> pseq G (deq triv triv (padmiss a c))
    -> pseq G (deq triv triv (padmiss a (prod b c))).
Proof.
intros G a b c.
revert G.
refine (seq_pseq 2 [hyp_emp] b [hyp_emp] c 2 [] _ [] _ _ _); cbn.
intros G Hclb Hclc Hseqb Hseqc.
rewrite -> seq_padmiss in Hseqb, Hseqc |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqb _#3 Hs) as (A & B & Hal & Har & Hbl & Hbr & HadmissB).
clear Hseqb.
so (Hseqc _#3 Hs) as (A' & C & Hal' & _ & Hcl & Hcr & HadmissC).
clear Hseqc.
so (interp_fun _#7 Hal Hal').
subst A'.
exists A.
assert (@nonexpansive (urelsp (den A)) siurel_ofe (fun X => iuprod stop (pi1 B X) (pi1 C X))) as Hne.
  {
  intros j X Y HXY.
  destruct j as [| j].
    {
    apply dist_zero.
    }
  apply iutruncate_collapse_conv.
  rewrite -> !iutruncate_iuprod.
  f_equal.
    {
    apply iutruncate_collapse.
    apply (pi2 B); auto.
    }

    {
    apply iutruncate_collapse.
    apply (pi2 C); auto.
    }
  }
exists (expair _ Hne).
invert Hbl.
intros Hclsb Hceil _.
invert Hcl.
intros Hclsc _ _.
do2 4 split; auto.
  {
  apply functional_i; auto.
    {
    simpsub.
    apply hygiene_auto; cbn.
    do2 2 split; auto.
    }
  intros j m p Hj Hmp.
  simpsub.
  cbn.
  apply interp_eval_refl.
  apply interp_prod.
    {
    invert Hbl.
    intros _ _ Hact.
    so (Hact _ _ _ Hj Hmp) as H.
    simpsubin H.
    exact H.
    }

    {
    invert Hcl.
    intros _ _ Hact.
    so (Hact _ _ _ Hj Hmp) as H.
    simpsubin H.
    exact H.
    }
  }

  {
  apply functional_i; auto.
    {
    eapply subst_closub_under_permit; eauto.
    apply hygiene_auto; cbn.
    do2 2 split; auto.
    }
  intros j m p Hj Hmp.
  simpsub.
  cbn.
  apply interp_eval_refl.
  apply interp_prod.
    {
    invert Hbr.
    intros _ _ Hact.
    so (Hact _ _ _ Hj Hmp) as H.
    simpsubin H.
    exact H.
    }

    {
    invert Hcr.
    intros _ _ Hact.
    so (Hact _ _ _ Hj Hmp) as H.
    simpsubin H.
    exact H.
    }
  }
unfold padmissible.
intros f g i' m p d e j Hde Hclf Hclg Hclm Hclp Hcld Hcle Hact.
destruct Hde as (Hi' & Hde).
split; auto.
cbn.
rewrite -> embed_ceiling_urelspinj.
exploit (HadmissB f g i' (ppi1 m) (ppi1 p) d e j (conj Hi' Hde)) as H1; auto; try prove_hygiene.
  {
  intros k Hk.
  so (Hact k Hk) as ((Hi'' & Hdek) & H).
  so (proof_irrelevance _ Hi' Hi'').
  subst Hi''.
  exists (conj Hi' Hdek).
  split; auto.
  simpsub.
  simpsubin H.
  cbn in H |- *.
  destruct H as (_ & H).
  rewrite -> !embed_ceiling_urelspinj in H |- *.
  exact (prod_action_ppi1 _#6 H).
  }
simpsubin H1.
cbn in H1.
destruct H1 as (_ & H1).
rewrite -> embed_ceiling_urelspinj in H1.
exploit (HadmissC f g i' (ppi2 m) (ppi2 p) d e j (conj Hi' Hde)) as H2; auto; try prove_hygiene.
  {
  intros k Hk.
  so (Hact k Hk) as ((Hi'' & Hdek) & H).
  so (proof_irrelevance _ Hi' Hi'').
  subst Hi''.
  exists (conj Hi' Hdek).
  split; auto.
  simpsub.
  simpsubin H.
  cbn in H |- *.
  destruct H as (_ & H).
  rewrite -> !embed_ceiling_urelspinj in H |- *.
  exact (prod_action_ppi2 _#6 H).
  }
simpsubin H2.
cbn in H2.
destruct H2 as (_ & H2).
rewrite -> embed_ceiling_urelspinj in H2.
so (Hact j (le_refl _)) as (Hcdj & Hmpj).
cbn in Hmpj.
destruct Hmpj as (_ & Hmpj).
decompose Hmpj.
intros x1 y1 x2 y2 _ _ Hstepsx Hstepsy _ _.
clear Hcdj.
so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _ f j Hclf) Hclm) (conj Hstepsx value_ppair)) as (w & (Hstepsm & _) & Hmc).
invertc_mc Hmc.
intros m1 _ m2 _ <-.
fold (ppair m1 m2) in Hstepsm.
so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _ g j Hclg) Hclp) (conj Hstepsy value_ppair)) as (w & (Hstepsp & _) & Hmc).
invertc_mc Hmc.
intros p1 _ p2 _ <-.
fold (ppair p1 p2) in Hstepsp.
clear x1 y1 x2 y2 Hstepsx Hstepsy.
assert (hygiene clo (app theta f)) as Hclfixf by prove_hygiene.
assert (hygiene clo (app theta g)) as Hclfixg by prove_hygiene.
eassert _ as H; [refine (steps_hygiene _ clo _ _ Hstepsm _) |].
  {
  prove_hygiene.
  }
so (hygiene_invert_auto _#5 H) as H'.
cbn in H'.
destruct H' as (Hclm1 & Hclm2 & _).
clear H.
eassert _ as H; [refine (steps_hygiene _ clo _ _ Hstepsp _) |].
  {
  prove_hygiene.
  }
so (hygiene_invert_auto _#5 H) as H'.
cbn in H'.
destruct H' as (Hclp1 & Hclp2 & _).
clear H.
exists m1, p1, m2, p2.
do2 5 split; auto; try prove_hygiene.
  {
  refine (urel_equiv _#7 _ _ _ _ H1); try prove_hygiene.
    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi11.
      }
    apply star_one.
    apply step_ppi12.
    }

    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi11.
      }
    apply star_one.
    apply step_ppi12.
    }
  }

  {
  refine (urel_equiv _#7 _ _ _ _ H2); try prove_hygiene.
    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi21.
      }
    apply star_one.
    apply step_ppi22.
    }

    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi21.
      }
    apply star_one.
    apply step_ppi22.
    }
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
  eapply urel_equiv; eauto; try prove_hygiene.
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


Lemma sound_sigma_admiss :
  forall G a b,
    pseq G (deq triv triv (admiss a))
    -> pseq G (deq triv triv (padmiss a b))
    -> pseq G (deq triv triv (admiss (sigma a b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 2 [] a [hyp_emp] b 2 [] _ [] _ _ _); cbn.
intros G Hcla Hclb Hseqa Hseqb.
rewrite -> seq_admiss in Hseqa |- *.
rewrite -> seq_padmiss in Hseqb.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & HadmissA).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
so (Hseqb _#3 Hs) as (A' & B & Hal' & _ & Hbl & Hbr & HadmissB).
so (interp_fun _#7 Hal Hal').
subst A'.
exists (iusigma stop A B).
simpsub.
clear Hseqa Hseqb.
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
so (Hmp j (le_refl _)) as (Hi' & Hmpj).
split; auto.
cbn in Hmpj.
decompose Hmpj.
intros x x' y y' _ _ _ Hstepsx Hstepsy _.
so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _ f j Hclf) Hclm) (conj Hstepsx value_ppair)) as (w & (Hstepsm & _) & Hmc).
invertc_mc Hmc.
intros m1 _ m2 _ <-.
fold (ppair m1 m2) in Hstepsm.
so (approx_action _#4 (approx_funct1 _#4 (afix_fix_approx _ g j Hclg) Hclp) (conj Hstepsy value_ppair)) as (w & (Hstepsp & _) & Hmc).
invertc_mc Hmc.
intros p1 _ p2 _ <-.
fold (ppair p1 p2) in Hstepsp.
clear x x' y y' Hstepsx Hstepsy.
exists m1, p1, m2, p2.
assert (rel (den A) i' (subst1 (app theta f) (ppi1 m)) (subst1 (app theta g) (ppi1 p))) as Hmp1.
  {
  unfold admissible in HadmissA.
  rewrite -> HeqA.
  apply (HadmissA f g i' (ppi1 m) (ppi1 p) j); auto; try prove_hygiene.
  intros k Hk.
  so (Hmp k Hk) as (_ & H).
  split; auto.
  cbn in H.
  decompose H.
  intros m1' p1' m2' p2' Hrel1 _ _ Hstepsm' Hstepsp' _.
  simpsub.
  refine (urel_equiv _#7 _ _ _ _ Hrel1); try prove_hygiene.
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi1); eauto.
      intros; apply step_ppi11; auto.
      }
    apply star_one.
    apply step_ppi12.
    }

    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi1); eauto.
      intros; apply step_ppi11; auto.
      }
    apply star_one.
    apply step_ppi12.
    }
  }
assert (hygiene clo (app theta f)) as Hclfixf by prove_hygiene.
assert (hygiene clo (app theta g)) as Hclfixg by prove_hygiene.
eassert _ as H; [refine (steps_hygiene _ clo _ _ Hstepsm _) |].
  {
  prove_hygiene.
  }
so (hygiene_invert_auto _#5 H) as H'.
cbn in H'.
destruct H' as (Hclm1 & Hclm2 & _).
clear H.
eassert _ as H; [refine (steps_hygiene _ clo _ _ Hstepsp _) |].
  {
  prove_hygiene.
  }
so (hygiene_invert_auto _#5 H) as H'.
cbn in H'.
destruct H' as (Hclp1 & Hclp2 & _).
clear H.
assert (rel (den A) i' m1 p1) as Hm1p1.
  {
  apply (urel_equiv _ _ _ (subst1 (app theta f) (ppi1 m)) _ (subst1 (app theta g) (ppi1 p))); auto.
    {
    simpsub.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi1).
        {
        intros.
        apply step_ppi11; auto.
        }
      exact Hstepsm.
      }
    apply star_one.
    apply step_ppi12.
    }

    {
    simpsub.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi1).
        {
        intros.
        apply step_ppi11; auto.
        }
      exact Hstepsp.
      }
    apply star_one.
    apply step_ppi12.
    }
  }
exists Hm1p1.
do2 4 split; auto.
  {
  apply hygiene_subst1; auto; prove_hygiene.
  }

  {
  apply hygiene_subst1; auto; prove_hygiene.
  }
cbn.
exploit (HadmissB f g i' (ppi2 m) (ppi2 p) (ppi1 m) (ppi1 p) j (conj Hi' Hmp1)) as H; auto; try prove_hygiene.
  {
  intros k Hk.
  so (Hmp k Hk) as (_ & Hmpk).
  cbn in Hmpk.
  decompose Hmpk.
  intros x1 y1 x2 y2 Hxy1 _ _ Hstepsx Hstepsy Hxy2.
  assert (rel (den A) i' (subst1 (afix k f) (ppi1 m)) (subst1 (afix k g) (ppi1 p))) as Hmp1_k.
    {
    apply (urel_equiv _#3 x1 _ y1); try prove_hygiene.
      {
      simpsub.
      apply equiv_symm.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1).
          {
          intros.
          apply step_ppi11; auto.
          }
        exact Hstepsx.
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
        apply (star_map' _ _ ppi1).
          {
          intros.
          apply step_ppi11; auto.
          }
        exact Hstepsy.
        }
      apply star_one.
      apply step_ppi12.
      }
    }
  exists (conj Hi' Hmp1_k).
  so (urel_closed _#5 Hxy1) as (Hclx1 & Hcly1).
  apply (urel_equiv _#3 x2 _ y2); try prove_hygiene.
    {
    simpsub.
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi2).
        {
        intros.
        apply step_ppi21; auto.
        }
      exact Hstepsx.
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
      apply (star_map' _ _ ppi2).
        {
        intros.
        apply step_ppi21; auto.
        }
      exact Hstepsy.
      }
    apply star_one.
    apply step_ppi22.
    }
  split; [omega |].
  force_exact Hxy2.
  f_equal.
  cbn [pi1 nearrow_compose2 nearrow_compose den_ne embed_ceiling_ne].
  f_equal.
  f_equal.
  rewrite -> embed_ceiling_urelspinj.
  apply urelspinj_equal.
  refine (urel_equiv _#7 _ _ _ _ Hmp1_k); auto; try prove_hygiene.
    {
    simpsub.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ ppi1).
        {
        intros.
        apply step_ppi11; auto.
        }
      exact Hstepsx.
      }
    apply star_one.
    apply step_ppi12.
    }

    {
    apply equiv_refl.
    }
  }
apply (urel_equiv _ _ _ (subst1 (app theta f) (ppi2 m)) _ (subst1 (app theta g) (ppi2 p))); auto.
  {
  simpsub.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi2).
      {
      intros.
      apply step_ppi21; auto.
      }
    exact Hstepsm.
    }
  apply star_one.
  apply step_ppi22.
  }

  {
  simpsub.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi2).
      {
      intros.
      apply step_ppi21; auto.
      }
    exact Hstepsp.
    }
  apply star_one.
  apply step_ppi22.
  }
destruct H as (_ & H).
force_exact H.
clear H.
cbn [pi1 den_ne embed_ceiling_ne].
f_equal.
f_equal.
f_equal.
rewrite -> embed_ceiling_urelspinj.
apply urelspinj_equal.
refine (urel_equiv _#7 _ _ _ _ Hm1p1); auto; try prove_hygiene.
  {
  simpsub.
  apply equiv_symm.
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ ppi1).
      {
      intros.
      apply step_ppi11; auto.
      }
    exact Hstepsm.
    }
  apply star_one.
  apply step_ppi12.
  }

  {
  apply equiv_refl.
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
      prove_hygiene.
      }
    so (hygiene_invert_auto _#5 H) as H'; cbn in H'; clear H.
    destruct H' as (Hcln & _).
    eassert _ as H; [refine (steps_hygiene _#4 Hstepsp _) |].
      {
      prove_hygiene.
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
      refine (urel_equiv _#7 _ _ _ _ Hnq); try prove_hygiene.
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


Lemma sound_equal_padmiss :
  forall G a b m n,
    pseq G (deq triv triv (padmiss a b))
    -> pseq (cons (hyp_tm a) G) (deq m m b)
    -> pseq (cons (hyp_tm a) G) (deq n n b)
    -> pseq G (deq triv triv (padmiss a (equal b m n))).
Proof.
intros G a b m p.
revert G.
refine (seq_pseq 3 [hyp_emp] b [hyp_emp] m [hyp_emp] p 3 [] _ [_] _ [_] _ _ _); cbn.
intros G Hclb Hclm Hclp Hseqadm Hseqm Hseqp.
rewrite -> seq_padmiss in Hseqadm |- *.
rewrite -> seq_deq in Hseqm, Hseqp.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqadm _#3 Hs) as (A & B & Hal & Har & Hbl & Hbr & Hadmiss).
assert (forall j n q, j <= i -> rel (den A) j n q -> pwctx j (dot n s) (dot q s') (hyp_tm a :: G)) as Hss.
  {
  intros j n q Hj Hnq.
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
    so (Hseqadm _#3 Ht) as (R & _ & Hl & Hr & _).
    eauto.
    }
  }
clear Hseqadm.
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  exact (f_equal den (basic_impl_iutruncate _#6 Hal)).
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) (equal b m p)) (subst (under 1 s') (equal b m p))) as H; auto; try prove_hygiene.
  {
  intros j n q Hnq.
  so Hnq as H.
  rewrite -> HeqA in H.
  destruct H as (Hj_lt & _).
  assert (j <= i) as Hj by omega.
  so (Hseqm _#3 (Hss _#3 Hj Hnq)) as (Rm & Hbml & _ & Hm & _).
  so (Hseqp _#3 (Hss _#3 Hj Hnq)) as (Rp & Hbpl & Hbpr & Hp & _).
  invert Hbl.
  intros _ _ Hact.
  so (Hact _#3 Hj Hnq) as H.
  simpsubin H.
  so (interp_fun _#7 H Hbml).
  subst Rm.
  so (interp_fun _#7 H Hbpl).
  subst Rp.
  exists (iuequal stop true j (pi1 B (urelspinj _#4 Hnq)) (subst (dot n s) m) (subst (dot n s) p) (subst (dot q s') m) (subst (dot q s') p) Hm Hp).
  simpsub.
  split.
    {
    apply interp_eval_refl.
    apply interp_equal; auto.
    }

    {
    apply interp_eval_refl.
    rewrite -> iuequal_swap.
    cbn.
    apply interp_equal; auto.
    }
  }
destruct H as (C & Hcl & Hcr).
exists A, C.
do2 4 split; auto.
intros f g i' r t d e j Hde Hclf Hclg Hclr Hclt Hcld Hcle Hadmact.
destruct Hde as (Hi'_lt, Hde).
assert (i' <= i) as Hi' by omega.
split; auto.
cbn.
rewrite -> embed_ceiling_urelspinj.
invert Hbl.
intros _ _ Hblact.
invert Hcl.
intros _ _ Hclact.
so (Hclact _#3 Hi' Hde) as H.
simpsubin H.
invert (basic_value_inv _#6 value_equal H).
clear H.
intros u v Bf Hu Hv Hbfl Heq.
match type of Heq with
?X = _ =>
  eassert (rel (den X) _ _ _) as H
end.
2:{
  force_exact H.
  f_equal.
  f_equal.
  exact Heq.
  }
clear Heq.
cbn.
assert (star step (subst1 (afix j f) r) triv /\ star step (subst1 (afix j g) t) triv) as (Hsteprj & Hsteptj).
  {
  so (Hadmact j (le_refl _)) as (Hdej & Hrtj).
  destruct Hdej as (Hi'_lt' & Hdej).
  so (proof_irrelevance _ Hi'_lt Hi'_lt').
  subst Hi'_lt'.
  cbn in Hrtj.
  destruct Hrtj as (_ & Hrtj).
  rewrite -> embed_ceiling_urelspinj in Hrtj.
  so (Hclact _#3 Hi' Hdej) as Hcfjl.
  simpsubin Hcfjl.
  invert (basic_value_inv _#6 value_equal Hcfjl).
  intros uj vj A' Hmpj Hnqj _ Heq.
  match type of Heq with
  ?X = _ =>
    eassert (rel (den X) _ _ _) as H
  end.
    {
    force_exact Hrtj.
    f_equal.
    f_equal.
    symmetry.
    exact Heq.
    }
  renameover H into Hrtj.
  cbn in Hrtj.
  decompose Hrtj.
  auto.
  }
do2 5 split; auto.
  {
  exists (subst (dot (subst1 (app theta g) e) s') p).
  unfold srel in Hu, Hv.
  split.
    {
    exploit (Hadmiss f g i' (subst (dot d (compose s sh1)) m) (subst (dot e (compose s' sh1)) p) d e j (conj Hi'_lt Hde)) as H; auto.
      {
      eapply hygiene_subst; eauto.
      intros l Hl.
      destruct l as [| l].
        {
        simpsub.
        auto.
        }
      simpsub.
      apply hygiene_shift_permit; auto.
      }
    
      {
      eapply hygiene_subst; eauto.
      intros l Hl.
      destruct l as [| l].
        {
        simpsub.
        auto.
        }
      simpsub.
      apply hygiene_shift_permit; auto.
      }
    
      {
      intros k Hk.
      so (Hadmact _ Hk) as (Hdek & Hrtk).
      exists Hdek.
      destruct Hdek as (Hi'_lt' & Hdek).
      so (proof_irrelevance _ Hi'_lt Hi'_lt').
      subst Hi'_lt'.
      cbn.
      split; auto.
      rewrite -> embed_ceiling_urelspinj.
      cbn in Hrtk.
      destruct Hrtk as (_ & Hrtk).
      rewrite -> embed_ceiling_urelspinj in Hrtk.
      simpsub.
      so (Hclact _#3 Hi' Hdek) as H.
      simpsubin H.
      invert (basic_value_inv _#6 value_equal H); clear H.
      intros uk vk Bfk Hmuk Hpvk Hbfkl Heq.
      simpsubin Hbfkl.
      match type of Heq with
      ?X = _ =>
        eassert (rel (den X) _ _ _) as H
      end.
        {
        force_exact Hrtk.
        f_equal.
        f_equal.
        symmetry.
        exact Heq.
        }
      renameover H into Hrtk.
      clear Heq.
      so (Hblact _#3 Hi' Hdek) as Hbfkl'.
      simpsubin Hbfkl'.
      so (interp_fun _#7 Hbfkl Hbfkl').
      subst Bfk.
      clear Hbfkl'.
      cbn in Hrtk.
      decompose Hrtk.
      intros x Hmx Hpx _ _ _ _ _.
      eapply urel_zigzag; eauto.
      so (Hseqp _#3 (Hss _#3 Hi' Hdek)) as (R & Hbfkl' & _ & Hpk & _).
      so (interp_fun _#7 Hbfkl Hbfkl').
      subst R.
      exact Hpk.
      }
    cbn in H.
    destruct H as (_ & H).
    rewrite -> embed_ceiling_urelspinj in H.
    so (Hblact _#3 Hi' Hde) as Hbfl'.
    simpsubin Hbfl'.
    so (interp_fun _#7 Hbfl Hbfl').
    subst Bf.
    simpsubin H.
    exact H.
    }

    {
    exploit (Hadmiss f g i' (subst (dot d (compose s sh1)) p) (subst (dot e (compose s' sh1)) p) d e j (conj Hi'_lt Hde)) as H; auto.
      {
      eapply hygiene_subst; eauto.
      intros l Hl.
      destruct l as [| l].
        {
        simpsub.
        auto.
        }
      simpsub.
      apply hygiene_shift_permit; auto.
      }
    
      {
      eapply hygiene_subst; eauto.
      intros l Hl.
      destruct l as [| l].
        {
        simpsub.
        auto.
        }
      simpsub.
      apply hygiene_shift_permit; auto.
      }
    
      {
      intros k Hk.
      so (Hadmact _ Hk) as (Hdek & Hrtk).
      exists Hdek.
      destruct Hdek as (Hi'_lt' & Hdek).
      so (proof_irrelevance _ Hi'_lt Hi'_lt').
      subst Hi'_lt'.
      cbn.
      split; auto.
      rewrite -> embed_ceiling_urelspinj.
      cbn in Hrtk.
      destruct Hrtk as (_ & Hrtk).
      rewrite -> embed_ceiling_urelspinj in Hrtk.
      simpsub.
      so (Hclact _#3 Hi' Hdek) as H.
      simpsubin H.
      invert (basic_value_inv _#6 value_equal H); clear H.
      intros uk vk Bfk Hmuk Hpvk Hbfkl Heq.
      simpsubin Hbfkl.
      match type of Heq with
      ?X = _ =>
        eassert (rel (den X) _ _ _) as H
      end.
        {
        force_exact Hrtk.
        f_equal.
        f_equal.
        symmetry.
        exact Heq.
        }
      renameover H into Hrtk.
      clear Heq.
      so (Hblact _#3 Hi' Hdek) as Hbfkl'.
      simpsubin Hbfkl'.
      so (interp_fun _#7 Hbfkl Hbfkl').
      subst Bfk.
      clear Hbfkl'.
      cbn in Hrtk.
      decompose Hrtk.
      intros x Hmx Hpx _ _ _ _ _.
      eapply urel_zigzag; eauto.
      so (Hseqp _#3 (Hss _#3 Hi' Hdek)) as (R & Hbfkl' & _ & Hpk & _).
      so (interp_fun _#7 Hbfkl Hbfkl').
      subst R.
      exact Hpk.
      }
    cbn in H.
    destruct H as (_ & H).
    rewrite -> embed_ceiling_urelspinj in H.
    so (Hblact _#3 Hi' Hde) as Hbfl'.
    simpsubin Hbfl'.
    so (interp_fun _#7 Hbfl Hbfl').
    subst Bf.
    simpsubin H.
    exact H.
    }
  }

  {
  apply hygiene_subst1; prove_hygiene.
  }

  {
  apply hygiene_subst1; prove_hygiene.
  }
  
  {
  assert (approx (subst1 (afix j f) r) (subst1 (app theta f) r)) as Happrox.
    {
    apply approx_funct1; auto.
    apply afix_fix_approx; auto.
    }
  so (approx_action _#4 Happrox (conj Hsteprj value_triv)) as (x & Heval & Hmc).
  destruct Heval as (Hsteps & _).
  invertc_mc Hmc.
  intros <-.
  exact Hsteps.
  }

  {
  assert (approx (subst1 (afix j g) t) (subst1 (app theta g) t)) as Happrox.
    {
    apply approx_funct1; auto.
    apply afix_fix_approx; auto.
    }
  so (approx_action _#4 Happrox (conj Hsteptj value_triv)) as (x & Heval & Hmc).
  destruct Heval as (Hsteps & _).
  invertc_mc Hmc.
  intros <-.
  exact Hsteps.
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


Lemma sound_set_admiss :
  forall G a b m n,
    pseq G (deq triv triv (admiss a))
    -> pseq G (deq triv triv (padmiss a b))
    -> pseq (cons (hyp_tm b) (cons (hyp_tm a) G)) (deq (subst sh1 m) (subst sh1 n) (subst sh1 b))
    -> pseq G (deq triv triv (admiss (set a b))).
Proof.
intros G a b n q.
revert G.
refine (seq_pseq 4 [] a [hyp_emp] b [hyp_emp] n [hyp_emp] q 3 [] _ [] _ [_; _] _ _ _); cbn.
intros G Hcla Hclb Hcln Hclq Hseqa Hseqb Hseqnq.
rewrite -> seq_admiss in Hseqa |- *.
rewrite -> seq_padmiss in Hseqb.
rewrite -> seq_deq in Hseqnq.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & HadmissA).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
so (Hseqb _#3 Hs) as (A' & B & Hal' & _ & Hbl & Hbr & HadmissB).
so (interp_fun _#7 Hal Hal').
subst A'.
clear Hal'.
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
intros f g i' m p j Hclf Hclg Hclm Hclp Hmp.
so (Hmp j (le_refl _)) as (Hi' & _).
split; auto.
cbn.
assert (rel (den A) i' (subst1 (app theta f) m) (subst1 (app theta g) p)) as Hmp1.
  {
  unfold admissible in HadmissA.
  rewrite -> HeqA.
  apply (HadmissA f g i' m p j); auto; try prove_hygiene.
  intros k Hk.
  so (Hmp k Hk) as (_ & H).
  split; auto.
  cbn in H.
  decompose H.
  intros _ _ H _.
  exact H.
  }
assert (hygiene clo (app theta f)) as Hclfixf by prove_hygiene.
assert (hygiene clo (app theta g)) as Hclfixg by prove_hygiene.
unfold set_action.
exists (subst (dot (subst1 (app theta f) m) s) n), (subst (dot (subst1 (app theta g) p) s') q), Hmp1.
exploit (HadmissB f g i' (subst (dot m (compose s sh1)) n) (subst (dot p (compose s' sh1)) q) m p j (conj Hi' Hmp1)) as H; auto.
  {
  eapply hygiene_subst; eauto.
  intros l Hl.
  destruct l as [| l]; auto.
  simpsub.
  cbn in Hl.
  apply hygiene_shift_permit.
  eapply project_closub; eauto.
  }

  {
  eapply hygiene_subst; eauto.
  intros l Hl.
  destruct l as [| l]; auto.
  simpsub.
  cbn in Hl.
  apply hygiene_shift_permit.
  eapply project_closub; eauto.
  }

  {
  intros k Hk.
  so (Hmp k Hk) as (_ & Hmpk).
  cbn in Hmpk.
  decompose Hmpk.
  intros r t Hmp1_k Hrt.
  exists (conj Hi' Hmp1_k).
  cbn.
  split; [omega |].
  assert (i' <= i) as Hi'' by omega.
  assert (pwctx i' (dot r (dot (subst1 (afix k f) m) s)) (dot t (dot (subst1 (afix k g) p) s')) (hyp_tm b :: hyp_tm a :: G)) as Hss.
    {
    apply pwctx_cons_tm_seq.
      {
      apply pwctx_cons_tm_seq.
        {
        eapply pwctx_downward; eauto.
        }

        {
        apply (seqhyp_tm _#5 (iutruncate (S i') A)); auto.
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
        intros i'' u u' Hu.
        so (Hseqa _#3 Hu) as (R & Hl & Hr & _).
        exists toppg, R.
        auto.
        }
      }

      {
      eapply seqhyp_tm; eauto.
        {
        invert Hbl.
        intros _ _ Hact.
        so (Hact _#3 Hi'' Hmp1_k) as H.
        simpsubin H.
        exact H.
        }

        {
        invert Hbr.
        intros _ _ Hact.
        so (Hact _#3 Hi'' Hmp1_k) as H.
        simpsubin H.
        exact H.
        }
      }

      {
      intros i'' uu uu' Huu.
      invert Huu.
      intros x y u u' Hu Hxy _ _ <- <-.
      clear Huu.
      invert Hxy.
      clear Hxy.
      intros R Hual Huar Hxy.
      so (Hseqb _#3 Hu) as (R' & C & Hual' & _ & Hubl & Hubr & _).
      so (interp_fun _#7 Hual Hual').
      subst R'.
      exists toppg, (pi1 C (urelspinj _#4 Hxy)).
      split.
        {
        invert Hubl.
        intros _ _ Hact.
        so (Hact _#3 (le_refl _) Hxy) as H.
        simpsubin H.
        exact H.
        }

        {
        invert Hubr.
        intros _ _ Hact.
        so (Hact _#3 (le_refl _) Hxy) as H.
        simpsubin H.
        exact H.
        }
      }
    }
  so (Hseqnq _#3 Hss) as (R & Hl & _ & _ & _ & Hnq).
  simpsubin Hnq.
  simpsubin Hl.
  invert Hbl.
  intros _ _ Hact.
  so (Hact _#3 Hi'' Hmp1_k) as Hl'.
  simpsubin Hl'.
  so (interp_fun _#7 Hl Hl').
  subst R.
  simpsub.
  force_exact Hnq.
  f_equal.
  f_equal.
  f_equal.
  rewrite -> embed_ceiling_urelspinj.
  reflexivity.
  }
simpsubin H.
destruct H as (_ & H).
force_exact H.
clear H.
f_equal.
cbn.
f_equal.
f_equal.
rewrite -> embed_ceiling_urelspinj.
reflexivity.
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


(* identical proof to sound_set_admiss *)
Lemma sound_iset_admiss :
  forall G a b m n,
    pseq G (deq triv triv (admiss a))
    -> pseq G (deq triv triv (padmiss a b))
    -> pseq (cons (hyp_tm b) (cons (hyp_tm a) G)) (deq (subst sh1 m) (subst sh1 n) (subst sh1 b))
    -> pseq G (deq triv triv (admiss (iset a b))).
Proof.
intros G a b n q.
revert G.
refine (seq_pseq 4 [] a [hyp_emp] b [hyp_emp] n [hyp_emp] q 3 [] _ [] _ [_; _] _ _ _); cbn.
intros G Hcla Hclb Hcln Hclq Hseqa Hseqb Hseqnq.
rewrite -> seq_admiss in Hseqa |- *.
rewrite -> seq_padmiss in Hseqb.
rewrite -> seq_deq in Hseqnq.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & HadmissA).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
so (Hseqb _#3 Hs) as (A' & B & Hal' & _ & Hbl & Hbr & HadmissB).
so (interp_fun _#7 Hal Hal').
subst A'.
clear Hal'.
exists (iuiset stop A B).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl.
  apply interp_iset; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_iset; auto.
  }
intros f g i' m p j Hclf Hclg Hclm Hclp Hmp.
so (Hmp j (le_refl _)) as (Hi' & _).
split; auto.
cbn.
assert (rel (den A) i' (subst1 (app theta f) m) (subst1 (app theta g) p)) as Hmp1.
  {
  unfold admissible in HadmissA.
  rewrite -> HeqA.
  apply (HadmissA f g i' m p j); auto; try prove_hygiene.
  intros k Hk.
  so (Hmp k Hk) as (_ & H).
  split; auto.
  cbn in H.
  decompose H.
  intros _ _ H _.
  exact H.
  }
assert (hygiene clo (app theta f)) as Hclfixf by prove_hygiene.
assert (hygiene clo (app theta g)) as Hclfixg by prove_hygiene.
unfold set_action.
exists (subst (dot (subst1 (app theta f) m) s) n), (subst (dot (subst1 (app theta g) p) s') q), Hmp1.
exploit (HadmissB f g i' (subst (dot m (compose s sh1)) n) (subst (dot p (compose s' sh1)) q) m p j (conj Hi' Hmp1)) as H; auto.
  {
  eapply hygiene_subst; eauto.
  intros l Hl.
  destruct l as [| l]; auto.
  simpsub.
  cbn in Hl.
  apply hygiene_shift_permit.
  eapply project_closub; eauto.
  }

  {
  eapply hygiene_subst; eauto.
  intros l Hl.
  destruct l as [| l]; auto.
  simpsub.
  cbn in Hl.
  apply hygiene_shift_permit.
  eapply project_closub; eauto.
  }

  {
  intros k Hk.
  so (Hmp k Hk) as (_ & Hmpk).
  cbn in Hmpk.
  decompose Hmpk.
  intros r t Hmp1_k Hrt.
  exists (conj Hi' Hmp1_k).
  cbn.
  split; [omega |].
  assert (i' <= i) as Hi'' by omega.
  assert (pwctx i' (dot r (dot (subst1 (afix k f) m) s)) (dot t (dot (subst1 (afix k g) p) s')) (hyp_tm b :: hyp_tm a :: G)) as Hss.
    {
    apply pwctx_cons_tm_seq.
      {
      apply pwctx_cons_tm_seq.
        {
        eapply pwctx_downward; eauto.
        }

        {
        apply (seqhyp_tm _#5 (iutruncate (S i') A)); auto.
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
        intros i'' u u' Hu.
        so (Hseqa _#3 Hu) as (R & Hl & Hr & _).
        exists toppg, R.
        auto.
        }
      }

      {
      eapply seqhyp_tm; eauto.
        {
        invert Hbl.
        intros _ _ Hact.
        so (Hact _#3 Hi'' Hmp1_k) as H.
        simpsubin H.
        exact H.
        }

        {
        invert Hbr.
        intros _ _ Hact.
        so (Hact _#3 Hi'' Hmp1_k) as H.
        simpsubin H.
        exact H.
        }
      }

      {
      intros i'' uu uu' Huu.
      invert Huu.
      intros x y u u' Hu Hxy _ _ <- <-.
      clear Huu.
      invert Hxy.
      clear Hxy.
      intros R Hual Huar Hxy.
      so (Hseqb _#3 Hu) as (R' & C & Hual' & _ & Hubl & Hubr & _).
      so (interp_fun _#7 Hual Hual').
      subst R'.
      exists toppg, (pi1 C (urelspinj _#4 Hxy)).
      split.
        {
        invert Hubl.
        intros _ _ Hact.
        so (Hact _#3 (le_refl _) Hxy) as H.
        simpsubin H.
        exact H.
        }

        {
        invert Hubr.
        intros _ _ Hact.
        so (Hact _#3 (le_refl _) Hxy) as H.
        simpsubin H.
        exact H.
        }
      }
    }
  so (Hseqnq _#3 Hss) as (R & Hl & _ & _ & _ & Hnq).
  simpsubin Hnq.
  simpsubin Hl.
  invert Hbl.
  intros _ _ Hact.
  so (Hact _#3 Hi'' Hmp1_k) as Hl'.
  simpsubin Hl'.
  so (interp_fun _#7 Hl Hl').
  subst R.
  simpsub.
  force_exact Hnq.
  f_equal.
  f_equal.
  f_equal.
  rewrite -> embed_ceiling_urelspinj.
  reflexivity.
  }
simpsubin H.
destruct H as (_ & H).
force_exact H.
clear H.
f_equal.
cbn.
f_equal.
f_equal.
rewrite -> embed_ceiling_urelspinj.
reflexivity.
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


Lemma sound_padmiss_closed :
  forall G a b,
    pseq G (deqtype a a)
    -> pseq G (deq triv triv (admiss b))
    -> pseq G (deq triv triv (padmiss a (subst sh1 b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 1 [] b 2 [] _ [] _ _ _); cbn.
intros G Hclb Ha Hb.
rewrite -> seq_eqtype in Ha.
rewrite -> seq_admiss in Hb.
rewrite -> seq_padmiss.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Ha _#3 Hs) as (A & Hal & Har & _).
so (Hb _#3 Hs) as (B & Hbl & Hbr & Hadmiss).
exists A.
exists (semiconst_ne (den A) B).
do2 4 split; auto.
  {
  apply functional_i.
    {
    simpsub.
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }

    {
    so (basic_impl_iutruncate _#6 Hal) as Heq.
    exact (@f_equal _ _ den _ _ Heq).
    }
  intros j m p Hj Hmp.
  simpsub.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  eapply basic_downward; eauto.
  }

  {
  apply functional_i.
    {
    simpsub.
    rewrite -> subst_compose.
    apply hygiene_shift_permit.
    eapply subst_closub; eauto.
    }

    {
    so (basic_impl_iutruncate _#6 Hal) as Heq.
    exact (@f_equal _ _ den _ _ Heq).
    }
  intros j m p Hj Hmp.
  simpsub.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  eapply basic_downward; eauto.
  }

  {
  intros f g i' m p c d j Hcd Hclf Hclg Hclm Hclp Hclc Hcld Hact.
  destruct Hcd as (Hi' & Hcd).
  do2 2 split.
    {
    omega.
    }

    {
    cbn.
    rewrite -> urelsp_index_embed_ceiling.
    rewrite -> urelsp_index_inj.
    omega.
    }
  exploit (Hadmiss f g i' m p j) as H; auto.
    {
    intros k Hk.
    split; auto.
    so (Hact k Hk) as (Hbck & H).
    cbn in H.
    destruct H as (_ & _ & H).
    exact H.
    }
  destruct H as (_ & H).
  exact H.
  }
Qed.
