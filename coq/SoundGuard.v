
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

Require Import Ceiling.
Require Import ProperLevel.
Require Import SoundUtil.
Require Import SemanticsGuard.
Require Import Truncate.
Require Import ProperDownward.
Require Import SemanticsPi.
Require Import Urelsp.


Lemma sound_guard_formation :
  forall G a a' b b',
    pseq G (deqtype a a')
    -> pseq (cons (hyp_tm a) G) (deqtype (subst sh1 b) (subst sh1 b'))
    -> pseq G (deqtype (guard a b) (guard a' b')).
Proof.
intros G a b c d.
revert G.
refine (seq_pseq 2 [] c [] d 2 [] _ [_] _ _ _); cbn.
intros G Hclc Hcld Hseqab Hseqcd.
rewrite -> seq_eqtype in Hseqab, Hseqcd |- *.
intros i s s' Hs.
so (seqctx_impl_closub _#4 (pwctx_impl_seqctx _#4 Hs)) as (Hcls & Hcls').
so (Hseqab _#3 Hs) as (A & Hal & Har & Hbl & Hbr).
exploit (extract_functional_multi toppg i (squash_urel stop (den A) i) (subst sh1 (subst s c)) (subst sh1 (subst s' c)) (subst sh1 (subst s d)) (subst sh1 (subst s' d))) as (C & Hcl & Hcr & Hdl & Hdr); eauto; try (rewrite <- hygiene_shift_permit_iff; eauto using subst_closub; done).
  {
  rewrite -> ceiling_squash.
  rewrite -> Nat.min_id.
  reflexivity.
  }

  {
  intros j m p Hmp.
  cbn in Hmp.
  decompose Hmp.
  intros n q Hnq Hj _ _ _ _.
  assert (pwctx j (dot n s) (dot q s') (cons (hyp_tm a) G)) as Hss.
    {
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
  simpsubin Hcl.
  simpsubin Hcr.
  simpsubin Hdl.
  simpsubin Hdr.
  auto.
  }
exists (iuguard stop i A C).
simpsub.
do2 3 split; auto;
apply interp_eval_refl;
apply interp_guard; auto.
Qed.


Lemma sound_guard_formation_iff :
  forall G a a' b b' mr ml,
    pseq G (deqtype a a)
    -> pseq G (deqtype a' a')
    (* a implies a' *)
    -> pseq (hyp_tm a :: G)
         (deq mr mr (subst sh1 a'))
    (* a' implies a *)
    -> pseq (hyp_tm a' :: G)
         (deq ml ml (subst sh1 a))
    -> pseq (cons (hyp_tm a) G) (deqtype (subst sh1 b) (subst sh1 b'))
    -> pseq G (deqtype (guard a b) (guard a' b')).
Proof.
intros G a b c d x y.
revert G.
refine (seq_pseq 2 [] c [] d 5 [] _ [] _ [_] _ [_] _ [_] _ _ _); cbn.
intros G Hclc Hcld Hseqa Hseqb Hseqab Hseqba Hseqcd.
rewrite -> seq_eqtype in Hseqa, Hseqb, Hseqcd |- *.
rewrite -> seq_deq in Hseqab, Hseqba.
intros i s s' Hs.
so (seqctx_impl_closub _#4 (pwctx_impl_seqctx _#4 Hs)) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
so (Hseqb _#3 Hs) as (B & Hbl & Hbr & _).
assert (forall j m p,
          j <= i
          -> rel (den B) j m p
          -> rel (den A) j (subst (dot m s) y) (subst (dot p s') y)) as Hba.
  {
  intros j m p Hj Hmp.
  exploit (Hseqba j (dot m s) (dot p s')) as (R & Hrl & _ & Hy & _).
    {
    apply pwctx_cons_tm_seq.
      {
      apply (pwctx_downward i); auto.
      }

      {
      apply (seqhyp_tm _#5 (iutruncate (S j) B)); auto.
        {
        apply (basic_downward _#3 i); auto.
        }
        
        {
        apply (basic_downward _#3 i); auto.
        }

        {
        rewrite -> den_iutruncate.
        split; auto.
        }
      }

      {
      intros i' t t' Ht.
      so (Hseqb _ _ _ Ht) as (R & Hl & Hr & _).
      exists toppg, R.
      auto.
      }
    }
  simpsubin Hrl.
  so (interp_fun _#7 Hrl (basic_downward _#7 Hj Hal)) as H.
  subst R.
  rewrite -> den_iutruncate in Hy.
  destruct Hy as (_ & Hy).
  auto.
  }
assert (forall j m p,
          j <= i
          -> rel (den A) j m p
          -> rel (den B) j (subst (dot m s) x) (subst (dot p s') x)) as Hab.
  {
  intros j m p Hj Hmp.
  exploit (Hseqab j (dot m s) (dot p s')) as (R & Hrl & _ & Hy & _).
    {
    apply pwctx_cons_tm_seq.
      {
      apply (pwctx_downward i); auto.
      }

      {
      apply (seqhyp_tm _#5 (iutruncate (S j) A)); auto.
        {
        apply (basic_downward _#3 i); auto.
        }
        
        {
        apply (basic_downward _#3 i); auto.
        }

        {
        rewrite -> den_iutruncate.
        split; auto.
        }
      }

      {
      intros i' t t' Ht.
      so (Hseqa _ _ _ Ht) as (R & Hl & Hr & _).
      exists toppg, R.
      auto.
      }
    }
  simpsubin Hrl.
  so (interp_fun _#7 Hrl (basic_downward _#7 Hj Hbl)) as H.
  subst R.
  rewrite -> den_iutruncate in Hy.
  destruct Hy as (_ & Hy).
  auto.
  }
exploit (extract_functional_multi toppg i (squash_urel stop (den A) i) (subst sh1 (subst s c)) (subst sh1 (subst s' c)) (subst sh1 (subst s d)) (subst sh1 (subst s' d))) as (C & Hcl & Hcr & Hdl & Hdr); eauto; try (rewrite <- hygiene_shift_permit_iff; eauto using subst_closub; done).
  {
  rewrite -> ceiling_squash.
  rewrite -> Nat.min_id.
  reflexivity.
  }

  {
  intros j m p Hmp.
  cbn in Hmp.
  decompose Hmp.
  intros n q Hnq Hj _ _ _ _.
  assert (pwctx j (dot n s) (dot q s') (cons (hyp_tm a) G)) as Hss.
    {
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
  so (Hseqcd _#3 Hss) as (R & Hcl & Hcr & Hdl & Hdr).
  exists R.
  simpsub.
  simpsubin Hcl.
  simpsubin Hcr.
  simpsubin Hdl.
  simpsubin Hdr.
  auto.
  }
exploit (extract_functional_multi toppg i (squash_urel stop (den B) i) (subst sh1 (subst s c)) (subst sh1 (subst s' c)) (subst sh1 (subst s d)) (subst sh1 (subst s' d))) as (D & Hcl' & Hcr' & Hdl' & Hdr'); eauto; try (rewrite <- hygiene_shift_permit_iff; eauto using subst_closub; done).
  {
  rewrite -> ceiling_squash.
  rewrite -> Nat.min_id.
  reflexivity.
  }

  {
  intros j m p Hmp.
  cbn in Hmp.
  decompose Hmp.
  intros n q Hnq Hj _ _ _ _.
  assert (pwctx j (dot (subst (dot n s) y) s) (dot (subst (dot q s') y) s') (cons (hyp_tm a) G)) as Hss.
    {
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
  so (Hseqcd _#3 Hss) as (R & Hcl' & Hcr' & Hdl' & Hdr').
  exists R.
  simpsub.
  simpsubin Hcl'.
  simpsubin Hcr'.
  simpsubin Hdl'.
  simpsubin Hdr'.
  auto.
  }
exists (iuguard stop i A C).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl.
  apply interp_guard; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_guard; auto.
  }
replace (iuguard stop i A C) with (iuguard stop i B D).
  {
  split.
    {
    apply interp_eval_refl.
    apply interp_guard; auto.
    }
  
    {
    apply interp_eval_refl.
    apply interp_guard; auto.
    }
  }
symmetry.
unfold iuguard.
f_equal.
  {
  apply urel_extensionality.
  fextensionality 3.
  intros j m p.
  pextensionality.
    {
    intro Hmp.
    cbn in Hmp |- *.
    decompose Hmp.
    intros Hj Hclm Hclp Hact.
    exists Hj.
    do2 2 split; auto.
    intros j' n q Hj' Hnq.
    so (Hba _ _ _ (le_trans _#3 Hj' Hj) Hnq) as Hy.
    so (Hact j' _ _ Hj' Hy) as Hcy.
    invert Hcl.
    intros _ _ Hactc.
    invert Hcl'.
    intros _ _ Hactd.
    so (Hactd j' _ _ (le_trans _#3 Hj' Hj) (squash_intro stop (den B) i j' n q (le_trans _#3 Hj' Hj) Hnq)) as Hinterp.
    so (Hactc j' _ _ (le_trans _#3 Hj' Hj) (squash_intro stop (den A) i j' (subst (dot n s) y) (subst (dot q s') y) (le_trans _#3 Hj' Hj) Hy)) as Hinterp'.
    simpsubin Hinterp.
    simpsubin Hinterp'.
    so (interp_fun _#7 Hinterp Hinterp') as Heq.
    so (f_equal (fun Z => rel (den Z) j' m p) Heq) as Heq'.
    cbn in Heq'.
    rewrite <- Heq' in Hcy.
    exact Hcy.
    }

    {
    intro Hmp.
    cbn in Hmp |- *.
    decompose Hmp.
    intros Hj Hclm Hclp Hact.
    exists Hj.
    do2 2 split; auto.
    intros j' n q Hj' Hnq.
    so (Hab _ _ _ (le_trans _#3 Hj' Hj) Hnq) as Hx.
    so (Hact j' _ _ Hj' Hx) as Hdx.
    invert Hcl.
    intros _ _ Hactc.
    invert Hcl'.
    intros _ _ Hactd.
    so (Hactc j' _ _ (le_trans _#3 Hj' Hj) (squash_intro stop (den A) i j' n q (le_trans _#3 Hj' Hj) Hnq)) as Hinterp.
    so (Hactd j' _ _ (le_trans _#3 Hj' Hj) (squash_intro stop (den B) i j' (subst (dot n s) x) (subst (dot q s') x) (le_trans _#3 Hj' Hj) Hx)) as Hinterp'.
    simpsubin Hinterp.
    simpsubin Hinterp'.
    so (interp_fun _#7 Hinterp Hinterp') as Heq.
    so (f_equal (fun Z => rel (den Z) j' m p) Heq) as Heq'.
    cbn in Heq'.
    rewrite <- Heq' in Hdx.
    exact Hdx.
    }
  }

  {
  f_equal.
  exploit (maximum_element (fun j => j <= i /\ exists m p, rel (den A) j m p)) as [Hnone | Hsome].
    {
    exists (S i).
    intros j (H, _).
    omega.
    }

    {
    exploit (pi2 (unguard stop (den A) i C) andel 0) as Htrunc.
      {
      intros j m p Hk Hmp.
      exfalso.
      refine (Hnone j _).
      eauto.
      }
    rewrite -> Htrunc; clear Htrunc.
    exploit (pi2 (unguard stop (den B) i D) andel 0) as Htrunc.
      {
      intros j m p Hj Hmp.
      exfalso.
      refine (Hnone j _).
      split; auto.
      exists (subst (dot m s) y), (subst (dot p s') y).
      apply Hba; auto.
      }
    rewrite -> Htrunc; clear Htrunc.
    apply iutruncate_collapse.
    apply dist_zero.
    }

    {
    destruct Hsome as (j & (Hj & m & p & Hmp) & Hmax).
    exploit (pi2 (unguard stop (den A) i C) andel (S j)) as Htrunc.
      {
      intros k n q Hk Hnq.
      cut (k <= j).
        {
        omega.
        }
      refine (Hmax k _).
      eauto.
      }
    rewrite -> Htrunc.
    clear Htrunc.
    exploit (pi2 (unguard stop (den B) i D) andel (S j)) as Htrunc.
      {
      intros k n q Hk Hnq.
      cut (k <= j).
        {
        omega.
        }
      refine (Hmax k _).
      split; auto.
      exists (subst (dot n s) y), (subst (dot q s') y).
      auto.
      }
    rewrite -> Htrunc.
    clear Htrunc.
    apply iutruncate_collapse.
    clear Hmax.
    eapply dist_trans.
      {
      exact (pi2 (unguard stop (den A) i C) ander j m p Hj Hmp).
      }
    eapply dist_trans.
    2:{
      apply dist_symm.
      exact (pi2 (unguard stop (den B) i D) ander j (subst (dot m s) x) (subst (dot p s') x) Hj (Hab _#3 Hj Hmp)).
      }
    apply dist_refl'.

    invert Hcl.
    intros _ _ Hactc.
    invert Hcl'.
    intros _ _ Hactd.
    so (Hactc j _ _ Hj (squash_intro stop (den A) i j m p Hj Hmp)) as Hinterp.
    so (Hactd j _ _ Hj (squash_intro stop (den B) i j (subst (dot m s) x) (subst (dot p s') x) Hj (Hab _#3 Hj Hmp))) as Hinterp'.
    simpsubin Hinterp.
    simpsubin Hinterp'.
    so (interp_fun _#7 Hinterp Hinterp') as Heq.
    exact Heq.
    }
  }
Qed.


Lemma sound_guard_formation_univ :
  forall G lv a a' b b',
    pseq G (deq a a' (univ lv))
    -> pseq (cons (hyp_tm a) G) (deq (subst sh1 b) (subst sh1 b') (univ (subst sh1 lv)))
    -> pseq G (deq (guard a b) (guard a' b') (univ lv)).
Proof.
intros G lv a b c d.
revert G.
refine (seq_pseq 2 [] c [] d 2 [] _ [_] _ _ _); cbn.
intros G Hclc Hcld Hseqab Hseqcd.
rewrite -> seq_univ in Hseqab, Hseqcd |- *.
intros i s s' Hs.
so (seqctx_impl_closub _#4 (pwctx_impl_seqctx _#4 Hs)) as (Hcls & Hcls').
so (Hseqab _#3 Hs) as (pg & A & Hlvl & Hlvr & Hal & Har & Hbl & Hbr).
exploit (extract_functional_multi pg i (squash_urel stop (den A) i) (subst sh1 (subst s c)) (subst sh1 (subst s' c)) (subst sh1 (subst s d)) (subst sh1 (subst s' d))) as (C & Hcl & Hcr & Hdl & Hdr); eauto; try (rewrite <- hygiene_shift_permit_iff; eauto using subst_closub; done).
  {
  rewrite -> ceiling_squash.
  rewrite -> Nat.min_id.
  reflexivity.
  }

  {
  intros j m p Hmp.
  cbn in Hmp.
  decompose Hmp.
  intros n q Hnq Hj _ _ _ _.
  assert (pwctx j (dot n s) (dot q s') (cons (hyp_tm a) G)) as Hss.
    {
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
  simpsubin Hcl.
  simpsubin Hcr.
  simpsubin Hdl.
  simpsubin Hdr.
  auto.
  }
exists pg, (iuguard stop i A C).
simpsub.
do2 5 split; auto;
apply interp_eval_refl;
apply interp_guard; auto.
Qed.


Local Ltac prove_hygiene :=
  repeat (apply hygiene_auto; cbn; repeat2 split; auto);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1, subst_closub;
  try (apply hygiene_var; cbn; auto; done).


Lemma sound_guard_sat_eq :
  forall G a b m n,
    pseq G (deq m n a)
    -> pseq G (deqtype b b)
    -> pseq G (deqtype b (guard a b)).
Proof.
intros G a b m n.
revert G.
refine (seq_pseq 1 [] b 2 [] _ [] _ _ _); cbn.
intros G Hclb Hseqm Hseqb.
rewrite -> seq_eqtype in Hseqb |- *.
rewrite -> seq_deq in Hseqm.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqm _#3 Hs) as (A & Hal & Har & Hm & _).
so (Hseqb _#3 Hs) as (B & Hbl & Hbr & _).
exists B.
simpsub.
do2 2 split; auto.
set (B' := semiconst_ne (squash_urel stop (den A) i) B).
assert (forall j p q (Hpq : rel (squash_urel stop (den A) i) j p q),
          j <= i
          -> pi1 B' (urelspinj (squash_urel stop (den A) i) j p q Hpq)
             =
             iutruncate (S j) B) as Heq.
  {
  intros j p q Hj Hpq.
  cbn.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  reflexivity.
  }
assert (interp toppg true i (guard (subst s a) (subst s b)) (iuguard stop i A B')) as Hguard.
  {
  apply interp_eval_refl.
  apply interp_guard; auto.
  apply functional_i.
    {
    rewrite <- hygiene_shift_permit_iff.
    eapply subst_closub; eauto.
    }

    {
    rewrite -> ceiling_squash.
    rewrite -> Nat.min_id.
    reflexivity.
    }
  intros j p q Hj Hpq.
  rewrite -> Heq; auto.
  simpsub.
  eapply basic_downward; eauto.
  }
assert (interp toppg false i (guard (subst s' a) (subst s' b)) (iuguard stop i A (semiconst_ne (squash_urel stop (den A) i) B))) as Hguard'.
  {
  apply interp_eval_refl.
  apply interp_guard; auto.
  apply functional_i.
    {
    rewrite <- hygiene_shift_permit_iff.
    eapply subst_closub; eauto.
    }

    {
    rewrite -> ceiling_squash.
    rewrite -> Nat.min_id.
    reflexivity.
    }
  intros j p q Hj Hpq.
  rewrite -> Heq; auto.
  simpsub.
  eapply basic_downward; eauto.
  }
assert (B = iuguard stop i A B') as Heq'.
  {
  rewrite -> (basic_impl_iutruncate _#6 Hguard).
  rewrite <- (iuguard_satisfied_eq _#7 (le_refl i) Hm).
  rewrite -> Heq; auto.
  rewrite <- !(basic_impl_iutruncate _#6 Hbl).
  reflexivity.
  }
rewrite -> Heq' at 1 2.
auto.
Qed.


Lemma sound_guard_intro :
  forall G a b m n,
    pseq G (deqtype a a)
    -> pseq (hyp_tm a :: G) (deq (subst sh1 m) (subst sh1 n) (subst sh1 b))
    -> pseq G (deq m n (guard a b)).
Proof.
intros G a b m n.
revert G.
refine (seq_pseq 3 [] m [] n [] b 2 [] _ [_] _ _ _); cbn.
intros G Hclm Hcln Hclb Hseqa Hseqmn.
rewrite -> seq_deq in Hseqmn |- *.
rewrite -> seq_eqtype in Hseqa.
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
exploit (extract_functional toppg i (squash_urel stop (den A) i) (subst sh1 (subst s b)) (subst sh1 (subst s' b))) as H.
  {
  rewrite -> ceiling_squash.
  rewrite -> Nat.min_id.
  reflexivity.
  }

  {
  rewrite <- hygiene_shift_permit_iff.
  eapply subst_closub; eauto.
  }

  {
  rewrite <- hygiene_shift_permit_iff.
  eapply subst_closub; eauto.
  }

  {
  intros j p q Hpq.
  destruct Hpq as ((r & t & Hrt) & _).
  so (Hseqmn _#3 (Hss j r t Hrt)) as (R & Hbl & Hbr & _).
  simpsubin Hbl.
  simpsubin Hbr.
  exists R.
  simpsub.
  auto.
  }
destruct H as (B & Hbl & Hbr).
exists (iuguard stop i A B).
do2 4 split.
  {
  simpsub.
  apply interp_eval_refl.
  apply interp_guard; auto.
  }

  {
  simpsub.
  apply interp_eval_refl.
  apply interp_guard; auto.
  }

  {
  exists (le_refl i).
  do2 2 split; eauto using subst_closub.
  intros j p q Hj Hpq.
  so (Hseqmn _#3 (Hss _#3 Hpq)) as (R & Hl & _ & Hm & _).
  simpsubin Hm.
  simpsubin Hl.
  invert Hbl.
  intros _ _ Hact.
  so (Hact _#3 Hj (squash_intro _#6 Hj Hpq)) as Hl'.
  simpsubin Hl'.
  so (interp_fun _#7 Hl Hl'); subst R.
  replace (le_trans _#3 Hj (le_refl i)) with Hj; auto.
  apply proof_irrelevance.
  }

  {
  exists (le_refl i).
  do2 2 split; eauto using subst_closub.
  intros j p q Hj Hpq.
  so (Hseqmn _#3 (Hss _#3 Hpq)) as (R & Hl & _ & _ & Hn & _).
  simpsubin Hn.
  simpsubin Hl.
  invert Hbl.
  intros _ _ Hact.
  so (Hact _#3 Hj (squash_intro _#6 Hj Hpq)) as Hl'.
  simpsubin Hl'.
  so (interp_fun _#7 Hl Hl'); subst R.
  replace (le_trans _#3 Hj (le_refl i)) with Hj; auto.
  apply proof_irrelevance.
  }

  {
  exists (le_refl i).
  do2 2 split; eauto using subst_closub.
  intros j p q Hj Hpq.
  so (Hseqmn _#3 (Hss _#3 Hpq)) as (R & Hl & _ & _ & _ & Hmn).
  simpsubin Hmn.
  simpsubin Hl.
  invert Hbl.
  intros _ _ Hact.
  so (Hact _#3 Hj (squash_intro _#6 Hj Hpq)) as Hl'.
  simpsubin Hl'.
  so (interp_fun _#7 Hl Hl'); subst R.
  replace (le_trans _#3 Hj (le_refl i)) with Hj; auto.
  apply proof_irrelevance.
  }
Qed.


Lemma sound_guard_elim :
  forall G a b m n p q,
    pseq G (deq m n (guard a b))
    -> pseq G (deq p q a)
    -> pseq G (deq m n b).
Proof.
intros G a b m n p q.
revert G.
refine (seq_pseq 2 [] p [] q 2 [] _ [] _ _ _); cbn.
intros G Hclp Hclq Hseqmn Hseqpq.
rewrite -> seq_deq in Hseqmn, Hseqpq |- *.
intros i s s' Hs.
so (Hseqpq _#3 Hs) as (A & Hal & Har & Hp & _).
so (Hseqmn _#3 Hs) as (R & Hl & Hr & Hm & Hn & Hmn).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_guard Hl).
intros A' B Hal' Hbl Heq1.
so (basic_fun _#7 Hal Hal'); subst A'; clear Hal'.
invert (basic_value_inv _#6 value_guard Hr).
intros A' B' Har' Hbr Heq2.
so (basic_fun _#7 Har Har'); subst A'; clear Har'.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
assert (B = B').
  {
  so (fun j (h : j <= i) => iuguard_satisfied_eq _#3 B _#3 h (urel_downward_leq _#6 h Hp)) as Heq1.
  so (fun j (h : j <= i) => iuguard_satisfied_eq _#3 B' _#3 h (urel_downward_leq _#6 h Hp)) as Heq2.
  rewrite -> Heq in Heq1.
  so (fun j h => eqtrans (Heq1 j h) (eqsymm (Heq2 j h))) as Heq'.
  clear Heq1 Heq2 Heq.
  apply nearrow_extensionality.
  intros x.
  cbn.
  so (urelsp_eta _ _ x) as (j & r & t & Hrt & ->).
  so Hrt as (_ & Hj & _).
  invert Hbl.
  intros _ _ Hactl.
  so (basic_impl_iutruncate _#6 (Hactl _#3 Hj Hrt)) as H.
  cbn in H.
  rewrite -> H.
  clear H Hactl.
  invert Hbr.
  intros _ _ Hactr.
  so (basic_impl_iutruncate _#6 (Hactr _#3 Hj Hrt)) as H.
  cbn in H.
  rewrite -> H.
  clear H Hactr.
  replace (urelspinj (squash_urel stop (den A) i) j r t Hrt) with (urelspinj (squash_urel stop (den A) i) j triv triv (squash_intro _#6 Hj (urel_downward_leq _#6 Hj Hp))).
  2:{
    apply urelspinj_equal.
    destruct Hrt as (Hinh & _ & _ & Hclt & _ & Hsteps).
    do2 5 split; auto using star_refl.
    apply hygiene_auto; cbn.
    trivial.
    }
  apply Heq'.
  }
subst B'.
set (Bp := pi1 B (urelspinj _#4 (squash_intro _#6 (le_refl i) Hp))).
exists Bp.
do2 4 split; auto.
  {
  invert Hbl.
  intros _ _ Hact.
  so (Hact _#3 (le_refl i) (squash_intro _#6 (le_refl i) Hp)) as H.
  unfold Bp.
  simpsubin H.
  exact H.
  }

  {
  invert Hbr.
  intros _ _ Hact.
  so (Hact _#3 (le_refl i) (squash_intro _#6 (le_refl i) Hp)) as H.
  unfold Bp.
  simpsubin H.
  exact H.
  }

  {
  destruct Hm as (Hrefl & _ & _ & Hact).
  so (Hact _#3 (le_refl _) Hp) as H.
  force_exact H.
  unfold Bp.
  repeat f_equal.
  apply proof_irrelevance.
  }

  {
  destruct Hn as (Hrefl & _ & _ & Hact).
  so (Hact _#3 (le_refl _) Hp) as H.
  force_exact H.
  unfold Bp.
  repeat f_equal.
  apply proof_irrelevance.
  }

  {
  destruct Hmn as (Hrefl & _ & _ & Hact).
  so (Hact _#3 (le_refl _) Hp) as H.
  force_exact H.
  unfold Bp.
  repeat f_equal.
  apply proof_irrelevance.
  }
Qed.
