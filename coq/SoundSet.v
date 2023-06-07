
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
Require Import Ceiling.
Require Import Truncate.
Require Import Urelsp.
Require Import SemanticsSet.
Require Import ProperDownward.
Require Import ProperLevel.
Require Import Equivalence.
Require Import Subsumption.
Require Import SemanticsSimple.
Require Import SemanticsPi.
Require Import Defined.


Local Ltac prove_hygiene :=
  repeat (first [ eapply subst_closub; eauto
                | apply closub_dot
                | apply hygiene_auto; cbn; repeat2 split; auto
                ]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1;
  try (apply hygiene_var; cbn; auto; done).



Lemma sound_set_formation_main :
  forall lvo G a b c d mr ml,
    hygiene (ctxpred G) a
    -> hygiene (ctxpred G) b
    -> hygiene (permit (ctxpred G)) c
    -> hygiene (permit (ctxpred G)) d
    -> (forall i s s',
          pwctx i s s' G
          -> exists pg R,
               pgointerp s lvo pg
               /\ pgointerp s' lvo pg
               /\ interp pg true i (subst s a) R
               /\ interp pg false i (subst s' a) R
               /\ interp pg true i (subst s b) R
               /\ interp pg false i (subst s' b) R)
    -> (forall i s s',
          pwctx i s s' (hyp_tm a :: G)
          -> exists pg R,
               pgointerp (compose sh1 s) lvo pg
               /\ interp pg true i (subst s c) R
               /\ interp pg false i (subst s' c) R)
    -> (forall i s s',
          pwctx i s s' (hyp_tm a :: G)
          -> exists pg R,
               pgointerp (compose sh1 s) lvo pg
               /\ interp pg true i (subst s d) R
               /\ interp pg false i (subst s' d) R)
    -> (forall i s s',
          pwctx i s s' (hyp_tm c :: hyp_tm a :: G)
          -> exists R,
               interp toppg true i (subst s (subst sh1 d)) R
               /\ interp toppg false i (subst s' (subst sh1 d)) R
               /\ rel (den R) i (subst s mr) (subst s' mr))
    -> (forall i s s',
          pwctx i s s' (hyp_tm d :: hyp_tm a :: G)
          -> exists R,
               interp toppg true i (subst s (subst sh1 c)) R
               /\ interp toppg false i (subst s' (subst sh1 c)) R
               /\ rel (den R) i (subst s ml) (subst s' ml))
    -> forall i s s',
         pwctx i s s' G
         -> exists pg R,
              pgointerp s lvo pg
              /\ pgointerp s' lvo pg
              /\ interp pg true i (subst s (set a c)) R
              /\ interp pg false i (subst s' (set a c)) R
              /\ interp pg true i (subst s (set b d)) R
              /\ interp pg false i (subst s' (set b d)) R.
Proof.
intros lvo G a b c d mr ml Hcla Hclb Hclc Hcld Hseqab Hseqc Hseqd Hseqcd Hseqdc i s s' Hs.
so (seqctx_impl_closub _#4 (pwctx_impl_seqctx _#4 Hs)) as (Hcls & Hcls').
so (Hseqab _#3 Hs) as (pg & A & Hlvl & Hlvr & Hal & Har & Hbl & Hbr).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional pg i (den A) (subst (under 1 s) c) (subst (under 1 s') c)) as (C & Hcl & Hcr); eauto using subst_closub_under_permit.
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
  so (Hseqc _#3 Hss) as (pg' & R & Hlv' & Hcl & Hcr).
  simpsubin Hlv'.
  so (pgointerp_fun _#4 Hlvl Hlv'); subst pg'.
  exists R.
  simpsub.
  auto.
  }
exploit (extract_functional pg i (den A) (subst (under 1 s) d) (subst (under 1 s') d)) as (D & Hdl & Hdr); eauto using subst_closub_under_permit.
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
  so (Hseqd _#3 Hss) as (pg' & R & Hlv' & Hdl & Hdr).
  simpsubin Hlv'.
  so (pgointerp_fun _#4 Hlvl Hlv'); subst pg'.
  exists R.
  simpsub.
  auto.
  }
exists pg, (iuset stop A C).
assert (forall j e m n p q E (Hmn : rel (den A) j m n),
          functional the_system pg true i (den A) (subst (under 1 s) e) E
          -> functional the_system pg false i (den A) (subst (under 1 s') e) E
          -> rel (den (pi1 E (urelspinj (den A) j m n Hmn))) j p q
          -> (forall i s s',
                pwctx i s s' (hyp_tm a :: G)
                -> exists pg R,
                     pgointerp (compose sh1 s) lvo pg
                     /\ interp pg true i (subst s e) R
                     /\ interp pg false i (subst s' e) R)
          -> pwctx j (dot p (dot m s)) (dot q (dot n s')) (hyp_tm e :: hyp_tm a :: G)) as Hext.
  {
  intros j e m n p q E Hmn Hel Her Hpq Hseqe.
  so (basic_member_index _#9 Hal Hmn) as Hj.
  apply pwctx_cons_tm_seq.
    {
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      eapply (seqhyp_tm _#5 (iutruncate (S j) A)).
        {
        apply (basic_downward _#3 i); auto.
        eapply interp_increase; eauto using toppg_max.
        }

        {
        apply (basic_downward _#3 i); auto.
        eapply interp_increase; eauto using toppg_max.
        }

        {
        split; auto.
        }
      }

      {
      intros k u u' Hu.
      so (Hseqab _#3 Hu) as (pg' & A' & _ & _ & Hl & Hr & _).
      eauto.
      }
    }

    {
    invert Hel.
    intros _ _ Hact.
    so (Hact _#3 Hj Hmn) as Hmel; clear Hact.
    simpsubin Hmel.
    invert Her.
    intros _ _ Hact.
    so (Hact _#3 Hj Hmn) as Hmer; clear Hact.
    simpsubin Hmer.
    eapply seqhyp_tm; eauto using interp_increase, toppg_max.
    }

    {
    intros k u u' Hu.
    so (Hseqe _#3 Hu) as (pg' & R & _ & Hl & Hr).
    simpsubin Hl.
    simpsubin Hr.
    eauto.
    }
  }
assert (iuset stop A C = iuset stop A D) as Heq.
  {
  apply prod_extensionality; cbn; auto.
  apply urel_extensionality.
  fextensionality 3.
  intros j m n.
  cbn.
  pextensionality.
    {
    intro H.
    decompose H.
    intros p q Hmn Hpq.
    so (basic_member_index _#9 Hal Hmn) as Hj.
    so (Hext _#7 Hmn Hcl Hcr Hpq Hseqc) as Hs'.
    so (Hseqcd _#3 Hs') as (R & Hmdl & _ & Hx).
    simpsubin Hmdl.
    invert Hdl.
    intros _ _ Hact.
    so (Hact _#3 Hj Hmn) as Hmdl'.
    simpsubin Hmdl'.
    so (interp_fun _#7 Hmdl Hmdl'); subst R.
    exists (subst (dot p (dot m s)) mr), (subst (dot q (dot n s')) mr), Hmn.
    auto.
    }

    {
    intro H.
    decompose H.
    intros p q Hmn Hpq.
    so (basic_member_index _#9 Hal Hmn) as Hj.
    so (Hext _#7 Hmn Hdl Hdr Hpq Hseqd) as Hs'.
    so (Hseqdc _#3 Hs') as (R & Hmdl & _ & Hx).
    simpsubin Hmdl.
    invert Hcl.
    intros _ _ Hact.
    so (Hact _#3 Hj Hmn) as Hmdl'.
    simpsubin Hmdl'.
    so (interp_fun _#7 Hmdl Hmdl'); subst R.
    exists (subst (dot p (dot m s)) ml), (subst (dot q (dot n s')) ml), Hmn.
    auto.
    }
  }
simpsub.
do2 5 split; auto.
  {
  apply interp_eval_refl.
  apply interp_set; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_set; auto.
  }

  {
  rewrite -> Heq.
  apply interp_eval_refl.
  apply interp_set; auto.
  }

  {
  rewrite -> Heq.
  apply interp_eval_refl.
  apply interp_set; auto.
  }
Qed.               


Lemma sound_set_formation :
  forall G a a' b b' mr ml,
    pseq G (deqtype a a')
    -> pseq (cons (hyp_tm a) G) (deqtype b b)
    -> pseq (cons (hyp_tm a) G) (deqtype b' b')
    (* b implies b' *)
    -> pseq (hyp_tm b :: hyp_tm a :: G)
         (deq mr mr (subst sh1 b'))
    (* b' implies b *)
    -> pseq (hyp_tm b' :: hyp_tm a :: G)
         (deq ml ml (subst sh1 b))
    -> pseq G (deqtype (set a b) (set a' b')).
Proof.
intros G a b c d mr ml.
revert G.
refine (seq_pseq 4 [] a [] b [hyp_emp] c [hyp_emp] d 5 [] _ [_] _ [_] _ [_; _] _ [_; _] _ _ _); cbn.
intros G Hcla Hclb Hclc Hcld Hseqab Hseqc Hseqd Hseqcd Hseqdc.
rewrite -> seq_eqtype in Hseqab, Hseqc, Hseqd |- *.
rewrite -> seq_deq in Hseqcd, Hseqdc.
exploit (sound_set_formation_main None G a b c d mr ml) as H; auto.
  {
  intros i s s' Hs.
  so (Hseqab _#3 Hs) as (R & H).
  exists toppg, R.
  do2 2 split; auto; cbn; auto.
  }

  {
  intros i s s' Hs.
  so (Hseqc _#3 Hs) as (R & Hl & Hr & _).
  exists toppg, R.
  split; auto.
  cbn.
  reflexivity.
  }

  {
  intros i s s' Hs.
  so (Hseqd _#3 Hs) as (R & Hl & Hr & _).
  exists toppg, R.
  split; auto.
  cbn.
  reflexivity.
  }

  {
  intros i s s' Hs.
  so (Hseqcd _#3 Hs) as (R & Hl & Hr & Hm & _).
  eauto.
  }

  {
  intros i s s' Hs.
  so (Hseqdc _#3 Hs) as (R & Hl & Hr & Hm & _).
  eauto.
  }
intros i s s' Hs.
so (H _#3 Hs) as (pg & R & Hlv & _ & H').
cbn in Hlv.
subst pg.
eauto.
Qed.


Lemma sound_iset_formation :
  forall G a a' b b',
    pseq G (deqtype a a')
    -> pseq (cons (hyp_tm a) G) (deqtype b b')
    -> pseq G (deqtype (iset a b) (iset a' b')).
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
exists (iuiset stop A C).
simpsub.
do2 3 split; auto;
apply interp_eval_refl;
apply interp_iset; auto.
Qed.


Lemma sound_set_formation_univ :
  forall G lv a a' b b' mr ml,
    pseq G (deq a a' (univ lv))
    -> pseq (cons (hyp_tm a) G) (deq b b (univ (subst sh1 lv)))
    -> pseq (cons (hyp_tm a) G) (deq b' b' (univ (subst sh1 lv)))
    (* b implies b' *)
    -> pseq (hyp_tm b :: hyp_tm a :: G)
         (deq mr mr (subst sh1 b'))
    (* b' implies b *)
    -> pseq (hyp_tm b' :: hyp_tm a :: G)
         (deq ml ml (subst sh1 b))
    -> pseq G (deq (set a b) (set a' b') (univ lv)).
Proof.
intros G lv a b c d mr ml.
revert G.
refine (seq_pseq 4 [] a [] b [hyp_emp] c [hyp_emp] d 5 [] _ [_] _ [_] _ [_; _] _ [_; _] _ _ _); cbn.
intros G Hcla Hclb Hclc Hcld Hseqab Hseqc Hseqd Hseqcd Hseqdc.
rewrite -> seq_univ in Hseqab, Hseqc, Hseqd |- *.
rewrite -> seq_deq in Hseqcd, Hseqdc.
exploit (sound_set_formation_main (Some lv) G a b c d mr ml) as H; auto.
  {
  intros i s s' Hs.
  so (Hseqc _#3 Hs) as (pg & R & Hlv & _ & Hl & Hr & _).
  exists pg, R.
  split; auto.
  unfold pgointerp.
  simpsubin Hlv.
  exact Hlv.
  }

  {
  intros i s s' Hs.
  so (Hseqd _#3 Hs) as (pg & R & Hlv & _ & Hl & Hr & _).
  exists pg, R.
  split; auto.
  unfold pgointerp.
  simpsubin Hlv.
  exact Hlv.
  }

  {
  intros i s s' Hs.
  so (Hseqcd _#3 Hs) as (R & Hl & Hr & Hm & _).
  eauto.
  }

  {
  intros i s s' Hs.
  so (Hseqdc _#3 Hs) as (R & Hl & Hr & Hm & _).
  eauto.
  }
Qed.


Lemma sound_iset_formation_univ :
  forall G lv a a' b b',
    pseq G (deq a a' (univ lv))
    -> pseq (cons (hyp_tm a) G) (deq b b' (univ (subst sh1 lv)))
    -> pseq G (deq (iset a b) (iset a' b') (univ lv)).
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
exists pg, (iuiset stop A C).
simpsub.
do2 5 split; auto;
apply interp_eval_refl;
apply interp_iset; auto.
Qed.


Lemma sound_set_intro :
  forall G a b m n p,
    pseq G (deq m n a)
    -> pseq G (deq p p (subst1 m b))
    -> pseq (hyp_tm a :: G) (deqtype b b)
    -> pseq G (deq m n (set a b)).
Proof.
intros G a b m n p.
revert G.
refine (seq_pseq 1 [hyp_emp] b 3 [] _ [] _ [_] _ _ _); cbn.
intros G Hclb Hseqmn Hseqp Hseqb.
rewrite -> seq_eqtype in Hseqb.
rewrite -> seq_deq in Hseqmn, Hseqp |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmn _#3 Hs) as (A & Hal & Har & Hm & Hn & Hmn).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr); eauto using subst_closub_under_permit.
  {
  intros j r t Hrt.
  assert (pwctx j (dot r s) (dot t s') (cons (hyp_tm a) G)) as Hss.
    {
    assert (j <= i) as Hj.
      {
      rewrite -> HeqA in Hrt.
      destruct Hrt.
      omega.
      }
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
      }

      {
      intros j' u u' Hu.
      so (Hseqmn _#3 Hu) as (R & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hss) as (R & Hbl & Hbr & _).
  exists R.
  simpsub.
  auto.
  }
so (Hseqp _#3 Hs) as (Bm & Hbml & _ & Hp & _).
simpsubin Hbml.
invert Hbl.
intros _ _ Hact.
so (Hact _#3 (le_refl _) Hm) as H.
simpsubin H.
so (basic_fun _#7 H Hbml); subst Bm; clear H Hbml.
exists (iuset stop A B).
simpsub.
do2 4 split;
try (apply interp_eval_refl;
     apply interp_set; auto).
  {
  cbn.
  exists (subst s p), (subst s' p), Hm.
  auto.
  }

  {
  cbn.
  exists (subst s p), (subst s' p), Hn.
  force_exact Hp.
  do 3 f_equal.
  apply urelspinj_equal; auto.
  }


  {
  cbn.
  exists (subst s p), (subst s' p), Hmn.
  force_exact Hp.
  do 3 f_equal.
  apply urelspinj_equal; auto.
  }
Qed.


Lemma sound_iset_intro :
  forall G a b m n p,
    pseq G (deq m n a)
    -> pseq G (deq p p (subst1 m b))
    -> pseq (hyp_tm a :: G) (deqtype b b)
    -> pseq G (deq m n (iset a b)).
Proof.
intros G a b m n p.
revert G.
refine (seq_pseq 1 [hyp_emp] b 3 [] _ [] _ [_] _ _ _); cbn.
intros G Hclb Hseqmn Hseqp Hseqb.
rewrite -> seq_eqtype in Hseqb.
rewrite -> seq_deq in Hseqmn, Hseqp |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmn _#3 Hs) as (A & Hal & Har & Hm & Hn & Hmn).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr); eauto using subst_closub_under_permit.
  {
  intros j r t Hrt.
  assert (pwctx j (dot r s) (dot t s') (cons (hyp_tm a) G)) as Hss.
    {
    assert (j <= i) as Hj.
      {
      rewrite -> HeqA in Hrt.
      destruct Hrt.
      omega.
      }
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
      }

      {
      intros j' u u' Hu.
      so (Hseqmn _#3 Hu) as (R & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hss) as (R & Hbl & Hbr & _).
  exists R.
  simpsub.
  auto.
  }
so (Hseqp _#3 Hs) as (Bm & Hbml & _ & Hp & _).
simpsubin Hbml.
invert Hbl.
intros _ _ Hact.
so (Hact _#3 (le_refl _) Hm) as H.
simpsubin H.
so (basic_fun _#7 H Hbml); subst Bm; clear H Hbml.
exists (iuiset stop A B).
simpsub.
do2 4 split;
try (apply interp_eval_refl;
     apply interp_iset; auto).
  {
  cbn.
  exists (subst s p), (subst s' p), Hm.
  auto.
  }

  {
  cbn.
  exists (subst s p), (subst s' p), Hn.
  force_exact Hp.
  do 3 f_equal.
  apply urelspinj_equal; auto.
  }


  {
  cbn.
  exists (subst s p), (subst s' p), Hmn.
  force_exact Hp.
  do 3 f_equal.
  apply urelspinj_equal; auto.
  }
Qed.


Lemma sound_set_elim1 :
  forall G a b m n,
    pseq G (deq m n (set a b))
    -> pseq G (deq m n a).
Proof.
intros G a b m n.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (Hseq i s s' Hs) as (R & Hl & Hr & Hm & Hn & Hmn); clear Hseq.
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_set Hl).
intros A B Ha Hb Heq1.
invert (basic_value_inv _#6 value_set Hr).
intros A' B' Ha' Hb' Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iuset_inj _#5 Heq); subst A'.
exists A.
do2 4 split; auto.
  {
  cbn in Hm.
  decompose Hm.
  intros _ _ H _.
  auto.
  }

  {
  cbn in Hn.
  decompose Hn.
  intros _ _ H _.
  auto.
  }

  {
  cbn in Hmn.
  decompose Hmn.
  intros _ _ H _.
  auto.
  }
Qed.


Lemma sound_iset_elim1 :
  forall G a b m n,
    pseq G (deq m n (iset a b))
    -> pseq G (deq m n a).
Proof.
intros G a b m n.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (Hseq i s s' Hs) as (R & Hl & Hr & Hm & Hn & Hmn); clear Hseq.
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_iset Hl).
intros A B Ha Hb Heq1.
invert (basic_value_inv _#6 value_iset Hr).
intros A' B' Ha' Hb' Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iuiset_inj _#5 Heq) as Heq'.
injectionT Heq'.
intros <-.
exists A.
do2 4 split; auto.
  {
  cbn in Hm.
  decompose Hm.
  intros _ _ H _.
  auto.
  }

  {
  cbn in Hn.
  decompose Hn.
  intros _ _ H _.
  auto.
  }

  {
  cbn in Hmn.
  decompose Hmn.
  intros _ _ H _.
  auto.
  }
Qed.


Lemma sound_set_elim2 :
  forall G a b m J,
    pseq G (deq m m (set a b))
    -> pseq (hyp_tm a :: G) (deqtype b b)
    -> pseq (hyp_tm (subst1 m b) :: G) (substj sh1 J)
    -> pseq G J.
Proof.
intros G a b m J.
revert G.
refine (seq_pseq 0 3 [] _ [_] _ [_] _ _ _); cbn.
intros G Hseqm Hseqb Hseqnp.
rewrite -> seq_eqtype in Hseqb.
destruct J as [n p c].
simpsubin Hseqnp.
rewrite -> seq_deq in Hseqm, Hseqnp |- *.
assert (forall i s s',
          pwctx i s s' G
          -> pwctx i (dot (subst s m) s) (dot (subst s' m) s') (hyp_tm a :: G)) as Hsm.
  {
  intros i s s' Hs.
  apply pwctx_cons_tm_seq; auto.
    {
    so (Hseqm _#3 Hs) as (R & Hl & Hr & Hm & _).
    simpsubin Hl.
    simpsubin Hr.
    invert (basic_value_inv _#6 value_set Hl).
    intros A B Hal _ Heq1.
    invert (basic_value_inv _#6 value_set Hr).
    intros A' B' Har _ Heq2.
    so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
    clear Heq2.
    subst R.
    so (iuset_inj _#5 Heq); subst A'.
    cbn in Hm.
    decompose Hm.
    intros _ _ Hm' _.
    apply (seqhyp_tm _#5 A); auto.
    }

    {
    intros j u u' Hu.
    so (Hseqm _#3 Hu) as (R & Hl & Hr & Hm & _).
    simpsubin Hl.
    simpsubin Hr.
    invert (basic_value_inv _#6 value_set Hl).
    intros A B Hal _ Heq1.
    invert (basic_value_inv _#6 value_set Hr).
    intros A' B' Har _ Heq2.
    so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
    clear Heq2.
    so (iuset_inj _#5 Heq); subst A'.
    eauto.
    }
  }
intros i s s' Hs.
so (Hseqm _#3 Hs) as (R & Hl & Hr & Hm & _).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_set Hl); clear Hl.
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_set Hr); clear Hr.
intros A' B' Har _ Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iuset_inj _#5 Heq); subst A'.
clear B' Heq.
cbn in Hm.
decompose Hm.
intros q r Hm Hqr.
assert (pwctx i (dot q s) (dot r s') (hyp_tm (subst1 m b) :: G)) as Hsqr.
  {
  apply pwctx_cons_tm_seq; auto.
    {
    simpsub.
    apply (seqhyp_tm _#5 (pi1 B (urelspinj _#4 Hm))); auto.
      {
      invert Hbl.
      intros _ _ Hact.
      so (Hact _#3 (le_refl _) Hm) as H.
      simpsubin H.
      exact H.
      }

      {
      invert Hbl.
      intros _ _ Hact.
      so (Hact _#3 (le_refl _) Hm) as Hbml.
      so (Hseqb _#3 (Hsm _#3 Hs)) as (Bm & Hbml' & Hbmr & _).
      simpsubin Hbml.
      simpsubin Hbml'.
      so (basic_fun _#7 Hbml Hbml'); subst Bm.
      exact Hbmr.
      }
    }

    {
    intros j u u' Hu.
    so (Hseqb _#3 (Hsm _#3 Hu)) as (R & Hl & Hr & _).
    simpsub.
    eauto.
    }
  }
so (Hseqnp _#3 Hsqr) as (C & Hcl & Hcr & Hn & Hp & Hnp).
simpsubin Hcl.
simpsubin Hcr.
simpsubin Hn.
simpsubin Hp.
simpsubin Hnp.
exists C.
do2 4 split; auto.
Qed.


Lemma sound_iset_elim2 :
  forall G a b m J,
    pseq G (deq m m (iset a b))
    -> pseq (hyp_tm (subst1 m b) :: G) (substj sh1 J)
    -> pseq G J.
Proof.
intros G a b m J.
revert G.
refine (seq_pseq 0 2 [] _ [_] _ _ _); cbn.
intros G Hseqm Hseqnp.
destruct J as [n p c].
simpsubin Hseqnp.
rewrite -> seq_deq in Hseqm, Hseqnp |- *.
assert (forall i s s',
          pwctx i s s' G
          -> pwctx i (dot (subst s m) s) (dot (subst s' m) s') (hyp_tm a :: G)) as Hsm.
  {
  intros i s s' Hs.
  apply pwctx_cons_tm_seq; auto.
    {
    so (Hseqm _#3 Hs) as (R & Hl & Hr & Hm & _).
    simpsubin Hl.
    simpsubin Hr.
    invert (basic_value_inv _#6 value_iset Hl).
    intros A B Hal _ Heq1.
    invert (basic_value_inv _#6 value_iset Hr).
    intros A' B' Har _ Heq2.
    so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
    clear Heq2.
    subst R.
    so (iuiset_inj _#5 Heq) as Heq'.
    injectionT Heq'.
    intros <-.
    cbn in Hm.
    decompose Hm.
    intros _ _ Hm' _.
    apply (seqhyp_tm _#5 A); auto.
    }

    {
    intros j u u' Hu.
    so (Hseqm _#3 Hu) as (R & Hl & Hr & Hm & _).
    simpsubin Hl.
    simpsubin Hr.
    invert (basic_value_inv _#6 value_iset Hl).
    intros A B Hal _ Heq1.
    invert (basic_value_inv _#6 value_iset Hr).
    intros A' B' Har _ Heq2.
    so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
    clear Heq2.
    so (iuiset_inj _#5 Heq) as Heq'.
    injectionT Heq'.
    intros <-.
    eauto.
    }
  }
intros i s s' Hs.
so (Hseqm _#3 Hs) as (R & Hl & Hr & Hm & _).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_iset Hl); clear Hl.
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_iset Hr); clear Hr.
intros A' B' Har Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iuiset_inj _#5 Heq) as Heq'.
injectionT Heq'.
intros <-.
injectionT Heq'.
intros <-.
clear Heq.
cbn in Hm.
decompose Hm.
intros q r Hm Hqr.
assert (pwctx i (dot q s) (dot r s') (hyp_tm (subst1 m b) :: G)) as Hsqr.
  {
  apply pwctx_cons_tm_seq; auto.
    {
    simpsub.
    apply (seqhyp_tm _#5 (pi1 B (urelspinj _#4 Hm))); auto.
      {
      invert Hbl.
      intros _ _ Hact.
      so (Hact _#3 (le_refl _) Hm) as H.
      simpsubin H.
      exact H.
      }

      {
      invert Hbr.
      intros _ _ Hact.
      so (Hact _#3 (le_refl _) Hm) as H.
      simpsubin H.
      exact H.
      }
    }
    
    {
    clear i s s' A B q r Hs Hal Hbl Har Hbr Hm Hqr.
    intros i s s' Hs.
    so (Hseqm _#3 Hs) as (R & Hl & Hr & Hm & _).
    simpsubin Hl.
    simpsubin Hr.
    invert (basic_value_inv _#6 value_iset Hl).
    intros A B Hal Hbl Heq1.
    invert (basic_value_inv _#6 value_iset Hr).
    intros A' B' Har Hbr Heq2.
    so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
    clear Heq2.
    so (iuiset_inj _#5 Heq) as Heq'.
    injectionT Heq'.
    intros <-.
    injectionT Heq'.
    intros <-.
    subst R.
    clear Heq.
    cbn in Hm.
    decompose Hm.
    intros _ _ Hm _.
    exists toppg.
    exists (pi1 B (urelspinj (den A) i (subst s m) (subst s' m) Hm)).
    split.
      {
      invert Hbl.
      intros _ _ Hact.
      so (Hact _ _ _ (le_refl _) Hm) as H.
      simpsubin H.
      simpsub.
      exact H.
      }

      {
      invert Hbr.
      intros _ _ Hact.
      so (Hact _ _ _ (le_refl _) Hm) as H.
      simpsubin H.
      simpsub.
      exact H.
      }
    }
  }
so (Hseqnp _#3 Hsqr) as (C & Hcl & Hcr & Hn & Hp & Hnp).
simpsubin Hcl.
simpsubin Hcr.
simpsubin Hn.
simpsubin Hp.
simpsubin Hnp.
exists C.
do2 4 split; auto.
Qed.


Lemma interp_set_invert :
  forall pg s s' i a a' b b' R,
    interp pg s i (set a b) R
    -> interp pg s' i (set a' b') R
    -> exists A,
         interp pg s i a A
         /\ interp pg s' i a' A.
Proof.
intros pg s s' i a a' b b' R Hl Hr.
invert (basic_value_inv _#6 value_set Hl).
intros A B Hal _ Heq1.
invert (basic_value_inv _#6 value_set Hr).
intros A' B' Hal' _ Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq1 Heq2.
so (iuset_inj _#5 Heq); subst A'.
eauto.
Qed.


Lemma interp_iset_invert1 :
  forall pg s s' i a a' b b' R,
    interp pg s i (iset a b) R
    -> interp pg s' i (iset a' b') R
    -> exists A,
         interp pg s i a A
         /\ interp pg s' i a' A.
Proof.
intros pg s s' i a a' b b' R Hl Hr.
invert (basic_value_inv _#6 value_iset Hl).
intros A B Hal _ Heq1.
invert (basic_value_inv _#6 value_iset Hr).
intros A' B' Hal' _ Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq1 Heq2.
so (iuiset_inj _#5 Heq) as Heq'.
injectionT Heq'.
intros <-.
eauto.
Qed.


Lemma sound_set_hyp_weaken :
  forall G1 G2 a b J,
    pseq (G2 ++ hyp_tm b :: hyp_tm a :: G1) J
    -> pseq (G2 ++ hyp_tm b :: hyp_tm (set a b) :: G1) J.
Proof.
intros G1 G2 a b J.
revert G1.
refine (seq_pseq_hyp 0 1 _ [_; _] _ _ [_; _] _ _); cbn.
intros G Hseq HclJ.
replace J with (substj (under (length G2) id) J) in Hseq by (simpsub; reflexivity).
replace G2 with (substctx id G2) in Hseq by (simpsub; reflexivity).
eapply (subsume_seq _ _ (under (length G2) id)); eauto.
rewrite -> length_substctx.
apply subsume_under.
do2 2 split.
  {
  intros j.
  split.
    {
    intros Hj.
    simpsub.
    apply hygiene_var.
    rewrite -> ctxpred_length in Hj |- *.
    cbn in Hj |- *.
    omega.
    }

    {
    intros Hj.
    simpsub.
    simpsubin Hj.
    invertc Hj.
    intro Hj.
    rewrite -> ctxpred_length in Hj |- *.
    cbn in Hj |- *.
    omega.
    }
  }

  {
  intros j.
  split.
    {
    intros Hj.
    simpsub.
    apply hygiene_var.
    rewrite -> ctxpred_length in Hj |- *.
    cbn in Hj |- *.
    omega.
    }

    {
    intros Hj.
    simpsub.
    simpsubin Hj.
    invertc Hj.
    intro Hj.
    rewrite -> ctxpred_length in Hj |- *.
    cbn in Hj |- *.
    omega.
    }
  }
intros i ss ss' Hss.
invertc Hss.
intros p q ss2 ss2' Hss Hpq Hleft2 Hright2 <- <-.
invertc Hss.
intros m n s s' Hs Hmn Hleft1 Hright1 <- <-.
simpsubin Hmn.
invertc Hmn.
intros R Hsetl Hsetr Hmn.
invertc Hpq.
intros Bm Hbml Hbnr Hpq.
invert (basic_value_inv _#6 value_set Hsetl).
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_set Hsetr).
intros A' B' Har Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iuset_inj _#5 Heq); subst A'; clear Heq.
so Hmn as Hmnset.
cbn in Hmn.
decompose Hmn.
intros _ _ Hmn _.
invert Hbl.
intros _ _ Hact.
so (Hact _ _ _ (le_refl _) Hmn) as H; clear Hact.
simpsubin H.
so (basic_fun _#7 Hbml H); subst Bm; clear H.
do2 4 split.
  {
  simpsub.
  apply pwctx_cons_tm.
    {
    apply pwctx_cons_tm; auto.
      {
      eapply seqhyp_tm; eauto.
      }

      {
      intros j u Hj Hu.
      exploit (Hleft1 j false u) as H; auto using smaller_le, pwctx_impl_seqctx.
      rewrite -> qpromote_hyp_tm in H.
      simpsubin H.
      invertc H.
      intros R Hsetr' Hsetu.
      so (interp_set_invert _#9 Hsetr' Hsetu) as (A' & Har' & Hau).
      eapply relhyp_tm; eauto.
      }

      {
      intros j u Hj Hu.
      exploit (Hright1 j false u) as H; auto using smaller_le, pwctx_impl_seqctx.
      rewrite -> qpromote_hyp_tm in H.
      simpsubin H.
      invertc H.
      intros R Hsetu Hsetl'.
      so (interp_set_invert _#9 Hsetu Hsetl') as (A' & Har' & Hau).
      eapply relhyp_tm; eauto.
      }
    }

    {
    eapply seqhyp_tm; eauto.
    }

    {
    intros j uu Hj Huu.
    exploit (Hleft2 j false uu) as H; auto using smaller_le, pwctx_impl_seqctx.
    rewrite -> qpromote_cons.
    cbn.
    invertc Huu.
    intros n' u Hu Hmn' _ _ <-.
    apply seqctx_cons; auto using pwctx_impl_seqctx.
    simpsub.
    simpsubin Hmn'.
    invertc Hmn'.
    intros A' Hal' Hau Hmn'.
    so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst A'; clear Hal'.
    apply (seqhyp_tm _#5 (iutruncate (S j) (iuset _ A B))).
      {
      eapply basic_downward; eauto.
      }

      {
      exploit (Hleft1 j false u) as H; auto using smaller_le, pwctx_impl_seqctx.
      rewrite -> qpromote_hyp_tm in H.
      simpsubin H.
      invertc H.
      intros R Hsetr' Hsetu.
      so (basic_fun _#7 (basic_downward _#7 Hj Hsetr) Hsetr'); subst R.
      exact Hsetu.
      }
    
      {
      cbn.
      split; [omega |].
      destruct Hmn' as (_ & Hmn').
      exists p, q, Hmn'.
      refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hpq)).
      apply den_nonexpansive.
      apply (pi2 B).
      apply urelspinj_dist_diff; auto.
      }
    }

    {
    intros j uu Hj Huu.
    exploit (Hright2 j false uu) as H; auto using smaller_le, pwctx_impl_seqctx.
    rewrite -> qpromote_cons.
    cbn.
    invertc Huu.
    intros m' u Hu Hmn' _ _ <-.
    apply seqctx_cons; auto using pwctx_impl_seqctx.
    simpsub.
    simpsubin Hmn'.
    invertc Hmn'.
    intros A' Hau Har' Hmn'.
    so (basic_fun _#7 (basic_downward _#7 Hj Har) Har'); subst A'; clear Har'.
    apply (seqhyp_tm _#5 (iutruncate (S j) (iuset _ A B))).
    2:{
      eapply basic_downward; eauto.
      }

      {
      exploit (Hright1 j false u) as H; auto using smaller_le, pwctx_impl_seqctx.
      rewrite -> qpromote_hyp_tm in H.
      simpsubin H.
      invertc H.
      intros R Hsetl' Hsetu.
      so (basic_fun _#7 (basic_downward _#7 Hj Hsetl) Hsetl'); subst R.
      exact Hsetu.
      }
    
      {
      cbn.
      split; [omega |].
      destruct Hmn' as (_ & Hmn').
      exists p, q, Hmn'.
      refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hpq)).
      apply den_nonexpansive.
      apply (pi2 B).
      apply urelspinj_dist_diff; auto.
      eapply urel_downward_leq; eauto.
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
  so (smaller_impl_le _#3 Hsmall) as Hj.
  simpsubin Huu.
  simpsub.
  rewrite -> !qpromote_cons in Huu |- *.
  rewrite -> !qpromote_hyp_tm in Huu |- *.
  invertc Huu.
  intros q' uu2 Huu Hpq' <-.
  invertc Huu.
  intros n' u Hu Hmn' <-.
  apply seqctx_cons.
    {
    apply seqctx_cons; auto.
    simpsub.
    apply (seqhyp_tm _#5 (iutruncate (S j) (iuset stop A B))).
      {
      apply (basic_downward _#3 i); auto.
      }

      {
      exploit (Hleft1 j d u) as H; auto.
      rewrite -> qpromote_hyp_tm in H.
      simpsubin H.
      simpsub.
      invertc H.
      intros R Hsetr' Hsetu.
      so (basic_fun _#7 (basic_downward _#7 Hj Hsetr) Hsetr'); subst R.
      auto.
      }

      {
      split; auto.
      cbn.
      simpsubin Hmn'.
      invertc Hmn'.
      intros R Hal' _ Hmn'.
      so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst R.
      destruct Hmn' as (_ & Hmn').
      exists p, q, Hmn'.
      refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hpq)).
      apply den_nonexpansive.
      apply (pi2 B).
      apply urelspinj_dist_diff; auto.
      }
    }

    {
    simpsub.
    invertc Hmn'.
    intros R Hal' _ Hmn'.
    so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst R.
    destruct Hmn' as (_ & Hmn').
    invert Hbl.
    intros _ _ Hact.
    so (Hact _#3 Hj Hmn') as Hmblj; clear Hact.
    simpsubin Hmblj.
    simpsubin Hpq'.
    invertc Hpq'.
    intros R Hmblj' Hmbu Hpq'.
    so (basic_fun _#7 Hmblj Hmblj'); subst R.
    apply (seqhyp_tm _#5 (pi1 B (urelspinj _#4 Hmn'))); auto.
    }
  }

  {
  intros j d uu Hsmall Huu.
  so (smaller_impl_le _#3 Hsmall) as Hj.
  simpsubin Huu.
  simpsub.
  rewrite -> !qpromote_cons in Huu |- *.
  rewrite -> !qpromote_hyp_tm in Huu |- *.
  invertc Huu.
  intros p' uu2 Huu Hpq' <-.
  invertc Huu.
  intros m' u Hu Hmn' <-.
  apply seqctx_cons.
    {
    apply seqctx_cons; auto.
    simpsub.
    apply (seqhyp_tm _#5 (iutruncate (S j) (iuset stop A B))).
      {
      exploit (Hright1 j d u) as H; auto.
      rewrite -> qpromote_hyp_tm in H.
      simpsubin H.
      simpsub.
      invertc H.
      intros R Hsetl' Hsetu.
      so (basic_fun _#7 (basic_downward _#7 Hj Hsetl) Hsetl'); subst R.
      auto.
      }

      {
      apply (basic_downward _#3 i); auto.
      }

      {
      split; auto.
      cbn.
      simpsubin Hmn'.
      invertc Hmn'.
      intros R _ Har' Hmn'.
      so (basic_fun _#7 (basic_downward _#7 Hj Har) Har'); subst R.
      destruct Hmn' as (_ & Hmn').
      exists p, q, Hmn'.
      refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hpq)).
      apply den_nonexpansive.
      apply (pi2 B).
      apply urelspinj_dist_diff; auto.
      eapply urel_downward_leq; eauto.
      }
    }

    {
    simpsub.
    invertc Hmn'.
    intros R _ Har' Hmn'.
    so (basic_fun _#7 (basic_downward _#7 Hj Har) Har'); subst R.
    destruct Hmn' as (_ & Hmn').
    invert Hbr.
    intros _ _ Hact.
    so (Hact _#3 Hj Hmn') as Hmblj; clear Hact.
    simpsubin Hmblj.
    simpsubin Hpq'.
    invertc Hpq'.
    intros R Hmbu Hmblj' Hpq'.
    so (basic_fun _#7 Hmblj Hmblj'); subst R.
    apply (seqhyp_tm _#5 (pi1 B' (urelspinj _#4 Hmn'))); auto.
    }
  }
Qed.


Lemma sound_iset_hyp_weaken :
  forall G1 G2 a b J,
    pseq (G2 ++ hyp_tm b :: hyp_tm a :: G1) J
    -> pseq (G2 ++ hyp_tm b :: hyp_tm (iset a b) :: G1) J.
Proof.
intros G1 G2 a b J.
revert G1.
refine (seq_pseq_hyp 0 1 _ [_; _] _ _ [_; _] _ _); cbn.
intros G Hseq HclJ.
replace J with (substj (under (length G2) id) J) in Hseq by (simpsub; reflexivity).
replace G2 with (substctx id G2) in Hseq by (simpsub; reflexivity).
eapply (subsume_seq _ _ (under (length G2) id)); eauto.
rewrite -> length_substctx.
apply subsume_under.
do2 2 split.
  {
  intros j.
  split.
    {
    intros Hj.
    simpsub.
    apply hygiene_var.
    rewrite -> ctxpred_length in Hj |- *.
    cbn in Hj |- *.
    omega.
    }

    {
    intros Hj.
    simpsub.
    simpsubin Hj.
    invertc Hj.
    intro Hj.
    rewrite -> ctxpred_length in Hj |- *.
    cbn in Hj |- *.
    omega.
    }
  }

  {
  intros j.
  split.
    {
    intros Hj.
    simpsub.
    apply hygiene_var.
    rewrite -> ctxpred_length in Hj |- *.
    cbn in Hj |- *.
    omega.
    }

    {
    intros Hj.
    simpsub.
    simpsubin Hj.
    invertc Hj.
    intro Hj.
    rewrite -> ctxpred_length in Hj |- *.
    cbn in Hj |- *.
    omega.
    }
  }
intros i ss ss' Hss.
invertc Hss.
intros p q ss2 ss2' Hss Hpq Hleft2 Hright2 <- <-.
invertc Hss.
intros m n s s' Hs Hmn Hleft1 Hright1 <- <-.
simpsubin Hmn.
invertc Hmn.
intros R Hsetl Hsetr Hmn.
invertc Hpq.
intros Bm Hbml Hbnr Hpq.
invert (basic_value_inv _#6 value_iset Hsetl).
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_iset Hsetr).
intros A' B' Har Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iuiset_inj _#5 Heq) as Heq'.
injectionT Heq'.
intros <-.
so Hmn as Hmnset.
cbn in Hmn.
decompose Hmn.
intros _ _ Hmn _.
invert Hbl.
intros _ _ Hact.
so (Hact _ _ _ (le_refl _) Hmn) as H; clear Hact.
simpsubin H.
so (basic_fun _#7 Hbml H); subst Bm; clear H.
do2 4 split.
  {
  simpsub.
  apply pwctx_cons_tm.
    {
    apply pwctx_cons_tm; auto.
      {
      eapply seqhyp_tm; eauto.
      }

      {
      intros j u Hj Hu.
      exploit (Hleft1 j false u) as H; auto using smaller_le, pwctx_impl_seqctx.
      rewrite -> qpromote_hyp_tm in H.
      simpsubin H.
      invertc H.
      intros R Hsetr' Hsetu.
      so (interp_iset_invert1 _#9 Hsetr' Hsetu) as (A' & Har' & Hau).
      eapply relhyp_tm; eauto.
      }

      {
      intros j u Hj Hu.
      exploit (Hright1 j false u) as H; auto using smaller_le, pwctx_impl_seqctx.
      rewrite -> qpromote_hyp_tm in H.
      simpsubin H.
      invertc H.
      intros R Hsetu Hsetl'.
      so (interp_iset_invert1 _#9 Hsetu Hsetl') as (A' & Har' & Hau).
      eapply relhyp_tm; eauto.
      }
    }

    {
    eapply seqhyp_tm; eauto.
    }

    {
    intros j uu Hj Huu.
    exploit (Hleft2 j false uu) as H; auto using smaller_le, pwctx_impl_seqctx.
    rewrite -> qpromote_cons.
    cbn.
    invertc Huu.
    intros n' u Hu Hmn' _ _ <-.
    apply seqctx_cons; auto using pwctx_impl_seqctx.
    simpsub.
    simpsubin Hmn'.
    invertc Hmn'.
    intros A' Hal' Hau Hmn'.
    so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst A'; clear Hal'.
    apply (seqhyp_tm _#5 (iutruncate (S j) (iuiset _ A B))).
      {
      eapply basic_downward; eauto.
      }

      {
      exploit (Hleft1 j false u) as H; auto using smaller_le, pwctx_impl_seqctx.
      rewrite -> qpromote_hyp_tm in H.
      simpsubin H.
      invertc H.
      intros R Hsetr' Hsetu.
      so (basic_fun _#7 (basic_downward _#7 Hj Hsetr) Hsetr'); subst R.
      exact Hsetu.
      }
    
      {
      cbn.
      split; [omega |].
      destruct Hmn' as (_ & Hmn').
      exists p, q, Hmn'.
      refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hpq)).
      apply den_nonexpansive.
      apply (pi2 B).
      apply urelspinj_dist_diff; auto.
      }
    }

    {
    intros j uu Hj Huu.
    exploit (Hright2 j false uu) as H; auto using smaller_le, pwctx_impl_seqctx.
    rewrite -> qpromote_cons.
    cbn.
    invertc Huu.
    intros m' u Hu Hmn' _ _ <-.
    apply seqctx_cons; auto using pwctx_impl_seqctx.
    simpsub.
    simpsubin Hmn'.
    invertc Hmn'.
    intros A' Hau Har' Hmn'.
    so (basic_fun _#7 (basic_downward _#7 Hj Har) Har'); subst A'; clear Har'.
    apply (seqhyp_tm _#5 (iutruncate (S j) (iuiset _ A B))).
    2:{
      eapply basic_downward; eauto.
      }

      {
      exploit (Hright1 j false u) as H; auto using smaller_le, pwctx_impl_seqctx.
      rewrite -> qpromote_hyp_tm in H.
      simpsubin H.
      invertc H.
      intros R Hsetl' Hsetu.
      so (basic_fun _#7 (basic_downward _#7 Hj Hsetl) Hsetl'); subst R.
      exact Hsetu.
      }
    
      {
      cbn.
      split; [omega |].
      destruct Hmn' as (_ & Hmn').
      exists p, q, Hmn'.
      refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hpq)).
      apply den_nonexpansive.
      apply (pi2 B).
      apply urelspinj_dist_diff; auto.
      eapply urel_downward_leq; eauto.
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
  so (smaller_impl_le _#3 Hsmall) as Hj.
  simpsubin Huu.
  simpsub.
  rewrite -> !qpromote_cons in Huu |- *.
  rewrite -> !qpromote_hyp_tm in Huu |- *.
  invertc Huu.
  intros q' uu2 Huu Hpq' <-.
  invertc Huu.
  intros n' u Hu Hmn' <-.
  apply seqctx_cons.
    {
    apply seqctx_cons; auto.
    simpsub.
    apply (seqhyp_tm _#5 (iutruncate (S j) (iuiset stop A B))).
      {
      apply (basic_downward _#3 i); auto.
      }

      {
      exploit (Hleft1 j d u) as H; auto.
      rewrite -> qpromote_hyp_tm in H.
      simpsubin H.
      simpsub.
      invertc H.
      intros R Hsetr' Hsetu.
      so (basic_fun _#7 (basic_downward _#7 Hj Hsetr) Hsetr'); subst R.
      auto.
      }

      {
      split; auto.
      cbn.
      simpsubin Hmn'.
      invertc Hmn'.
      intros R Hal' _ Hmn'.
      so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst R.
      destruct Hmn' as (_ & Hmn').
      exists p, q, Hmn'.
      refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hpq)).
      apply den_nonexpansive.
      apply (pi2 B).
      apply urelspinj_dist_diff; auto.
      }
    }

    {
    simpsub.
    invertc Hmn'.
    intros R Hal' _ Hmn'.
    so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst R.
    destruct Hmn' as (_ & Hmn').
    invert Hbl.
    intros _ _ Hact.
    so (Hact _#3 Hj Hmn') as Hmblj; clear Hact.
    simpsubin Hmblj.
    simpsubin Hpq'.
    invertc Hpq'.
    intros R Hmblj' Hmbu Hpq'.
    so (basic_fun _#7 Hmblj Hmblj'); subst R.
    apply (seqhyp_tm _#5 (pi1 B (urelspinj _#4 Hmn'))); auto.
    }
  }

  {
  intros j d uu Hsmall Huu.
  so (smaller_impl_le _#3 Hsmall) as Hj.
  simpsubin Huu.
  simpsub.
  rewrite -> !qpromote_cons in Huu |- *.
  rewrite -> !qpromote_hyp_tm in Huu |- *.
  invertc Huu.
  intros p' uu2 Huu Hpq' <-.
  invertc Huu.
  intros m' u Hu Hmn' <-.
  apply seqctx_cons.
    {
    apply seqctx_cons; auto.
    simpsub.
    apply (seqhyp_tm _#5 (iutruncate (S j) (iuiset stop A B))).
      {
      exploit (Hright1 j d u) as H; auto.
      rewrite -> qpromote_hyp_tm in H.
      simpsubin H.
      simpsub.
      invertc H.
      intros R Hsetl' Hsetu.
      so (basic_fun _#7 (basic_downward _#7 Hj Hsetl) Hsetl'); subst R.
      auto.
      }

      {
      apply (basic_downward _#3 i); auto.
      }

      {
      split; auto.
      cbn.
      simpsubin Hmn'.
      invertc Hmn'.
      intros R _ Har' Hmn'.
      so (basic_fun _#7 (basic_downward _#7 Hj Har) Har'); subst R.
      destruct Hmn' as (_ & Hmn').
      exists p, q, Hmn'.
      refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hpq)).
      apply den_nonexpansive.
      apply (pi2 B).
      apply urelspinj_dist_diff; auto.
      eapply urel_downward_leq; eauto.
      }
    }

    {
    simpsub.
    invertc Hmn'.
    intros R _ Har' Hmn'.
    so (basic_fun _#7 (basic_downward _#7 Hj Har) Har'); subst R.
    destruct Hmn' as (_ & Hmn').
    invert Hbr.
    intros _ _ Hact.
    so (Hact _#3 Hj Hmn') as Hmblj; clear Hact.
    simpsubin Hmblj.
    simpsubin Hpq'.
    invertc Hpq'.
    intros R Hmbu Hmblj' Hpq'.
    so (basic_fun _#7 Hmblj Hmblj'); subst R.
    apply (seqhyp_tm _#5 (pi1 B' (urelspinj _#4 Hmn'))); auto.
    }
  }
Qed.


Lemma sound_set_formation_invert :
  forall G a a' b b',
    pseq G (deqtype (set a b) (set a' b'))
    -> pseq G (deqtype a a').
Proof.
intros G a b c d.
revert G.
refine (seq_pseq 0 1 [] _ _ _).
cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (Hseq _ _ _ Hs) as (R & Hacl & Hacr & Hbdl & Hbdr).
simpsubin Hacl.
invert (basic_value_inv _#6 value_set Hacl).
intros A B1 Hal _ Heq.
simpsubin Hacr.
invert (basic_value_inv _#6 value_set Hacr).
intros A' B2 Har _ Heq'.
so (eqtrans Heq (eqsymm Heq')) as H.
so (iuset_inj _#5 H); subst A'.
clear H Heq'.
simpsubin Hbdl.
invert (basic_value_inv _#6 value_set Hbdl).
intros A' B3 Hbl _ Heq'.
so (eqtrans Heq (eqsymm Heq')) as H.
so (iuset_inj _#5 H); subst A'.
clear H Heq'.
simpsubin Hbdr.
invert (basic_value_inv _#6 value_set Hbdr).
intros A' B4 Hbr _ Heq'.
so (eqtrans Heq (eqsymm Heq')) as H.
so (iuset_inj _#5 H); subst A'.
clear H Heq' Heq.
exists A.
auto.
Qed.


Lemma sound_iset_formation_invert1 :
  forall G a a' b b',
    pseq G (deqtype (iset a b) (iset a' b'))
    -> pseq G (deqtype a a').
Proof.
intros G a b c d.
revert G.
refine (seq_pseq 0 1 [] _ _ _).
cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (Hseq _ _ _ Hs) as (R & Hacl & Hacr & Hbdl & Hbdr).
simpsubin Hacl.
invert (basic_value_inv _#6 value_iset Hacl).
intros A B1 Hal _ Heq.
simpsubin Hacr.
invert (basic_value_inv _#6 value_iset Hacr).
intros A' B2 Har _ Heq'.
so (eqtrans Heq (eqsymm Heq')) as H.
so (iuiset_inj _#5 H) as Heq''.
injectionT Heq''.
intros <-.
clear H Heq' Heq''.
simpsubin Hbdl.
invert (basic_value_inv _#6 value_iset Hbdl).
intros A' B3 Hbl _ Heq'.
so (eqtrans Heq (eqsymm Heq')) as H.
so (iuiset_inj _#5 H) as Heq''.
injectionT Heq''.
intros <-.
clear H Heq' Heq''.
simpsubin Hbdr.
invert (basic_value_inv _#6 value_iset Hbdr).
intros A' B4 Hbr _ Heq'.
so (eqtrans Heq (eqsymm Heq')) as H.
so (iuiset_inj _#5 H) as Heq''.
injectionT Heq''.
intros <-.
clear H Heq' Heq Heq''.
exists A.
auto.
Qed.


Lemma sound_iset_formation_invert2 :
  forall G a a' b b',
    pseq G (deqtype (iset a b) (iset a' b'))
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
invert (basic_value_inv _#6 value_iset Hpil).
intros A B Hal Hcl Heqacl.
invert (basic_value_inv _#6 value_iset Hpir).
intros A' B' Har Hcr Heqacr.
so (eqtrans Heqacl (eqsymm Heqacr)) as Heq.
clear Heqacr.
invert (basic_value_inv _#6 value_iset Hpil').
intros A'' B'' Hbl Hdl Heqbdl.
so (eqtrans Heqacl (eqsymm Heqbdl)) as Heq'.
clear Heqbdl.
invert (basic_value_inv _#6 value_iset Hpir').
intros A''' B''' Hbr Hdr Heqbdr.
so (eqtrans Heqacl (eqsymm Heqbdr)) as Heq''.
clear Heqbdr.
subst R.
so (iuiset_inj _#5 Heq) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
so (iuiset_inj _#5 Heq') as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
so (iuiset_inj _#5 Heq'') as H.
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


Lemma unit_urel_dist :
  forall i i' j,
    j <= i
    -> j <= i'
    -> @dist (wurel_ofe stop) (S j) (unit_urel stop i) (unit_urel stop i').
Proof.
intros i i' j Hji Hji'.
intros k Hk.
fextensionality 2.
intros m p.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros _ _ Hclm Hclp Hsteps Hsteps'.
  do2 5 split; auto.
  omega.
  }

  {
  intro H.
  decompose H.
  intros _ _ Hclm Hclp Hsteps Hsteps'.
  do2 5 split; auto.
  omega.
  }
Qed.


Lemma sound_squash_idem :
  forall G a b,
    pseq G (deqtype (set a b) (set a b))
    -> pseq G (deqtype (set a b) (set a (squash b))).
Proof.
intros G a b.
revert G.
refine (seq_pseq 1 [hyp_emp] b 1 [] _ _ _); cbn.
intros G Hclb Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq _#3 Hs) as (R & Hsetl & Hsetr & _).
exists R.
do2 2 split; auto.
simpsubin Hsetl.
simpsubin Hsetr.
simpsub.
invert (basic_value_inv _#6 value_set Hsetl).
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_set Hsetr).
intros A' B' Har Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iuset_inj _#5 Heq); subst A'.
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  exact (f_equal den (basic_impl_iutruncate _#6 Hal)).
  }
set (Cf := fun (D : urelsp (den A) -n> siurel_ofe) x => iuset stop (iubase (unit_urel stop (urelsp_index _ x))) (semiconst_ne (unit_urel stop (urelsp_index _ x)) (pi1 D x))).
assert (forall D,
          @nonexpansive (urelsp (den A)) siurel_ofe (Cf D)) as Hne.
  {
  intros D j x y Hxy.
  destruct j as [| j].
    {
    apply dist_zero.
    }
  so (urelsp_eta _ _ x) as (k & m & p & Hmp & ->).
  so (urelsp_eta _ _ y) as (k' & n & q & Hnq & ->).
  unfold Cf.
  rewrite -> !urelsp_index_inj.
  so (urelspinj_dist_index' _#11 Hxy) as [(<- & Hkj) | (Hjk & Hjk')].
    {
    apply dist_refl'.
    do 3 f_equal.
    apply urelspinj_equal.
    so (urelspinj_dist_invert _#11 Hxy).
    rewrite -> Nat.min_r in H; auto.
    omega.
    }
  split; cbn -[dist].
    {
    intros j' Hj'.
    cbn.
    fextensionality 2.
    intros r t.
    pextensionality.
      {
      intro H.
      decompose H.
      intros u v Hrt Huv.
      rewrite -> urelsp_index_inj in Huv.
      exists u, v.
      assert (rel (unit_urel stop k') j' r t) as Hrt'.
        {
        refine (rel_from_dist _#6 _ Hrt).
        apply unit_urel_dist; omega.
        }
      exists Hrt'.
      rewrite -> urelsp_index_inj.
      force_exact Huv.
      f_equal.
      apply ceiling_collapse.
      apply den_nonexpansive.
      apply (pi2 D).
      apply urelspinj_dist_diff; try omega.
      so (urelspinj_dist_invert _#11 Hxy) as H.
      rewrite -> Nat.min_l in H; [| omega].
      apply (urel_downward_leq _#3 j); auto.
      omega.
      }

      {
      intro H.
      decompose H.
      intros u v Hrt Huv.
      rewrite -> urelsp_index_inj in Huv.
      exists u, v.
      assert (rel (unit_urel stop k) j' r t) as Hrt'.
        {
        refine (rel_from_dist _#6 _ Hrt).
        apply unit_urel_dist; omega.
        }
      exists Hrt'.
      rewrite -> urelsp_index_inj.
      force_exact Huv.
      f_equal.
      apply ceiling_collapse.
      apply den_nonexpansive.
      apply (pi2 D).
      apply urelspinj_dist_diff; try omega.
      so (urelspinj_dist_invert _#11 Hxy) as H.
      apply (urel_zigzag _#4 q m).
        {
        apply (urel_downward_leq _#3 k'); auto.
        omega.
        }

        {
        rewrite -> Nat.min_l in H; [| omega].
        apply (urel_downward_leq _#3 j); auto.
        omega.
        }

        {
        apply (urel_downward_leq _#3 k); auto.
        omega.
        }
      }
    }

    {
    apply meta_iurel_nonexpansive.
    split; cbn -[dist]; [| apply dist_refl].
    apply unit_urel_dist; omega.
    }
  }
set (C := fun D => ((expair (Cf D) (Hne D)) : urelsp (den A) -n> siurel_ofe)).
assert (forall D,
          iuset stop A D = iuset stop A (C D)) as Heq'.
  {
  intro D.
  apply prod_extensionality; cbn; auto.
  apply urel_extensionality.
  fextensionality 3.
  intros j m n.
  cbn.
  pextensionality.
    {
    intro H.
    decompose H.
    intros p q Hmn Hpq.
    exists triv, triv, Hmn.
    cbn.
    so (unit_urel_triv stop _ _ (le_refl j)) as Htriv.
    exists p, q.
    rewrite -> urelsp_index_inj.
    exists Htriv.
    rewrite -> !urelsp_index_inj.
    split; auto.
    }

    {
    intro H.
    decompose H.
    unfold semiconst_ne.
    cbn.
    intros p q Hmn Hpq.
    rewrite -> urelsp_index_inj in Hpq.
    decompose Hpq.
    intros r t Hpq Hrt.
    rewrite -> urelsp_index_inj in Hrt.
    exists r, t, Hmn.
    destruct Hrt as (_ & Hrt).
    exact Hrt.
    }
  }
split.
  {
  apply interp_eval_refl.
  rewrite -> Heq'.
  apply interp_set; auto.
  apply functional_i; auto.
    {
    eapply subst_closub_under_permit; eauto.
    unfold squash.
    prove_hygiene.
    }
  intros j m p Hj Hmp.
  unfold squash.
  simpsub.
  apply interp_eval_refl.
  apply interp_set.
    {
    apply interp_eval_refl.
    rewrite -> urelsp_index_inj.
    apply interp_unit.
    }
  rewrite -> urelsp_index_inj.
  apply functional_i.
    {
    eapply hygiene_subst; eauto.
    intros k Hk.
    destruct k as [| k]; simpsub.
      {
      apply hygiene_shift_permit; auto.
      exact (urel_closed _#5 Hmp andel).
      }

      {
      apply hygiene_shift_permit.
      eapply project_closub; eauto.
      }
    }

    {
    cbn.
    rewrite -> ceiling_unit.
    rewrite -> Nat.min_id.
    reflexivity.
    }
  intros j' q r Hj' Hqr.
  cbn.
  simpsub.
  invert Hbl.
  intros _ _ Hact.
  so (Hact _ _ _ (le_trans _#3 Hj' Hj) (urel_downward_leq _#6 Hj' Hmp)) as H.
  simpsubin H.
  so (basic_downward _#7 (le_refl _) H) as Hint; clear H.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  force_exact Hint.
  f_equal.
  apply iutruncate_collapse.
  apply (pi2 B).
  apply urelspinj_dist_diff; auto.
  eapply urel_downward_leq; eauto.
  }

  {
  rewrite -> Heq.
  apply interp_eval_refl.
  rewrite -> Heq'.
  apply interp_set; auto.
  apply functional_i; auto.
    {
    eapply subst_closub_under_permit; eauto.
    unfold squash.
    prove_hygiene.
    }
  intros j m p Hj Hmp.
  unfold squash.
  simpsub.
  apply interp_eval_refl.
  apply interp_set.
    {
    apply interp_eval_refl.
    rewrite -> urelsp_index_inj.
    apply interp_unit.
    }
  rewrite -> urelsp_index_inj.
  apply functional_i.
    {
    eapply hygiene_subst; eauto.
    intros k Hk.
    destruct k as [| k]; simpsub.
      {
      apply hygiene_shift_permit; auto.
      exact (urel_closed _#5 Hmp ander).
      }

      {
      apply hygiene_shift_permit.
      eapply project_closub; eauto.
      }
    }

    {
    cbn.
    rewrite -> ceiling_unit.
    rewrite -> Nat.min_id.
    reflexivity.
    }
  intros j' q r Hj' Hqr.
  cbn.
  simpsub.
  invert Hbr.
  intros _ _ Hact.
  so (Hact _ _ _ (le_trans _#3 Hj' Hj) (urel_downward_leq _#6 Hj' Hmp)) as H.
  simpsubin H.
  so (basic_downward _#7 (le_refl _) H) as Hint; clear H.
  unfold semiconst.
  rewrite -> urelsp_index_inj.
  force_exact Hint.
  f_equal.
  apply iutruncate_collapse.
  apply (pi2 B').
  apply urelspinj_dist_diff; auto.
  eapply urel_downward_leq; eauto.
  }
Qed.
