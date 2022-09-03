
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

Require Import SemanticsEqual.
Require Import ProperLevel.
Require Import Subsumption.


Local Ltac prove_hygiene :=
  repeat (apply hygiene_auto; cbn; repeat2 split; auto);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1, subst_closub;
  try (apply hygiene_var; cbn; auto; done).


Lemma sound_equal_formation :
  forall G a b m n p q,
    pseq G (deqtype a b)
    -> pseq G (deq m n a)
    -> pseq G (deq p q a)
    -> pseq G (deqtype (equal a m p) (equal b n q)).
Proof.
intros G a b m n p q.
revert G.
refine (seq_pseq 0 3 [] _ [] _ [] _ _ _); cbn.
intros G Hseqab Hseqmn Hseqpq.
rewrite -> seq_eqtype in Hseqab |- *.
rewrite -> seq_deq in Hseqmn, Hseqpq.
intros i s s' Hs.
so (Hseqab _#3 Hs) as (A & Hal & Har & Hbl & Hbr); clear Hseqab.
so (Hseqmn _#3 Hs) as (A' & Hal' & _ & Hm & Hn & Hmn); clear Hseqmn.
so (basic_fun _#7 Hal Hal'); subst A'; clear Hal'.
so (Hseqpq _#3 Hs) as (A' & Hal' & _ & Hp & Hq & Hpq).
so (basic_fun _#7 Hal Hal'); subst A'.
exists (iuequal stop true i A _#4 Hm Hp).
simpsub.
do2 3 split; auto.
  {
  apply interp_eval_refl.
  apply interp_equal; auto.
  }

  {
  apply interp_eval_refl.
  relquest.
    {
    apply (interp_equal _ _ false _#7 Hm Hp).
    exact Har.
    }
  rewrite -> (iuequal_swap _ false).
  cbn.
  apply iuequal_equal; auto.
  }

  {
  apply interp_eval_refl.
  relquest.
    {
    apply (interp_equal _ _ true _#7 Hn Hq).
    exact Hbl.
    }
  apply iuequal_equal; eauto using srel_zigzag.
  }

  {
  apply interp_eval_refl.
  relquest.
    {
    apply (interp_equal _ _ false _#7 Hn Hq).
    exact Hbr.
    }
  rewrite -> (iuequal_swap _ false).
  cbn.
  apply iuequal_equal; eauto using srel_zigzag.
  }
Qed.


Lemma sound_equal_formation_univ :
  forall G lv a b m n p q,
    pseq G (deq a b (univ lv))
    -> pseq G (deq m n a)
    -> pseq G (deq p q a)
    -> pseq G (deq (equal a m p) (equal b n q) (univ lv)).
Proof.
intros G lv a b m n p q.
revert G.
refine (seq_pseq 0 3 [] _ [] _ [] _ _ _); cbn.
intros G Hseqab Hseqmn Hseqpq.
rewrite -> seq_univ in Hseqab |- *.
rewrite -> seq_deq in Hseqmn, Hseqpq.
intros i s s' Hs.
so (Hseqab _#3 Hs) as (pg & A & Hlvl & Hlvr & Hal & Har & Hbl & Hbr); clear Hseqab.
so (Hseqmn _#3 Hs) as (A' & Hal' & _ & Hm & Hn & Hmn); clear Hseqmn.
so (basic_fun _#7 (interp_increase _#6 (toppg_max _) Hal) Hal'); subst A'; clear Hal'.
so (Hseqpq _#3 Hs) as (A' & Hal' & _ & Hp & Hq & Hpq).
so (basic_fun _#7 (interp_increase _#6 (toppg_max _) Hal) Hal'); subst A'.
exists pg, (iuequal stop true i A _#4 Hm Hp).
simpsub.
do2 5 split; auto.
  {
  apply interp_eval_refl.
  apply interp_equal; auto.
  }

  {
  apply interp_eval_refl.
  relquest.
    {
    apply (interp_equal _ _ false _#7 Hm Hp).
    exact Har.
    }
  rewrite -> (iuequal_swap _ false).
  cbn.
  apply iuequal_equal; auto.
  }

  {
  apply interp_eval_refl.
  relquest.
    {
    apply (interp_equal _ _ true _#7 Hn Hq).
    exact Hbl.
    }
  apply iuequal_equal; eauto using srel_zigzag.
  }

  {
  apply interp_eval_refl.
  relquest.
    {
    apply (interp_equal _ _ false _#7 Hn Hq).
    exact Hbr.
    }
  rewrite -> (iuequal_swap _ false).
  cbn.
  apply iuequal_equal; eauto using srel_zigzag.
  }
Qed.


Lemma sound_equal_intro :
  forall G a m n,
    pseq G (deq m n a)
    -> pseq G (deq triv triv (equal a m n)).
Proof.
intros G a m n.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (A & Hal & Har & Hm & Hn & Hmn).
exists (iuequal stop true i A (subst s m) (subst s n) (subst s' m) (subst s' n) Hm Hn).
simpsub.
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_equal; auto.
  }

  {
  apply interp_eval_refl.
  relquest.
    {
    apply (interp_equal _ _ false _#7 Hm Hn).
    exact Har.
    }
  rewrite -> (iuequal_swap _ false).
  cbn.
  apply iuequal_equal; auto.
  }

  {
  cbn.
  do2 5 split; auto using star_refl; try prove_hygiene.
  }

  {
  cbn.
  do2 5 split; auto using star_refl; try prove_hygiene.
  }

  {
  cbn.
  do2 5 split; auto using star_refl; try prove_hygiene.
  }
Qed.


Lemma sound_equal_elim :
  forall G a m n,
    pseq G (deq triv triv (equal a m n))
    -> pseq G (deq m n a).
Proof.
intros G a m n.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hequall & Hequalr & Htrue & _).
simpsubin Hequall.
simpsubin Hequalr.
invert (basic_value_inv _#6 value_equal Hequall).
intros p q A Hmp Hnq Hal Heql.
invert (basic_value_inv _#6 value_equal Hequalr).
intros p' q' A' Hmp' Hnq' Har Heqr.
so (eqtrans Heql (eqsymm Heqr)) as Heq.
clear Heqr.
subst R.
rewrite -> (iuequal_swap _ false) in Heq.
cbn in Heq.
so (iuequal_inj _#17 Heq) as (<- & Hm & Hn).
clear Heq.
exists A.
do2 4 split; auto.
destruct Htrue as ((r & Hmr & Hnr) & _).
apply (urel_zigzag _#3 _ r (subst s n)); auto.
Qed.


Lemma sound_equal_eta :
  forall G a m n p,
    pseq G (deq p p (equal a m n))
    -> pseq G (deq p triv (equal a m n)).
Proof.
intros G a m n p.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hequall & Hequalr & Htrue & _).
exists R.
do2 4 split; auto.
  {
  simpsub.
  simpsubin Hequall.
  invert (basic_value_inv _#6 value_equal Hequall).
  intros q r A Hmq Hnr _ <-.
  cbn.
  destruct Htrue as (H & _).
  do2 5 split; auto using star_refl; try prove_hygiene.
  }

  {
  simpsub.
  simpsubin Hequall.
  invert (basic_value_inv _#6 value_equal Hequall).
  intros q r A Hmq Hnr _ <-.
  cbn.
  destruct Htrue as (H & _ & Hclsp & _ & Hsteps & _).
  do2 5 split; auto using star_refl; try prove_hygiene.
  }
Qed.


Lemma sound_equal_eta_hyp :
  forall G1 G2 a p q m n b,
    pseq (substctx (dot triv id) G2 ++ G1) (deq m n (subst (under (length G2) (dot triv id)) b))
    -> pseq (G2 ++ hyp_tm (equal a p q) :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) b).
Proof.
intros G1 G2 a p q m n b Hseq.
eapply sound_property_eta_hyp; eauto.
intros s pg z i R H.
simpsubin H.
invert (basic_value_inv _#6 value_equal H).
intros x y A H1 H2 _ <-.
do 3 eexists.
reflexivity.
Qed.


Lemma sound_equal_formation_invert1 :
  forall G a a' m m' n n',
    pseq G (deqtype (equal a m n) (equal a' m' n'))
    -> pseq G (deqtype a a').
Proof.
intros G a b m n p q.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hl & Hr & Hl' & Hr').
simpsubin Hl.
simpsubin Hr.
simpsubin Hl'.
simpsubin Hr'.
invert (basic_value_inv _#6 value_equal Hl).
intros m1 p1 A Hm1 Hp1 Hal Heql.
invert (basic_value_inv _#6 value_equal Hl').
intros m2 p2 A' Hm2 Hp2 Hal' Heql'.
so (iuequal_inj _#17 (eqtrans Heql (eqsymm Heql'))) as (<- & _).
invert (basic_value_inv _#6 value_equal Hr).
intros m3 p3 A' Hm3 Hp3 Har Heqr.
invert (basic_value_inv _#6 value_equal Hr').
intros m4 p4 A'' Hm4 Hp4 Har' Heqr'.
so (iuequal_inj _#17 (eqtrans Heqr (eqsymm Heqr'))) as (<- & _).
rewrite -> iuequal_swap in Heqr.
so (iuequal_inj _#17 (eqtrans Heql (eqsymm Heqr))) as (<- & _).
exists A.
do2 3 split; auto.
Qed.


Lemma sound_equal_formation_invert1_univ :
  forall G lv a a' m m' n n',
    pseq G (deq (equal a m n) (equal a' m' n') (univ lv))
    -> pseq G (deq a a' (univ lv)).
Proof.
intros G lv a b m n p q.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_univ in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (pg & R & Hlvl & Hlvr & Hl & Hr & Hl' & Hr').
simpsubin Hl.
simpsubin Hr.
simpsubin Hl'.
simpsubin Hr'.
invert (basic_value_inv _#6 value_equal Hl).
intros m1 p1 A Hm1 Hp1 Hal Heql.
invert (basic_value_inv _#6 value_equal Hl').
intros m2 p2 A' Hm2 Hp2 Hal' Heql'.
so (iuequal_inj _#17 (eqtrans Heql (eqsymm Heql'))) as (<- & _).
invert (basic_value_inv _#6 value_equal Hr).
intros m3 p3 A' Hm3 Hp3 Har Heqr.
invert (basic_value_inv _#6 value_equal Hr').
intros m4 p4 A'' Hm4 Hp4 Har' Heqr'.
so (iuequal_inj _#17 (eqtrans Heqr (eqsymm Heqr'))) as (<- & _).
rewrite -> iuequal_swap in Heqr.
so (iuequal_inj _#17 (eqtrans Heql (eqsymm Heqr))) as (<- & _).
exists pg, A.
do2 5 split; auto.
Qed.
