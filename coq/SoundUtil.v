
Require Import Coq.Lists.List.

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

Require Import Ceiling.
Require Import Truncate.
Require Import Urelsp.
Require Import ProperDownward.


Lemma extract_functional :
  forall pg i A b c,
    A = ceiling (S i) A
    -> hygiene (permit clo) b
    -> hygiene (permit clo) c
    -> (forall j m p,
          rel A j m p
          -> exists R,
               interp pg true j (subst1 m b) R
               /\ interp pg false j (subst1 p c) R)
    -> exists (B : urelsp A -n> siurel_ofe),
         functional the_system pg true i A b B
         /\ functional the_system pg false i A c B.
Proof.
intros pg i A b c HeqA Hclb Hclc Hact.
assert (forall (C : urelsp_car A), exists! (R : siurel),
          forall j m p Hmp,
            C = urelspinj A j m p Hmp
            -> interp pg true j (subst1 m b) R
               /\ interp pg false j (subst1 p c) R) as Huniq.
  {
  intros C.
  so (urelsp_eta _ _ C) as (j & m & p & Hmp & ->).
  so (Hact j m p Hmp) as (R & Hmb & Hpc).
  exists R.
  split.
    {
    intros j' n q Hnq Heq.
    so (urelspinj_equal_invert _#10 Heq) as (<- & Hmq).  
    so (Hact _#3 Hmq) as (R' & Hmb' & Hqc).
    so (basic_fun _#7 Hmb Hmb'); subst R'.
    so (Hact _#3 Hnq) as (R' & Hnb & Hqc').
    so (basic_fun _#7 Hqc Hqc'); subst R'.
    split; auto.
    }
    
    {
    intros R' HR'.
    so (HR' j m p Hmp (eq_refl _)) as (Hmb' & _).
    exact (basic_fun _#7 Hmb Hmb').
    }
  }
so (choice _#3 Huniq) as (f & Hf).
assert (@nonexpansive (urelsp A) siurel_ofe f) as Hne.
  {
  intros j C D HCD.
  destruct j as [| j].
    {
    apply dist_zero.
    }
  so (urelsp_eta _ _ C) as (k & m & p & Hmp & ->).
  so (urelsp_eta _ _ D) as (k' & n & q & Hnq & ->).
  so (urelspinj_dist_invert _#11 HCD) as Hmq.
  so (urelspinj_dist_index' _#11 HCD) as [H | H].
    {
    destruct H as (<- & Hlt).
    assert (k <= j) as Hkj by omega; clear Hlt.
    apply dist_refl'.
    so (Hf _#4 Hmp (eq_refl _)) as (Hmb & _).
    so (Hf _#4 Hnq (eq_refl _)) as (_ & Hqc).
    so (Hf _#4 Hmq (eq_refl _)) as (Hmb' & Hqc').
    rewrite -> (Nat.min_r j k) in Hmb' at 1; auto.
    rewrite -> (Nat.min_r j k) in Hqc' at 1; auto.
    rewrite -> (basic_fun _#7 Hmb Hmb').
    rewrite -> (basic_fun _#7 Hqc Hqc').
    reflexivity.
    }

    {
    assert (j <= k) as Hjk by omega.
    assert (j <= k') as Hjk' by omega.
    clear H.
    rewrite -> Nat.min_l in Hmq; auto.
    eapply dist_trans.
      {
      apply dist_symm.
      apply iutruncate_near.
      }
    eapply dist_trans.
    2:{
      apply iutruncate_near.
      }
    apply dist_refl'.
    so (Hf _#4 Hmp (eq_refl _)) as (Hmb & _).
    so (Hf _#4 Hnq (eq_refl _)) as (_ & Hqc).
    so (Hf _#4 Hmq (eq_refl _)) as (Hmb' & Hqc').
    rewrite -> (basic_fun _#7 (basic_downward _#7 Hjk Hmb) Hmb').
    rewrite -> (basic_fun _#7 (basic_downward _#7 Hjk' Hqc) Hqc').
    reflexivity.
    }
  }
exists (expair f Hne).
split.
  {
  apply functional_i; auto.
  intros j m p Hj Hmp.
  cbn.
  exact (Hf _#4 Hmp (eq_refl _) andel).
  }

  {
  apply functional_i; auto.
  intros j m p Hj Hmp.
  cbn.
  exact (Hf _#4 Hmp (eq_refl _) ander).
  }
Qed.


Lemma extract_functional_multi :
  forall pg i A b b' c c',
    A = ceiling (S i) A
    -> hygiene (permit clo) b
    -> hygiene (permit clo) b'
    -> hygiene (permit clo) c
    -> hygiene (permit clo) c'
    -> (forall j m p,
          rel A j m p
          -> exists R,
               interp pg true j (subst1 m b) R
               /\ interp pg false j (subst1 p b') R
               /\ interp pg true j (subst1 m c) R
               /\ interp pg false j (subst1 p c') R)
    -> exists (B : urelsp A -n> siurel_ofe),
         functional the_system pg true i A b B
         /\ functional the_system pg false i A b' B
         /\ functional the_system pg true i A c B
         /\ functional the_system pg false i A c' B.
Proof.
intros pg i A b c d e HeqA Hclb Hclc Hcld Hcle Hact.
eassert _ as H; [refine (extract_functional pg _#4 HeqA Hclb Hclc _) |].
  {
  intros j m p Hmp.
  so (Hact j m p Hmp) as (R & H1 & H2 & _).
  eauto.
  }
destruct H as (B & Hb & Hc).
eassert _ as H; [refine (extract_functional pg _#4 HeqA Hcld Hcle _) |].
  {
  intros j m p Hmp.
  so (Hact j m p Hmp) as (R & _ & _ & H1 & H2).
  eauto.
  }
destruct H as (B' & Hd & He).
eassert _ as H; [refine (extract_functional pg _#4 HeqA Hclb Hcle _) |].
  {
  intros j m p Hmp.
  so (Hact j m p Hmp) as (R & H1 & _ & _ & H2).
  eauto.
  }
destruct H as (B'' & Hb' & He').
so (functional_fun _#8 Hb Hb'); subst B''.
so (functional_fun _#8 He He'); subst B'.
exists B.
auto.
Qed.


Definition pgointerp (s : ssub) (lvo : option sterm) (pg : page) : Prop
  :=
  match lvo with
  | Some lv => pginterp (subst s lv) pg
  | None => pg = toppg
  end.


Lemma pgointerp_fun :
  forall s lvo pg pg',
    pgointerp s lvo pg
    -> pgointerp s lvo pg'
    -> pg = pg'.
Proof.
intros s lvo pg pg' H H'.
destruct lvo as [lv |].
  {
  cbn in H, H'.
  eapply pginterp_fun; eauto.
  }

  {
  cbn in H, H'.
  subst pg pg'.
  reflexivity.
  }
Qed.
