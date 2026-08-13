Require Import Axioms.
Require Import Tactics.
Require Import Sigma.
Require Import Equality.
Require Import Relation.
Require Import Syntax.
Require Import Ofe.
Require Import Uniform.
Require Import Spaces.
Require Import Dynamic.
Require Import Hygiene.
Require Import Equivalence.
Require Import Urelsp.
Require Import Intensional.
Require Import Ordinal.
Require Import Candidate.
Require Import Ceiling.
Require Import Truncate.
Require Import MapTerm.
Require Import Extend.
Require Import Spaces.

Require Import SemanticsProperty.
Require Import ExtendTruncate.


Definition symmrel w (A : wurel w) : Prop :=
  forall i m p,
    rel A i m p
    -> rel A i m m /\ rel A i p p.


Definition symmetrical_property w (A : wurel w) : nat -> Prop :=
  fun i =>
    forall j, j <= i -> symmrel w (ceiling (S j) A).


Lemma symmetrical_property_downward :
  forall w A i,
    symmetrical_property w A (S i)
    -> symmetrical_property w A i.
Proof.
intros w A i Hsymmrel.
unfold symmetrical_property in Hsymmrel |- *.
intros j Hj.
apply Hsymmrel.
omega.
Qed.


Definition symmetrical_urel (w : ordinal) (i : nat) (A : wurel w) : wurel w :=
  property_urel
    (symmetrical_property w A)
    w i
    (symmetrical_property_downward w A).


Lemma ceiling_symmetrical_internal :
  forall w i A,
    symmetrical_urel w i A = symmetrical_urel w i (ceiling (S i) A).
Proof.
intros w i A.
unfold symmetrical_urel.
apply property_urel_extensionality; auto.
intros j Hj.
unfold symmetrical_property.
split.
  {
  intros H k Hk.
  rewrite -> ceiling_combine_le; auto.
  omega.
  }

  {
  intros H k Hk.
  rewrite <- (ceiling_combine_le _ (S k) (S i)); auto.
  omega.
  }
Qed.


Lemma ceiling_symmetrical :
  forall n w i A,
    ceiling (S n) (symmetrical_urel w i A)
    =
    symmetrical_urel w (min i n) (ceiling (S n) A).
Proof.
intros n w i A.
unfold symmetrical_urel.
apply urel_extensionality.
fextensionality 3.
intros j m p.
pextensionality.
  {
  intros Hmp.
  destruct Hmp as (Hjn & Hmp).
  destruct Hmp as (Hsymmetrical & Hji & Hclm & Hclp & Hm & Hp).
  do2 5 split; auto.
  2:{
    so (Min.min_glb i n j).
    omega.
    }
  unfold symmetrical_property in Hsymmetrical |- *.
  intros k Hk.
  rewrite -> ceiling_combine_le; auto.
  omega.
  }

  {
  intros Hmp.
  destruct Hmp as (Hsymmetrical & Hj & Hclm & Hclp & Hm & Hp).
  split.
    {
    so (Nat.min_glb_r i n j).
    omega.
    }
  do2 5 split; auto.
  2:{
    so (Nat.min_glb_l i n j).
    omega.
    }
  unfold symmetrical_property in Hsymmetrical |- *.
  intros k Hk.
  rewrite <- (ceiling_combine_le _ _ (S n)); auto.
  so (Nat.le_min_r i n).
  omega.
  }
Qed.


Lemma extend_symmrel :
  forall v w (A : wurel v),
    v <<= w
    -> symmrel w (extend_urel v w A) <-> symmrel v A.
Proof.
intros v w A Hvw.
split.
  {
  intro Hsymmrel.
  intros j m p Hmp.
  exploit (Hsymmrel j (map_term (extend v w) m) (map_term (extend v w) p)) as H.
    {
    cbn.
    rewrite -> !extend_term_cancel; auto.
    }
  cbn in H.
  rewrite -> !extend_term_cancel in H; auto.
  }

  {
  intro Hsymmrel.
  intros j m p Hmp.
  exploit (Hsymmrel j (map_term (extend w v) m) (map_term (extend w v) p)) as H; auto.
  }
Qed.


Lemma extend_symmetrical :
  forall v w (h : v <<= w) i A,
    extend_urel v w (symmetrical_urel v i A)
    =
    symmetrical_urel w i (extend_urel v w A).
Proof.
intros v w h i A.
unfold symmetrical_urel.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros Hsymmetrical Hj Hclm Hclp Hstepsm Hstepsp.
  do2 5 split; eauto using map_hygiene_conv.
    {
    unfold symmetrical_property.
    intros k Hk.
    rewrite -> ceiling_extend_urel.
    so (Hsymmetrical k Hk) as H.
    apply extend_symmrel; auto.
    }

    {
    so (map_steps_form _#5 Hstepsm) as (q & Heq & Hstepsm').
    so (map_eq_triv_invert _#4 (eqsymm Heq)); subst q.
    auto.
    }

    {
    so (map_steps_form _#5 Hstepsp) as (q & Heq & Hstepsp').
    so (map_eq_triv_invert _#4 (eqsymm Heq)); subst q.
    auto.
    }
  }

  {
  intro H.
  decompose H.
  intros Hsymmetrical Hj Hclm Hclp Hstepsm Hstepsp.
  do2 5 split; eauto using map_hygiene.
    {
    unfold symmetrical_property in Hsymmetrical.
    intros k Hk.
    so (Hsymmetrical k Hk) as H.
    rewrite -> ceiling_extend_urel in H.
    rewrite -> extend_symmrel in H; auto.
    }

    {
    so (map_steps _ _ (extend w v) _ _ Hstepsm) as H.
    simpmapin H.
    auto.
    }

    {
    so (map_steps _ _ (extend w v) _ _ Hstepsp) as H.
    simpmapin H.
    auto.
    }
  }
Qed.


Definition iusymmetrical w i A
  :=
  (symmetrical_urel w i (den A),
   meta_iurel A).


Lemma iutruncate_iusymmetrical :
  forall n w i A,
    iutruncate (S n) (iusymmetrical w i A)
    =
    iusymmetrical w
      (min i n)
      (iutruncate (S n) A).
Proof.
intros n w i A.
unfold iusymmetrical.
unfold iutruncate.
unfold den.
cbn [fst snd].
f_equal.
  {
  apply ceiling_symmetrical.
  }

  {
  fold (iutruncate (S n) A).
  rewrite -> meta_truncate_iurel; auto.
  omega.
  }
Qed.


Lemma extend_iusymmetrical :
  forall v w (h : v <<= w) i A,
    extend_iurel h (iusymmetrical v i A)
    =
    iusymmetrical w i (extend_iurel h A).
Proof.
intros v w h i A.
unfold iusymmetrical, extend_iurel.
cbn.
f_equal.
  {
  apply extend_symmetrical; auto.
  }

  {
  rewrite -> extend_meta_iurel.
  unfold extend_iurel.
  reflexivity.
  }
Qed.


Lemma iusymmetrical_inj :
  forall w i A A',
    iusymmetrical w i A = iusymmetrical w i A'
    -> A = A'.
Proof.
intros w i A A' Heq.
so (f_equal (fun z => snd z) Heq) as Heq'.
cbn in Heq'.
exact (meta_iurel_inj _#3 Heq').
Qed.
