
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
Require Import Intensional.
Require Import Ordinal.
Require Import Candidate.
Require Import System.
Require Import MapTerm.
Require Import Extend.
Require Import Model.
Require Import Standard.
Require Import Truncate.
Require Import Equivalences.
Require Import Ceiling.
Require Import SemanticsProperty.


Definition eqtype_property w (R R' : wiurel w) : nat -> Prop
  :=
  fun j => iutruncate (S j) R = iutruncate (S j) R'.


Lemma eqtype_property_downward :
  forall w R R' j,
    eqtype_property w R R' (S j)
    -> eqtype_property w R R' j.
Proof.
unfold eqtype_property.
intros w R R' j Heq.
so (f_equal (iutruncate (S j)) Heq) as Heq'.
rewrite -> !iutruncate_combine_le in Heq'; auto.
Qed.


Definition eqtype_urel w i (R R' : wiurel w) : wurel w :=
  property_urel (eqtype_property w R R') w i (eqtype_property_downward w R R').


Definition iueqtype w i (R R' : wiurel w) : wiurel w
  :=
  (eqtype_urel w i R R',
   meta_pair
     (meta_iurel R)
     (meta_iurel R')).


Lemma iueqtype_inj :
  forall w i R1 R1' R2 R2',
    iueqtype w i R1 R2 = iueqtype w i R1' R2'
    -> R1 = R1' /\ R2 = R2'.
Proof.
intros w i R1 R1' R2 R2' Heq.
so (f_equal snd Heq) as Heq'.
cbn in Heq'.
so (meta_pair_inj _#5 Heq') as (Heq1 & Heq2).
split.
  {
  eapply meta_iurel_inj; eauto.
  }

  {
  eapply meta_iurel_inj; eauto.
  }
Qed.
