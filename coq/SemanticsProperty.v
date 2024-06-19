
(* Semantics for subsingleton types *)

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


Definition property_action
  (P : nat -> Prop) (w : ordinal) i
  : nat -> relation (wterm w)
  :=
  fun i' m m' =>
    P i'
    /\ i' <= i
    /\ hygiene clo m
    /\ hygiene clo m'
    /\ star step m triv
    /\ star step m' triv.


Lemma property_uniform :
  forall (P : nat -> Prop) w i, 
    (forall j, P (S j) -> P j)
    -> uniform _ (property_action P w i).
Proof.
intros P w I Hdown.
do2 3 split.

(* closed *)
{
intros i m n H.
decompose H; auto.
}

(* equiv *)
{
intros i m m' n n' Hclm' Hcln' Hm Hn H.
decompose H.
intros HP Hi _ _ Hstepsm Hstepsn.
do2 5 split; auto.
  {
  so (equiv_eval _#4 Hm (conj Hstepsm value_triv)) as (? & (Hstepsm' & _) & H).
  invertc_mc H.
  intros <-.
  exact Hstepsm'.
  }

  {
  so (equiv_eval _#4 Hn (conj Hstepsn value_triv)) as (? & (Hstepsn' & _) & H).
  invertc_mc H.
  intros <-.
  exact Hstepsn'.
  }
}

(* zigzag *)
{
intros i m n p q Hmn Hpn Hpq.
decompose Hmn.
intros HP Hi Hclm _ Hstepsm _.
decompose Hpq.
intros _ _ _ Hclq _ Hstepsq.
do2 5 split; auto.
}

(* downward *)
{
intros i m n Hmn.
decompose Hmn.
intros.
do2 5 split; auto.
omega.
}
Qed.


Definition property_urel P w i Hdown := mk_urel (property_action P w i) (property_uniform P w i Hdown).


Lemma property_urel_extensionality :
  forall (P P' : nat -> Prop) w i i' Hdown Hdown',
    i = i'
    -> (forall j, j <= i -> P j <-> P' j)
    -> property_urel P w i Hdown = property_urel P' w i' Hdown'.
Proof.
intros P P' w I I' Hdown Hdown' H Hiff.
subst I'.
apply urel_extensionality.
fextensionality 3.
intros j m p.
pextensionality.
  {
  intros Hmp.
  cbn in Hmp.
  decompose Hmp.
  intros HP; intros.
  do2 5 split; auto.
  apply Hiff; auto.
  }

  {
  intros Hmp.
  cbn in Hmp.
  decompose Hmp.
  intros HP; intros.
  do2 5 split; auto.
  apply Hiff; auto.
  }
Qed.


Lemma property_urel_eq_invert :
  forall P Q w i H H',
    property_urel P w i H = property_urel Q w i H'
    -> (forall j, j <= i -> P j <-> Q j).
Proof.
intros P Q w i Hdown Hdown' Heq.
intros j Hj.
split.
  {
  intro HP.
  assert (rel (property_urel P w i Hdown) j triv triv) as H.
    {
    do2 5 split; auto using star_refl; apply hygiene_auto; cbn; auto.
    }
  rewrite -> Heq in H.
  exact (H andel).
  }

  {
  intro HQ.
  assert (rel (property_urel Q w i Hdown') j triv triv) as H.
    {
    do2 5 split; auto using star_refl; apply hygiene_auto; cbn; auto.
    }
  rewrite <- Heq in H.
  exact (H andel).
  }
Qed.


Lemma ceiling_property :
  forall P n w i Hdown,
    ceiling (S n) (property_urel P w i Hdown)
    =
    property_urel P w (min i n) Hdown.
Proof.
intros P n w i Hdown.
apply urel_extensionality.
fextensionality 3.
intros j m p.
pextensionality.
  {
  intros (Hjn, Hact).
  cbn in Hact.
  decompose Hact.
  intros HP Hj; intros.
  do2 5 split; auto.
  apply Nat.min_glb; omega.
  }

  {
  intros Hact.
  cbn in Hact.
  decompose Hact.
  intros HP Hj; intros.
  cbn in Hj.
  split; auto.
    {
    so (Nat.min_glb_r _#3 Hj).
    omega.
    }
  do2 5 split; auto.
  eapply Nat.min_glb_l; eauto.
  }
Qed.


Lemma extend_property :
  forall P v w (h : v <<= w) I Hdown,
    extend_urel v w (property_urel P v I Hdown)
    =
    property_urel P w I Hdown.
Proof.
intros P v w h I Hdown.
apply urel_extensionality.
fextensionality 3.
intros j m p.
pextensionality.
  {
  intro H.
  cbn in H.
  decompose H.
  intros HP Hj Hclm Hclp Hstepsm Hstepsp.
  do2 5 split; eauto using map_hygiene_conv.
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
  intros H.
  cbn in H.
  decompose H.
  intros HP Hj Hclm Hclp Hstepsm Hstepsp.
  cbn.
  do2 5 split; eauto using map_hygiene.
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


Lemma property_action_triv :
  forall (P : nat -> Prop) w i i',
    i' <= i
    -> P i'
    -> property_action P w i i' triv triv.
Proof.
intros P w I i Hi HPi.
do2 5 split; auto using star_refl; apply hygiene_auto; cbn; auto.
Qed.    


Definition triv_urel w i : wurel w := property_urel (fun _ => True) w i (fun _ x => x).


Lemma ceiling_triv :
  forall n w i,
    ceiling (S n) (triv_urel w i)
    =
    triv_urel w (min i n).
Proof.
intros n w I.
apply ceiling_property.
Qed.


Lemma extend_triv :
  forall v w (h : v <<= w) i,
    extend_urel v w (triv_urel v i)
    =
    triv_urel w i.
Proof.
intros v w h I.
apply extend_property; auto.
Qed.
