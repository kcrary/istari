
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

Require Import SemanticsProperty.


Definition void_urel (w : ordinal) := @empty_urel (obj w).


Definition unit_urel w i := triv_urel w i.


Definition bool_action w i : nat -> relation (wterm w)
  :=
  fun i' m m' =>
    i' <= i
    /\ hygiene clo m
    /\ hygiene clo m'
    /\ ((star step m btrue /\ star step m' btrue)
        \/ (star step m bfalse /\ star step m' bfalse)).


Lemma bool_uniform :
  forall w i, uniform _ (bool_action w i).
Proof.
intros w i.
do2 3 split.

(* closed *)
{
intros i' m n H.
decompose H; auto.
}

(* equiv *)
{
intros i' m m' n n' Hclm' Hcln' Hequivm Hequivn Hact.
decompose Hact.
intros Hi' _ _ H.
do2 3 split; auto.
destruct H as [(Hstepsm & Hstepsn) | (Hstepsm & Hstepsn)].
  {
  left.
  split.
    {
    so (equiv_eval _#4 Hequivm (conj Hstepsm value_btrue)) as (p & (Hsteps & _) & Hmc).
    invertc_mc Hmc.
    intros <-.
    exact Hsteps.
    }

    {
    so (equiv_eval _#4 Hequivn (conj Hstepsn value_btrue)) as (p & (Hsteps & _) & Hmc).
    invertc_mc Hmc.
    intros <-.
    exact Hsteps.
    }
  }

  {
  right.
  split.
    {
    so (equiv_eval _#4 Hequivm (conj Hstepsm value_bfalse)) as (p & (Hsteps & _) & Hmc).
    invertc_mc Hmc.
    intros <-.
    exact Hsteps.
    }

    {
    so (equiv_eval _#4 Hequivn (conj Hstepsn value_bfalse)) as (p & (Hsteps & _) & Hmc).
    invertc_mc Hmc.
    intros <-.
    exact Hsteps.
    }
  }
}

(* zigzag *)
{
intros i' m n p q Hmn Hpn Hpq.
destruct Hmn as (Hi' & Hclm & _ & Hmn).
destruct Hpn as (_ & _ & _ & Hpn).
destruct Hpq as (_ & _ & Hclq & Hpq).
do2 3 split; auto.
destruct Hmn as [(Hstepsm & Hstepsn) | (Hstepsm & Hstepsn)].
  {
  left.
  split; auto.
  destruct Hpn as [(Hstepsp & Hstepsn') | (Hstepsp & Hstepsn')].
  2:{
    so (determinism_eval _#4 (conj Hstepsn value_btrue) (conj Hstepsn' value_bfalse)) as H.
    discriminate H.
    }
  destruct Hpq as [(Hstepsp' & Hstepsq) | (Hstepsp' & Hstepsq)].
  2:{
    so (determinism_eval _#4 (conj Hstepsp value_btrue) (conj Hstepsp' value_bfalse)) as H.
    discriminate H.
    }
  exact Hstepsq.
  }

  {
  right.
  split; auto.
  destruct Hpn as [(Hstepsp & Hstepsn') | (Hstepsp & Hstepsn')].
    {
    so (determinism_eval _#4 (conj Hstepsn' value_btrue) (conj Hstepsn value_bfalse)) as H.
    discriminate H.
    }
  destruct Hpq as [(Hstepsp' & Hstepsq) | (Hstepsp' & Hstepsq)].
    {
    so (determinism_eval _#4 (conj Hstepsp' value_btrue) (conj Hstepsp value_bfalse)) as H.
    discriminate H.
    }
  exact Hstepsq.
  }
}

(* downward *)
{
intros i' m n Hact.
decompose Hact.
intros Hle Hclm Hcln Hact.
do2 3 split; auto.
omega.
}
Qed.


Definition bool_urel w i :=
  mk_urel (bool_action w i) (bool_uniform w i).


Lemma ceiling_void :
  forall n w,
    ceiling (S n) (void_urel w) = void_urel w.
Proof.
intros n w.
apply ceiling_empty_urel.
Qed.


Lemma ceiling_unit :
  forall n w i,
    ceiling (S n) (unit_urel w i) = unit_urel w (min i n).
Proof.
intros n w i.
apply ceiling_property.
Qed.


Lemma ceiling_bool :
  forall n w i,
    ceiling (S n) (bool_urel w i) = bool_urel w (min i n).
Proof.
intros n w i.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros (Hjn, Hact).
  decompose Hact.
  intros Hji Hclm Hclp Hsteps.
  do2 3 split; auto.
  apply Nat.min_glb; omega.
  }

  {
  intros Hact.
  decompose Hact.
  intros Hj Hclm Hclp Hsteps.
  split.
    {
    so (Nat.min_glb_r _#3 Hj); omega.
    }
  do2 3 split; auto.
  so (Nat.min_glb_l _#3 Hj); omega.
  }
Qed.


Lemma extend_void :
  forall v w (h : v <<= w),
    extend_urel v w (void_urel v)
    =
    void_urel w.
Proof.
intros v w h.
apply extend_empty_urel; auto.
Qed.


Lemma extend_unit :
  forall v w i (h : v <<= w),
    extend_urel v w (unit_urel v i)
    =
    unit_urel w i.
Proof.
intros v w i h.
apply extend_property; auto.
Qed.


Lemma extend_bool :
  forall v w i (h : v <<= w),
    extend_urel v w (bool_urel v i)
    =
    bool_urel w i.
Proof.
intros v w i h.
apply urel_extensionality.
fextensionality 3.
intros j m n.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros Hj Hclm Hcln Hsteps.
  do2 3 split; eauto using map_hygiene_conv.
  destruct Hsteps as [(Hstepsm & Hstepsn) | (Hstepsm & Hstepsn)].
    {
    left.
    so (map_steps_form _#5 Hstepsm) as (q & Heq & Hstepsm').
    so (map_eq_btrue_invert _#4 (eqsymm Heq)); subst q.
    so (map_steps_form _#5 Hstepsn) as (q & Heq' & Hstepsn').
    so (map_eq_btrue_invert _#4 (eqsymm Heq')); subst q.
    auto.
    }

    {
    right.
    so (map_steps_form _#5 Hstepsm) as (q & Heq & Hstepsm').
    so (map_eq_bfalse_invert _#4 (eqsymm Heq)); subst q.
    so (map_steps_form _#5 Hstepsn) as (q & Heq' & Hstepsn').
    so (map_eq_bfalse_invert _#4 (eqsymm Heq')); subst q.
    auto.
    }
  }

  {
  intro H.
  decompose H.
  intros Hj Hclm Hcln Hsteps.
  do2 3 split; eauto using map_hygiene.
  destruct Hsteps as [(Hstepsm & Hstepsn) | (Hstepsm & Hstepsn)]; [left | right];
  split; (relquest; [eapply map_steps; eauto | simpmap; reflexivity]).
  }
Qed.


Lemma void_urel_elim :
  forall w i m n,
    rel (void_urel w) i m n
    -> False.
Proof.
intros w i m n H.
exact H.
Qed.


Lemma unit_urel_triv :
  forall w i i',
    i' <= i
    -> rel (unit_urel w i) i' triv triv.
Proof.
intros w i i' H.
apply property_action_triv; auto.
Qed.


Lemma bool_action_btrue :
  forall w i i',
    i' <= i
    -> bool_action w i i' btrue btrue.
Proof.
intros w i i' Hi'.
do2 3 split; auto; try (apply hygiene_auto; cbn; auto).
left; auto using star_refl.
Qed.


Lemma bool_action_bfalse :
  forall w i i',
    i' <= i
    -> bool_action w i i' bfalse bfalse.
Proof.
intros w i i' Hi'.
do2 3 split; auto; try (apply hygiene_auto; cbn; auto).
right; auto using star_refl.
Qed.
