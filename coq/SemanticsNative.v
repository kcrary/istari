
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

Require Import Native.


Definition native_action (A : Type) (f : A -> native) (w : ordinal) (i : nat) : nat -> relation (wterm w)
  :=
  fun i' m m' =>
    i' <= i
    /\ hygiene clo m
    /\ hygiene clo m'
    /\ (exists x, star step m (native_elem (f x)) /\ star step m' (native_elem (f x))).


Lemma native_uniform :
  forall A f w i, uniform _ (native_action A f w i).
Proof.
intros A f w.
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
intros Hi _ _ x Hstepsm Hstepsn.
do2 3 split; auto.
exists x.
so (equiv_eval _#4 Hequivm (conj Hstepsm value_native_elem)) as (p & (Hstepsp & _) & Hmc).
invertc_mc Hmc.
fold (@native_elem (obj w) (f x)).
intros <-.
so (equiv_eval _#4 Hequivn (conj Hstepsn value_native_elem)) as (q & (Hstepsq & _) & Hmc).
invertc_mc Hmc.
fold (@native_elem (obj w) (f x)).
intros <-.
auto.
}

(* zigzag *)
{
intros i' m n p q Hmn Hpn Hpq.
destruct Hmn as (Hi & Hclm & _ & (x & Hm & Hn)).
destruct Hpn as (_ & _ & _ & (y & Hp & Hn')).
destruct Hpq as (_ & _ & Hclq & (z & Hp' & Hq)).
so (determinism_eval _#4 (conj Hn value_native_elem) (conj Hn' value_native_elem)) as H.
injectionc H.
intro Hxy.
so (determinism_eval _#4 (conj Hp value_native_elem) (conj Hp' value_native_elem)) as H.
injectionc H.
intro Hyz.
do2 3 split; auto.
exists x.
split; auto.
rewrite -> Hxy.
rewrite -> Hyz.
auto.
}

(* downward *)
{
intros i' m n Hact.
decompose Hact.
intros Hi Hclm Hcln x Hstepsm Hstepsn.
do2 3 split; eauto.
omega.
}
Qed.


Definition native_urel A f w i :=
  mk_urel
    (native_action A f w i)
    (native_uniform A f w i).


Lemma ceiling_native :
  forall A f n w i,
    ceiling (S n) (native_urel A f w i) = native_urel A f w (min i n).
Proof.
intros A f n w i.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros (Hjn & Hact).
  decompose Hact.
  intros Hj Hclm Hclp x Hstepsm Hstepsp.
  do2 3 split; eauto.
  apply Nat.min_glb; omega.
  }

  {
  intros Hact.
  decompose Hact.
  intros Hj Hclm Hclp x Hstepsm Hstepsp.
  split.
    {
    so (Nat.min_glb_r _#3 Hj).
    omega.
    }

    {
    do2 3 split; eauto.
    so (Nat.min_glb_l _#3 Hj).
    auto.
    }
  }
Qed.


Lemma extend_native :
  forall v w (h : v <<= w) A f i,
    extend_urel v w (native_urel A f v i)
    =
    native_urel A f w i.
Proof.
intros v w h A f i.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros H.
  decompose H.
  intros Hj Hm Hp x Hstepsm Hstepsp.
  do2 3 split; auto.
    {
    eapply map_hygiene_conv; eauto.
    }

    {
    eapply map_hygiene_conv; eauto.
    }
  exists x.
  so (map_steps_form _#5 Hstepsm) as (n & Hmap & Hstepsm').
  so (map_steps_form _#5 Hstepsp) as (q & Hmap' & Hstepsp').
  so (map_eq_native_elem_invert _#5 (eqsymm Hmap)).
  so (map_eq_native_elem_invert _#5 (eqsymm Hmap')).
  subst n q.
  split; auto.
  }

  {
  intros H.
  decompose H.
  intros Hj Hclm Hclp x Hstepsm Hstepsp.
  do2 3 split; auto.
    {
    apply map_hygiene; auto.
    }

    {
    apply map_hygiene; auto.
    }
  exists x.
  split.
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
