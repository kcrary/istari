
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
Require Import Equivalences.


(* Do we need the index i here?  I think we probably don't. *)

Definition fut_action
  (w : ordinal) i (A : wurel w)
  : nat -> relation (wterm w)
  :=
  fun i' m p =>
    exists m' p',
      i' <= i
      /\ hygiene clo m
      /\ hygiene clo p
      /\ star step m (next m')
      /\ star step p (next p')
      /\ (i' > 0 -> rel A (pred i') m' p').


Lemma fut_uniform :
  forall w i A, uniform _ (fut_action w i A).
Proof.
intros w I A.
do2 3 split.

(* closed *)
{
intros i m n H.
decompose H; auto.
}

(* equiv *)
{
intros i m m' p p' Hclm' Hclp' Hequivm Hequivp Hact.
decompose Hact.
intros n q Hi _ _ Hstepsm Hstepsp Hact.
so (equiv_eval _#4 Hequivm (conj Hstepsm value_next)) as (x & (Hstepsm' & _) & Hmc).
invertc_mc Hmc.
intros n' Hequivn <-.
fold (next n') in *.
so (equiv_eval _#4 Hequivp (conj Hstepsp value_next)) as (x & (Hstepsp' & _) & Hmc).
invertc_mc Hmc.
intros q' Hequivq <-.
fold (next q') in *.
exists n', q'.
do2 5 split; auto.
intro Hpos.
so (Hact Hpos) as Hrel.
eapply urel_equiv; eauto.
  {
  so (steps_hygiene _#4 Hstepsm' Hclm') as H.
  so (hygiene_invert_auto _#5 H) as H'; cbn in H'.
  destruct H'; auto.
  }

  {
  so (steps_hygiene _#4 Hstepsp' Hclp') as H.
  so (hygiene_invert_auto _#5 H) as H'; cbn in H'.
  destruct H'; auto.
  }
}

(* zigzag *)
{
intros i m n p q Hmn Hpn Hpq.
decompose Hmn.
intros m' n' Hi Hclm Hcln Hstepsm Hstepsn Hmn.
decompose Hpn.
intros p' n'' _ Hclp _ Hstepsp Hstepsn' Hpn.
so (determinism_eval _#4 (conj Hstepsn value_next) (conj Hstepsn' value_next)) as H.
injectionc H.
intros <-.
decompose Hpq.
intros p'' q' _ _ Hclq Hstepsp' Hstepsq Hpq.
so (determinism_eval _#4 (conj Hstepsp value_next) (conj Hstepsp' value_next)) as H.
injectionc H.
intros <-.
exists m', q'.
do2 5 split; auto.
intro Hpos.
so (Hmn Hpos).
so (Hpn Hpos).
so (Hpq Hpos).
eapply urel_zigzag; eauto.
}

(* downward *)
{
intros i m p H.
decompose H.
intros m' p' Hi Hclm Hclp Hstepsm Hstepsp Hact.
exists m', p'.
do2 5 split; eauto.
  {
  omega.
  }
intro Hpos.
so (Hact (Nat.lt_0_succ _)) as H.
cbn in H.
apply (urel_downward_leq _#3 i); auto.
omega.
}
Qed.


Definition fut_urel w i A :=
  mk_urel (fut_action w i A) (fut_uniform _#3).


Definition iufut (w : ordinal) (i : nat) (A : wiurel w) : wiurel w
  :=
  (fut_urel w i (den A),
   meta_half (meta_iurel A)).


Definition iufut0 (w : ordinal) : wiurel w
  :=
  (fut_urel w 0 empty_urel,
   meta_half meta_null).


Lemma den_iufut :
  forall w i A,
    den (iufut w i A) = fut_urel w i (den A).
Proof.
reflexivity.
Qed.


Lemma den_iufut0 :
  forall w,
    den (iufut0 w) = fut_urel w 0 empty_urel.
Proof.
reflexivity.
Qed.


Lemma iufut_inj :
  forall w I I' A A',
    iufut w I A = iufut w I' A'
    -> A = A'.
Proof.
intros w I I' A A' Heq.
unfold iufut in Heq.
so (f_equal (fun z => snd z) Heq) as Heq'.
cbn in Heq'.
exact (meta_iurel_inj _#3 (meta_half_inj _#3 Heq')).
Qed.


Lemma ceiling_fut :
  forall n w i A,
    ceiling (S n) (fut_urel w i A)
    =
    fut_urel w
      (min i n)
      (ceiling n A).
Proof.
intros n w i A.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros (Hj & Hact).
  decompose Hact.
  intros m' p' Hj' Hclm Hclp Hstepsm Hstepsp Hact.
  exists m', p'.
  do2 5 split; auto.
    {
    apply Nat.min_glb; omega.
    }

    {
    intro Hpos.
    cbn.
    so (Hact Hpos) as H.
    split; auto.
    omega.
    }
  }

  {
  intro Hact.
  decompose Hact.
  intros m' p' Hj Hclm Hclp Hstepsm Hstepsp Hact.
  so (Nat.min_glb_l _#3 Hj) as Hji.
  so (Nat.min_glb_r _#3 Hj) as Hjn.
  split; [omega |].
  exists m', p'.
  do2 5 split; auto.
  intro Hpos.
  so (Hact Hpos) as H.
  destruct H as (_ & H).
  auto.
  }
Qed.


Lemma iutruncate_iufut :
  forall n w i A,
    n > 1
    -> iutruncate n (iufut w i A)
       =
       iufut w
         (min i (pred n))
         (iutruncate (pred n) A).
Proof.
intros n w i A Hpos.
unfold iufut.
unfold iutruncate.
cbn [fst snd].
f_equal.
  {
  destruct n as [| n]; [omega |].
  apply ceiling_fut.
  }

  {
  rewrite -> meta_truncate_half; [| omega].
  f_equal.
  rewrite -> meta_truncate_iurel; auto.
  omega.
  }
Qed.


Lemma iutruncate_iufut_one :
  forall w i A,
    iutruncate 1 (iufut w i A)
    =
    iufut0 w.
Proof.
intros w i A.
unfold iufut, iufut0.
unfold iutruncate.
cbn [fst snd].
f_equal.
  {
  rewrite -> ceiling_fut.
  f_equal.
    {
    rewrite -> Nat.min_r; omega.
    }
  cbn.
  apply ceiling_zero.
  }

  {
  rewrite -> meta_truncate_half; [| omega].
  reflexivity.
  }
Qed.


Lemma iutruncate_iufut0 :
  forall n w,
    n > 0
    -> iutruncate n (iufut0 w)
       =
       iufut0 w.
Proof.
intros n w Hpos.
unfold iufut0.
unfold iutruncate.
cbn [fst snd].
f_equal.
  {
  destruct n as [| n]; [omega |].
  rewrite -> ceiling_fut.
  f_equal.
  apply ceiling_empty_urel.
  }

  {
  rewrite -> meta_truncate_half; auto.
  rewrite -> meta_truncate_null.
  reflexivity.
  }
Qed.


Lemma extend_fut :
  forall v w (h : v <<= w) I A,
    extend_urel v w (fut_urel v I A)
    =
    fut_urel w I
      (extend_urel v w A).
Proof.
intros v w h I A.
apply urel_extensionality.
fextensionality 3.
intros i m p.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros m' p' Hi Hclm Hclp Hstepsm Hstepsp Hact.
  so (map_steps_form _#5 Hstepsm) as (m'' & Heq & Hstepsn).
  so (map_steps_form _#5 Hstepsp) as (p'' & Heq' & Hstepsn').
  so (map_eq_next_invert _#5 (eqsymm Heq)) as (n & -> & <-).
  so (map_eq_next_invert _#5 (eqsymm Heq')) as (n' & -> & <-).
  exists n, n'.
  do2 5 split; eauto using map_hygiene_conv.
  }

  {
  intro H.
  decompose H.
  intros m' p' Hi Hclm Hclp Hstepsm Hstepsp Hact.
  exists (map_term (extend w v) m'), (map_term (extend w v) p').
  do2 5 split; auto using map_hygiene.
    {
    so (map_steps _ _ (extend w v) _ _ Hstepsm) as H.
    simpmapin H.
    exact H.
    }
    {
    so (map_steps _ _ (extend w v) _ _ Hstepsp) as H.
    simpmapin H.
    exact H.
    }
  }
Qed.


Lemma extend_iufut :
  forall v w (h : v <<= w) I A,
    extend_iurel h (iufut v I A)
    =
    iufut w I (extend_iurel h A).
Proof.
intros v w h I A.
unfold iufut, extend_iurel.
cbn.
f_equal.
  {
  apply extend_fut; auto.
  }

  {
  rewrite -> extend_meta_half.
  f_equal.
  rewrite -> extend_meta_iurel.
  reflexivity.
  }
Qed.


Lemma extend_iufut0 :
  forall v w (h : v <<= w),
    extend_iurel h (iufut0 v)
    =
    iufut0 w.
Proof.
intros v w h.
unfold iufut0, extend_iurel.
cbn.
f_equal.
  {
  rewrite -> extend_fut; auto.
  rewrite -> extend_empty_urel; auto.
  }

  {
  rewrite -> extend_meta_half.
  rewrite -> extend_meta_null.
  reflexivity.
  }
Qed.


Lemma fut_action_next_zero :
  forall w i A m n,
    hygiene clo (next m)
    -> hygiene clo (next n)
    -> fut_action w i A 0 (next m) (next n).
Proof.
intros w i A m n Hcl Hcl'.
so (hygiene_invert_auto _#5 Hcl) as H; cbn in H.
destruct H as (Hclm & _).
so (hygiene_invert_auto _#5 Hcl') as H; cbn in H.
destruct H as (Hcln & _).
exists m, n.
do2 5 split; auto using star_refl; omega.
Qed.


Lemma fut_action_next :
  forall w i A i' m n,
    S i' <= i
    -> rel A i' m n
    -> fut_action w i A (S i') (next m) (next n).
Proof.
intros w I A i m n Hi Hmn.
so (urel_closed _#5 Hmn) as (Hm & Hn).
exists m, n.
do2 5 split; auto using star_refl.
  {
  apply hygiene_auto; cbn; auto.
  }

  {
  apply hygiene_auto; cbn; auto.
  }
Qed.


Lemma fut_action_prev :
  forall w i A i' m n,
    fut_action w i A (S i') m n
    -> rel A i' (prev m) (prev n).
Proof.
intros w I A i m n Hmn.
decompose Hmn.
intros p q Hi Hp Hq Hsteps Hsteps' Hact.
lapply Hact; [| omega].
cbn.
intro Hpq.
eapply urel_equiv; eauto.
  {
  apply hygiene_auto; cbn; auto.
  }

  {
  apply hygiene_auto; cbn; auto.
  }

  {
  apply equiv_symm.
  eapply equiv_trans.
    {
    apply equiv_prev.
    apply steps_equiv.
    exact Hsteps.
    }
  apply steps_equiv; apply star_one.
  apply step_prev2.
  }

  {
  apply equiv_symm.
  eapply equiv_trans.
    {
    apply equiv_prev.
    apply steps_equiv.
    exact Hsteps'.
    }
  apply steps_equiv; apply star_one.
  apply step_prev2.
  }
Qed.


Definition semifut_action
  (w : ordinal) i (A : wurel w) : nat -> relation (wterm w)
  :=
  fun i' m p =>
    i' <= i
    /\ hygiene clo m
    /\ hygiene clo p
    /\ (i' > 0 -> rel A (pred i') m p).


Lemma semifut_uniform :
  forall w i A, uniform _ (semifut_action w i A).
Proof.
intros w i A.
do2 3 split.

(* closed *)
{
intros i' m n H.
decompose H; auto.
}

(* equiv *)
{
intros i' m m' p p' Hclm' Hclp' Hequivm Hequivp Hact.
decompose Hact.
intros Hi _ _ Hact.
do2 3 split; auto.
intro Hpos.
so (Hact Hpos) as H.
eapply urel_equiv; eauto.
}

(* zigzag *)
{
intros i' m n p q Hmn Hpn Hpq.
decompose Hmn.
intros Hi Hclm _ Hmn.
decompose Hpn.
intros _ _ _ Hpn.
decompose Hpq.
intros _ _ Hclq Hpq.
do2 3 split; auto.
intro Hpos.
apply (urel_zigzag _#4 n p); auto.
}

(* downward *)
{
intros i' m p H.
decompose H.
intros Hi Hclm Hclp Hact.
do2 3 split; auto.
  {
  omega.
  }
intro Hpos.
apply (urel_downward_leq _#3 i').
  {
  omega.
  }
apply Hact.
omega.
}
Qed.


Definition semifut_urel w i A :=
  mk_urel (semifut_action w i A) (semifut_uniform _#3).


Definition iusemifut (w : ordinal) (i : nat) (A : wiurel w) : wiurel w
  :=
  (semifut_urel w i (den A),
   meta_half (meta_iurel A)).


Definition iusemifut0 (w : ordinal) : wiurel w
  :=
  (semifut_urel w 0 empty_urel,
   meta_half meta_null).


Lemma den_iusemifut :
  forall w i A,
    den (iusemifut w i A) = semifut_urel w i (den A).
Proof.
reflexivity.
Qed.


Lemma den_iusemifut0 :
  forall w,
    den (iusemifut0 w) = semifut_urel w 0 empty_urel.
Proof.
reflexivity.
Qed.


Lemma iusemifut_inj :
  forall w I I' A A',
    iusemifut w I A = iusemifut w I' A'
    -> A = A'.
Proof.
intros w I I' A A' Heq.
unfold iusemifut in Heq.
so (f_equal (fun z => snd z) Heq) as Heq'.
cbn in Heq'.
exact (meta_iurel_inj _#3 (meta_half_inj _#3 Heq')).
Qed.


Lemma ceiling_semifut :
  forall n w i A,
    ceiling (S n) (semifut_urel w i A)
    =
    semifut_urel w
      (min i n)
      (ceiling n A).
Proof.
intros n w i A.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros (Hj & Hact).
  decompose Hact.
  intros Hj' Hclm Hclp Hact.
  do2 3 split; auto.
    {
    apply Nat.min_glb; omega.
    }

    {
    intro Hpos.
    cbn.
    so (Hact Hpos) as H.
    split; auto.
    omega.
    }
  }

  {
  intro Hact.
  decompose Hact.
  intros Hj Hclm Hclp Hact.
  so (Nat.min_glb_l _#3 Hj) as Hji.
  so (Nat.min_glb_r _#3 Hj) as Hjn.
  split; [omega |].
  do2 3 split; auto.
  intro Hpos.
  so (Hact Hpos) as H.
  destruct H as (_ & H).
  auto.
  }
Qed.


Lemma iutruncate_iusemifut :
  forall n w i A,
    n > 1
    -> iutruncate n (iusemifut w i A)
       =
       iusemifut w
         (min i (pred n))
         (iutruncate (pred n) A).
Proof.
intros n w i A Hpos.
unfold iusemifut.
unfold iutruncate.
cbn [fst snd].
f_equal.
  {
  destruct n as [| n]; [omega |].
  apply ceiling_semifut.
  }

  {
  rewrite -> meta_truncate_half; [| omega].
  f_equal.
  rewrite -> meta_truncate_iurel; auto.
  omega.
  }
Qed.


Lemma iutruncate_iusemifut_one :
  forall w i A,
    iutruncate 1 (iusemifut w i A)
    =
    iusemifut0 w.
Proof.
intros w i A.
unfold iusemifut, iusemifut0.
unfold iutruncate.
cbn [fst snd].
f_equal.
  {
  rewrite -> ceiling_semifut.
  f_equal.
    {
    rewrite -> Nat.min_r; omega.
    }
  cbn.
  apply ceiling_zero.
  }

  {
  rewrite -> meta_truncate_half; [| omega].
  reflexivity.
  }
Qed.


Lemma iutruncate_iusemifut0 :
  forall n w,
    n > 0
    -> iutruncate n (iusemifut0 w)
       =
       iusemifut0 w.
Proof.
intros n w Hpos.
unfold iusemifut0.
unfold iutruncate.
cbn [fst snd].
f_equal.
  {
  destruct n as [| n]; [omega |].
  rewrite -> ceiling_semifut.
  f_equal.
  apply ceiling_empty_urel.
  }

  {
  rewrite -> meta_truncate_half; auto.
  rewrite -> meta_truncate_null.
  reflexivity.
  }
Qed.


Lemma extend_semifut :
  forall v w (h : v <<= w) I A,
    extend_urel v w (semifut_urel v I A)
    =
    semifut_urel w I
      (extend_urel v w A).
Proof.
intros v w h I A.
apply urel_extensionality.
fextensionality 3.
intros i m p.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros Hi Hclm Hclp Hact.
  do2 3 split; eauto using map_hygiene_conv.
  }

  {
  intro H.
  decompose H.
  intros Hi Hclm Hclp Hact.
  do2 3 split; auto using map_hygiene.
  }
Qed.


Lemma extend_iusemifut :
  forall v w (h : v <<= w) I A,
    extend_iurel h (iusemifut v I A)
    =
    iusemifut w I (extend_iurel h A).
Proof.
intros v w h I A.
unfold iusemifut, extend_iurel.
cbn.
f_equal.
  {
  apply extend_semifut; auto.
  }

  {
  rewrite -> extend_meta_half.
  f_equal.
  rewrite -> extend_meta_iurel.
  reflexivity.
  }
Qed.


Lemma extend_iusemifut0 :
  forall v w (h : v <<= w),
    extend_iurel h (iusemifut0 v)
    =
    iusemifut0 w.
Proof.
intros v w h.
unfold iusemifut0, extend_iurel.
cbn.
f_equal.
  {
  rewrite -> extend_semifut; auto.
  rewrite -> extend_empty_urel; auto.
  }

  {
  rewrite -> extend_meta_half.
  rewrite -> extend_meta_null.
  reflexivity.
  }
Qed.
