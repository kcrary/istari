
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
Require Import Standard.
Require Import Equivalences.
Require Import ExtendTruncate.
Require Import SemanticsSigma.


Definition set_action
  (w : ordinal) (A : wurel w) (B : urelsp_car A -> wurel w)
  : nat -> relation (wterm w)
  :=
  fun i m m' =>
    exists n n' (Hm : rel A i m m'),
      rel (B (urelspinj A i m m' Hm)) i n n'.


Lemma set_uniform :
  forall w A (B : urelsp A -n> wurel_ofe w), uniform _ (set_action w A (pi1 B)).
Proof.
intros w A B.
do2 3 split.

(* closed *)
{
intros i m n H.
destruct H as (_ & _ & H & _).
eapply urel_closed; eauto.
}

(* equiv *)
{
intros i m m' n n' Hclm' Hcln' Hequivm Hequivn Hmn.
destruct Hmn as (p & q & Hmn & Hpq).
assert (rel A i m' n') as Hmn'.
  {
  eapply urel_equiv; eauto.
  }
exists p, q, Hmn'.
force_exact Hpq.
do 2 f_equal.
apply urelspinj_equal.
eapply urel_equiv_2; eauto.
}

(* zigzag *)
{
intros i m n p q Hmn Hpn Hpq.
destruct Hmn as (r & t & Hmn & Hrt).
destruct Hpn as (_ & _ & Hpn & _).
destruct Hpq as (_ & _ & Hpq & _).
assert (rel A i m q) as Hmq.
  {
  eapply urel_zigzag; eauto.
  }
exists r, t, Hmq.
force_exact Hrt.
do 2 f_equal.
apply urelspinj_equal; auto.
}

(* downward *)
{
intros i m m' Hm.
destruct Hm as (n & n' & Hm & Hn).
exists n, n', (urel_downward _#5 Hm).
refine (rel_from_dist _#6 _ (urel_downward _#5 Hn)).
apply (pi2 B).
apply urelspinj_dist_diff; auto.
apply urel_downward; auto.
}
Qed.


Definition set_urel w A B :=
  mk_urel (set_action w A (pi1 B)) (set_uniform _ _ _).


Lemma ceiling_set :
  forall n w A B,
    ceiling (S n) (set_urel w A B)
    =
    set_urel w
      (ceiling (S n) A)
      (nearrow_compose2 (embed_ceiling_ne (S n) A) (ceiling_ne (S n)) B).
Proof.
intros n w A B.
apply urel_extensionality.
fextensionality 3.
intros i m p.
cbn.
pextensionality.
  {
  intros (Hi, Hact).
  decompose Hact.
  intros q r Hmp Hqr.
  exists q, r, (conj Hi Hmp).
  rewrite -> embed_ceiling_urelspinj.
  split; auto.
  }

  {
  intro Hact.
  decompose Hact.
  intros q r Hmp Hqr.
  destruct Hmp as (Hi & Hmp).
  destruct Hqr as (_ & Hqr).
  split; auto.
  exists q, r, Hmp.
  rewrite -> embed_ceiling_urelspinj in Hqr; auto.
  }
Qed.


Lemma extend_set :
  forall v w (h : v <<= w) A B,
    extend_urel v w (set_urel v A B)
    =
    set_urel w 
      (extend_urel v w A)
      (nearrow_compose2 (deextend_urelsp_ne h A) (extend_urel_ne v w) B).
Proof.
intros v w h A B.
apply urel_extensionality.
fextensionality 3.
intros i m p.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros n q Hmp Hnq.
  exists (map_term (extend v w) n), (map_term (extend v w) q), Hmp.
  cbn.
  rewrite -> deextend_urelsp_urelspinj.
  rewrite -> !extend_term_cancel; auto.
  }

  {
  intro H.
  decompose H.
  intros n q Hmp Hnq.
  rewrite -> deextend_urelsp_urelspinj in Hnq.
  cbn in Hnq.
  exists (map_term (extend w v) n), (map_term (extend w v) q), Hmp.
  exact Hnq.
  }
Qed.


Definition iuset (w : ordinal) (A : wiurel w) (B : urelsp (den A) -n> wiurel_ofe w) : wiurel w
  :=
  (set_urel w (den A) (nearrow_compose den_ne B),
   meta_iurel A).


Lemma iuset_inj :
  forall w A A' B B',
    iuset w A B = iuset w A' B'
    -> A = A'.
Proof.
intros w A A' B B' Heq.
unfold iuset in Heq.
so (f_equal (fun z => snd z) Heq) as Heq'.
cbn in Heq'.
exact (meta_iurel_inj _#3 Heq').
Qed.


Lemma iutruncate_iuset :
  forall n w A B,
    iutruncate (S n) (iuset w A B)
    =
    iuset w 
      (iutruncate (S n) A)
      (nearrow_compose
         (nearrow_compose (iutruncate_ne (S n)) B)
         (embed_ceiling_ne (S n) (den A))).
Proof.
intros n w A B.
assert (S n > 0) as Hpos by omega.
unfold iuset.
unfold iutruncate.
unfold den.
cbn [fst snd].
f_equal.
  {
  rewrite -> ceiling_set.
  f_equal.
  apply nearrow_extensionality.
  auto.
  }

  {
  apply meta_truncate_iurel; auto.
  }
Qed.


Lemma extend_iuset :
  forall v w (h : v <<= w) A B,
    extend_iurel h (iuset v A B)
    =
    iuset w (extend_iurel h A)
      (nearrow_compose
         (nearrow_compose (extend_iurel_ne h) B)
         (deextend_urelsp_ne h (den A))).
Proof.
intros v w h A B.
unfold iuset, extend_iurel.
cbn.
f_equal.
  {
  rewrite -> (extend_set _ _ h).
  f_equal.
  apply nearrow_extensionality; auto.
  }
rewrite -> extend_meta_iurel.
reflexivity.
Qed.
