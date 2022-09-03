
Require Import Axioms.
Require Import Tactics.
Require Import Relation.
Require Import Sigma.
Require Import Equality.
Require Import Syntax.
Require Import Hygiene.
Require Import Reduction.
Require Import Equivalence.
Require Import MapTerm.
Require Import Ofe.
Require Import Uniform.
Require Import Urelsp.
Require Import Ordinal.
Require Import Candidate.
Require Import Intensional.
Require Import IntensionalNerect.
Require Import Ceiling.
Require Import Truncate.
Require Import Standard.
Require Import Extend.


(* Doesn't really belong here, but it has to go somewhere. *)
Lemma urelsp_index_deextend :
  forall v w (h : v <<= w) A (x : urelsp_car (extend_urel v w A)),
    urelsp_index A (deextend_urelsp h A x) = urelsp_index (extend_urel v w A) x.
Proof.
intros v w h A x.
so (urelsp_eta _ _ x) as (i & m & p & Hmp & ->).
rewrite -> deextend_urelsp_urelspinj.
rewrite -> !urelsp_index_inj.
reflexivity.
Qed.


Lemma ceiling_extend_urel :
  forall v w i A,
    ceiling i (extend_urel v w A)
    = extend_urel v w (ceiling i A).
Proof.
intros v w i A.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
reflexivity.
Qed.


Lemma extend_meta_truncate :
  forall i v w R (h : v <<= w),
    extend_meta h (meta_truncate i R)
    =
    meta_truncate i (extend_meta h R).
Proof.
intros i v w x h.
destruct i as [| i].
  {
  rewrite -> !meta_truncate_zero.
  rewrite -> extend_meta_nats.
  reflexivity.
  }
assert (S i > 0) as Hpos by omega.
revert i Hpos.
pattern x.
apply meta_rect; clear x.

(* nats *)
{
intros I i Hpos.
rewrite -> meta_truncate_nats.
rewrite -> !extend_meta_nats.
rewrite -> meta_truncate_nats.
reflexivity.
}

(* fn *)
{
intros R f IH i Hpos.
rewrite -> meta_truncate_fn; auto.
rewrite -> !extend_meta_fn.
rewrite -> meta_truncate_fn; auto.
set (heq := ceiling_extend_urel v w (S i) R).
symmetry.
apply f_equal_dep.
apply (eq_impl_eq_dep _#6 heq).  
apply nearrow_extensionality.
intros x.
rewrite -> (pi1_transport_dep_lift _ _ (fun R' g => @nonexpansive (urelsp R') (meta_ofe (obj w)) g) _ _ heq).
rewrite -> (app_transport_dom _ urelsp_car (meta (obj w)) _ _ heq).
unfold nearrow_compose.
cbn [pi1].
cbn -[meta_truncate].
symmetry.
rewrite -> IH; auto.
f_equal.
f_equal.
f_equal.
apply exT_extensionality_prop.
cbn.
fextensionality 2.
intros j m.
rewrite -> (pi1_transport_lift _ _ urelsp_car_rhs _ _ (eqsymm heq)).
reflexivity.
}

(* pair *)
{
intros x IH1 y IH2 i Hpos.
rewrite -> meta_truncate_pair; auto.
rewrite -> !extend_meta_pair.
rewrite -> meta_truncate_pair; auto.
f_equal; auto.
}

(* half *)
{
intros x IH i Hpos.
rewrite -> meta_truncate_half; auto.
rewrite -> !extend_meta_half.
rewrite -> meta_truncate_half; auto.
f_equal; auto.
cbn.
destruct i as [| i].
  {
  rewrite -> !meta_truncate_zero.
  rewrite -> extend_meta_nats.
  reflexivity.
  }
apply IH.
omega.
}

(* page *)
{
intros pg i Hpos.
rewrite -> meta_truncate_page; auto.
rewrite -> !extend_meta_page.
rewrite -> meta_truncate_page; auto.
}
Qed.


Lemma iutruncate_extend_iurel :
  forall i v w R (h : v <<= w),
    iutruncate i (extend_iurel h R)
    =
    extend_iurel h (iutruncate i R).
Proof.
intros i v w R h.
unfold iutruncate, extend_iurel.
cbn.
f_equal.
  {
  rewrite -> ceiling_extend_urel.
  reflexivity.
  }

  {
  rewrite -> extend_meta_truncate.
  reflexivity.
  }
Qed.
