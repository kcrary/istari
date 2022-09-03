
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
Require Import Model.
Require Import Page.
Require Import PreSpacify.
Require Import Standard.


Definition all_action
  (w : ordinal) (K : qkind) (B : spcar K -> wurel w)
  : nat -> relation (wterm w)
  :=
  fun i m m' =>
    forall j (x : spcar (approx j K)),
      j <= i
      -> rel (B (embed j K x)) j m m'.


Lemma all_uniform :
  forall w K B, uniform _ (all_action w K B).
Proof.
intros w K B.
do2 3 split.

(* closed *)
{
intros j m n Hact.
exact (urel_closed _#5 (Hact j (space_inhabitant _) (le_refl _))).
}

(* equiv *)
{
intros j m m' n n' Hclm' Hcln' Hm Hn Hact.
intros j' x Hj'.
eapply urel_equiv; eauto.
}

(* zigzag *)
{
intros j m n p q Hmn Hpn Hpq.
intros j' x Hj'.
so (Hmn j' x Hj') as Hmn'.
so (Hpn j' x Hj') as Hpn'.
so (Hpq j' x Hj') as Hpq'.
eapply urel_zigzag; eauto.
}

(* downward *)
{
intros j m n H.
intros k x Hk.
apply H.
omega.
}
Qed.


Definition all_urel w K B :=
  mk_urel (all_action w K B) (all_uniform _ _ _).


Lemma extend_all_urel :
  forall v w K B,
    v <<= w
    -> extend_urel v w (all_urel v K B)
       =
       all_urel w K (fun x => extend_urel v w (B x)).
Proof.
intros v w K B Hvw.
apply urel_extensionality.
fextensionality 3.
intros j m m'.
cbn.
pextensionality; auto.
Qed.


Lemma ceiling_all_urel :
  forall n w K (B : car (space K) -> car (wurel_ofe w)),
    ceiling (S n) (all_urel w K B)
    =
    all_urel w
      (approx n K)
      (fun x => ceiling (S n) (B (embed n K x))).
Proof.
intros n w K B.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros (Hj & Hact).
  intros j' x Hj'.
  assert (j' <= n) as Hj'_n by omega.
  so (Hact j' (transport (approx_combine_le _#3 Hj'_n) spcar x) Hj') as Hrel.
  rewrite -> (embed_combine_le _#4 Hj'_n).
  split; auto.
  omega.
  }

  {
  intro Hact.
  so (Hact j (space_inhabitant _) (le_refl _)) as (Hjn & _).
  split; auto.
  intros j' x Hj'.
  assert (j' <= n) as Hj'_n by omega.
  so (Hact j' (transport (eqsymm (approx_combine_le _#3 Hj'_n)) spcar x) Hj') as H.
  destruct H as (_ & H).
  rewrite -> (embed_combine_le _#4 Hj'_n) in H.
  rewrite -> transport_compose in H.
  rewrite <- (proof_irrelevance _ (eq_refl (approx j' K)) (eqtrans (eqsymm (approx_combine_le _#3 Hj'_n)) (approx_combine_le _#3 Hj'_n))) in H.
  exact H.
  }
Qed.


Definition iuall w (K : qkind) (B : space K -n> wiurel_ofe w) : wiurel w
  :=
  iubase (all_urel w K (fun x => den (pi1 B x))).


Lemma extend_iuall :
  forall v w (h : v <<= w) K B,
    extend_iurel h (iuall v K B)
    =
    iuall w K (nearrow_compose (extend_iurel_ne h) B).
Proof.
intros v w h K B.
unfold iuall, extend_iurel, extend_iurel, iubase.
cbn.
f_equal.
  {
  apply extend_all_urel; auto.
  }

  {
  apply extend_meta_null.
  }
Qed.


Lemma iutruncate_iuall :
  forall n w K (B : space K -n> wiurel_ofe w),
    iutruncate (S n) (iuall w K B)
    =
    iuall w (approx n K)
      (nearrow_compose2 
         (embed_ne n K) (iutruncate_ne (S n)) B).
Proof.
intros n w K B.
unfold iuall, iutruncate, iubase.
f_equal.
  {
  apply ceiling_all_urel.
  }

  {
  apply meta_truncate_null.
  }
Qed.


Definition alltp_action w (B : wiurel top -> wurel w)
  : nat -> relation (wterm w)
  :=
  fun i m m' =>
    forall j (X : wiurel top),
      j <= i
      -> rel (B X) j m m'.


Lemma alltp_uniform :
  forall w B, uniform _ (alltp_action w B).
Proof.
intros w B.
do2 3 split.

(* closed *)
{
intros j m n Hact.
exact (urel_closed _#5 (Hact j (iubase empty_urel) (le_refl _))).
}

(* equiv *)
{
intros j m m' n n' Hclm' Hcln' Hm Hn Hact.
intros j' x Hj'.
eapply urel_equiv; eauto.
}

(* zigzag *)
{
intros j m n p q Hmn Hpn Hpq.
intros j' x Hj'.
so (Hmn j' x Hj') as Hmn'.
so (Hpn j' x Hj') as Hpn'.
so (Hpq j' x Hj') as Hpq'.
eapply urel_zigzag; eauto.
}

(* downward *)
{
intros j m n H.
intros k x Hk.
apply H.
omega.
}
Qed.


Definition alltp_urel w B :=
  mk_urel (alltp_action w B) (alltp_uniform _ _).


Lemma extend_alltp_urel :
  forall v w B,
    v <<= w
    -> extend_urel v w (alltp_urel v B)
       =
       alltp_urel w (fun X => extend_urel v w (B X)).
Proof.
intros v w B Hvw.
apply urel_extensionality.
fextensionality 3.
intros j m m'.
cbn.
pextensionality; auto.
Qed.


Lemma ceiling_alltp_urel :
  forall n w (B : wiurel top -> car (wurel_ofe w)),
    ceiling (S n) (alltp_urel w B)
    =
    alltp_urel w
      (fun X => ceiling (S n) (B X)).
Proof.
intros n w B.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros (Hj & Hact).
  intros j' X Hj'.
  split; [omega |].
  apply Hact; auto.
  }

  {
  intro Hact.
  so (Hact j (iubase empty_urel) (le_refl _)) as (Hjn & _).
  split; auto.
  intros j' X Hj'.
  so (Hact j' X Hj') as Hmp.
  destruct Hmp; auto.
  }
Qed.


Definition iualltp w (B : wiurel_ofe top -n> wiurel_ofe w) : wiurel w
  :=
  iubase (alltp_urel w (fun X => den (pi1 B X))).


Lemma extend_iualltp :
  forall v w (h : v <<= w) B,
    extend_iurel h (iualltp v B)
    =
    iualltp w (nearrow_compose (extend_iurel_ne h) B).
Proof.
intros v w h B.
unfold iualltp, extend_iurel, extend_iurel, iubase.
cbn.
f_equal.
  {
  apply extend_alltp_urel; auto.
  }

  {
  apply extend_meta_null.
  }
Qed.


Lemma iutruncate_iualltp :
  forall n w (B : wiurel_ofe top -n> wiurel_ofe w),
    iutruncate (S n) (iualltp w B)
    =
    iualltp w
      (nearrow_compose (iutruncate_ne (S n)) B).
Proof.
intros n w B.
unfold iualltp, iutruncate, iubase.
f_equal.
  {
  apply ceiling_alltp_urel.
  }

  {
  apply meta_truncate_null.
  }
Qed.
