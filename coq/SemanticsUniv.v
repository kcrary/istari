
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
Require Import Page.


Definition univ_action (system : System) (i : nat) (pg : page) 
  : nat -> relation sterm
  :=
  fun j a b =>
    j <= i
    /\ exists (R : siurel),
         sint system pg true j a R
         /\ sint system pg false j b R.


Lemma univ_uniform :
  forall system i pg, uniform _ (univ_action system i pg).
Proof.
intros system i pg.
do2 3 split.

(* closed *)
{
intros j a b H.
decompose H.
intros Hj R HaR HbR.
eauto using sint_closed.
}

(* equiv *)
{
intros j a a' b b' Hcla' Hclb' Ha Hb H.
decompose H.
intros Hj R Hc Hd.
split; auto.
exists R.
split; eapply sint_equiv; eauto.
}

(* zigzag *)
{
intros j a b c d Hab Hcb Hcd.
decompose Hab.
intros Hj R HaR HbR.
decompose Hcb.
intros _ R' HcR HbR'.
so (sint_fun _#7 HbR HbR'); subst R'.
decompose Hcd.
intros _ R' HcR' HdR.
so (sint_fun _#7 HcR HcR'); subst R'.
split; auto.
exists R.
auto.
}

(* downward *)
{
intros j a b H.
decompose H.
intros Hj R Hl Hr.
assert (j <= S j) as Hle by omega.
so (sint_downward _#7 Hle Hl) as Hl'.
so (sint_downward _#7 Hle Hr) as Hr'.
split; [omega |].
exists (iutruncate (S j) R).
auto.
}
Qed.


Definition univ_urel system i pg : surel :=
  mk_urel (univ_action system i pg) (univ_uniform _ _ _).


Definition iuuniv system i pg : siurel :=
  (univ_urel system i pg,
   meta_page pg).


Lemma den_iuuniv :
  forall system i pg,
    den (iuuniv system i pg) = univ_urel system i pg.
Proof.
reflexivity.
Qed.


Lemma iuuniv_inj :
  forall system i i' pg pg',
    iuuniv system i pg = iuuniv system i' pg'
    -> pg = pg'.
Proof.
intros system i i' pg pg' Heq.
unfold iuuniv in Heq.
so (f_equal (fun z => snd z) Heq) as Heq'.
cbn in Heq'.
exact (meta_page_inj _#3 Heq').
Qed.


Lemma ceiling_univ_urel :
  forall n system i pg,
    ceiling (S n) (univ_urel system i pg)
    =
    univ_urel system (min i n) pg.
Proof.
intros n system i pg.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros (Hj & Hj' & Hmp).
  split; auto.
  apply Nat.min_glb; omega.
  }

  {
  intros (Hj & Hmp).
  so (Nat.min_glb_l _#3 Hj).
  so (Nat.min_glb_r _#3 Hj).
  split; [omega |].
  split; auto.
  }
Qed.


Lemma iutruncate_iuuniv :
  forall n system i pg,
    iutruncate (S n) (iuuniv system i pg)
    =
    iuuniv system (min i n) pg.
Proof.
intros n system i pg.
unfold iuuniv, iutruncate.
cbn [fst snd].
f_equal.
  {
  apply ceiling_univ_urel.
  }

  {
  rewrite -> meta_truncate_page; auto.
  omega.
  }
Qed.
