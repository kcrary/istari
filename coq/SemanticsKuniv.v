
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


Definition kuniv_action (system : System) (i : nat) (pg : page) (h : lt_page pg toppg)
  : nat -> relation sterm
  :=
  fun j a b =>
    j <= i
    /\ exists (K : qkind) (R : siurel),
         sintk system pg true j a K
         /\ sintk system pg false j b K
         /\ sint system (succ_page pg h) true j a R
         /\ sint system (succ_page pg h) false j b R.


Lemma kuniv_uniform :
  forall system i pg h, uniform _ (kuniv_action system i pg h).
Proof.
intros system i pg.
do2 3 split.

(* closed *)
{
intros j a b H.
decompose H.
intros Hj K R _ _ HaR HbR.
eauto using sint_closed.
}

(* equiv *)
{
intros j a a' b b' Hcla' Hclb' Ha Hb H.
decompose H.
intros Hj K R Hc Hd Hct Hdt.
split; auto.
exists K, R.
do2 3 split; eauto using sint_equiv, sintk_equiv.
}

(* zigzag *)
{
intros j a b c d Hab Hcb Hcd.
decompose Hab.
intros Hj K R HaK HbK HaR HbR.
decompose Hcb.
intros _ K' R' HcK HbK' HcR HbR'.
so (sintk_fun _#7 HbK HbK'); subst K'.
so (sint_fun _#7 HbR HbR'); subst R'.
decompose Hcd.
intros _ K' R' HcK' HdK HcR' HdR.
so (sintk_fun _#7 HcK HcK'); subst K'.
so (sint_fun _#7 HcR HcR'); subst R'.
split; auto.
exists K, R.
auto.
}

(* downward *)
{
intros j a b H.
decompose H.
intros Hj K R Hl Hr Hlt Hrt.
assert (j <= S j) as Hle by omega.
so (sintk_downward _#7 Hle Hl) as Hl'.
so (sintk_downward _#7 Hle Hr) as Hr'.
so (sint_downward _#7 Hle Hlt) as Hlt'.
so (sint_downward _#7 Hle Hrt) as Hrt'.
split; [omega |].
exists (approx j K), (iutruncate (S j) R).
auto.
}
Qed.


Definition kuniv_urel system i pg h : surel :=
  mk_urel (kuniv_action system i pg h) (kuniv_uniform _ _ _ _).


Definition iukuniv system i pg h : siurel :=
  (kuniv_urel system i pg h,
   meta_page pg).


Lemma den_iukuniv :
  forall system i pg h,
    den (iukuniv system i pg h) = kuniv_urel system i pg h.
Proof.
reflexivity.
Qed.


Lemma iukuniv_inj :
  forall system i i' pg pg' h h',
    iukuniv system i pg h = iukuniv system i' pg' h'
    -> pg = pg'.
Proof.
intros system i i' pg pg' h h' Heq.
unfold iukuniv in Heq.
so (f_equal (fun z => snd z) Heq) as Heq'.
cbn in Heq'.
exact (meta_page_inj _#3 Heq').
Qed.


Lemma ceiling_kuniv_urel :
  forall n system i pg h,
    ceiling (S n) (kuniv_urel system i pg h)
    =
    kuniv_urel system (min i n) pg h.
Proof.
intros n system i pg h.
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


Lemma iutruncate_iukuniv :
  forall n system i pg h,
    iutruncate (S n) (iukuniv system i pg h)
    =
    iukuniv system (min i n) pg h.
Proof.
intros n system i pg h.
unfold iukuniv, iutruncate.
cbn [fst snd].
f_equal.
  {
  apply ceiling_kuniv_urel.
  }

  {
  rewrite -> meta_truncate_page; auto.
  omega.
  }
Qed.
