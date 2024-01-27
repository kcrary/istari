
Require Import Axioms.
Require Import Tactics.
Require Import Sigma.
Require Import Syntax.
Require Import Ordinal.
Require Import Candidate.
Require Import Semantics.
Require Import Extend.
Require Import System.
Require Import Uniform.
Require Import Ofe.
Require Import SemanticsKind.
Require Import SemanticsUniv.
Require Import Page.
Require Import Equality.
Require Import SemanticsProperty.


Definition agree (pg : page) (system system' : System) : Prop :=
  sint system pg = sint system' pg
  /\ sintk system pg = sintk system' pg.


Lemma semantics_mono :
  forall system system',
    (forall pg s i a X,
       (forall pg', str pg' << str pg -> agree pg' system system')
       -> kbasic system pg s i a X
       -> kbasic system' pg s i a X)
    /\
    (forall pg s i a X,
       (forall pg', str pg' << str pg -> agree pg' system system')
       -> cbasic system pg s i a X
       -> cbasic system' pg s i a X)
    /\
    (forall pg s i a X,
       (forall pg', str pg' << str pg -> agree pg' system system')
       -> basic system pg s i a X
       -> basic system' pg s i a X).
Proof.
intros system system'.
exploit
  (semantics_ind system
     (fun pg s i a X => 
        (forall pg', str pg' << str pg -> agree pg' system system')
        -> kbasicv system' pg s i a X)
     (fun pg s i a X => 
        (forall pg', str pg' << str pg -> agree pg' system system')
        -> cbasicv system' pg s i a X)
     (fun pg s i a X => 
        (forall pg', str pg' << str pg -> agree pg' system system')
        -> basicv system' pg s i a X)
     (fun pg s i a X => 
        (forall pg', str pg' << str pg -> agree pg' system system')
        -> kbasic system' pg s i a X)
     (fun pg s i a X => 
        (forall pg', str pg' << str pg -> agree pg' system system')
        -> cbasic system' pg s i a X)
     (fun pg s i a X => 
        (forall pg', str pg' << str pg -> agree pg' system system')
        -> basic system' pg s i a X)
     (fun pg s i A a X => 
        (forall pg', str pg' << str pg -> agree pg' system system')
        -> functional system' pg s i A a X)) as Hind;
try (intros; eauto using kbasicv, cbasicv, basicv, kbasic, cbasic, basic, functional, lt_le_ord_trans; done).

(* con *)
{
intros pg s i lv a gpg R Hlv Hle _ IH Hincl.
apply interp_con; auto.
apply IH.
intros pg' Hlt.
apply Hincl.
eapply lt_le_ord_trans; eauto.
apply str_mono; auto.
}

(* all *)
{
intros pg s i lv k a gpg K A h Hlv _ IH1 Hle _ IH2 Hincl.
apply (interp_all _#7 gpg _ _ h); auto.
apply IH1.
intros pg' Hlt.
apply Hincl.
eapply lt_le_ord_trans; eauto.
apply str_mono; auto.
}

(* exist *)
{
intros pg s i lv k a gpg K A h Hlv _ IH1 Hle _ IH2 Hincl.
apply (interp_exist _#7 gpg _ _ h); auto.
apply IH1.
intros pg' Hlt.
apply Hincl.
eapply lt_le_ord_trans; eauto.
apply str_mono; auto.
}

(* univ *)
{
intros pg s i lv gpg Hlv Hstr Hcex Hincl.
replace (iuuniv system i gpg) with (iuuniv system' i gpg).
  {
  apply interp_univ; auto.
  }
unfold iuuniv.
f_equal.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
so (Hincl gpg Hstr andel) as Heq.
pextensionality.
  {
  intros (Hj & R & H).
  split; auto.
  exists R.
  rewrite <- Heq in H.
  auto.
  }

  {
  intros (Hj & R & H).
  split; auto.
  exists R.
  rewrite -> Heq in H.
  auto.
  }
}

(* kind *)
{
intros pg s i lv gpg h Hlv Hlt Hincl.
replace (iukind system i gpg h) with (iukind system' i gpg h).
  {
  apply interp_kind; auto.
  }
unfold iukind.
f_equal.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
so (lt_le_page_trans _#3 (lt_page_succ _ _) (lt_page_impl_le_page _ _ Hlt)) as Hlt'.
so (Hincl gpg (Hlt' andel) ander) as HeqK.
so (Hincl (succ_page gpg h) (Hlt andel) andel) as HeqR.
pextensionality.
  {
  intros (Hj & K & R & H).
  split; auto.
  exists K, R.
  rewrite <- HeqK in H.
  rewrite <- HeqR in H.
  auto.
  }

  {
  intros (Hj & K & R & H).
  split; auto.
  exists K, R.
  rewrite -> HeqK in H.
  rewrite -> HeqR in H.
  auto.
  }
}

(* wrapup *)
{
destruct_all Hind; do2 2 split; intros; eauto.
}
Qed.


Lemma kbasic_mono :
  forall system system' pg s i a R,
    (forall pg', str pg' << str pg -> agree pg' system system')
    -> kbasic system pg s i a R
    -> kbasic system' pg s i a R.
Proof.
intros system system'.
exact (semantics_mono system system' andel).
Qed.


Lemma basic_mono :
  forall system system' pg s i a R,
    (forall pg', str pg' << str pg -> agree pg' system system')
    -> basic system pg s i a R
    -> basic system' pg s i a R.
Proof.
intros system system'.
exact (semantics_mono system system' anderr).
Qed.
