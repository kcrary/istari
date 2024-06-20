
Require Import Tactics.
Require Import Sigma.
Require Import Relation.
Require Import Syntax.
Require Import SimpSub.
Require Import Dynamic.
Require Import Ofe.
Require Import Spaces.
Require Import Uniform.
Require Import Urelsp.
Require Import Intensional.
Require Import Ordinal.
Require Import Candidate.
Require Import Model.
Require Import Standard.
Require Import Hygiene.
Require Import Equivalence.
Require Import Equivalences.
Require Import System.
Require Import Extend.
Require Import Semantics.
Require Import MapTerm.
Require Import Model.
Require Import SemanticsEqual.
Require Import SemanticsPartial.


Section semantics.


Variable system : System.


Lemma interp_kext_closed :
  forall pg i k K,
    interp_kext pg i k K
    -> hygiene clo k.
Proof.
intros pg i k K H.
decompose H; auto.
Qed.


Lemma interp_uext_closed :
  forall pg i a A,
    interp_uext pg i a A
    -> hygiene clo a.
Proof.
intros pg i a A H.
decompose H; auto.
Qed.


Lemma semantics_closed :
  (forall pg s i a K,
     kbasicv system pg s i a K
     -> hygiene clo a)
  /\
  (forall pg s i a Q,
     cbasicv system pg s i a Q
     -> hygiene clo a)
  /\
  (forall pg s i a R,
     basicv system pg s i a R
     -> hygiene clo a)
  /\
  (forall pg s i a K,
     kbasic system pg s i a K
     -> hygiene clo a)
  /\
  (forall pg s i a Q,
     cbasic system pg s i a Q
     -> hygiene clo a)
  /\
  (forall pg s i a R,
     basic system pg s i a R
     -> hygiene clo a).
Proof.
exploit
  (semantics_ind system
     (fun _ s i a _ => hygiene clo a)
     (fun _ s i a _ => hygiene clo a)
     (fun _ s i a _ => hygiene clo a)
     (fun _ s i a _ => hygiene clo a)
     (fun _ s i a _ => hygiene clo a)
     (fun _ s i a _ => hygiene clo a)
     (fun _ s i A b _ => hygiene (permit clo) b)) as Hind;
try (intros;
     auto;
     apply hygiene_auto;
     cbn;
     eauto 6 using map_hygiene_conv, pginterp_closed;
     done).

(* krec *)
{
intros pg s i k K _ IH.
apply hygiene_auto.
cbn.
split; auto.
eapply hygiene_clo_subst1_invert_permit; eauto.
}

(* clam *)
{
intros pg s i k a K L A h _ Hk _ IH.
so (interp_kext_closed _#4 Hk).
so (hygiene_clo_subst1_invert_permit _#3 (IH i (le_refl _) (space_inhabitant _))).
apply hygiene_auto; cbn.
auto.
}

(* ctlam *)
{
intros pg s i a b k K A f B Hclb Ka Hk _ _ _.
apply hygiene_auto; cbn.
do2 2 split; eauto using interp_kext_closed, interp_uext_closed.
}

(* ctapp *)
{
intros pg s i b m l A K B n p Hnp Hm _ IH.
apply hygiene_auto; cbn.
do2 2 split; auto.
apply (map_hygiene_conv _ _ (extend stop l)).
rewrite -> Hm.
so (urel_closed _#5 Hnp) as (Hcln, Hclp).
destruct s; auto.
}

(* quotient *)
{
intros pg s i a b A B hs ht _ IH1 _ IH2.
apply hygiene_auto; cbn.
do2 2 split; auto.
so (hygiene_subst_invert _#4 IH2) as H.
eapply hygiene_weaken; eauto; clear H.
intros j Hj.
destruct j as [|[|j]]; cbn; auto.
simpsubin Hj.
unfold clo.
invert Hj.
intro H.
cbn in H.
destruct H.
}

(* guard *)
{
intros pg s i a b A B _ IH1 _ IH2.
apply hygiene_auto; cbn.
do2 2 split; auto.
apply hygiene_shift_permit_iff; auto.
}

(* coguard *)
{
intros pg s i a b A B _ IH1 _ IH2.
apply hygiene_auto; cbn.
do2 2 split; auto.
apply hygiene_shift_permit_iff; auto.
}

(* equal *)
{
intros pg s i a m n p q A Hmp Hnq _ IH.
so (srel_closed _#6 Hmp) as (Hclm & _).
so (srel_closed _#6 Hnq) as (Hcln & _).
apply hygiene_auto; cbn.
do2 3 split; eauto using map_hygiene_conv.
}

(* all *)
{
intros pg s i lv k a gpg K A h Hlv _ Hclk _ _ IH.
so (pginterp_closed _ _ Hlv) as Hcllv.
so (hygiene_clo_subst1_invert_permit _#3 (IH i (le_refl _) (space_inhabitant _))).
apply hygiene_auto; cbn; auto.
}

(* alltp *)
{
intros pg s i a A _ IH.
so (hygiene_clo_subst1_invert_permit _#3 (IH i (le_refl _) (iubase empty_urel))).
apply hygiene_auto; cbn; auto.
}

(* exist *)
{
intros pg s i lv k a gpg K A h Hlv _ Hclk _ _ IH.
so (pginterp_closed _ _ Hlv) as Hcllv.
so (hygiene_clo_subst1_invert_permit _#3 (IH i (le_refl _) (space_inhabitant _))).
apply hygiene_auto; cbn; auto.
}

(* mu *)
{
intros pg w s i a F Hw _ IH _ _ _.
so (hygiene_clo_subst1_invert_permit _#3 (IH empty_urel (le_ord_succ _ _ (le_ord_trans _#3 Hw (cin_top pg))))) as H.
apply hygiene_auto; cbn; auto.
}

(* rec *)
{
intros pg s i k K _ IH.
apply hygiene_auto.
cbn.
split; auto.
eapply hygiene_clo_subst1_invert_permit; eauto.
}

(* wrapup *)
{
do 6 (destruct Hind as (? & Hind)).
do2 3 split; intros; eauto.
}
Qed.


Lemma kbasicv_closed :
  forall pg s i a K,
    kbasicv system pg s i a K
    -> hygiene clo a.
Proof.
exact (semantics_closed andel).
Qed.


Lemma cbasicv_closed :
  forall pg s i a Q,
    cbasicv system pg s i a Q
    -> hygiene clo a.
Proof.
exact (semantics_closed anderl).
Qed.


Lemma basicv_closed :
  forall pg s i a R,
    basicv system pg s i a R
    -> hygiene clo a.
Proof.
exact (semantics_closed anderrl).
Qed.


Lemma kbasic_closed :
  forall pg s i a K,
    kbasic system pg s i a K
    -> hygiene clo a.
Proof.
exact (semantics_closed anderrrl).
Qed.


Lemma cbasic_closed :
  forall pg s i a Q,
    cbasic system pg s i a Q
    -> hygiene clo a.
Proof.
exact (semantics_closed anderrrrl).
Qed.


Lemma basic_closed :
  forall pg s i a R,
    basic system pg s i a R
    -> hygiene clo a.
Proof.
exact (semantics_closed anderrrrr).
Qed.


Lemma kinterp_eval_refl :
  forall pg s i a K,
    kbasicv system pg s i a K
    -> kbasic system pg s i a K.
Proof.
intros pg s i a K H.
eapply kinterp_eval; eauto using star_refl, kbasicv_closed.
Qed.


Lemma cinterp_eval_refl :
  forall pg s i a Q,
    cbasicv system pg s i a Q
    -> cbasic system pg s i a Q.
Proof.
intros pg s i a K H.
eapply cinterp_eval; eauto using star_refl, cbasicv_closed.
Qed.


Lemma interp_eval_refl :
  forall pg s i a R,
    basicv system pg s i a R
    -> basic system pg s i a R.
Proof.
intros pg s i a K H.
eapply interp_eval; eauto using star_refl, basicv_closed.
Qed.


End semantics.
