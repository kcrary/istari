
Require Import Omega.
Require Import Relation_Definitions.

Require Import Axioms.

Require Import Tactics.
Require Import Sigma.
Require Import Equality.
Require Import Ofe.
Require Import Spaces.
Require Import Syntax.
Require Import Uniform.
Require Import Urelsp.
Require Import Intensional.
Require Import IntensionalNerect.
Require Import Equivalence.
Require Import MapTerm.


Definition mapped_meta_fn {A B : ofe} (f : car A -> car B) (h : noncontractive f)
  (R : urel A)
  (a : urelsp R -n> iurel_ofe A)
  (b : urelsp R -n> meta_ofe B)
  : meta B.
Proof.
refine (meta_fn (map_urel f h R) _).
refine (nearrow_compose _ (demap_urelsp_ne f h R)).
apply pair_ne.
  {
  exact (nearrow_compose (map_urel_ne f h) (nearrow_compose fst_ne a)).
  }

  {
  exact b.
  }
Defined.


Definition map_meta {A B : ofe} (f : car A -> car B) (h : noncontractive f) (m : car (meta_ofe A)) 
  : car (meta_ofe B).
Proof.
apply 
  (meta_nerect A (meta_ofe B)
     (fun I => meta_nats I)
     (fun r m => meta_single (map_urel f h (fst r), m))
     (fun R a b => mapped_meta_fn f h R a b)
     (fun R C => meta_term (map_urel f h R) (map_urelsp f h R C))
     (fun _ x _ y => (meta_pair x y))); eauto with meta_dist.

(* single *)
{
intros n r s x y Hrs Hxy.
apply meta_dist_single.
split; cbn; auto.
apply map_urel_nonexpansive.
exact (Hrs andel).
}

(* fn *)
{
intros i C D a b c d HCD Hab Hcd.
apply meta_dist_fn.
  {
  apply map_urel_nonexpansive; auto.
  }

  {
  intros E F HEF.
  cbn.
  split.
    {
    cbn.
    apply map_urel_nonexpansive.
    apply Hab; auto.
    apply demap_urelsp_nonexpansive_dep; auto.
    }

    {
    cbn.
    apply Hcd; auto.
    apply demap_urelsp_nonexpansive_dep; auto.
    }
  }
}

(* term *)
{
intros i C D E F HCD HEF.
apply meta_dist_term.
  {
  apply map_urel_nonexpansive; auto.
  }

  {
  apply map_urelsp_nonexpansive_dep; auto.
  }
}
Defined.


Lemma map_meta_nonexpansive :
  forall A B (f : car A -> car B) (h : noncontractive f),
    nonexpansive (map_meta f h).
Proof.
intros A B f h.
unfold map_meta.
apply meta_nerect_nonexpansive.
Qed.


Definition map_meta_ne {A B : ofe} (f : car A -> car B) (h : noncontractive f)
  : meta_ofe A -n> meta_ofe B
  :=
  expair
    (map_meta f h)
    (map_meta_nonexpansive _#4).


Definition map_iurel {A B : ofe} (f : car A -> car B) (h : noncontractive f) (r : car (iurel_ofe A))
  : car (iurel_ofe B)
  :=
  (map_urel f h (fst r), map_meta f h (snd r)).


Lemma map_iurel_nonexpansive :
  forall A B (f : car A -> car B) (h : noncontractive f),
    nonexpansive (map_iurel f h).
Proof.
intros A B f h.
unfold map_iurel.
intros i x y Hxy.
destruct Hxy.
split; cbn.
  {
  apply map_urel_nonexpansive; auto.
  }

  {
  apply map_meta_nonexpansive; auto.
  }
Qed.


Definition map_iurel_ne {A B : ofe} (f : car A -> car B) (h : noncontractive f)
  : iurel_ofe A -n> iurel_ofe B
  :=
  expair
    (map_iurel f h)
    (map_iurel_nonexpansive _#4).


Lemma map_meta_nats :
  forall A B (f : car A -> car B) (h : noncontractive f) I,
    map_meta f h (meta_nats I) = meta_nats I.
Proof.
intros A B f h I.
unfold map_meta.
rewrite -> meta_nerect_nats.
reflexivity.
Qed.


Lemma map_meta_single :
  forall A B (f : car A -> car B) (h : noncontractive f) r,
    map_meta f h (meta_single r)
    =
    meta_single (map_iurel f h r).
Proof.
intros A B f h r.
unfold map_meta.
rewrite -> meta_nerect_single.
reflexivity.
Qed.


Lemma map_meta_fn :
  forall A B (f : car A -> car B) (h : noncontractive f) R g,
    map_meta f h (meta_fn R g)
    =
    mapped_meta_fn f h R g (nearrow_compose (map_meta_ne f h) (nearrow_compose snd_ne g)).
Proof.
intros A B f h R g.
unfold map_meta_ne.
unfold map_meta.
rewrite -> meta_nerect_fn.
(* Why so slow? *)
f_equal.
f_equal.
apply exT_extensionality_prop.
cbn.
reflexivity.
Qed.


Lemma map_meta_term :
  forall A B (f : car A -> car B) (h : noncontractive f) R C,
    map_meta f h (meta_term R C)
    =
    meta_term (map_urel f h R) (map_urelsp f h R C).
Proof.
intros A B f h R C.
unfold map_meta.
rewrite -> meta_nerect_term.
reflexivity.
Qed.


Lemma map_meta_pair :
  forall A B (f : car A -> car B) (h : noncontractive f) m n,
    map_meta f h (meta_pair m n)
    =
    meta_pair (map_meta f h m) (map_meta f h n).
Proof.
intros A B f h m n.
unfold map_meta.
rewrite -> meta_nerect_pair.
reflexivity.
Qed.


Hint Rewrite map_meta_nats map_meta_single map_meta_fn map_meta_term map_meta_pair : map_meta.


Ltac meta_discriminate Heq :=
  let H := fresh
  in
    so (f_equal (meta_rect _ (fun _ => nat) (fun _ => 0) (fun _ _ => 1) (fun _ _ _ => 2) (fun _ _ => 3) (fun _ _ _ _ => 4)) Heq) as H;
    autorewrite with meta_rect in H;
    cbn in H;
    discriminate Heq.


Lemma map_meta_inj :
  forall A B (f : car A -> car B) (h : noncontractive f), injective (map_meta f h).
Proof.
intros A B f h.
intros m n Heq.
revert n Heq.
pattern m.
apply meta_rect.

(* nats *)
{
intros I n Heq.
revert Heq.
pattern n.
apply meta_rect;
try (intros;
     autorewrite with map_meta in Heq;
     meta_discriminate Heq).
intros J Heq.
f_equal.
rewrite -> !map_meta_nats in Heq.
eapply meta_nats_inj; eauto.
}

(* single *)
{
intros r IH n Heq.
revert Heq.
pattern n.
apply meta_rect;
try (intros;
     autorewrite with map_meta in Heq;
     meta_discriminate Heq).
intros r' _ Heq.
rewrite -> !map_meta_single in Heq.
so (meta_single_inj _#3 Heq) as Heq'.
f_equal.
apply prod_extensionality.
  {
  so (f_equal fst Heq') as H.
  cbn in H.
  apply (map_urel_inj _ _ f h); auto.
  }

  {
  apply IH.
  exact (f_equal snd Heq').
  }
}

(* fn *)
{
intros R g IH n Heq.
revert Heq.
pattern n.
apply meta_rect;
try (intros;
     autorewrite with map_meta in Heq;
     meta_discriminate Heq).
intros R' g' _ Heq.
rewrite -> !map_meta_fn in Heq.
so (meta_fn_inj _#5 Heq) as Heq'.
so (map_urel_inj _#6 (eq_dep_impl_eq_fst _#6 Heq')).
subst R'.
f_equal.
so (eq_dep_impl_eq_snd _#5 Heq') as Heqg.
clear Heq Heq'.
apply exT_extensionality_prop.
fextensionality 1.
intro C.
so (f_equal (fun z => pi1 z (map_urelsp f h R C)) Heqg) as Heq.
cbn in Heq.
rewrite -> demap_map_urelsp in Heq.
apply prod_extensionality.
  {
  so (f_equal fst Heq) as H.
  cbn in H.
  exact (map_urel_inj _#6 H).
  }

  {
  so (f_equal snd Heq) as H.
  cbn in H.
  exact (IH C (snd (pi1 g' C)) H).
  }
}

(* term *)
{
intros R C n Heq.
revert Heq.
pattern n.
apply meta_rect;
try (intros;
     autorewrite with map_meta in Heq;
     meta_discriminate Heq).
intros R' C' Heq.
rewrite -> !map_meta_term in Heq.
so (meta_term_inj _#5 Heq) as Heq'.
so (map_urel_inj _#6 (eq_dep_impl_eq_fst _#6 Heq')).
subst R'.
f_equal.
exact (map_urelsp_inj _#7 (eq_dep_impl_eq_snd _#5 Heq')).
}

(* pair *)
{
intros x IH1 y IH2 n Heq.
revert Heq.
pattern n.
apply meta_rect;
try (intros;
     autorewrite with map_meta in Heq;
     meta_discriminate Heq).
intros x' _ y' _ Heq.
rewrite -> !map_meta_pair in Heq.
so (meta_pair_inj _#5 Heq) as (Heq1 & Heq2).
f_equal; eauto.
}
Qed.


Lemma map_iurel_inj :
  forall A B (f : car A -> car B) (h : noncontractive f), injective (map_iurel f h).
Proof.
intros A B f h.
intros r s Heq.
so (f_equal fst Heq) as Heq1.
so (f_equal snd Heq) as Heq2.
cbn in Heq1, Heq2.
apply prod_extensionality.
  {
  apply (map_urel_inj _ _ f h); auto.
  }

  {
  apply (map_meta_inj _ _ f h); auto.
  }
Qed.
