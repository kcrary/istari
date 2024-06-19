
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Tactics.
Require Import Axioms.
Require Import Sigma.
Require Import Equality.
Require Import Sequence.
Require Import Relation.
Require Import Ordinal.
Require Import Syntax.
Require Import SimpSub.
Require Import Dynamic.
Require Import Ofe.
Require Import Uniform.
Require Import Intensional.
Require Import Candidate.
Require Import System.
Require Import Semantics.
Require Import SemanticsKnot.
Require Import Judgement.
Require Import Hygiene.
Require Import ProperClosed.
Require Import ProperFun.
Require Import Shut.

Require Import Defined.
Require Import PageCode.
Require Import ProperLevel.
Require Import Approximation.
Require Import Compactness.
Require Import SemanticsProperty.
Require Import SemanticsPartial.
Require Import SemanticsPi.
Require Import Ceiling.
Require Import SoundSimple.
Require Import Equivalence.
Require Import Truncate.
Require Import ProperDownward.
Require Import SemanticsSimple.
Require Import MapTerm.


Local Ltac prove_hygiene :=
  repeat (apply hygiene_auto; cbn; repeat2 split; auto);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1, subst_closub;
  try (eapply subst_closub_under_permit; eauto; done);
  try (apply hygiene_var; cbn; auto; done).


Lemma halts_elim :
  forall pg s i m R r t,
    interp pg s i (halts m) R
    -> rel (den R) i r t
    -> converges m.
Proof.
intros pg s i m R r t Hinterp Hrt.
invert (basic_value_inv _#6 value_halts Hinterp).
intros _ <-.
destruct Hrt as (H & _).
exact H.
Qed.


Lemma upward_impl_admissible :
  forall w A,
    upward w A
    -> admissible w A.
Proof.
intros w A Hupward f g i' m p j Hclf Hclg Hclm Hclp Hact.
apply (Hupward _ (subst1 (afix j f) m) _ (subst1 (afix j g) p)).
  {
  apply sapprox_funct1; auto.
  intros T h.
  simpmap.
  apply afix_fix_approx.
  apply map_hygiene; auto.
  }

  {
  apply sapprox_funct1; auto.
  intros T h.
  simpmap.
  apply afix_fix_approx.
  apply map_hygiene; auto.
  }

  {
  apply Hact.
  auto.
  }
Qed.


Lemma seq_halts :
  forall G m,
    seq G (deq triv triv (halts m))
    <->
    forall i s s',
      pwctx i s s' G
      -> hygiene clo (subst s m)
         /\ hygiene clo (subst s' m)
         /\ converges (subst s m) 
         /\ converges (subst s' m).
Proof.
intros G m.
rewrite -> seq_deq.
split.
  {
  intros Hseq i s s' Hs.
  so (Hseq _#3 Hs) as (R & Hl & Hr & Hhalt & _).
  simpsubin Hl.
  simpsubin Hr.
  so (halts_elim _#7 Hl Hhalt) as Hconv.
  so (halts_elim _#7 Hr Hhalt) as Hconv'.
  invert (basic_value_inv _#6 value_halts Hl).
  intros Hcl _.
  invert (basic_value_inv _#6 value_halts Hr).
  intros Hcl' _.
  auto.
  }

  {
  intros Hhalts i s s' Hs.
  exists (iubase (halts_urel stop i (subst s m))).
  simpsub.
  so (Hhalts _#3 Hs) as (Hcl & Hcl' & Hconv & Hconv').
  assert (rel (den (iubase (halts_urel stop i (subst s m)))) i triv triv) as Htriv.
    {
    do2 5 split; auto using star_refl; prove_hygiene.
    }
  do2 4 split; auto.
    {
    apply interp_eval_refl.
    apply interp_halts; auto.
    }

    {
    replace (halts_urel stop i (subst s m)) with (halts_urel stop i (subst s' m)).
    2:{
      unfold halts_urel.
      apply property_urel_extensionality; auto.
      intros _ _.
      split; auto.
      }
    apply interp_eval_refl.
    apply interp_halts; auto.
    }
  }
Qed.


Lemma seq_admiss :
  forall G a,
    seq G (deq triv triv (admiss a))
    <->
    (forall i s s',
       pwctx i s s' G
       -> exists A,
            interp toppg true i (subst s a) A
            /\ interp toppg false i (subst s' a) A
            /\ admissible stop (ceiling (S i) (den A))).
Proof.
intros G a.
rewrite -> seq_deq.
split.
  {
  intros Hseq i s s' Hs.
  so (Hseq _#3 Hs) as (R & Hl & Hr & H & _).
  simpsubin Hl.
  simpsubin Hr.
  invert (basic_value_inv _#6 value_admiss Hl).
  intros A Hal Heql.
  invert (basic_value_inv _#6 value_admiss Hr).
  intros A' Har Heqr.
  so (iuadmiss_inj _#4 (eqtrans Heql (eqsymm Heqr))).
  subst A'.
  subst R.
  destruct H as (H & _).
  unfold admiss_property in H.
  exists A.
  auto.
  }

  {
  intros Hupward i s s' Hs.
  so (Hupward _#3 Hs) as (A & Hal & Har & H).
  exists (iuadmiss stop i A).
  simpsub.
  assert (rel (den (iuadmiss stop i A)) i triv triv) as Htriv.
    {
    do2 5 split; auto using star_refl; prove_hygiene.
    }
  do2 4 split; auto.
    {
    apply interp_eval_refl.
    apply interp_admiss; auto.
    }

    {
    apply interp_eval_refl.
    apply interp_admiss; auto.
    }
  }
Qed.


Lemma seq_uptype :
  forall G a,
    seq G (deq triv triv (uptype a))
    <->
    (forall i s s',
       pwctx i s s' G
       -> exists A,
            interp toppg true i (subst s a) A
            /\ interp toppg false i (subst s' a) A
            /\ upward stop (ceiling (S i) (den A))).
Proof.
intros G a.
rewrite -> seq_deq.
split.
  {
  intros Hseq i s s' Hs.
  so (Hseq _#3 Hs) as (R & Hl & Hr & H & _).
  simpsubin Hl.
  simpsubin Hr.
  invert (basic_value_inv _#6 value_uptype Hl).
  intros A Hal Heql.
  invert (basic_value_inv _#6 value_uptype Hr).
  intros A' Har Heqr.
  so (iuuptype_inj _#4 (eqtrans Heql (eqsymm Heqr))).
  subst A'.
  subst R.
  destruct H as (H & _).
  unfold uptype_property in H.
  exists A.
  auto.
  }

  {
  intros Hupward i s s' Hs.
  so (Hupward _#3 Hs) as (A & Hal & Har & H).
  exists (iuuptype stop i A).
  simpsub.
  assert (rel (den (iuuptype stop i A)) i triv triv) as Htriv.
    {
    do2 5 split; auto using star_refl; prove_hygiene.
    }
  do2 4 split; auto.
    {
    apply interp_eval_refl.
    apply interp_uptype; auto.
    }

    {
    apply interp_eval_refl.
    apply interp_uptype; auto.
    }
  }
Qed.


Lemma step_converges_conv :
  forall (m n : @term obj),
    step m n
    -> converges n
    -> converges m.
Proof.
intros m n Hstep (v & (Hsteps & Hval)).
exists v.
split; auto.
eapply star_step; eauto.
Qed.


Lemma equiv_converges :
  forall (m n : @term obj),
    equiv m n
    -> converges m
    -> converges n.
Proof.
intros m n Hequiv (v & Heval).
so (equiv_eval _#4 Hequiv Heval) as (w & Heval' & _).
exists w.
auto.
Qed.


Lemma converges_seq_invert :
  forall (m n : @term obj),
    converges (Syntax.seq m n)
    -> converges m.
Proof.
intros m n Hconv.
destruct Hconv as (v & (Hsteps & Hval)).
remember (Syntax.seq m n) as p eqn:Heq.
revert m Hval Heq.
induct Hsteps.

(* refl *)
{
intros ? m Hval ->.
invert Hval.
intro H.
invert H.
}

(* step *)
{
intros ? p q Hstep _ IH m Hval ->.
invert Hstep.
  {
  intros m' Hstep' <-.
  eapply step_converges_conv; eauto.
  }

  {
  intros Hvalm <-.
  exists m.
  split; auto.
  apply star_refl.
  }
}
Qed.


Lemma converges_app_invert :
  forall (m n : @term obj),
    converges (app m n)
    -> converges m.
Proof.
intros m n Hconv.
destruct Hconv as (v & (Hsteps & Hval)).
remember (app m n) as p eqn:Heq.
revert m Hval Heq.
induct Hsteps.

(* refl *)
{
intros ? m Hval ->.
invert Hval.
intro H.
invert H.
}

(* step *)
{
intros ? p q Hstep _ IH m Hval ->.
invert Hstep.
  {
  intros m' Hstep' <-.
  eapply step_converges_conv; eauto.
  }

  {
  intros m' <- <-.
  exists (lam m').
  split; auto using star_refl, value_lam.
  }
}
Qed.


Lemma converges_prev_invert :
  forall (m : @term obj),
    converges (prev m)
    -> converges m.
Proof.
intros m Hconv.
destruct Hconv as (v & (Hsteps & Hval)).
remember (prev m) as p eqn:Heq.
revert m Hval Heq.
induct Hsteps.

(* refl *)
{
intros ? m Hval ->.
invert Hval.
intro H.
invert H.
}

(* step *)
{
intros ? p q Hstep _ IH m Hval ->.
invert Hstep.
  {
  intros m' Hstep' <-.
  eapply step_converges_conv; eauto.
  }

  {
  intros <-.
  exists (next p).
  split; auto using star_refl, value_next.
  }
}
Qed.


Lemma converges_ppi1_invert :
  forall (m : @term obj),
    converges (ppi1 m)
    -> converges m.
Proof.
intros m Hconv.
destruct Hconv as (v & (Hsteps & Hval)).
remember (ppi1 m) as p eqn:Heq.
revert m Hval Heq.
induct Hsteps.

(* refl *)
{
intros ? m Hval ->.
invert Hval.
intro H.
invert H.
}

(* step *)
{
intros ? p q Hstep _ IH m Hval ->.
invert Hstep.
  {
  intros m' Hstep' <-.
  eapply step_converges_conv; eauto.
  }

  {
  intros m' <-.
  exists (ppair p m').
  split; auto using star_refl, value_ppair.
  }
}
Qed.


Lemma converges_ppi2_invert :
  forall (m : @term obj),
    converges (ppi2 m)
    -> converges m.
Proof.
intros m Hconv.
destruct Hconv as (v & (Hsteps & Hval)).
remember (ppi2 m) as p eqn:Heq.
revert m Hval Heq.
induct Hsteps.

(* refl *)
{
intros ? m Hval ->.
invert Hval.
intro H.
invert H.
}

(* step *)
{
intros ? p q Hstep _ IH m Hval ->.
invert Hstep.
  {
  intros m' Hstep' <-.
  eapply step_converges_conv; eauto.
  }

  {
  intros m' <-.
  exists (ppair m' p).
  split; auto using star_refl, value_ppair.
  }
}
Qed.


Lemma converges_bite_invert :
  forall (m n p : @term obj),
    converges (bite m n p)
    -> converges m.
Proof.
intros m n r Hconv.
destruct Hconv as (v & (Hsteps & Hval)).
remember (bite m n r) as p eqn:Heq.
revert m Hval Heq.
induct Hsteps.

(* refl *)
{
intros ? m Hval ->.
invert Hval.
intro H.
invert H.
}

(* step *)
{
intros ? p q Hstep _ IH m Hval ->.
invert Hstep.
  {
  intros m' Hstep' <-.
  eapply step_converges_conv; eauto.
  }

  {
  intros <- <-.
  exists btrue.
  split; auto using star_refl, value_btrue.
  }

  {
  intros <- <-.
  exists bfalse.
  split; auto using star_refl, value_bfalse.
  }
}
Qed.


Lemma equiv_seq_converges :
  forall (m n : @term obj),
    converges m
    -> equiv (Syntax.seq m n) (subst1 m n).
Proof.
intros m n (v & (Hsteps & Hval)).
apply (equiv_trans _ _ (subst1 v n)).
  {
  apply steps_equiv.
  eapply star_trans.
    {
    apply (star_map' _ _ (fun z => Syntax.seq z _)); eauto using step_seq1.
    }
  apply star_one.
  apply step_seq2; auto.
  }

  {
  apply equiv_funct1; auto using equiv_refl.
  apply equiv_symm.
  apply steps_equiv; auto.
  }
Qed.


Lemma converges_seq_invert2 :
  forall (m n : @term obj),
    converges (Syntax.seq m n)
    -> converges (subst1 m n).
Proof.
intros m n Hconv.
eapply equiv_converges; eauto.
so (converges_seq_invert _ _ Hconv) as Hconvm.
apply equiv_seq_converges; auto.
Qed.


Lemma converges_seq :
  forall (m n : @term obj),
    converges m
    -> converges (subst1 m n)
    -> converges (Syntax.seq m n).
Proof.
intros m n Hconvm Hconv.
refine (equiv_converges _ _ _ Hconv).
apply equiv_symm.
apply equiv_seq_converges; auto.
Qed.
