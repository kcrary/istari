
Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.

Require Import Tactics.
Require Import Relation.
Require Import Syntax.
Require Import SimpSub.
Require Import Dynamic.
Require Import Equivalence.
Require Import Equivalences.
Require Import Hygiene.
Require Import Morphism.
Require Import Defined.
Require Rules.
Require Defs.


Lemma subst_leqtp :
  forall object (s : @sub object), subst s leqtp = leqtp.
Proof.
prove_subst.
Qed.


Hint Rewrite subst_leqtp : subst.


Ltac prove_the_hygiene :=
  repeat
    (match goal with
     | Hh : hygiene _ _ |- _ =>
         let H := fresh
         in
           so (hygiene_invert_auto _#5 Hh) as H; cbn in H; clear Hh; destruct_all H
     end);
  repeat (apply hygiene_auto; cbn; repeat split); auto; 
  first [apply hygiene_var | apply hygiene_shift' | idtac]; auto.


Lemma def_admiss :
  forall a, equiv (app Defs.admiss a) (admiss a).
Proof.
intros a.
unfold Defs.admiss.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }

  {
  simpsub.
  apply star_refl.
  }
Qed.


Lemma def_alltp :
  forall a, equiv (app Defs.foralltp (lam a)) (alltp a).
Proof.
intros a.
unfold Defs.foralltp.
eapply equiv_trans.
  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app2.
    }
  apply star_refl.
  }

  {
  simpsub.
  cbn [Nat.add].
  apply equiv_alltp.
  apply steps_equiv.
  eapply star_step.
    { 
    apply step_app2.
    }

    {
    simpsub.
    rewrite -> subst_var0_sh1.
    apply star_refl.
    }
}
Qed.


Lemma def_arrow :
  forall a b,
    equiv (app (app Defs.arrow a) b) (pi a (subst sh1 b)).
Proof.
intros a m.
unfold Defs.arrow.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_coguard :
  forall a b,
    equiv (app (app Defs.coguard a) b) (coguard a b).
Proof.
intros a b.
unfold Defs.coguard.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_eeqtp :
  forall a b,
    equiv (app (app Defs.eeqtp a) b) (prod (subtype a b) (subtype b a)).
Proof.
intros a b.
unfold Defs.eeqtp.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_eq :
  forall a m n,
    equiv (app (app (app Defs.eq a) m) n) (equal a m n).
Proof.
intros a m n.
unfold Defs.eq.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_eqtp :
  forall a b,
    equiv (app (app Defs.eqtp a) b) (eqtype a b).
Proof.
intros a b.
unfold Defs.eqtp.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_guard :
  forall a b,
    equiv (app (app Defs.guard a) b) (guard a b).
Proof.
intros a b.
unfold Defs.guard.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_halts :
  forall m, equiv (app Defs.halts m) (halts m).
Proof.
intros m.
unfold Defs.halts.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }

  {
  simpsub.
  apply star_refl.
  }
Qed.


Lemma def_iexists :
  forall i k a,
    equiv (app (app (app Defs.iexists i) k) (lam a)) (exist i k a).
Proof.
intros i k a.
unfold Defs.iexists.
eapply equiv_trans.
  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app1.
    apply step_app1.
    apply step_app2.
    }
  simpsub.
  eapply star_step.
    {
    apply step_app1.
    apply step_app2.
    }
  simpsub.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
apply equiv_exist; auto using equiv_refl.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl'.
rewrite <- eqsub_expand_id.
simpsub.
reflexivity.
Qed.


Lemma def_iff :
  forall a b,
    equiv (app (app Defs.iff a) b) (prod (pi a (subst sh1 b)) (pi b (subst sh1 a))).
Proof.
intros a b.
unfold Defs.iff.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_iforall :
  forall i k a,
    equiv (app (app (app Defs.iforall i) k) (lam a)) (all i k a).
Proof.
intros i k a.
unfold Defs.iforall.
eapply equiv_trans.
  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app1.
    apply step_app1.
    apply step_app2.
    }
  simpsub.
  eapply star_step.
    {
    apply step_app1.
    apply step_app2.
    }
  simpsub.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
apply equiv_all; auto using equiv_refl.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl'.
rewrite <- eqsub_expand_id.
simpsub.
reflexivity.
Qed.


Lemma def_inl :
  forall m,
    equiv (app Defs.inl m) (sumleft m).
Proof.
intros m.
unfold Defs.inl.
eapply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_inr :
  forall m,
    equiv (app Defs.inr m) (sumright m).
Proof.
intros m.
unfold Defs.inl.
eapply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_intersect :
  forall a b,
    equiv (app (app Defs.intersect a) (lam b)) (intersect a b).
Proof.
intros a m.
unfold Defs.intersect.
eapply equiv_trans.
  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app1.
    apply step_app2.
    }
  simpsub.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
apply equiv_intersect; auto using equiv_refl.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl'.
rewrite <- eqsub_expand_id.
simpsub.
reflexivity.
Qed.


Lemma def_iset :
  forall a b,
    equiv (app (app Defs.iset a) (lam b)) (iset a b).
Proof.
intros a m.
unfold Defs.iset.
eapply equiv_trans.
  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app1.
    apply step_app2.
    }
  simpsub.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
apply equiv_iset; auto using equiv_refl.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl'.
rewrite <- eqsub_expand_id.
simpsub.
reflexivity.
Qed.


Lemma def_istp :
  forall a,
    equiv (app Defs.istp a) (eqtype a a).
Proof.
intros a.
unfold Defs.istp.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_karrow :
  forall a b,
    equiv (app (app Defs.karrow a) b) (karrow a b).
Proof.
intros a m.
unfold Defs.karrow.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_kind :
  forall i,
    equiv (app Defs.kind i) (kind i).
Proof.
intros i.
unfold Defs.kind.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_level : Defs.level = nattp.
Proof.
auto.
Qed.


Add Parametric Morphism object : (@lam object)
  with signature equiv ==> equiv
  as equiv_lam.
Proof.
intros m1 m1' H1.
apply equiv_lam.
auto.
Qed.


Lemma def_letnext :
  forall m n,
    equiv (app (app Defs.letnext m) (lam n)) (subst1 (prev m) n).
Proof.
intros m n.
unfold Defs.letnext.
apply steps_equiv.
eapply star_trans.
  {
  eapply star_step.
    {
    apply step_app1.
    apply step_app2.
    }
  simpsub.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
apply star_one.
apply step_app2.
Qed.


Lemma def_lsucc :
  forall m, equiv (app Defs.lsucc m) (nsucc m).
Proof.
intro m.
unfold Defs.lsucc.
eapply equiv_trans.
  {
  apply steps_equiv.
  apply star_one.
  apply step_app2.
  }
simpsub.
rewrite -> def_inr.
apply equiv_refl.
Qed.


Lemma def_lzero :
  equiv Defs.lzero Defined.nzero.
Proof.
unfold Defs.lzero.
unfold Defined.nzero.
rewrite -> def_inl.
unfold Defined.sumleft.
apply equiv_refl.
Qed.


Lemma def_mu :
  forall a, equiv (app Defs.mu (lam a)) (mu a).
Proof.
intros a.
unfold Defs.mu.
eapply equiv_trans.
  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app2.
    }
  apply star_refl.
  }

  {
  simpsub.
  cbn [Nat.add].
  apply equiv_mu.
  apply steps_equiv.
  eapply star_step.
    { 
    apply step_app2.
    }

    {
    simpsub.
    rewrite -> subst_var0_sh1.
    apply star_refl.
    }
}
Qed.


Lemma def_nat : eq Defs.nat nattp.
Proof.
auto.
Qed.


Lemma def_negative :
  forall a,
    equiv 
      (app Defs.negative (lam a))
      (isnegative a).
Proof.
intros a.
unfold Defs.negative.
eapply equiv_trans.
  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app2.
    }
  apply star_refl.
  }

  {
  simpsub.
  cbn [Nat.add].
  apply equiv_isnegative.
  apply steps_equiv.
  eapply star_step.
    { 
    apply step_app2.
    }
  simpsub.
  rewrite -> subst_var0_sh1.
  apply star_refl.
  }
Qed.


Lemma def_of :
  forall a m,
    equiv (app (app Defs.of a) m) (equal a m m).
Proof.
intros a m.
unfold Defs.of.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_partial :
  forall a, equiv (app Defs.partial a) (partial a).
Proof.
intros a.
unfold Defs.partial.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }

  {
  simpsub.
  apply star_refl.
  }
Qed.


Lemma def_pi :
  forall a b,
    equiv (app (app Defs.pi a) (lam b)) (pi a b).
Proof.
intros a m.
unfold Defs.pi.
eapply equiv_trans.
  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app1.
    apply step_app2.
    }
  simpsub.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
apply equiv_pi; auto using equiv_refl.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl'.
rewrite <- eqsub_expand_id.
simpsub.
reflexivity.
Qed.


Lemma def_positive :
  forall a,
    equiv 
      (app Defs.positive (lam a))
      (ispositive a).
Proof.
intros a.
unfold Defs.positive.
eapply equiv_trans.
  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app2.
    }
  apply star_refl.
  }

  {
  simpsub.
  cbn [Nat.add].
  apply equiv_ispositive.
  apply steps_equiv.
  eapply star_step.
    { 
    apply step_app2.
    }
  simpsub.
  rewrite -> subst_var0_sh1.
  apply star_refl.
  }
Qed.


Lemma def_seq :
  forall m n,
    equiv (app (app Defs.seq m) (lam n)) (seq m n).
Proof.
intros m n.
unfold Defs.seq.
eapply equiv_trans.
  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app1.
    apply step_app2.
    }
  simpsub.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
apply equiv_seq; auto using equiv_refl.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl'.
rewrite <- eqsub_expand_id.
simpsub.
reflexivity.
Qed.


Lemma def_sequal :
  forall m n,
    equiv (app (app Defs.sequal m) n) (sequal m n).
Proof.
intros m n.
unfold Defs.sequal.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_set :
  forall a b,
    equiv (app (app Defs.set a) (lam b)) (set a b).
Proof.
intros a m.
unfold Defs.set.
eapply equiv_trans.
  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app1.
    apply step_app2.
    }
  simpsub.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
apply equiv_set; auto using equiv_refl.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl'.
rewrite <- eqsub_expand_id.
simpsub.
reflexivity.
Qed.


Lemma def_sigma :
  forall a b,
    equiv (app (app Defs.sigma a) (lam b)) (sigma a b).
Proof.
intros a m.
unfold Defs.sigma.
eapply equiv_trans.
  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app1.
    apply step_app2.
    }
  simpsub.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
apply equiv_sigma; auto using equiv_refl.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl'.
rewrite <- eqsub_expand_id.
simpsub.
reflexivity.
Qed.


Lemma def_subtype :
  forall a b,
    equiv (app (app Defs.subtype a) b) (subtype a b).
Proof.
intros a b.
unfold Defs.subtype.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_sum :
  forall a b,
    equiv (app (app Defs.sum a) b) (sumtype a b).
Proof.
intros a b.
unfold Defs.sum.
eapply equiv_trans.
  {
  apply equiv_app; [| apply equiv_refl].
  apply steps_equiv.
  apply star_one.
  apply step_app2.
  }
simpsub.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_sum_case :
  forall m n p,
    equiv 
      (app (app (app Defs.sum_case m) (lam n)) (lam p))
      (sumcase m n p).
Proof.
intros m n p.
unfold Defs.sum_case.
eapply equiv_trans.
  {
  apply equiv_app; [| apply equiv_refl].
  eapply equiv_trans.
    {
    apply equiv_app; [| apply equiv_refl].
    apply steps_equiv.
    apply star_one.
    apply step_app2.
    }
  simpsub.
  apply steps_equiv.
  apply star_one.
  apply step_app2.
  }
simpsub.
rewrite -> equiv_beta.
simpsub.
rewrite -> !equiv_beta.
simpsub.
unfold sumcase.
apply equiv_refl.
Qed.


Lemma def_tarrow :
  forall a b,
    equiv (app (app Defs.tarrow a) b) (tarrow a b).
Proof.
intros a m.
unfold Defs.arrow.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_union :
  forall a b,
    equiv (app (app Defs.union a) (lam b)) (union a b).
Proof.
intros a m.
unfold Defs.union.
eapply equiv_trans.
  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app1.
    apply step_app2.
    }
  simpsub.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
apply equiv_union; auto using equiv_refl.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl'.
rewrite <- eqsub_expand_id.
simpsub.
reflexivity.
Qed.


Lemma def_univ :
  forall i,
    equiv (app Defs.univ i) (univ i).
Proof.
intros i.
unfold Defs.univ.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_uptype :
  forall a, equiv (app Defs.uptype a) (uptype a).
Proof.
intros a.
unfold Defs.uptype.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }

  {
  simpsub.
  apply star_refl.
  }
Qed.


Lemma def_prod : forall a b,
    equiv (app (app Defs.prod a) b) (prod a b).
Proof.
intros a m.
unfold Defs.prod.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_fut : forall a,
    equiv (app Defs.future a) (fut a).
Proof.
intros a.
unfold Defs.future.
  apply steps_equiv.
  eapply star_step.
  {
    apply step_app2.
  }
  {
    simpsub.
    apply star_refl.
  }
Qed.


Lemma def_rec : forall a,
    equiv (app Defs.rec (lam a)) (rec a).
Proof.
intros a.
unfold Defs.rec.
eapply equiv_trans.
{
  apply steps_equiv.
  eapply star_step.
  apply step_app2.
  apply star_refl.
}
{
  simpsub. simpl.
  apply equiv_rec.
  apply steps_equiv.
  eapply star_step.
  { apply step_app2. }
  {
    simpsub.
    replace (subst (dot (var 0) sh1) a) with a.
    { apply star_refl. }
    { replace a with (subst id a) at 1.
    apply subst_eqsub. apply eqsub_expand_sh.
    simpsub; auto. }
  }
}
Qed.


Lemma def_squash : 
  forall a,
    equiv (app Defs.squash a) (squash a).
Proof.
intros a.
unfold Defs.squash.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }

  {
  simpsub.
  apply star_refl.
  }
Qed.


Lemma def_ite: forall m p r, equiv (app (app (app Defs.ite m) p) r) (bite m p r).
intros m p r.
unfold Defs.ite.
    apply steps_equiv.
    eapply star_step.
    - do 2 apply step_app1. apply step_app2.
    - simpsub. eapply star_step.
      + apply step_app1. apply step_app2.
      + simpsub. eapply star_step.
        * apply step_app2.
        * simpsub. auto. apply star_refl.
Qed.


Lemma equiv_to_equivh {m m'} : @equiv Rules.obj m m' -> equivh (hyp_tm m) (hyp_tm m') /\
                                                  equivh (hyp_tml m) (hyp_tml m')
.
  intros Hequiv.
  split; try (constructor; assumption);
  intros P; split; intros Hctx_hyg; constructor; apply Hhyg;
            inversion Hctx_hyg; subst; assumption.
Qed.


Lemma def_sigmah: forall a b,
    equivh (hyp_tm (app (app Defs.sigma a) (lam b)))
            (hyp_tm (sigma a b)).
  intros a b.
  apply (equiv_to_equivh (def_sigma a b)).
Qed.

Lemma def_prodh: forall a b,
    equivh (hyp_tm (app (app Defs.prod a) b))
            (hyp_tm (prod a b)).
  intros a b.
  apply (equiv_to_equivh (def_prod a b)).
Qed.

Lemma def_futh: forall a,
    equivh (hyp_tm (app Defs.future a))
            (hyp_tm (fut a)).
  intros a.
  apply (equiv_to_equivh (def_fut a)).
Qed.

Lemma def_kindh_l: forall i,
    equivh (hyp_tml (app Defs.kind i))
            (hyp_tml (kind i)).
  intros i.
  apply (equiv_to_equivh (def_kind i)).
Qed.

Lemma def_univh_l: forall i,
    equivh (hyp_tml (app Defs.univ i))
            (hyp_tml (univ i)).
  intros i.
  apply (equiv_to_equivh (def_univ i)).
Qed.
