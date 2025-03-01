
Require Import Coq.Setoids.Setoid.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Tactics.
Require Import Sequence.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.
Require Import Promote.
Require Import Hygiene.
Require Import Rules.
Require Import DerivedRules.
Require Defs.
Require Import Obligations.
Require Import Morphism.
Require Import DefsEquiv.
Require Import Equivalence.
Require Import Equivalences.
Require Import Dots.

Require Import Relation.
Require Import Dynamic.
Require Import ValidationUtil.
Require Import Defined.
Require ValidationPi.


Definition conjoin a b : @term obj :=
  intersect booltp (bite (var 0) (subst sh1 a) (subst sh1 b)).


Lemma subst_conjoin :
  forall (s : @sub obj) m1 m2, subst s (conjoin m1 m2) = conjoin (subst s m1) (subst s m2).
Proof.
unfold conjoin.
intros s m1 m2.
simpsub.
reflexivity.
Qed.


Hint Rewrite subst_conjoin : subst.


Lemma tr_conjoin_formation :
  forall G a a' b b',
    tr G (deqtype a a')
    -> tr G (deqtype b b')
    -> tr G (deqtype (conjoin a b) (conjoin a' b')).
Proof.
intros G a a' b b' Ha Hb.
apply tr_intersect_formation.
  {
  apply tr_booltp_istype.
  }
apply tr_booltp_elim_eqtype.
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  eapply (weakening _ [_] []).
    {
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  auto.
  }

  {
  eapply (weakening _ [_] []).
    {
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  auto.
  }
Qed.


Lemma tr_conjoin_formation_univ :
  forall G a a' b b' lv,
    tr G (deq a a' (univ lv))
    -> tr G (deq b b' (univ lv))
    -> tr G (deq (conjoin a b) (conjoin a' b') (univ lv)).
Proof.
intros G a a' b b' lv Ha Hb.
assert (tr G (deq lv lv pagetp)) as Hlv.
  {
  apply tr_univ_formation_invert.
  eapply tr_inhabitation_formation; eauto.
  }
apply tr_intersect_formation_univ.
  {
  apply (tr_univ_cumulative _ Defined.nzero); auto.
    {
    apply tr_booltp_formation_univ.
    }

    {
    rewrite -> leqpagetp_nzero_equiv.
    apply tr_unittp_intro.
    }
  }
replace (univ (subst sh1 lv)) with (subst1 (var 0) (univ (subst (sh 2) lv))) by (simpsub; auto).
apply tr_booltp_elim.
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  eapply (weakening _ [_] []).
    {
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  auto.
  }

  {
  eapply (weakening _ [_] []).
    {
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  auto.
  }
Qed.


Lemma tr_conjoin_intro :
  forall G a b m n,
    tr G (deq m n a)
    -> tr G (deq m n b)
    -> tr G (deq m n (conjoin a b)).
Proof.
intros G a b m n Ha Hb.
unfold conjoin.
apply tr_intersect_intro.
  {
  apply tr_booltp_istype.
  }
apply tr_equal_elim.
apply (tr_equal_eta2 _#4 
         (bite (var 0) (subst (under 0 sh1) triv) (subst (under 0 sh1) triv))
         (bite (var 0) (subst (under 0 sh1) triv) (subst (under 0 sh1) triv))).
apply (tr_booltp_eta_hyp _ []).
  {
  cbn [length].
  simpsub.
  cbn [List.app].
  apply tr_equal_intro.
  apply (tr_compute _ _ a _ m _ n); auto using equiv_refl.
  apply steps_equiv.
  apply star_one.
  apply step_bite2.
  }

  {
  cbn [length].
  simpsub.
  cbn [List.app].
  apply tr_equal_intro.
  apply (tr_compute _ _ b _ m _ n); auto using equiv_refl.
  apply steps_equiv.
  apply star_one.
  apply step_bite3.
  }
Qed.


Lemma tr_conjoin_elim1 :
  forall G a b m n,
    tr G (deq m n (conjoin a b))
    -> tr G (deq m n a).
Proof.
intros G a b m n H.
unfold conjoin in H.
apply (tr_compute _ _ (bite btrue a b) _ m _ n); auto using equiv_refl.
  {
  apply equiv_symm.
  apply steps_equiv.
  apply star_one.
  apply step_bite2.
  }
replace (bite btrue a b) with (subst1 btrue (bite (var 0) (subst sh1 a) (subst sh1 b))) by (simpsub; auto).
apply (tr_intersect_elim _ booltp _ _ _ _ btrue); auto.
apply tr_booltp_intro_btrue.
Qed.


Lemma tr_conjoin_elim2 :
  forall G a b m n,
    tr G (deq m n (conjoin a b))
    -> tr G (deq m n b).
Proof.
intros G a b m n H.
unfold conjoin in H.
apply (tr_compute _ _ (bite bfalse a b) _ m _ n); auto using equiv_refl.
  {
  apply equiv_symm.
  apply steps_equiv.
  apply star_one.
  apply step_bite3.
  }
replace (bite bfalse a b) with (subst1 bfalse (bite (var 0) (subst sh1 a) (subst sh1 b))) by (simpsub; auto).
apply (tr_intersect_elim _ booltp _ _ _ _ bfalse); auto.
apply tr_booltp_intro_bfalse.
Qed.


Lemma tr_conjoin_formation_invert1 :
  forall G a a' b b',
    tr G (deqtype (conjoin a b) (conjoin a' b'))
    -> tr G (deqtype a a').
Proof.
intros G a a' b b' H.
unfold conjoin in H.
assert (forall (x y : @term obj), equiv x (bite btrue x y)) as Hequiv.
  {
  intros x y.
  apply equiv_symm.
  apply steps_equiv.
  apply star_one.
  apply step_bite2.
  }
rewrite -> (Hequiv a b).
rewrite -> (Hequiv a' b').
clear Hequiv.
replace (deqtype (bite btrue a b) (bite btrue a' b')) with (substj (dot btrue id) (deqtype (bite (var 0) (subst sh1 a) (subst sh1 b)) (bite (var 0) (subst sh1 a') (subst sh1 b')))) by (simpsub; auto).
apply (tr_generalize _ booltp).
  {
  apply tr_booltp_intro_btrue.
  }
eapply tr_intersect_formation_invert2; eauto.
Qed.


Lemma def_parametric :
  forall a b,
    equiv (app (app Defs.parametric a) (lam b)) (conjoin (pi a b) constfn).
Proof.
intros a m.
unfold Defs.parametric.
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
unfold conjoin.
apply equiv_intersect; auto using equiv_refl.
apply equiv_bite; auto using equiv_refl.
simpsub.
apply equiv_pi; auto using equiv_refl.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl'.
reflexivity.
Qed.


Lemma def_paramapp :
  forall m n,
    equiv
      (app (app Defs.paramapp m) n)
      (app m triv).
Proof.
intros m n.
unfold Defs.paramapp.
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


Lemma def_irrelevant :
  forall m,
    equiv 
      (app Defs.irrelevant (lam m))
      (intersect nonsense (sequal m (subst (dot triv sh1) m))).
Proof.
intro m.
unfold Defs.irrelevant.
eapply equiv_trans.
  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  cbn [Nat.add].
  apply star_refl.
  }
apply equiv_intersect.
  {
  apply equiv_refl.
  }
apply equiv_sequal.
  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  rewrite -> subst_var0_sh1.
  apply star_refl.
  }

  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
Qed.


Hint Rewrite def_parametric def_paramapp def_irrelevant def_nonsense def_sequal : prepare.


Lemma tr_parametric_formation :
  forall G a a' b b',
    tr G (deqtype a a')
    -> tr (hyp_tm a :: G) (deqtype b b')
    -> tr G (deqtype
               (conjoin (pi a b) constfn)
               (conjoin (pi a' b') constfn)).
Proof.
intros G a a' b b' Ha Hb.
apply tr_conjoin_formation.
  {
  apply tr_pi_formation; auto.
  }
  
  {
  apply (tr_formation_weaken _ nzero).
  apply tr_constfn_formation.
  }
Qed.


Lemma parametricForm_valid : parametricForm_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_parametric_formation; auto.
Qed.


Lemma parametricEq_valid : parametricEq_obligation.
Proof.
prepare.
intros G a a' b b' ext1 ext0 Ha Hb.
apply tr_parametric_formation; auto.
Qed.


Lemma parametricFormUniv_valid : parametricFormUniv_obligation.
Proof.
prepare.
intros G a b lv ext1 ext0 Ha Hb.
assert (tr G (deq lv lv pagetp)) as Hlv.
  {
  apply tr_univ_formation_invert.
  eapply tr_inhabitation_formation; eauto.
  }
apply tr_conjoin_formation_univ.
  {
  apply tr_pi_formation_univ; auto.
  }

  {
  apply (tr_univ_cumulative _ Defined.nzero); auto.
    {
    apply tr_constfn_formation.
    }

    {
    rewrite -> leqpagetp_nzero_equiv.
    apply tr_unittp_intro.
    }
  }
Qed.


Lemma parametricEqUniv_valid : parametricEqUniv_obligation.
Proof.
prepare.
intros G a a' b b' lv ext1 ext0 Ha Hb.
assert (tr G (deq lv lv pagetp)) as Hlv.
  {
  apply tr_univ_formation_invert.
  eapply tr_inhabitation_formation; eauto.
  }
apply tr_conjoin_formation_univ.
  {
  apply tr_pi_formation_univ; auto.
  }

  {
  apply (tr_univ_cumulative _ Defined.nzero); auto.
    {
    apply tr_constfn_formation.
    }

    {
    rewrite -> leqpagetp_nzero_equiv.
    apply tr_unittp_intro.
    }
  }
Qed.


Lemma parametricSub_valid : parametricSub_obligation.
Proof.
prepare.
intros G a a' b b' ext2 ext1 ext0 Ha Hb Hb'.
apply tr_subtype_intro.
  {
  apply tr_parametric_formation; auto.
  eapply tr_subtype_istype2; eauto.
  }

  {
  apply tr_parametric_formation.
    {
    eapply tr_subtype_istype1; eauto.
    }

    {
    apply (tr_subtype_istype2 _ b); auto.
    }
  }
simpsub.
cbn [Nat.add].
apply tr_conjoin_intro.
  {
  apply (tr_subtype_elim _ (subst sh1 (pi a b))).
    {
    eapply (weakening _ [_] []).
      {
      simpsub.
      auto.
      }
  
      {
      cbn [length unlift].
      simpsub.
      auto.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    apply ValidationPi.tr_pi_sub; auto.
      {
      rewrite -> !subst_var0_sh1; auto.
      }

      {
      rewrite -> !subst_var0_sh1; auto.
      }
    }
  apply (tr_conjoin_elim1 _ _ constfn).
  eapply hypothesis; eauto using index_0.
  simpsub.
  auto.
  }

  {
  apply (tr_conjoin_elim2 _ (subst sh1 (pi a b))).
  eapply hypothesis; eauto using index_0.
  simpsub.
  auto.
  }
Qed.


Lemma parametricForallSub_valid : parametricForallSub_obligation.
Proof.
prepare.
intros G a a' b b' ext2 ext1 ext0 Ha Hb Hb'.
apply tr_subtype_intro.
  {
  apply tr_parametric_formation; auto.
  eapply tr_subtype_istype2; eauto.
  }

  {
  apply tr_pi_formation.
    {
    eapply tr_subtype_istype1; eauto.
    }

    {
    apply (tr_subtype_istype2 _ b); auto.
    }
  }
simpsub.
cbn [Nat.add].
apply (tr_subtype_elim _ (subst sh1 (pi a b))).
  {
  eapply (weakening _ [_] []).
    {
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  apply ValidationPi.tr_pi_sub; auto.
    {
    rewrite -> !subst_var0_sh1; auto.
    }

    {
    rewrite -> !subst_var0_sh1; auto.
    }
  }
apply (tr_conjoin_elim1 _ _ constfn).
eapply hypothesis; eauto using index_0.
simpsub.
auto.
Qed.


Lemma tr_intersect_elim' :
  forall G a b c m n p,
    tr G (deq m n (intersect a b))
    -> tr G (deq p p a)
    -> c = subst1 p b
    -> tr G (deq m n c).
Proof.
intros G a b c m n p H1 H2 ->.
eapply tr_intersect_elim; eauto.
Qed.


Lemma irrelevant_elim :
  forall G m p,
    tr G (deq p p (intersect nonsense (sequal m (subst (dot triv sh1) m))))
    -> tr (hyp_tm nonsense :: G) (deq triv triv (sequal m (subst (dot triv sh1) m))).
Proof.
intros G m p H.
apply (tr_sequal_eta2 _ (subst sh1 p) (subst sh1 p)).
eapply (tr_intersect_elim' _ _ (sequal (subst (dot (var 0) (sh 2)) m) (subst (dot triv (sh 2)) m))).
2:{
  eapply hypothesis; eauto using index_0.
  }

  {
  eapply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  rewrite -> subst_var0_sh1.
  exact H.
  }

  {
  simpsub.
  rewrite -> subst_var0_sh1; auto.
  }
Qed.


Lemma parametricIntroOf_valid : parametricIntroOf_obligation.
Proof.
prepare.
unfold Defs.orphan.
intros G a b m ext2 p ext0 Ha Hsequal Hm.
apply tr_conjoin_intro.
  {
  apply tr_pi_intro; auto.
  }

  {
  apply tr_constfn_intro.
    {
    apply tr_sequal_symm.
    eapply irrelevant_elim; eauto.
    }
    
    {
    apply tr_sequal_symm.
    eapply irrelevant_elim; eauto.
    }
  }
Qed.


Lemma parametricIntroEq_valid : parametricIntroEq_obligation.
Proof.
prepare.
unfold Defs.orphan.
intros G a b m n ext3 p q ext0 Ha Hsequalm Hsequaln Hmn.
apply tr_conjoin_intro.
  {
  apply tr_pi_intro; auto.
  }

  {
  apply tr_constfn_intro.
    {
    apply tr_sequal_symm.
    eapply irrelevant_elim; eauto.
    }
    
    {
    apply tr_sequal_symm.
    eapply irrelevant_elim; eauto.
    }
  }
Qed.


Lemma parametricIntro_valid : parametricIntro_obligation.
Proof.
prepare.
intros G a b ext0 m Hhyg Ha Hm.
apply tr_conjoin_intro.
  {
  apply tr_pi_intro; auto.
  }

  {
  apply tr_constfn_intro.
    {
    so (subst_into_absent_single _ 0 m triv Hhyg) as H.
    simpsubin H.
    rewrite -> H.
    apply tr_sequal_intro.
    }

    {
    so (subst_into_absent_single _ 0 m triv Hhyg) as H.
    simpsubin H.
    rewrite -> H.
    apply tr_sequal_intro.
    }
  }
Qed.


Lemma tr_sequal_equal2 :
  forall G a m m' n n',
    tr G (deq triv triv (sequal m m'))
    -> tr G (deq triv triv (sequal n n'))
    -> tr G (deq m n a)
    -> tr G (deq m' n' a).
Proof.
intros G a m m' n n' Hm Hn Hmn.
apply (tr_transitivity _ _ m).
  {
  apply tr_symmetry.
  apply tr_sequal_equal; auto.
  eapply tr_eq_reflexivity; eauto.
  }
apply (tr_transitivity _ _ n); auto.
apply tr_sequal_equal; auto.
eapply tr_eq_reflexivity.
apply tr_symmetry; eauto.
Qed.


Lemma parametricIntroOfForall_valid : parametricIntroOfForall_obligation.
Proof.
prepare.
intros G a b m ext1 p Hm Hirr.
apply tr_conjoin_intro; auto.
apply (tr_sequal_equal2 _ _ (lam (app (subst sh1 m) (var 0))) _ (lam (app (subst sh1 m) (var 0)))).
  {
  apply tr_sequal_symm.
  eapply tr_pi_eta_sequal; eauto.
  }

  {
  apply tr_sequal_symm.
  eapply tr_pi_eta_sequal; eauto.
  }
assert (tr (hyp_tm nonsense :: G) (deq triv triv (sequal (app (subst sh1 m) triv) (app (subst sh1 m) (var 0))))) as Htr.
  {
  simpsubin Hirr.
  apply tr_sequal_symm.
  apply (tr_sequal_eta2 _ (subst sh1 p) (subst sh1 p)).
  replace (sequal (app (subst sh1 m) (var 0)) (app (subst sh1 m) triv)) with (subst1 (var 0) (sequal (app (subst (sh 2) m) (var 0)) (app (subst (sh 2) m) triv))) by (simpsub; auto).
  apply (tr_intersect_elim _ nonsense _ _ _ _ (var 0)).
    {
    eapply (weakening _ [_] []).
      {
      cbn [length unlift].
      simpsub.
      auto.
      }

      {
      cbn [length unlift].
      simpsub.
      auto.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    exact Hirr.
    }
  
    {
    eapply hypothesis; eauto using index_0.
    }
  }
apply tr_constfn_intro; simpsub; auto.
Qed.


Lemma parametricElimOf_valid : parametricElimOf_obligation.
Proof.
prepare.
intros G a b m p ext1 ext0 Hm Hp.
apply (tr_transitivity _ _ (app m p)).
  {
  apply tr_symmetry.
  apply tr_sequal_equal.
    {
    apply tr_constfn_elim.
    eapply tr_conjoin_elim2; eauto.
    }
  eapply tr_pi_elim; eauto.
  eapply tr_conjoin_elim1; eauto.
  }

  {
  apply tr_sequal_equal.
    {
    apply tr_constfn_elim.
    eapply tr_conjoin_elim2; eauto.
    }
  eapply tr_pi_elim; eauto.
  eapply tr_conjoin_elim1; eauto.
  }
Qed.


Lemma parametricElimEq_valid : parametricElimEq_obligation.
Proof.
prepare.
intros G a b m n p q ext1 ext0 Hm Hp.
assert (tr G (deq (app m p) (app n q) (subst1 p b))) as Heq.
  {
  eapply tr_pi_elim; eauto.
  eapply tr_conjoin_elim1; eauto.
  }
apply (tr_transitivity _ _ (app m p)).
  {
  apply tr_symmetry.
  apply tr_sequal_equal.
    {
    apply tr_constfn_elim.
    eapply tr_conjoin_elim2.
    eapply tr_eq_reflexivity; eauto.
    }
  eapply tr_eq_reflexivity; eauto.
  }
apply (tr_transitivity _ _ (app n q)); auto.
apply tr_sequal_equal.
  {
  apply tr_constfn_elim.
  eapply tr_conjoin_elim2.
  eapply tr_eq_reflexivity.
  apply tr_symmetry; eauto.
  }
eapply tr_eq_reflexivity.
eapply tr_symmetry; eauto.
Qed.


Lemma parametricElim_valid : parametricElim_obligation.
Proof.
prepare.
intros G a b p m ext0 Hm Hp.
apply (tr_transitivity _ _ (app m p)).
  {
  apply tr_symmetry.
  apply tr_sequal_equal.
    {
    apply tr_constfn_elim.
    eapply tr_conjoin_elim2; eauto.
    }
  eapply tr_pi_elim; eauto.
  eapply tr_conjoin_elim1; eauto.
  }

  {
  apply tr_sequal_equal.
    {
    apply tr_constfn_elim.
    eapply tr_conjoin_elim2; eauto.
    }
  eapply tr_pi_elim; eauto.
  eapply tr_conjoin_elim1; eauto.
  }
Qed.


Lemma tr_constfn_intro1 :
  forall G (m : @term obj),
    tr (cons (hyp_tm nonsense) G) (deq triv triv (sequal (subst (dot triv sh1) m) m))
    -> tr G (deq (lam m) (lam m) constfn).
Proof.
intros G m H.
apply tr_constfn_intro; auto.
Qed.


Lemma parametricBeta_valid : parametricBeta_obligation.
Proof.
prepare.
intros G m n p H.
apply (tr_compute _ _ (sequal (subst1 triv m) (subst1 n m)) _ triv _ triv); auto using equiv_refl.
  {
  apply equiv_sequal.
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
    apply equiv_refl.
    }
  }
apply tr_sequal_symm.
apply (tr_sequal_eta2 _ p p).
eapply tr_intersect_elim'; eauto.
  {
  apply tr_nonsense_intro.
  }
simpsub.
reflexivity.
Qed.


Lemma parametricEta_valid : parametricEta_obligation.
Proof.
prepare.
intros G a b m ext0 H.
apply tr_conjoin_intro.
  {
  apply (tr_transitivity _ _ (lam (app (subst sh1 m) (var 0)))).
    {
    apply tr_pi_eta.
    eapply tr_conjoin_elim1; eauto.
    }
  apply tr_pi_intro.
    {
    apply (tr_pi_formation_invert1 _#3 b b).
    eapply tr_conjoin_formation_invert1.
    eapply tr_inhabitation_formation; eauto.
    }
  apply tr_sequal_equal.
    {
    apply tr_constfn_elim.
    eapply (weakening _ [_] []).
      {
      cbn [length unlift].
      simpsub.
      auto.
      }

      {
      cbn [length unlift].
      simpsub.
      auto.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_conjoin_elim2; eauto.
    }
  eapply (tr_pi_elim' _ _ (subst (under 1 sh1) b)).
  2:{
    eapply hypothesis; eauto using index_0.
    }

    {
    eapply (weakening _ [_] []).
      {
      cbn [length unlift].
      simpsub.
      auto.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    rewrite -> subst_var0_sh1.
    eapply tr_conjoin_elim1; eauto.
    }
    
    {
    simpsub.
    rewrite -> subst_var0_sh1.
    auto.
    }
  }

  {
  apply tr_constfn_ext.
    {
    eapply tr_conjoin_elim2; eauto.
    }
  apply tr_constfn_intro1.
  simpsub.
  apply tr_sequal_intro.
  }
Qed.


Lemma parametricExt_valid : parametricExt_obligation.
Proof.
prepare.
intros G a b m n ext2 ext1 ext0 Hm Hn Heq.
apply tr_conjoin_intro.
2:{
  apply tr_constfn_ext.
    {
    eapply tr_conjoin_elim2; eauto.
    }

    {
    eapply tr_conjoin_elim2; eauto.
    }
  }
eapply tr_pi_ext; auto.
  {
  eapply (tr_pi_formation_invert1 _ _ _ b b).
  apply (tr_conjoin_formation_invert1 _ _ _ constfn constfn).
  eapply tr_inhabitation_formation; eauto.
  }

2:{
  eapply tr_conjoin_elim1; eauto.
  }

2:{
  eapply tr_conjoin_elim1; eauto.
  }
eapply tr_sequal_equal2; eauto.
  {
  apply tr_constfn_elim.
  eapply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  eapply tr_conjoin_elim2; eauto.
  }

  {
  apply tr_constfn_elim.
  eapply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  eapply tr_conjoin_elim2; eauto.
  }
Qed.


Lemma parametricExt'_valid : parametricExt'_obligation.
Proof.
prepare.
intros G a a' a'' b b' b'' m n ext3 ext2 ext1 ext0 Ha Hm Hn Hmn.
apply tr_conjoin_intro.
2:{
  apply tr_constfn_ext.
    {
    eapply tr_conjoin_elim2; eauto.
    }

    {
    eapply tr_conjoin_elim2; eauto.
    }
  }
eapply tr_pi_ext; auto.
2:{
  eapply tr_conjoin_elim1; eauto.
  }

2:{
  eapply tr_conjoin_elim1; eauto.
  }
eapply tr_sequal_equal2; eauto.
  {
  apply tr_constfn_elim.
  eapply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  eapply tr_conjoin_elim2; eauto.
  }

  {
  apply tr_constfn_elim.
  eapply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  eapply tr_conjoin_elim2; eauto.
  }
Qed.


Lemma parametricOfExt_valid : parametricOfExt_obligation.
Proof.
prepare.
intros G a a' b b' m ext2 ext1 ext0 Ha Hm Hmapp.
apply tr_conjoin_intro.
2:{
  eapply tr_conjoin_elim2; eauto.
  }
eapply tr_pi_ext; eauto.
2:{
  eapply tr_conjoin_elim1; eauto.
  }

2:{
  eapply tr_conjoin_elim1; eauto.
  }
eapply tr_sequal_equal2; eauto.
  {
  apply tr_constfn_elim.
  eapply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  eapply tr_conjoin_elim2; eauto.
  }

  {
  apply tr_constfn_elim.
  eapply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  eapply tr_conjoin_elim2; eauto.
  }
Qed.


Lemma parametricFormInv1_valid : parametricFormInv1_obligation.
Proof.
prepare.
intros G a b ext0 H.
apply (tr_pi_formation_invert1 _#3 b b).
eapply tr_conjoin_formation_invert1; eauto.
Qed.


Lemma parametricFormInv2_valid : parametricFormInv2_obligation.
Proof.
prepare.
intros G a b m ext1 ext0 H Hm.
replace (deqtype (subst (dot m (sh 0)) b)  (subst (dot m (sh 0)) b)) with (substj (dot m id) (deqtype b b)) by (simpsub; auto).
apply (tr_generalize _ a); auto.
apply (tr_pi_formation_invert2 _ a a).
eapply tr_conjoin_formation_invert1; eauto.
Qed.


Lemma parametricElimIrrelevant_valid : parametricElimIrrelevant_obligation.
Proof.
prepare.
intros G m p q.
apply tr_sequal_intro.
Qed.


Lemma irrelevance_valid : irrelevance_obligation.
Proof.
prepare.
unfold Defs.unavailable.
intros G m p H.
apply tr_intersect_intro.
  {
  apply tr_nonsense_formation.
  }
simpsub.
apply (tr_sequal_eta2 _ p p).
exact H.
Qed.
