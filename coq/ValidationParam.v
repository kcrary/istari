
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


Hint Rewrite def_irrelevant def_nonsense def_parametric def_sequal : prepare.


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


Lemma irrelevant_elim :
  forall G m p,
    tr G (deq p p (pi nonsense (sequal m (subst (dot triv sh1) m))))
    -> tr (hyp_tm nonsense :: G) (deq triv triv (sequal m (subst (dot triv sh1) m))).
Proof.
intros G m p H.
apply (tr_sequal_eta2 _ (app (subst sh1 p) (var 0)) (app (subst sh1 p) (var 0))).
eapply (tr_pi_elim' _ _ (sequal (subst (dot (var 0) (sh 2)) m) (subst (dot triv (sh 2)) m))).
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


Lemma parametricElimOf_valid : parametricElimOf_obligation.
Proof.
prepare.
intros G a b m p ext1 ext0 Hm Hp.
eapply tr_pi_elim; eauto.
eapply tr_conjoin_elim1; eauto.
Qed.


Lemma parametricElimEq_valid : parametricElimEq_obligation.
Proof.
prepare.
intros G a b m n p q ext1 ext0 Hm Hp.
eapply tr_pi_elim; eauto.
eapply tr_conjoin_elim1; eauto.
Qed.


Lemma parametricElim_valid : parametricElim_obligation.
Proof.
prepare.
intros G a b p m ext0 Hm Hp.
eapply tr_pi_elim; eauto.
eapply tr_conjoin_elim1; eauto.
Qed.


Lemma parametricEta_valid : parametricEta_obligation.
Proof.
prepare.
intros G a b m ext0 H.
apply tr_conjoin_intro.
  {
  apply tr_pi_eta.
  eapply tr_conjoin_elim1; eauto.
  }

  {
  apply tr_sequal_equal.
    {
    apply (tr_pi_eta_sequal _ a b); auto.
    eapply tr_conjoin_elim1; eauto.
    }

    {
    eapply tr_conjoin_elim2; eauto.
    }
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


  {
  eapply tr_conjoin_elim1; eauto.
  }

  {
  eapply tr_conjoin_elim1; eauto.
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
  {
  eapply tr_conjoin_elim1; eauto.
  }

  {
  eapply tr_conjoin_elim1; eauto.
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
  {
  eapply tr_conjoin_elim1; eauto.
  }

  {
  eapply tr_conjoin_elim1; eauto.
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


Lemma parametricIntroIntersectEq_valid : parametricIntroIntersectEq_obligation.
Proof.
prepare.
intros G a b m n ext0 H.
assert (tr G (deqtype a a)) as Ha.
  {
  apply (tr_intersect_formation_invert1 _ _ _ b b).
  eapply tr_inhabitation_formation; eauto.
  }
apply tr_conjoin_intro.
  {
  apply tr_pi_intro; auto.
  replace b with (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)).
  2:{
    simpsub.
    rewrite -> subst_var0_sh1; auto.
    }
  apply (tr_intersect_elim _ (subst sh1 a) _#4 (var 0)).
  2:{
    eapply hypothesis; eauto using index_0.
    }
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
  rewrite -> subst_var0_sh1; auto.
  }

  {
  apply tr_constfn_intro.
    {
    simpsub.
    apply tr_sequal_intro.
    }

    {
    simpsub.
    apply tr_sequal_intro.
    }
  }
Qed.


Lemma parametricIntroIntersectOf_valid : parametricIntroIntersectOf_obligation.
Proof.
prepare.
intros G a b m ext0 H.
assert (tr G (deqtype a a)) as Ha.
  {
  apply (tr_intersect_formation_invert1 _ _ _ b b).
  eapply tr_inhabitation_formation; eauto.
  }
apply tr_conjoin_intro.
  {
  apply tr_pi_intro; auto.
  replace b with (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)).
  2:{
    simpsub.
    rewrite -> subst_var0_sh1; auto.
    }
  apply (tr_intersect_elim _ (subst sh1 a) _#4 (var 0)).
  2:{
    eapply hypothesis; eauto using index_0.
    }
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
  rewrite -> subst_var0_sh1; auto.
  }

  {
  apply tr_constfn_intro.
    {
    simpsub.
    apply tr_sequal_intro.
    }

    {
    simpsub.
    apply tr_sequal_intro.
    }
  }
Qed.


Lemma parametricIntroIntersect_valid : parametricIntroIntersect_obligation.
Proof.
prepare.
intros G a b m H.
assert (tr G (deqtype a a)) as Ha.
  {
  apply (tr_intersect_formation_invert1 _ _ _ b b).
  eapply tr_inhabitation_formation; eauto.
  }
apply tr_conjoin_intro.
  {
  apply tr_pi_intro; auto.
  replace b with (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)).
  2:{
    simpsub.
    rewrite -> subst_var0_sh1; auto.
    }
  apply (tr_intersect_elim _ (subst sh1 a) _#4 (var 0)).
  2:{
    eapply hypothesis; eauto using index_0.
    }
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
  rewrite -> subst_var0_sh1; auto.
  }

  {
  apply tr_constfn_intro.
    {
    simpsub.
    apply tr_sequal_intro.
    }

    {
    simpsub.
    apply tr_sequal_intro.
    }
  }
Qed.


Lemma tr_parametric_elim_intersect :
  forall G a b m n p q,
    tr G (deq m n (conjoin (pi a b) constfn))
    -> tr G (deq (app m p) (app n q) (intersect a b)).
Proof.
intros G a b m n p q Hmn.
assert (tr G (deqtype a a)) as Ha.
  {
  apply (tr_pi_formation_invert1 _#3 b b).
  apply (tr_conjoin_formation_invert1 _#3 constfn constfn).
  eapply tr_inhabitation_formation; eauto.
  }
apply tr_intersect_intro; auto.
simpsub.
apply (tr_transitivity _ _ (app (subst sh1 m) (var 0))).
  {
  apply tr_symmetry.
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
    apply (tr_eq_reflexivity _ _ n).
    eapply tr_conjoin_elim2; eauto.
    }

    {
    replace b with (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)).
    2:{
      simpsub.
      rewrite -> subst_var0_sh1; auto.
      }
    apply (tr_pi_elim _ (subst sh1 a)).
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
      apply (tr_eq_reflexivity _ _ n).
      eapply tr_conjoin_elim1; eauto.
      }
      
      {
      eapply hypothesis; eauto using index_0.
      }
    }
  }
apply (tr_transitivity _ _ (app (subst sh1 n) (var 0))).
2:{
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
    apply (tr_eq_reflexivity _ _ m).
    apply tr_symmetry.
    eapply tr_conjoin_elim2; eauto.
    }

    {
    replace b with (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)).
    2:{
      simpsub.
      rewrite -> subst_var0_sh1; auto.
      }
    apply (tr_pi_elim _ (subst sh1 a)).
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
      apply (tr_eq_reflexivity _ _ m).
      apply tr_symmetry.
      eapply tr_conjoin_elim1; eauto.
      }
      
      {
      eapply hypothesis; eauto using index_0.
      }
    }
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
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  rewrite -> subst_var0_sh1; auto.
  eapply tr_conjoin_elim1; eauto.
  }

  {
  simpsub.
  rewrite -> subst_var0_sh1; auto.
  }
Qed.


Lemma parametricElimIntersectEq_valid : parametricElimIntersectEq_obligation.
Proof.
prepare.
intros G a b m n p q ext0 Hmn.
apply tr_parametric_elim_intersect; auto.
Qed.


Lemma parametricElimIntersectOf_valid : parametricElimIntersectOf_obligation.
Proof.
prepare.
intros G a b m p ext0 Hm.
apply tr_parametric_elim_intersect; auto.
Qed.


Lemma parametricElimIntersect_valid : parametricElimIntersect_obligation.
Proof.
prepare.
intros G a b m H.
apply tr_parametric_elim_intersect; auto.
Qed.


Lemma parametricElimIrrelevant_valid : parametricElimIrrelevant_obligation.
Proof.
prepare.
intros G a b m p q ext0 H.
apply tr_constfn_elim.
eapply tr_conjoin_elim2; eauto.
Qed.


Lemma tr_sequal_subst :
  forall G m n p,
    tr (hyp_tm nonsense :: G) (deq triv triv (sequal m n))
    -> tr G (deq triv triv (sequal (subst1 p m) (subst1 p n))).
Proof.
intros G m n p H.
replace (deq triv triv (sequal (subst1 p m) (subst1 p n))) with (substj (dot p id) (deq triv triv (sequal m n))) by (simpsub; auto).
apply (tr_generalize _ nonsense p); auto.
unfold nonsense.
apply tr_guard_intro.
  {
  apply tr_voidtp_istype.
  }
apply (tr_voidtp_elim _ (var 0) (var 0)).
eapply hypothesis; eauto using index_0.
Qed.


Lemma irrelevantCompat_valid : irrelevantCompat_obligation.
Proof.
prepare.
intros G m n p q Hm Hn.
apply tr_pi_intro.
  {
  apply tr_nonsense_formation.
  }
simpsub.
so (irrelevant_elim _ _ _ Hm) as Hm'.
so (irrelevant_elim _ _ _ Hn) as Hn'.
apply (tr_sequal_trans _ _ (subst1 n (subst (dot (var 0) (dot triv (sh 2))) m))).
2:{
  replace
    (subst (dot (subst (dot triv sh1) n) (dot triv sh1)) m)
    with 
    (subst1 (subst (dot triv sh1) n) (subst (dot (var 0) (dot triv (sh 2))) m)) 
    by (simpsub; auto).
  apply tr_sequal_compat; auto.
  }

  {
  apply tr_sequal_subst.
  simpsubin Hm'.
  cbn [Nat.add] in Hm'.
  apply (exchange_1_1 _ _ _ []).
    {
    simpsub.
    auto.
    }
  cbn [length].
  simpsub.
  cbn [List.app].
  exact Hm'.
  }
Qed.


Lemma irrelevantLam_valid : irrelevantLam_obligation.
Proof.
prepare.
intros G m p H.
apply tr_pi_intro.
  {
  apply tr_nonsense_formation.
  }
simpsub.
cbn [Nat.add].
apply tr_sequal_compat_lam.
apply (exchange_1_1 _ _ _ []).
  {
  simpsub.
  auto.
  }
cbn [length].
simpsub.
cbn [List.app].
so (irrelevant_elim _#3 H) as H'.
simpsubin H'.
cbn [Nat.add] in H'.
exact H'.
Qed.


Lemma irrelevantApp_valid : irrelevantApp_obligation.
Proof.
prepare.
intros G m n ext1 ext0 Hm Hn.
apply tr_pi_intro.
  {
  apply tr_nonsense_formation.
  }
simpsub.
so (irrelevant_elim _ _ _ Hm) as Hm'.
so (irrelevant_elim _ _ _ Hn) as Hn'.
so (tr_sequal_compat _ _ _ (app (var 0) (subst sh1 n)) Hm') as H1.
simpsubin H1.
so (tr_sequal_compat _ _ _ (app (subst sh1 (subst (dot triv sh1) m)) (var 0)) Hn') as H2.
simpsubin H2.
eapply tr_sequal_trans; eauto.
Qed.


Lemma irrelevantAppParametric_valid : irrelevantAppParametric_obligation.
Proof.
prepare.
intros G a b m n ext1 ext0 Hirr Hparam.
apply tr_pi_intro.
  {
  apply tr_nonsense_formation.
  }
simpsub.
so (irrelevant_elim _ _ _ Hirr) as Hirr'.
so (tr_sequal_compat _ _ _ (app (var 0) (subst sh1 (subst (dot triv sh1) n))) Hirr') as H2.
simpsubin H2.
eapply tr_sequal_trans; eauto.
apply tr_constfn_elim.
eapply tr_conjoin_elim2; eauto.
Qed.


Lemma irrelevantPair_valid : irrelevantPair_obligation.
Proof.
prepare.
intros G m n ext1 ext0 Hm Hn.
apply tr_pi_intro.
  {
  apply tr_nonsense_formation.
  }
simpsub.
so (irrelevant_elim _ _ _ Hm) as Hm'.
so (irrelevant_elim _ _ _ Hn) as Hn'.
so (tr_sequal_compat _ _ _ (ppair (var 0) (subst sh1 n)) Hm') as H1.
simpsubin H1.
so (tr_sequal_compat _ _ _ (ppair (subst sh1 (subst (dot triv sh1) m)) (var 0)) Hn') as H2.
simpsubin H2.
eapply tr_sequal_trans; eauto.
Qed.


Lemma irrelevantPi1_valid : irrelevantPi1_obligation.
Proof.
prepare.
intros G m ext0 Hm.
apply tr_pi_intro.
  {
  apply tr_nonsense_formation.
  }
simpsub.
so (irrelevant_elim _ _ _ Hm) as Hm'.
so (tr_sequal_compat _ _ _ (ppi1 (var 0)) Hm') as H.
simpsubin H.
exact H.
Qed.


Lemma irrelevantPi2_valid : irrelevantPi2_obligation.
Proof.
prepare.
intros G m ext0 Hm.
apply tr_pi_intro.
  {
  apply tr_nonsense_formation.
  }
simpsub.
so (irrelevant_elim _ _ _ Hm) as Hm'.
so (tr_sequal_compat _ _ _ (ppi2 (var 0)) Hm') as H.
simpsubin H.
exact H.
Qed.


Lemma irrelevantNext_valid : irrelevantNext_obligation.
Proof.
prepare.
intros G m ext0 Hm.
apply tr_pi_intro.
  {
  apply tr_nonsense_formation.
  }
simpsub.
so (irrelevant_elim _ _ _ Hm) as Hm'.
so (tr_sequal_compat _ _ _ (next (var 0)) Hm') as H.
simpsubin H.
exact H.
Qed.


Lemma irrelevantPrev_valid : irrelevantPrev_obligation.
Proof.
prepare.
intros G m ext0 Hm.
apply tr_pi_intro.
  {
  apply tr_nonsense_formation.
  }
simpsub.
so (irrelevant_elim _ _ _ Hm) as Hm'.
so (tr_sequal_compat _ _ _ (prev (var 0)) Hm') as H.
simpsubin H.
exact H.
Qed.
