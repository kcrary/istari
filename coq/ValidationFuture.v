
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

Require Import ValidationUtil.
Require Import Relation.
Require Import Equivalence.
Require Import Equivalences.
Require Import Dynamic.


Hint Rewrite def_fut def_eq def_letnext : prepare.


Lemma futureKind_valid : futureKind_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G i k triv0 triv1 H0 H1.
  valid_rewrite. 
  constructor.
  apply tr_fut_kind_formation; eauto using deq_intro.
  Qed.

Lemma futureKindEq_valid : futureKindEq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G i k l triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  apply tr_fut_kind_formation; eauto using deq_intro; eauto using deq.
Qed.

Lemma futureForm_valid : futureForm_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a triv0 H.
  valid_rewrite. 
  constructor; eauto using deqtype_intro.
  Qed.

Lemma futureEq_valid : futureEq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b triv0 H.
  valid_rewrite.
  constructor; eauto using deqtype_intro.
  Qed.

Lemma futureFormUniv_valid : futureFormUniv_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a i triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  eapply tr_fut_formation_univ; eauto using deq_intro.
  Qed.

Lemma futureEqUniv_valid : futureEqUniv_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b i triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  eapply tr_fut_formation_univ; eauto using deq_intro.
  Qed.

Lemma futureIntroOf_valid : futureIntroOf_obligation. 
  unfoldtop. autounfold with valid_hint.
  intros G  a m triv0 H.
  valid_rewrite. 
  constructor.
  eapply tr_fut_intro; eauto using deq_intro.
Qed.

Lemma futureIntroEq_valid : futureIntroEq_obligation. 
  unfoldtop. autounfold with valid_hint.
  intros G  a m triv0 H.
  valid_rewrite. 
  constructor.
  eapply tr_fut_intro; eauto using deq_intro.
Qed.

Lemma futureIntro_valid : futureIntro_obligation. 
  unfoldtop. autounfold with valid_hint.
  intros G a m H.
  valid_rewrite. 
  eapply tr_fut_intro; eauto using deq_intro.
Qed.

Lemma futureElimOf_valid : futureElimOf_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m p triv0 triv1 triv2 H0 H1 H2.
  valid_rewrite.
  constructor.
  eapply tr_fut_elim; eauto using deq_intro; eauto using deqtype_intro.
Qed.

Lemma futureElimEq_valid : futureElimEq_obligation. 
 unfoldtop. autounfold with valid_hint.
  intros G a b m n p q triv0 triv1 triv2 H0 H1 H2.
  valid_rewrite.
  constructor.
  eapply tr_fut_elim; eauto using deq_intro; eauto using deqtype_intro.
Qed.


Lemma futureElim_valid : futureElim_obligation.
Proof.
prepare.
intros G a b m ext1 ext0 p Ha Hm Hp.
eapply tr_fut_elim; eauto.
Qed.


Lemma futureElimIstype_valid : futureElimIstype_obligation. 
 unfoldtop. autounfold with valid_hint.
  intros G a b m triv0 triv1 triv2 H0 H1 H2.
  valid_rewrite.
  eapply tr_fut_elim_eqtype; eauto using deq_intro; eauto using deqtype_intro.
Qed.

Lemma futureElimEqtype_valid : futureElimEqtype_obligation. 
 unfoldtop. autounfold with valid_hint.
  intros G a b c m n triv0 triv1 triv2 H0 H1 H2.
  valid_rewrite.
  eapply tr_fut_elim_eqtype; eauto using deq_intro; eauto using deqtype_intro.
Qed.

Lemma futureEta_valid : futureEta_obligation. 
  unfoldtop. autounfold with valid_hint.
  intros G a m triv0 H.
  valid_rewrite.
  constructor.
  eapply tr_fut_eta; eauto using deq_intro.
Qed.

Lemma futureLeft_valid : futureLeft_obligation. 
 unfoldtop. autounfold with valid_hint.
  intros G1 G2 a b triv0 m H0 H1.
  valid_rewrite.
  match goal with |- tr ?G ?J =>
                  assert (equivctx G
    (G2 ++
     hyp_tm (fut a) :: G1)
                         ) as Hctx end.

  { apply equivctx_refl. }
  apply tr_fut_eta_hyp; auto.
  eauto using deqtype_intro.
Qed.


Lemma futureLeftHidden_valid : futureLeftHidden_obligation.
Proof.
prepare.
intros G1 G2 a b ext0 m Hhyp Ha Hm.
replace (subst (under (length G2) (dot triv (sh 1))) m) with (subst (under (length G2) (dot (prev (var 0)) sh1)) (subst (under (length G2) (dot triv sh1)) m)).
2:{
  simpsub.
  rewrite <- compose_under.
  simpsub.
  reflexivity.
  }
apply tr_fut_eta_hyp; auto.
replace (subst (under (length G2) (dot triv sh1)) m) with m; auto.
symmetry.
apply subst_into_absent_single.
auto.
Qed.


Lemma tr_future_sub :
  forall G a b,
    tr (promote G) (dsubtype a b)
    -> tr G (dsubtype (fut a) (fut b)).
Proof.
intros G a b Ha.
apply tr_subtype_intro.
  {
  apply tr_fut_formation.
  eapply tr_subtype_istype1; eauto.
  }

  {
  apply tr_fut_formation.
  eapply tr_subtype_istype2; eauto.
  }
simpsub.
apply (tr_fut_ext _ _ (subst sh1 a) (subst sh1 a)).
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  eapply hypothesis; eauto using index_0.
  }
replace (next (prev (var 0))) with (@subst1 obj (prev (var 0)) (next (var 0))).
2:{
  simpsub.
  auto.
  }
replace (fut (subst sh1 b)) with (subst1 (prev (var 0)) (fut (subst (sh 2) b))).
2:{
  simpsub.
  auto.
  }
apply (tr_fut_elim _ (var 0) (var 0) (subst sh1 a) (next (var 0)) (next (var 0)) (fut (subst (sh 2) b))).
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  cbn.
  fold (promote G).
  eapply (weakening _ [_] []).
    {
    cbn [length Dots.unlift].
    simpsub.
    auto.
    }
  
    {
    cbn [length Dots.unlift].
    simpsub.
    auto.
    }
  cbn [length Dots.unlift].
  simpsub.
  cbn [List.app].
  eapply tr_subtype_istype1; eauto.
  }
apply tr_fut_intro.
cbn.
fold (promote G).
eapply (weakening _ [_] [_]).
  {
  cbn [length Dots.unlift].
  simpsub.
  auto.
  }

  {
  cbn [length Dots.unlift].
  simpsub.
  auto.
  }
cbn [length Dots.unlift].
simpsub.
cbn [List.app].
apply (tr_subtype_elim _ (subst sh1 a)).
  {
  eapply (weakening _ [_] []).
    {
    cbn [length Dots.unlift].
    simpsub.
    auto.
    }
  
    {
    cbn [length Dots.unlift].
    simpsub.
    auto.
    }
  cbn [length Dots.unlift].
  simpsub.
  cbn [List.app].
  exact Ha.
  }

  {
  eapply hypothesis; eauto using index_0.
  }
Qed.
 

Lemma futureSub_valid : futureSub_obligation.
Proof.
prepare.
intros G a b ext0 H.
apply tr_future_sub; auto.
Qed.


Lemma futureElimOfLetnext_valid : futureElimOfLetnext_obligation.
Proof.
prepare.
intros G a b m p ext2 ext1 ext0 Ha Hm Hp.
eapply tr_fut_elim; eauto.
Qed.


Lemma futureElimOfLetnextNondep_valid : futureElimOfLetnextNondep_obligation.
Proof.
prepare.
intros G a b m p ext2 ext1 ext0 Ha Hm Hp.
replace b with (subst1 (prev m) (subst sh1 b)) by (simpsub; reflexivity).
eapply tr_fut_elim; eauto.
Qed.


Lemma futureElimIstypeLetnext_valid : futureElimIstypeLetnext_obligation.
Proof.
prepare.
intros G a b m ext2 ext1 ext0 Ha Hm Hb.
eapply tr_fut_elim_eqtype; eauto.
Qed.


Lemma futureExt_valid : futureExt_obligation.
Proof.
prepare.
intros G a m n ext2 ext1 ext0 Hm Hn Hmn.
eapply tr_fut_ext; eauto.
apply tr_fut_intro; auto.
Qed.


Lemma futureInjection_valid : futureInjection_obligation.
Proof.
prepare.
intros G a m n ext1 ext0 Ha Hmn.
assert (equiv m (prev (next m))) as Hequivm.
  {
  apply equiv_symm.
  apply steps_equiv.
  apply star_one.
  apply step_prev2.
  }
assert (equiv n (prev (next n))) as Hequivn.
  {
  apply equiv_symm.
  apply steps_equiv.
  apply star_one.
  apply step_prev2.
  }
apply (tr_eqtype_convert _ _ _ (fut (equal a m m))).
  {
  unfold deqtype.
  apply (tr_compute _ _ (eqtype (fut (equal a (prev (next m)) (prev (next m)))) (fut (equal a (prev (next m)) (prev (next n))))) _ triv _ triv); auto using equiv_refl.
    {
    apply equiv_eqtype.
      {
      apply equiv_fut.
      apply equiv_equal; auto using equiv_refl.
      }

      {
      apply equiv_fut.
      apply equiv_equal; auto using equiv_refl.
      }
    }
  fold (deqtype (fut (equal a (prev (next m)) (prev (next m)))) (fut (equal a (prev (next m)) (prev (next n))))).
  cut (tr G (deqtype (subst (dot (prev (next m)) id) (subst (dot (prev (next (subst sh1 m))) id) (fut (equal (subst (sh 2) a) (var 0) (var 1))))) (subst (dot (prev (next n)) id) (subst (dot (prev (next (subst sh1 m))) id) (fut (equal (subst (sh 2) a) (var 0) (var 1))))))).
    {
    simpsub.
    auto.
    }
  apply (tr_fut_elim_eqtype _ _ _ a); auto.
  apply (tr_fut_elim_eqtype _ _ _ (subst sh1 a)); auto.
    {
    apply (weakening _ [_] []).
      {
      cbn [length].
      simpsub.
      auto.
      }

      {
      cbn [length Dots.unlift].
      simpsub.
      auto.
      }
    cbn [length Dots.unlift].
    simpsub.
    cbn [List.app].
    apply (tr_transitivity _ _ (next n)).
      {
      exact Hmn.
      }
      
      {
      apply tr_symmetry.
      exact Hmn.
      }
    }

    {
    cbn.
    apply (weakening _ [_] []).
      {
      cbn [length].
      simpsub.
      auto.
      }

      {
      cbn [length Dots.unlift].
      simpsub.
      auto.
      }
    cbn [length Dots.unlift].
    simpsub.
    cbn [List.app].
    exact Ha.
    }
  
    {
    apply tr_fut_formation.
    cbn.
    fold (promote G).
    apply tr_equal_formation.
      {
      apply (weakening _ [_; _] []).
        {
        cbn [length].
        simpsub.
        auto.
        }
  
        {
        cbn [length Dots.unlift].
        simpsub.
        auto.
        }
      cbn [length Dots.unlift].
      simpsub.
      cbn [List.app].
      exact Ha.
      }

      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      auto.
      }

      {
      eapply hypothesis; eauto using index_S, index_0.
      }
    }
  }

  {
  apply (tr_compute _ _ (fut (equal a (prev (next m)) (prev (next m)))) _ (next triv) _ (next triv)); auto using equiv_refl.
    {
    apply equiv_fut.
    apply equiv_equal; auto using equiv_refl.
    }
  cut (tr G (deq (subst (dot (prev (next m)) id) (next triv)) (subst (dot (prev (next m)) id) (next triv)) (subst (dot (prev (next m)) id) (fut (equal (subst sh1 a) (var 0) (var 0)))))).
    {
    simpsub.
    auto.
    }
  apply (tr_fut_elim _ _ _ a).
    {
    apply (tr_transitivity _ _ (next n)).
      {
      exact Hmn.
      }
      
      {
      apply tr_symmetry.
      exact Hmn.
      }
    }

    {
    exact Ha.
    }

    {
    apply tr_fut_intro.
    cbn.
    fold (promote G).
    apply tr_equal_intro.
    eapply hypothesis; eauto using index_0.
    }
  }
Qed.


Lemma futureSquashSwap_valid : futureSquashSwap_obligation.
Proof.
prepare.
intros G a ext1 m Ha Hm.
rewrite -> def_squash in Hm |- *.
eapply tr_future_squash_swap; eauto.
Qed.


Lemma futureIsquashSwap_valid : futureIsquashSwap_obligation.
Proof.
prepare.
intros G a ext1 m Ha Hm.
rewrite -> def_isquash in Hm |- *.
eapply tr_future_isquash_swap; eauto.
Qed.


Lemma squashFutureSwap_valid : squashFutureSwap_obligation.
Proof.
prepare.
intros G a m ext0 Ha Hm.
rewrite -> def_squash in Hm |- *.
simpsub.
eapply tr_squash_future_swap; eauto.
Qed.


Lemma isquashFutureSwap_valid : isquashFutureSwap_obligation.
Proof.
prepare.
intros G a m ext0 Ha Hm.
rewrite -> def_isquash in Hm |- *.
simpsub.
eapply tr_isquash_future_swap; eauto.
Qed.
