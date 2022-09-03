
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

Require Import ValidationUtil.


Hint Rewrite def_pi def_arrow def_tarrow def_karrow : prepare.


Lemma forallForm_valid : forallForm_obligation.
Proof.
prepare.
intros G a b m n Ha Hb.
apply tr_pi_formation; auto.
Qed.


Lemma forallEq_valid: forallEq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a a' b b' m n Ha Hb.
  valid_rewrite.
  apply tr_pi_formation; eauto using deqtype_intro.
Qed.

Lemma forallFormUniv_valid : forallFormUniv_obligation.
Proof.
prepare.
intros G a b i ext1 ext0 Ha Hb.
apply tr_pi_formation_univ; auto.
Qed.


Lemma forallEqUniv_valid : forallEqUniv_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a a' b b' i triv0 triv1 Ha Hb.
  valid_rewrite.
  constructor.
  apply tr_pi_formation_univ; eauto using deq_intro.
  Qed.


Lemma tr_pi_sub :
  forall G a a' b b',
    tr G (dsubtype a' a)
    -> tr (hyp_tm a' :: G) (dsubtype b b')
    -> tr (hyp_tm a :: G) (deqtype b b)
    -> tr G (dsubtype (pi a b) (pi a' b')).
Proof.
intros G a a' b b' Hsuba Hsubb Hb.
apply tr_subtype_intro.
  {
  apply tr_pi_formation; auto.
  eapply tr_subtype_istype2; eauto.
  }

  {
  apply tr_pi_formation.
    {
    eapply tr_subtype_istype1; eauto.
    }

    {
    eapply tr_subtype_istype2; eauto.
    }
  }
simpsub.
eapply tr_pi_ext; eauto.
3:{
  eapply hypothesis; eauto using index_0.
  simpsub.
  auto.
  }

3:{
  eapply hypothesis; eauto using index_0.
  simpsub.
  auto.
  }

  {
  apply (weakening _ [_] []).
    {
    simpsub.
    auto.
    }
  
    {
    simpsub.
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  eapply tr_subtype_istype1; eauto.
  }

  {
  simpsub.
  cbn [Nat.add].
  apply (tr_subtype_elim _ (subst (dot (var 0) (sh 2)) b)).
    {
    eapply (weakening _ [_] [_]).
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
    rewrite -> !subst_var0_sh1; auto.
    }

    {
    eapply tr_pi_elim'.
      {
      eapply hypothesis; eauto using index_S, index_0.
      simpsub; auto.
      }
  
      {
      eapply (tr_subtype_elim _ (subst (sh 2) a')).
        {
        eapply (weakening _ [_; _] []).
          {
          simpsub; auto.
          }
  
          {
          cbn [length unlift].
          simpsub.
          reflexivity.
          }
        cbn [length unlift].
        simpsub.
        cbn [List.app].
        auto.
        }
  
        {
        eapply hypothesis; eauto using index_0.
        simpsub; auto.
        }
      }
      
      {
      simpsub.
      cbn [Nat.add].
      simpsub.
      auto.
      }
    }
  }
Qed.



Lemma forallSub_valid : forallSub_obligation.
Proof.
prepare.
intros G a a' b b' ext2 ext1 ext0 Hsuba Hsubb Hb.
apply tr_pi_sub; auto.
Qed.


Lemma forallIntroOf_valid : forallIntroOf_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m triv0 triv1 Ha Hb.
  valid_rewrite.
  constructor.
  apply tr_pi_intro.
    - eauto using deqtype_intro.
    - eauto using deq_intro.
  Qed.

Lemma forallIntroEq_valid : forallIntroEq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m n triv0 triv1 Ha Hb.
  valid_rewrite.
  constructor.
  apply tr_pi_intro.
    - eauto using deqtype_intro.
    - eauto using deq_intro.
  Qed.


Lemma forallIntro_valid : forallIntro_obligation.
Proof.
prepare.
intros G a b ext0 m Ha Hb.
apply tr_pi_intro; auto.
Qed.


Lemma forallElimOf_valid : forallElimOf_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m p triv0 triv1 Ha Hforall.
  valid_rewrite.
  constructor.
  eapply tr_pi_elim; eauto using deq_intro.
  Qed.

Lemma forallElimEq_valid : forallElimEq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m n p q triv0 triv1 H1 H2.
  valid_rewrite.
  constructor.
  eapply tr_pi_elim; eauto using deq_intro.
  Qed.


Lemma forallElim_valid : forallElim_obligation.
Proof.
prepare.
intros G a b p m ext0 Hm Hp.
eapply tr_pi_elim; eauto.
Qed.


Lemma forallEta_valid : forallEta_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m triv0 Hforall.
  valid_rewrite.
  constructor.
  apply tr_pi_eta. eauto using deq_intro.
  Qed.


Lemma forallExt_valid : forallExt_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m n ext2 ext1 ext0 Hm Hn Hmn.
rewrite -> def_eq in Hmn |- *.
rewrite -> def_of in Hm, Hn.
rewrite -> def_pi in Hm, Hn |- *.
unfold Defs.triv.
apply tr_equal_intro.
eapply tr_pi_ext; eauto.
3:{
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

3:{
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  eapply tr_pi_formation_invert1.
  eapply tr_equal_formation_invert1.
  eapply tr_inhabitation_formation; eauto.
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma forallOfExt_valid : forallOfExt_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a a' b b' m ext2 ext1 ext0 Ha Hm Happ.
rewrite -> def_istp in Ha.
rewrite -> def_of in * |- *.
rewrite -> def_pi in Hm |- *.
unfold Defs.triv.
apply tr_equal_intro.
eapply tr_pi_ext; eauto.
3:{
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

3:{
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  eapply tr_eqtype_eta2; eauto.
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma forallFormInv1_valid : forallFormInv1_obligation.
Proof.
prepare.
intros G a b ext0 Histp.
eapply tr_pi_formation_invert1; eauto.
Qed.


Lemma forallFormInv2_valid : forallFormInv2_obligation.
Proof.
prepare.
intros G a b m ext1 ext0 Hpi Hm.
simpsub.
cut (tr (hyp_tm a :: G) (deqtype b b)).
  {
  intro Hb.
  so (tr_generalize _#4 Hm Hb) as H.
  simpsubin H.
  exact H.
  }
eapply tr_pi_formation_invert2; eauto.
Qed.


Lemma arrowForm_valid : arrowForm_obligation.
Proof.
prepare.
intros G a b ext1 ext0 H0 H1.
apply tr_pi_formation; auto.
Qed.


Lemma arrowEq_valid : arrowEq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a a' b b' triv0 triv1 H1 H2.
  valid_rewrite.
  constructor; eauto using deqtype_intro.
  Qed.

Lemma arrowFormUniv_valid : arrowFormUniv_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b i triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  apply tr_pi_formation_univ; eauto using deq_intro.
  Qed.

Lemma arrowEqUniv_valid : arrowEqUniv_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a a' b b' i triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  apply tr_pi_formation_univ; eauto using deq_intro.
Qed.


Lemma arrowSub_valid : arrowSub_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a a' b b' ext1 ext0 Hsuba Hsubb.
unfold Defs.triv.
rewrite -> def_subtype in Hsuba, Hsubb |- *.
rewrite -> !def_arrow.
apply tr_pi_sub.
  {
  eapply tr_subtype_eta2; eauto.
  }

  {
  apply (weakening _ [_] []).
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
  eapply tr_subtype_eta2; eauto.
  }

  {
  apply (weakening _ [_] []).
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
  eapply tr_subtype_istype1.
  eapply tr_subtype_eta2; eauto.
  }
Qed.


Lemma arrowForallSub_valid : arrowForallSub_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a a' b b' ext2 ext1 ext0 Hsuba Hsubb Hb.
unfold Defs.triv.
rewrite -> def_subtype in Hsuba, Hsubb |- *.
rewrite -> def_istp in Hb.
rewrite -> def_arrow.
rewrite -> def_pi.
apply tr_pi_sub.
  {
  eapply tr_subtype_eta2; eauto.
  }

  {
  eapply tr_subtype_eta2; eauto.
  }

  {
  apply (weakening _ [_] []).
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
  eapply tr_eqtype_eta2; eauto.
  }
Qed.


Lemma forallArrowSub_valid : forallArrowSub_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a a' b b' ext2 ext1 ext0 Hsuba Hsubb Hb.
unfold Defs.triv.
rewrite -> def_subtype in Hsuba, Hsubb |- *.
rewrite -> def_istp in Hb.
rewrite -> def_arrow.
rewrite -> def_pi.
apply tr_pi_sub.
  {
  eapply tr_subtype_eta2; eauto.
  }

  {
  eapply tr_subtype_eta2; eauto.
  }

  {
  eapply tr_eqtype_eta2; eauto.
  }
Qed.


Lemma arrowIntroOf_valid: arrowIntroOf_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  apply tr_pi_intro; eauto using deq_intro;
    eauto using deqtype_intro.
Qed.

Lemma arrowIntroEq_valid: arrowIntroEq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m n triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  apply tr_pi_intro; eauto using deq_intro;
    eauto using deqtype_intro.
Qed.


Lemma arrowIntro_valid : arrowIntro_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b ext0 m Ha Hm.
rewrite -> def_arrow.
rewrite -> def_istp in Ha.
apply tr_pi_intro; auto.
eapply tr_eqtype_eta2; eauto.
Qed.


Lemma arrowElimOf_valid: arrowElimOf_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m p triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  assert ((subst1 p (subst sh1 b)) = b) as Heq.
  { simpsub. auto. }
  rewrite <- Heq.
  eapply tr_pi_elim; eauto using deq_intro;
    eauto using deqtype_intro.
Qed.

Lemma arrowElimEq_valid: arrowElimEq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m n p q triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  assert ((subst1 p (subst sh1 b)) = b) as Heq.
  { simpsub. auto. }
  rewrite <- Heq.
  eapply tr_pi_elim; eauto using deq_intro;
    eauto using deqtype_intro.
Qed.


Lemma arrowElim_valid : arrowElim_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m p Hm Hp.
rewrite -> def_arrow in Hm.
replace b with (subst1 p (subst sh1 b)) by (simpsub; auto).
eapply tr_pi_elim; eauto.
Qed.


Lemma arrowEta_valid : arrowEta_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m triv0 Harrow.
  valid_rewrite.
  constructor.
  apply tr_pi_eta. eauto using deq_intro.
Qed.


Lemma arrowExt_valid : arrowExt_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m n ext2 ext1 ext0 Hm Hn Heq.
rewrite -> def_eq in Heq |- *.
rewrite -> def_of in Hm, Hn.
rewrite -> def_arrow in Hm, Hn |- *.
unfold Defs.triv.
apply tr_equal_intro.
apply (tr_pi_ext _#5 a a (subst sh1 b) (subst sh1 b)).
  {
  apply (tr_pi_formation_invert1 _#3 (subst sh1 b) (subst sh1 b)).
  eapply tr_equal_formation_invert1.
  eapply tr_inhabitation_formation; eauto.
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma arrowOfExt_valid : arrowOfExt_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a a' b b' m ext2 ext1 ext0 Ha Halt Hof.
rewrite -> def_of in Halt, Hof |- *.
rewrite -> def_istp in Ha.
rewrite -> def_pi in Halt.
rewrite -> def_arrow.
unfold Defs.triv.
apply tr_equal_intro.
apply (tr_pi_ext _#5 a' a' b' b').
  {
  eapply tr_eqtype_eta2; eauto.
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma arrowFormInv1_valid : arrowFormInv1_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b ext0 Hab.
rewrite -> def_istp in Hab |- *.
rewrite -> def_arrow in Hab.
unfold Defs.triv.
eapply tr_pi_formation_invert1.
eapply tr_eqtype_eta2; eauto.
Qed.


Lemma tarrowKind_valid : tarrowKind_obligation.
Proof.
prepare.
intros G a i k ext1 ext0 H0 H1.
apply tr_arrow_kind_formation; auto.
Qed.


Lemma tarrowKindEq_valid : tarrowKindEq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a a' i k k' triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  apply tr_arrow_kind_formation; eauto using deq_intro.
  Qed.

Lemma tarrowForm_valid : tarrowForm_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor; eauto using deqtype_intro.
  Qed.

Lemma tarrowEq_valid : tarrowEq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a a' b b' triv0 triv1 H1 H2.
  valid_rewrite.
  constructor; eauto using deqtype_intro.
  Qed.

Lemma tarrowFormUniv_valid : tarrowFormUniv_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b i triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  apply tr_arrow_formation_univ; eauto using deq_intro.
  Qed.

Lemma tarrowEqUniv_valid : tarrowEqUniv_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a a' b b' i triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  apply tr_arrow_formation_univ; eauto using deq_intro.
Qed.


Lemma tarrowArrowEq_valid : tarrowArrowEq_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a a' b b' ext1 ext0 Ha Hb.
rewrite -> def_eqtp in Ha, Hb |- *.
rewrite -> def_tarrow.
rewrite -> def_arrow.
unfold Defs.triv.
apply (tr_eqtype_transitivity _ _ (arrow a' b')).
  {
  apply tr_arrow_formation; eapply tr_eqtype_eta2; eauto.
  }
apply tr_arrow_pi_equal.
  {
  apply (tr_eqtype_transitivity _ _ a); [apply tr_eqtype_symmetry |]; eapply tr_eqtype_eta2; eauto.
  }

  {
  apply (tr_eqtype_transitivity _ _ b); [apply tr_eqtype_symmetry |]; eapply tr_eqtype_eta2; eauto.
  }
Qed.


Lemma tarrowArrowEqUniv_valid : tarrowArrowEqUniv_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a a' b b' i ext1 ext0 Ha Hb.
rewrite -> def_eq, -> def_univ in Ha, Hb |- *.
rewrite -> def_tarrow.
rewrite -> def_arrow.
unfold Defs.triv.
apply tr_equal_intro.
apply (tr_transitivity _ _ (arrow a' b')).
  {
  apply tr_arrow_formation_univ; apply tr_equal_elim; eapply tr_equal_eta2; eauto.
  }
apply tr_arrow_pi_equal_univ.
  {
  apply (tr_transitivity _ _ a); [apply tr_symmetry |]; apply tr_equal_elim; eapply tr_equal_eta2; eauto.
  }

  {
  apply (tr_transitivity _ _ b); [apply tr_symmetry |]; apply tr_equal_elim; eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma tarrowIntroOf_valid: tarrowIntroOf_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m triv0 triv1 triv2 H1 H2 H3.
  valid_rewrite. 
  constructor.
  eapply tr_eqtype_convert.
  apply tr_eqtype_symmetry.
  apply tr_arrow_pi_equal; eauto using deqtype_intro.
  eapply tr_pi_intro; eauto using deq_intro, deqtype_intro. Qed.

Lemma tarrowIntroEq_valid : tarrowIntroEq_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m n ext2 ext1 ext0 Ha Hb Hmn.
rewrite -> def_istp in Ha, Hb.
rewrite -> def_eq in Hmn |- *.
rewrite -> def_tarrow.
unfold Defs.triv.
apply tr_equal_intro.
apply (tr_eqtype_convert _#3 (pi a (subst sh1 b))).
  {
  apply tr_eqtype_symmetry.
  apply tr_arrow_pi_equal; eapply tr_eqtype_eta2; eauto.
  }
apply tr_pi_intro.
  {
  eapply tr_eqtype_eta2; eauto.
  }

  {
  apply tr_equal_elim; eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma tarrowIntro_valid : tarrowIntro_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b ext1 ext0 m Ha Hb Hm.
rewrite -> def_istp in Ha, Hb.
rewrite -> def_tarrow.
apply (tr_eqtype_convert _#3 (pi a (subst sh1 b))).
  {
  apply tr_eqtype_symmetry.
  apply tr_arrow_pi_equal; eapply tr_eqtype_eta2; eauto.
  }
apply tr_pi_intro; auto.
eapply tr_eqtype_eta2; eauto.
Qed.


Lemma tarrowElimOf_valid : tarrowElimOf_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m p ext1 ext0 Hm Hp.
rewrite -> def_of in Hm, Hp |- *.
rewrite -> def_tarrow in Hm.
unfold Defs.triv.
apply tr_equal_intro.
eapply tr_pi_elim'.
  {
  apply (tr_eqtype_convert _#3 (arrow a b)).
    {
    apply tr_arrow_pi_equal.
      {
      eapply tr_equal_formation_invert1.
      eapply tr_inhabitation_formation; eauto.
      }

      {
      replace (deqtype b b) with (substj (dot p id) (deqtype (subst sh1 b) (subst sh1 b))) by (simpsub; auto).
      eapply tr_generalize.
        {
        apply tr_equal_elim.
        eapply tr_equal_eta2; eauto.
        }
      apply (tr_arrow_formation_invert2 _ a a).
      eapply tr_equal_formation_invert1.
      eapply tr_inhabitation_formation; eauto.
      }
    }

    {
    apply tr_equal_elim.
    eapply tr_equal_eta2; eauto.
    }
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  simpsub; auto.
  }
Qed.


Lemma tarrowElimEq_valid : tarrowElimEq_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m n p q ext1 ext0 Hm Hp.
rewrite -> def_eq in Hm, Hp |- *.
rewrite -> def_tarrow in Hm.
unfold Defs.triv.
apply tr_equal_intro.
eapply tr_pi_elim'.
  {
  apply (tr_eqtype_convert _#3 (arrow a b)).
    {
    apply tr_arrow_pi_equal.
      {
      eapply tr_equal_formation_invert1.
      eapply tr_inhabitation_formation; eauto.
      }

      {
      replace (deqtype b b) with (substj (dot p id) (deqtype (subst sh1 b) (subst sh1 b))) by (simpsub; auto).
      eapply tr_generalize.
        {
        apply (tr_transitivity _ _ q); [| apply tr_symmetry]; apply tr_equal_elim; eapply tr_equal_eta2; eauto.
        }
      apply (tr_arrow_formation_invert2 _ a a).
      eapply tr_equal_formation_invert1.
      eapply tr_inhabitation_formation; eauto.
      }
    }

    {
    apply tr_equal_elim.
    eapply tr_equal_eta2; eauto.
    }
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  simpsub; auto.
  }
Qed.


Lemma tarrowElim_valid : tarrowElim_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m p Hm Hp.
rewrite -> def_tarrow in Hm.
eapply tr_pi_elim'.
  {
  apply (tr_eqtype_convert _#3 (arrow a b)).
    {
    apply tr_arrow_pi_equal.
      {
      eapply tr_inhabitation_formation; eauto.
      }

      {
      replace (deqtype b b) with (substj (dot p id) (deqtype (subst sh1 b) (subst sh1 b))) by (simpsub; auto).
      eapply tr_generalize; eauto.
      apply (tr_arrow_formation_invert2 _ a a).
      eapply tr_inhabitation_formation; eauto.
      }
    }

    {
    auto.
    }
  }

  {
  auto.
  }

  {
  simpsub; auto.
  }
Qed.


Lemma tarrowEta_valid : tarrowEta_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m ext0 Hm.
rewrite -> def_of in Hm.
rewrite -> def_eq.
rewrite -> def_tarrow in Hm |- *.
unfold Defs.triv.
apply tr_equal_intro.
apply tr_arrow_eta.
apply tr_equal_elim.
eapply tr_equal_eta2; eauto.
Qed.


Lemma tarrowExt_valid : tarrowExt_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m n ext3 ext2 ext1 ext0 Hb Hm Hn Heq.
rewrite -> def_istp in Hb.
rewrite -> def_of in Hm, Hn.
rewrite -> def_eq in Heq |- *.
rewrite -> def_tarrow in Hm, Hn |- *.
unfold Defs.triv.
apply tr_equal_intro.
eapply tr_transitivity.
  {
  apply tr_arrow_eta.
  apply tr_equal_elim; eapply tr_equal_eta2; eauto.
  }
eapply tr_transitivity.
2:{
  apply tr_symmetry.
  apply tr_arrow_eta.
  apply tr_equal_elim; eapply tr_equal_eta2; eauto.
  }
apply (tr_eqtype_convert _#3 (pi a (subst sh1 b))).
  {
  apply tr_eqtype_symmetry.
  apply tr_arrow_pi_equal.
    {
    apply (tr_arrow_formation_invert1 _ _ _ b b).
    eapply tr_equal_formation_invert1.
    eapply tr_inhabitation_formation; eauto.
    }

    {
    eapply tr_eqtype_eta2; eauto.
    }
  }
apply tr_pi_intro.
  {
  apply (tr_arrow_formation_invert1 _ _ _ b b).
  eapply tr_equal_formation_invert1.
  eapply tr_inhabitation_formation; eauto.
  }
  
  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma karrowKind_valid : karrowKind_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a i k triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  rewrite -> def_karrow.
  apply tr_karrow_kind_formation; eauto using deq_intro.
  Qed.

Lemma karrowKindEq_valid : karrowKindEq_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G i k k' l l' ext1 ext0 Hk Hl.
rewrite -> def_eq in Hk, Hl |- *.
rewrite -> def_kind in Hk, Hl |- *.
rewrite -> !def_karrow.
unfold Defs.triv.
apply tr_equal_intro.
apply tr_karrow_kind_formation; apply tr_equal_elim; eapply tr_equal_eta2; eauto.
Qed.


Lemma karrowForm_valid : karrowForm_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b triv0 triv1 H1 H2.
  valid_rewrite.
  rewrite -> !def_karrow.
  constructor; eauto using deqtype_intro.
  Qed.

Lemma karrowEq_valid : karrowEq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a a' b b' triv0 triv1 H1 H2.
  valid_rewrite.
  rewrite -> !def_karrow.
  constructor; eauto using deqtype_intro.
  Qed.

Lemma karrowFormUniv_valid : karrowFormUniv_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b i triv0 triv1 H1 H2.
  valid_rewrite. 
  rewrite -> !def_karrow.
  constructor.
  eapply tr_karrow_formation_univ; eauto using deq_intro.
  Qed.

Lemma karrowEqUniv_valid : karrowEqUniv_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a a' b b' i triv0 triv1 H1 H2.
  valid_rewrite. 
  rewrite -> !def_karrow.
  constructor.
  eapply tr_karrow_formation_univ; eauto using deq_intro.
Qed.


Lemma karrowArrowEq_valid : karrowArrowEq_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a a' b b' ext1 ext0 Ha Hb.
rewrite -> def_eqtp in Ha, Hb |- *.
rewrite -> def_karrow.
rewrite -> def_arrow.
unfold Defs.triv.
apply (tr_eqtype_transitivity _ _ (karrow a' b')).
  {
  apply tr_karrow_formation; eapply tr_eqtype_eta2; eauto.
  }
apply tr_karrow_pi_equal.
  {
  apply (tr_eqtype_transitivity _ _ a); [apply tr_eqtype_symmetry |]; eapply tr_eqtype_eta2; eauto.
  }

  {
  apply (tr_eqtype_transitivity _ _ b); [apply tr_eqtype_symmetry |]; eapply tr_eqtype_eta2; eauto.
  }
Qed.


Lemma karrowArrowEqUniv_valid : karrowArrowEqUniv_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a a' b b' i ext1 ext0 Ha Hb.
rewrite -> def_eq, -> def_univ in Ha, Hb |- *.
rewrite -> def_karrow.
rewrite -> def_arrow.
unfold Defs.triv.
apply tr_equal_intro.
apply (tr_transitivity _ _ (karrow a' b')).
  {
  apply tr_karrow_formation_univ; apply tr_equal_elim; eapply tr_equal_eta2; eauto.
  }
apply tr_karrow_pi_equal_univ.
  {
  apply (tr_transitivity _ _ a); [apply tr_symmetry |]; apply tr_equal_elim; eapply tr_equal_eta2; eauto.
  }

  {
  apply (tr_transitivity _ _ b); [apply tr_symmetry |]; apply tr_equal_elim; eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma karrowIntroOf_valid: karrowIntroOf_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m triv0 triv1 triv2 H1 H2 H3.
  valid_rewrite. 
  constructor.
  rewrite -> def_karrow.
  eapply tr_eqtype_convert.
  apply tr_eqtype_symmetry.
  apply tr_karrow_pi_equal; eauto using deqtype_intro.
  eapply tr_pi_intro; eauto using deq_intro, deqtype_intro. Qed.


Lemma karrowIntroEq_valid : karrowIntroEq_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m n ext2 ext1 ext0 Ha Hb Hmn.
rewrite -> def_istp in Ha, Hb.
rewrite -> def_eq in Hmn |- *.
rewrite -> def_karrow.
unfold Defs.triv.
apply tr_equal_intro.
apply (tr_eqtype_convert _#3 (pi a (subst sh1 b))).
  {
  apply tr_eqtype_symmetry.
  apply tr_karrow_pi_equal; eapply tr_eqtype_eta2; eauto.
  }
apply tr_pi_intro.
  {
  eapply tr_eqtype_eta2; eauto.
  }

  {
  apply tr_equal_elim; eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma karrowIntro_valid : karrowIntro_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b ext1 ext0 m Ha Hb Hm.
rewrite -> def_istp in Ha, Hb.
rewrite -> def_karrow.
apply (tr_eqtype_convert _#3 (pi a (subst sh1 b))).
  {
  apply tr_eqtype_symmetry.
  apply tr_karrow_pi_equal; eapply tr_eqtype_eta2; eauto.
  }
apply tr_pi_intro; auto.
eapply tr_eqtype_eta2; eauto.
Qed.


Lemma karrowElimOf_valid : karrowElimOf_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m p ext1 ext0 Hm Hp.
rewrite -> def_of in Hm, Hp |- *.
rewrite -> def_karrow in Hm.
unfold Defs.triv.
apply tr_equal_intro.
eapply tr_pi_elim'.
  {
  apply (tr_eqtype_convert _#3 (karrow a b)).
    {
    apply tr_karrow_pi_equal.
      {
      eapply tr_equal_formation_invert1.
      eapply tr_inhabitation_formation; eauto.
      }

      {
      replace (deqtype b b) with (substj (dot p id) (deqtype (subst sh1 b) (subst sh1 b))) by (simpsub; auto).
      eapply tr_generalize.
        {
        apply tr_equal_elim.
        eapply tr_equal_eta2; eauto.
        }
      apply (tr_karrow_formation_invert2 _ a a).
      eapply tr_equal_formation_invert1.
      eapply tr_inhabitation_formation; eauto.
      }
    }

    {
    apply tr_equal_elim.
    eapply tr_equal_eta2; eauto.
    }
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  simpsub; auto.
  }
Qed.


Lemma karrowElimEq_valid : karrowElimEq_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m n p q ext1 ext0 Hm Hp.
rewrite -> def_eq in Hm, Hp |- *.
rewrite -> def_karrow in Hm.
unfold Defs.triv.
apply tr_equal_intro.
eapply tr_pi_elim'.
  {
  apply (tr_eqtype_convert _#3 (karrow a b)).
    {
    apply tr_karrow_pi_equal.
      {
      eapply tr_equal_formation_invert1.
      eapply tr_inhabitation_formation; eauto.
      }

      {
      replace (deqtype b b) with (substj (dot p id) (deqtype (subst sh1 b) (subst sh1 b))) by (simpsub; auto).
      eapply tr_generalize.
        {
        apply (tr_transitivity _ _ q); [| apply tr_symmetry]; apply tr_equal_elim; eapply tr_equal_eta2; eauto.
        }
      apply (tr_karrow_formation_invert2 _ a a).
      eapply tr_equal_formation_invert1.
      eapply tr_inhabitation_formation; eauto.
      }
    }

    {
    apply tr_equal_elim.
    eapply tr_equal_eta2; eauto.
    }
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  simpsub; auto.
  }
Qed.


Lemma karrowElim_valid : karrowElim_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m p Hm Hp.
rewrite -> def_karrow in Hm.
eapply tr_pi_elim'.
  {
  apply (tr_eqtype_convert _#3 (karrow a b)).
    {
    apply tr_karrow_pi_equal.
      {
      eapply tr_inhabitation_formation; eauto.
      }

      {
      replace (deqtype b b) with (substj (dot p id) (deqtype (subst sh1 b) (subst sh1 b))) by (simpsub; auto).
      eapply tr_generalize; eauto.
      apply (tr_karrow_formation_invert2 _ a a).
      eapply tr_inhabitation_formation; eauto.
      }
    }

    {
    auto.
    }
  }

  {
  auto.
  }

  {
  simpsub; auto.
  }
Qed.


Lemma karrowEta_valid : karrowEta_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m ext0 Hm.
rewrite -> def_of in Hm.
rewrite -> def_eq.
rewrite -> def_karrow in Hm |- *.
unfold Defs.triv.
apply tr_equal_intro.
apply tr_karrow_eta.
apply tr_equal_elim.
eapply tr_equal_eta2; eauto.
Qed.


Lemma karrowExt_valid : karrowExt_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m n ext3 ext2 ext1 ext0 Hb Hm Hn Heq.
rewrite -> def_istp in Hb.
rewrite -> def_of in Hm, Hn.
rewrite -> def_eq in Heq |- *.
rewrite -> def_karrow in Hm, Hn |- *.
unfold Defs.triv.
apply tr_equal_intro.
eapply tr_transitivity.
  {
  apply tr_karrow_eta.
  apply tr_equal_elim; eapply tr_equal_eta2; eauto.
  }
eapply tr_transitivity.
2:{
  apply tr_symmetry.
  apply tr_karrow_eta.
  apply tr_equal_elim; eapply tr_equal_eta2; eauto.
  }
apply (tr_eqtype_convert _#3 (pi a (subst sh1 b))).
  {
  apply tr_eqtype_symmetry.
  apply tr_karrow_pi_equal.
    {
    apply (tr_karrow_formation_invert1 _ _ _ b b).
    eapply tr_equal_formation_invert1.
    eapply tr_inhabitation_formation; eauto.
    }

    {
    eapply tr_eqtype_eta2; eauto.
    }
  }
apply tr_pi_intro.
  {
  apply (tr_karrow_formation_invert1 _ _ _ b b).
  eapply tr_equal_formation_invert1.
  eapply tr_inhabitation_formation; eauto.
  }
  
  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma intersectForm_valid : intersectForm_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m n Ha Hb.
rewrite -> def_istp in * |- *.
unfold Defs.triv.
rewrite -> def_intersect.
apply tr_intersect_formation; eauto using deqtype_intro.
Qed.


Lemma intersectEq_valid: intersectEq_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a a' b b' m n Ha Hb.
rewrite -> !def_eqtp in * |- *.
unfold Defs.triv.
rewrite -> !def_intersect.
apply tr_intersect_formation; eauto using deqtype_intro.
Qed.


Lemma intersectFormUniv_valid : intersectFormUniv_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b i m n Ha Hb.
rewrite -> def_of in * |- *.
rewrite -> def_univ in * |- *.
unfold Defs.triv.
rewrite -> def_intersect.
apply tr_equal_intro.
apply tr_intersect_formation_univ; eauto using deq_intro.
Qed.


Lemma intersectEqUniv_valid : intersectEqUniv_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a a' b b' i m n Ha Hb.
rewrite -> def_eq in * |- *.
rewrite -> def_univ in * |- *.
unfold Defs.triv.
rewrite -> !def_intersect.
apply tr_equal_intro.
apply tr_intersect_formation_univ; eauto using deq_intro.
Qed.


Lemma intersectIntroOf_valid : intersectIntroOf_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m ext1 ext0 Hab Hm.
rewrite -> def_istp in Hab.
rewrite -> def_of in Hm |- *.
rewrite -> def_intersect.
unfold Defs.triv.
apply tr_equal_intro.
apply tr_intersect_intro.
  {
  eapply tr_eqtype_eta2; eauto.
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma intersectIntroEq_valid : intersectIntroEq_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m n ext1 ext0 Hab Hmn.
rewrite -> def_istp in Hab.
rewrite -> def_eq in Hmn |- *.
rewrite -> def_intersect.
unfold Defs.triv.
apply tr_equal_intro.
apply tr_intersect_intro.
  {
  eapply tr_eqtype_eta2; eauto.
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma intersectElimOf_valid : intersectElimOf_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m p ext1 ext0 Hm Hp.
rewrite -> def_of in Hp, Hm |- *.
rewrite -> def_intersect in Hm.
unfold Defs.triv.
simpsub.
apply tr_equal_intro.
eapply tr_intersect_elim.
  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }
Qed.


Lemma intersectElimEq_valid : intersectElimEq_obligation.
Proof.
unfoldtop.
unfold Defs.dof.
intros G a b m n p ext1 ext0 Hm Hp.
rewrite -> def_of in Hp.
rewrite -> def_eq in Hm |- *.
rewrite -> def_intersect in Hm.
unfold Defs.triv.
simpsub.
apply tr_equal_intro.
eapply tr_intersect_elim.
  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }

  {
  apply tr_equal_elim.
  eapply tr_equal_eta2; eauto.
  }
Qed.
