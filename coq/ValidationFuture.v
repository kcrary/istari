
Require Import Coq.Lists.List.
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

Lemma recKind_valid : recKind_obligation.
 unfoldtop. autounfold with valid_hint.
  intros G i k triv0 triv1 H0 H1.
  valid_rewrite. 
  constructor.
  assert (equivctx (hyp_tml (app Defs.kind i) :: G)
                    (hyp_tml (kuniv i) :: G)) as Hctx.
  {constructor. apply def_kindh_l. apply equivctx_refl. } 
    rewrite -> Hctx in * |- *.
  rewrite -> def_kind in * |- *.
  apply tr_rec_kind_formation; eauto using deq_intro.
  Qed.

Lemma recKindEq_valid : recKindEq_obligation.
 unfoldtop. autounfold with valid_hint.
  intros G i k l triv0 triv1 H0 H1.
  valid_rewrite. 
  constructor.
  assert (equivctx (hyp_tml (app Defs.kind i) :: G)
                    (hyp_tml (kuniv i) :: G)) as Hctx.
  {constructor. apply def_kindh_l. apply equivctx_refl. } 
    rewrite -> Hctx in * |- *.
  rewrite -> def_kind in * |- *.
  apply tr_rec_kind_formation; eauto using deq_intro.
Qed.

Lemma recForm_valid : recForm_obligation. 
 unfoldtop. autounfold with valid_hint.
  intros G a triv0 H.
  valid_rewrite. 
  constructor.
  eauto using deqtype_intro.
Qed.

 Lemma recEq_valid : recEq_obligation.
 unfoldtop. autounfold with valid_hint.
  intros G a b triv0 H.
  valid_rewrite. 
  constructor.
  eauto using deqtype_intro.
 Qed.

Lemma recFormUniv_valid : recFormUniv_obligation. 
 unfoldtop. autounfold with valid_hint.
  intros G a i triv0 triv1 H0 H1.
  valid_rewrite. 
  assert (equivctx (hyp_tml (app Defs.univ i) :: G)
                    (hyp_tml (univ i) :: G)) as Hctx.
  {constructor. apply def_univh_l. apply equivctx_refl. } 
    rewrite -> Hctx in * |- *.
  rewrite -> def_univ in * |- *.
  constructor.
  apply tr_rec_formation_univ; eauto using deq_intro.
  Qed.

  Lemma recEqUniv_valid : recEqUniv_obligation.
 unfoldtop. autounfold with valid_hint.
  intros G a b i triv0 triv1 H0 H1.
  valid_rewrite. 
  assert (equivctx (hyp_tml (app Defs.univ i) :: G)
                    (hyp_tml (univ i) :: G)) as Hctx.
  {constructor. apply def_univh_l. apply equivctx_refl. } 
    rewrite -> Hctx in * |- *.
  rewrite -> def_univ in * |- *.
  constructor.
  apply tr_rec_formation_univ; eauto using deq_intro.
Qed.


Lemma recUnroll_valid : recUnroll_obligation. 
 unfoldtop. autounfold with valid_hint.
 intros G a triv0 H.
 valid_rewrite.
 apply tr_rec_unroll.
 eauto using deqtype_intro.
Qed.

Lemma recBisimilar_valid : recBisimilar_obligation.
 unfoldtop. autounfold with valid_hint.
 intros G a b triv0 triv1 H0.
 valid_rewrite. 
 constructor; eauto using deqtype_intro.
Qed.
