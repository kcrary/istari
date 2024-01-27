
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


Lemma recKind_valid : recKind_obligation.
 unfoldtop. autounfold with valid_hint.
  intros G i k triv0 triv1 H0 H1.
  valid_rewrite. 
  constructor.
  assert (equivctx (hyp_tml (app Defs.kind i) :: G)
                    (hyp_tml (kind i) :: G)) as Hctx.
  {constructor. apply def_kindh_l. apply equivctx_refl. } 
  rewrite -> def_kind in * |- *.
  apply tr_rec_kind_formation; eauto using deq_intro.
  Qed.

Lemma recKindEq_valid : recKindEq_obligation.
 unfoldtop. autounfold with valid_hint.
  intros G i k l triv0 triv1 H0 H1.
  valid_rewrite. 
  constructor.
  assert (equivctx (hyp_tml (app Defs.kind i) :: G)
                    (hyp_tml (kind i) :: G)) as Hctx.
  {constructor. apply def_kindh_l. apply equivctx_refl. } 
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


Hint Rewrite def_rec : prepare.


Lemma recUnrollUniv_valid : recUnrollUniv_obligation.
Proof.
prepare.
intros G a i ext1 ext0 Hi Ha.
apply tr_rec_unroll_univ; auto.
Qed.
