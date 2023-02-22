
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
Require Import ValidationNat.


Lemma voidForm_valid : voidForm_obligation. 
  unfoldtop. autounfold with valid_hint.
  intros G.
  valid_rewrite.
  eapply tr_formation_weaken.
  apply tr_voidtp_formation_univ.
Qed.

Lemma voidEq_valid : voidEq_obligation. 
 unfoldtop. autounfold with valid_hint.
  intros G.
  valid_rewrite.
  eapply tr_formation_weaken.
  apply tr_voidtp_formation_univ.
Qed.


Lemma voidFormUniv_valid : voidFormUniv_obligation.
Proof.
prepare.
unfold Defs.void.
intros G i ext0 H.
apply (tr_univ_cumulative _ Defined.nzero); auto.
  {
  apply tr_voidtp_formation_univ.
  }

  {
  rewrite -> leqpagetp_nzero_equiv.
  apply tr_unittp_intro.
  }
Qed.


Lemma voidEqUniv_valid : voidEqUniv_obligation.
Proof.
prepare.
intros G i ext0 H.
unfold Defs.void.
apply (tr_univ_cumulative _ Defined.nzero); auto.
  {
  apply tr_voidtp_formation_univ.
  }

  {
  rewrite -> leqpagetp_nzero_equiv.
  apply tr_unittp_intro.
  }
Qed.


Lemma voidElim_valid : voidElim_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a triv0 H.
  eapply tr_voidtp_elim; eauto.
Qed.


Lemma voidSub_valid : voidSub_obligation.
Proof.
prepare.
intros G A ext0 H.
unfold Defs.void.
apply tr_subtype_intro; auto.
  {
  apply tr_voidtp_istype.
  }
apply (tr_voidtp_elim _ (var 0) (var 0)).
eapply hypothesis; eauto using index_0.
Qed.


Lemma abortType_valid : abortType_obligation.
Proof.
prepare.
intro G.
rewrite -> def_intersect.
rewrite -> def_intersect.
rewrite -> def_univ.
rewrite -> def_arrow.
unfold Defs.void.
unfold Defs.abort.
apply tr_intersect_intro.
  {
  apply tr_nattp_formation.
  }
apply tr_intersect_intro.
  {
  apply tr_univ_formation.
  unfold Defined.pagetp.
  eapply hypothesis; eauto using index_0.
  }
simpsub.
apply tr_pi_intro.
  {
  apply tr_voidtp_istype.
  }
apply (tr_voidtp_elim _ (var 0) (var 0)).
eapply hypothesis; eauto using index_0.
Qed.


Lemma unitKind_valid : unitKind_obligation. 
  unfoldtop. autounfold with valid_hint. 
  intros G i triv0 H.
  valid_rewrite.
  constructor.
  apply tr_unittp_kind_formation.
  eauto using deq_intro.
Qed.


Lemma unitKindEq_valid : unitKindEq_obligation. 
 unfoldtop. autounfold with valid_hint.
  intros G i triv0 H.
  valid_rewrite.
  constructor.
  apply tr_unittp_kind_formation.
  eauto using deq_intro.
Qed.


Lemma unitForm_valid : unitForm_obligation. 
 unfoldtop. autounfold with valid_hint.
  intros G.
  valid_rewrite.
  eapply tr_formation_weaken; apply tr_unittp_formation_univ.
Qed.

  Lemma unitEq_valid : unitEq_obligation.
 unfoldtop. autounfold with valid_hint.
  intros G.
  valid_rewrite.
  eapply tr_formation_weaken; apply tr_unittp_formation_univ.
  Qed.


Lemma unitFormUniv_valid : unitFormUniv_obligation.
Proof.
prepare.
unfold Defs.unit.
intros G i ext0 H.
apply (tr_univ_cumulative _ Defined.nzero); auto.
  {
  apply tr_unittp_formation_univ.
  }

  {
  rewrite -> leqpagetp_nzero_equiv.
  apply tr_unittp_intro.
  }
Qed.


Lemma unitEqUniv_valid : unitEqUniv_obligation.
Proof.
prepare.
intros G i ext0 H.
unfold Defs.unit.
apply (tr_univ_cumulative _ Defined.nzero); auto.
  {
  apply tr_unittp_formation_univ.
  }

  {
  rewrite -> leqpagetp_nzero_equiv.
  apply tr_unittp_intro.
  }
Qed.


Lemma unitIntroOf_valid : unitIntroOf_obligation. 
 unfoldtop. autounfold with valid_hint.
  intros G.
  valid_rewrite.
  constructor. apply tr_unittp_intro.
Qed.

Lemma unitIntro_valid : unitIntro_obligation. 
 unfoldtop. autounfold with valid_hint.
  intros G.
  valid_rewrite.
  constructor. 
Qed.


Lemma unitExt_valid : unitExt_obligation.
Proof.
prepare.
unfold Defs.unit.
intros G m n ext1 ext0 Hm Hn.
apply (tr_transitivity _ _ triv).
  {
  apply tr_unittp_eta; auto.
  }

  {
  apply tr_symmetry.
  apply tr_unittp_eta; auto.
  }
Qed.


Lemma unitLeft_valid : unitLeft_obligation. 
  unfoldtop. autounfold with valid_hint.
  intros G1 G2 B M.
  apply tr_unittp_eta_hyp.
Qed.


Lemma boolForm_valid : boolForm_obligation. 
  unfoldtop. autounfold with valid_hint.
  intros G.
  valid_rewrite.
  eapply tr_formation_weaken; apply tr_booltp_formation_univ.
Qed.

Lemma boolEq_valid : boolEq_obligation. 
  unfoldtop. autounfold with valid_hint.
  intros G.
  valid_rewrite.
  eapply tr_formation_weaken; apply tr_booltp_formation_univ.
Qed.


Lemma boolFormUniv_valid : boolFormUniv_obligation.
Proof.
prepare.
unfold Defs.bool.
intros G i ext0 H.
apply (tr_univ_cumulative _ Defined.nzero); auto.
  {
  apply tr_booltp_formation_univ.
  }

  {
  rewrite -> leqpagetp_nzero_equiv.
  apply tr_unittp_intro.
  }
Qed.


Lemma boolEqUniv_valid : boolEqUniv_obligation.
Proof.
prepare.
intros G i ext0 H.
unfold Defs.bool.
apply (tr_univ_cumulative _ Defined.nzero); auto.
  {
  apply tr_booltp_formation_univ.
  }

  {
  rewrite -> leqpagetp_nzero_equiv.
  apply tr_unittp_intro.
  }
Qed.


Lemma boolIntro1Of_valid : boolIntro1Of_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G.
  valid_rewrite.
  do 2 constructor.
  Qed.

 Lemma boolIntro2Of_valid : boolIntro2Of_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G.
  valid_rewrite.
  do 2 constructor.
 Qed.


Hint Rewrite def_ite : prepare.


Lemma boolElimOf_valid : boolElimOf_obligation.
Proof.
prepare.
unfold Defs.true.
unfold Defs.false.
intros G a m p r ext2 ext1 ext0 Hm Hp Hr.
apply tr_booltp_elim; auto.
Qed.


Lemma boolElimEq_valid : boolElimEq_obligation.
Proof.
prepare.
unfold Defs.true.
unfold Defs.false.
intros G a m n p q r s ext2 ext1 ext0 Hmn Hpq Hrs.
apply tr_booltp_elim; auto.
Qed.


Lemma boolElim_valid : boolElim_obligation.
Proof.
prepare.
unfold Defs.true.
unfold Defs.false.
intros G a m ext0 p r Hm Hp Hr.
apply tr_booltp_elim; auto.
Qed.


 Lemma boolElimIstype_valid : boolElimIstype_obligation.
   unfoldtop. autounfold with valid_hint.
   intros G a c m triv0 triv1 triv2 H0 H1 H2.
 valid_rewrite.
 constructor; eauto using deq_intro; eauto using deqtype_intro.
 Qed.

 Lemma boolElimEqtype_valid : boolElimEqtype_obligation.
   unfoldtop. autounfold with valid_hint.
   intros G a c m triv0 triv1 triv2 H0 H1 H2.
 valid_rewrite.
 constructor; eauto using deq_intro; eauto using deqtype_intro.
 Qed.

Lemma boolLeft_valid : boolLeft_obligation. 
 unfoldtop. autounfold with valid_hint.
   intros G1 G2 a m n H0 H1.
 valid_rewrite.
 constructor; eauto using deq_intro; eauto using deqtype_intro.
 Qed.
