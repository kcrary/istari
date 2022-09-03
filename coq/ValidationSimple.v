
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


Lemma voidForm_valid : voidForm_obligation. 
  unfoldtop. autounfold with valid_hint.
  intros G.
  valid_rewrite.
  eapply tr_formation_weaken.
  apply tr_voidtp_formation.
Qed.

Lemma voidEq_valid : voidEq_obligation. 
 unfoldtop. autounfold with valid_hint.
  intros G.
  valid_rewrite.
  eapply tr_formation_weaken.
  apply tr_voidtp_formation.
Qed.

(*should this be void : Ui for any i, or should it be void : U0
 both are provable but the first one is harder (induction over nats i think)*)
Lemma voidFormUniv_valid : voidFormUniv_obligation. 
 unfoldtop. autounfold with valid_hint.
  intros G i triv0 H.
  valid_rewrite.
  (*apply tr_voidtp_formation. *)
Abort.

Lemma voidEqUniv_valid : voidEqUniv_obligation. 
 unfoldtop. autounfold with valid_hint.
  intros G i triv0 H.
  valid_rewrite.
Abort.

Lemma voidElim_valid : voidElim_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a triv0 H.
  eapply tr_voidtp_elim; eauto.
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
  eapply tr_formation_weaken; apply tr_unittp_formation.
Qed.

  Lemma unitEq_valid : unitEq_obligation.
 unfoldtop. autounfold with valid_hint.
  intros G.
  valid_rewrite.
  eapply tr_formation_weaken; apply tr_unittp_formation.
  Qed.

(*same problem as void*)
Lemma unitFormUniv_valid : unitFormUniv_obligation. 
 unfoldtop. autounfold with valid_hint.
  intros G i triv0 H.
  valid_rewrite.
Abort.

Lemma unitEqUniv_valid : unitEqUniv_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G i triv0 H.
  valid_rewrite.
Abort.

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


(* obsolete
Lemma unitEta_valid : unitEta_obligation. 
  unfoldtop. autounfold with valid_hint.
  intros G M triv0 H.
  valid_rewrite.
  constructor.
  apply tr_unittp_eta; eauto using deq_intro.
Qed.
*)


Lemma unitLeft_valid : unitLeft_obligation. 
  unfoldtop. autounfold with valid_hint.
  intros G1 G2 B M.
  apply tr_unittp_eta_hyp.
Qed.


Lemma boolForm_valid : boolForm_obligation. 
  unfoldtop. autounfold with valid_hint.
  intros G.
  valid_rewrite.
  eapply tr_formation_weaken; apply tr_booltp_formation.
Qed.

Lemma boolEq_valid : boolEq_obligation. 
  unfoldtop. autounfold with valid_hint.
  intros G.
  valid_rewrite.
  eapply tr_formation_weaken; apply tr_booltp_formation.
Qed.

(*same problem as void*)
Lemma boolFormUniv_valid : boolFormUniv_obligation. 
 unfoldtop. autounfold with valid_hint.
  intros G i triv0 H.
  valid_rewrite.
  constructor.
  Abort.

Lemma boolEqUniv_valid : boolEqUniv_obligation. 
  unfoldtop. autounfold with valid_hint.
  Abort.

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

Lemma boolElimOf_valid : boolElimOf_obligation. 
Abort.

Lemma boolElimEq_valid : boolElimEq_obligation. 
  unfoldtop. autounfold with valid_hint.
  intros G a b m n p q r s triv0 triv1 triv2 H0 H1 H2.
  valid_rewrite.
  constructor.
  apply tr_booltp_elim; eauto using deq_intro.
Abort.


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
