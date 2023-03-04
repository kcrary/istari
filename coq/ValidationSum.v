
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Tactics.
Require Import Sequence.
Require Import Relation.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.
Require Import Dynamic.
Require Import Promote.
Require Import Hygiene.
Require Import Rules.
Require Defs.
Require Import Obligations.
Require Import Morphism.
Require Import DefsEquiv.
Require Import Equivalence.
Require Import Equivalences.
Require Import Dots.

Require Import DerivedRules.
Require Import ValidationUtil.
Require Import Defined.

Require Import SumLemmas.
Require Import ValidationSigma.


Hint Rewrite def_inl def_inr def_sum def_sumcase : prepare.


Lemma sum_body_formation :
  forall G a b c d,
    tr G (deqtype a c)
    -> tr G (deqtype b d)
    -> tr (hyp_tm booltp :: G) (deqtype (bite (var 0) (subst sh1 a) (subst sh1 b)) (bite (var 0) (subst sh1 c) (subst sh1 d))).
Proof.
intros G a b c d Hac Hbd.
apply tr_booltp_elim_eqtype.
  {
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
  auto.
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
  auto.
  }
Qed.


Lemma sumForm_valid : sumForm_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_sigma_formation.
  {
  apply tr_booltp_istype.
  }
apply sum_body_formation; auto.
Qed.


Lemma sumEq_valid : sumEq_obligation.
Proof.
prepare.
intros G a b c d ext1 ext0 Ha Hb.
apply tr_sigma_formation.
  {
  apply tr_booltp_istype.
  }
apply sum_body_formation; auto.
Qed.


Lemma sumFormUniv_valid : sumFormUniv_obligation.
Proof.
prepare.
intros G a b i ext1 ext0 Ha Hb.
apply tr_sigma_formation_univ.
  {
  apply (tr_univ_cumulative _ Defined.nzero); auto.
    {
    apply tr_booltp_formation_univ.
    }

    {
    apply tr_univ_formation_invert.
    eapply tr_inhabitation_formation; eauto.
    }

    {
    rewrite -> leqpagetp_nzero_equiv.
    apply tr_unittp_intro.
    }
  }
replace (univ (subst sh1 i)) with (subst1 (var 0) (univ (subst (sh 2) i))) by (simpsub; auto).
apply tr_booltp_elim.
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  simpsub.
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
  exact Ha.
  }

  {
  simpsub.
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
  exact Hb.
  }
Qed.


Lemma sumEqUniv_valid : sumEqUniv_obligation.
Proof.
prepare.
intros G a b c d i ext1 ext0 Ha Hb.
apply tr_sigma_formation_univ.
  {
  apply (tr_univ_cumulative _ Defined.nzero); auto.
    {
    apply tr_booltp_formation_univ.
    }

    {
    apply tr_univ_formation_invert.
    eapply tr_inhabitation_formation; eauto.
    }

    {
    rewrite -> leqpagetp_nzero_equiv.
    apply tr_unittp_intro.
    }
  }
replace (univ (subst sh1 i)) with (subst1 (var 0) (univ (subst (sh 2) i))) by (simpsub; auto).
apply tr_booltp_elim.
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  simpsub.
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
  exact Ha.
  }

  {
  simpsub.
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
  exact Hb.
  }
Qed.


Lemma sumSub_valid : sumSub_obligation.
Proof.
prepare.
intros G a b c d ext1 ext0 Hab Hcd.
apply tr_sigma_sub.
  {
  apply tr_subtype_intro; auto using tr_booltp_istype.
  eapply hypothesis; eauto using index_0.
  }

  {
  apply (tr_subtype_eta2 _ _ _ (bite (var 0) (subst (under 0 sh1) triv) (subst (under 0 sh1) triv)) (bite (var 0) (subst (under 0 sh1) triv) (subst (under 0 sh1) triv))).
  apply (tr_booltp_eta_hyp _ []).
    {
    simpsub.
    cbn [List.app].
    rewrite -> !equiv_bite_l.
    auto.
    }

    {
    simpsub.
    cbn [List.app].
    rewrite -> !equiv_bite_r.
    auto.
    }
  }

  {
  apply sum_body_formation.
    {
    eapply tr_subtype_formation_invert2.
    eapply tr_inhabitation_formation; eauto.
    }

    {
    eapply tr_subtype_formation_invert2.
    eapply tr_inhabitation_formation; eauto.
    }
  }
Qed.


Lemma sumIntro1Of_valid : sumIntro1Of_obligation.
Proof.
prepare.
intros G a b m ext1 ext0 Hb Hm.
apply tr_sigma_intro.
  {
  apply tr_booltp_intro_btrue.
  }

  {
  simpsub.
  rewrite -> equiv_bite_l.
  auto.
  }

  {
  apply sum_body_formation; auto.
  eapply tr_inhabitation_formation; eauto.
  }
Qed.


Lemma sumIntro1Eq_valid : sumIntro1Eq_obligation.
Proof.
prepare.
intros G a b m n ext1 ext0 Hb Hm.
apply tr_sigma_intro.
  {
  apply tr_booltp_intro_btrue.
  }

  {
  simpsub.
  rewrite -> equiv_bite_l.
  auto.
  }

  {
  apply sum_body_formation; auto.
  eapply tr_inhabitation_formation; eauto.
  }
Qed.


Lemma sumIntro1_valid : sumIntro1_obligation.
Proof.
prepare.
intros G a b ext0 m Hb Hm.
apply tr_sigma_intro.
  {
  apply tr_booltp_intro_btrue.
  }

  {
  simpsub.
  rewrite -> equiv_bite_l.
  auto.
  }

  {
  apply sum_body_formation; auto.
  eapply tr_inhabitation_formation; eauto.
  }
Qed.


Lemma sumIntro2Of_valid : sumIntro2Of_obligation.
Proof.
prepare.
intros G a b m ext1 ext0 Hb Hm.
apply tr_sigma_intro.
  {
  apply tr_booltp_intro_bfalse.
  }

  {
  simpsub.
  rewrite -> equiv_bite_r.
  auto.
  }

  {
  apply sum_body_formation; auto.
  eapply tr_inhabitation_formation; eauto.
  }
Qed.


Lemma sumIntro2Eq_valid : sumIntro2Eq_obligation.
Proof.
prepare.
intros G a b m n ext1 ext0 Hb Hm.
apply tr_sigma_intro.
  {
  apply tr_booltp_intro_bfalse.
  }

  {
  simpsub.
  rewrite -> equiv_bite_r.
  auto.
  }

  {
  apply sum_body_formation; auto.
  eapply tr_inhabitation_formation; eauto.
  }
Qed.


Lemma sumIntro2_valid : sumIntro2_obligation.
Proof.
prepare.
intros G a b ext0 m Hb Hm.
apply tr_sigma_intro.
  {
  apply tr_booltp_intro_bfalse.
  }

  {
  simpsub.
  rewrite -> equiv_bite_r.
  auto.
  }

  {
  apply sum_body_formation; auto.
  eapply tr_inhabitation_formation; eauto.
  }
Qed.


Lemma sumElimOf_valid : sumElimOf_obligation.
Proof.
prepare.
intros G a b c m p r ext2 ext1 ext0 Hm Hp Hr.
eapply tr_sumtype_elim; eauto.
Qed.


Lemma sumElimOfNondep_valid : sumElimOfNondep_obligation.
Proof.
prepare.
intros G a b c m p r ext2 ext1 ext0 Hm Hp Hr.
replace c with (subst1 m (subst sh1 c)) by (simpsub; auto).
eapply tr_sumtype_elim; eauto; simpsub; auto.
Qed.


Lemma sumElimEq_valid : sumElimEq_obligation.
Proof.
prepare.
intros G a b c m n p q r s ext2 ext1 ext0 Hab Hpq Hrs.
eapply tr_sumtype_elim; eauto.
Qed.


Lemma sumElim_valid : sumElim_obligation.
Proof.
prepare.
intros G a b c m ext0 p r Hm Hp Hr.
eapply tr_sumtype_elim; eauto.
Qed.


Lemma sumElimNondep_valid : sumElimNondep_obligation.
Proof.
prepare.
intros G a b c m p r Hm Hp Hr.
replace c with (subst1 m (subst sh1 c)) by (simpsub; auto).
eapply tr_sumtype_elim; eauto; simpsub; auto.
Qed.


Lemma sumElimIstype_valid : sumElimIstype_obligation.
Proof.
prepare.
intros G a b c e m ext2 ext1 ext0 Hab Hc He.
eapply tr_sumtype_elim_eqtype; eauto.
Qed.


Lemma sumElimEqtype_valid : sumElimEqtype_obligation.
Proof.
prepare.
intros G a b c d e f m n ext2 ext1 ext0 Hmn Hcd Hef.
eapply tr_sumtype_elim_eqtype; eauto.
Qed.


Lemma sumFormInv1_valid : sumFormInv1_obligation.
Proof.
prepare.
intros G a b ext0 Hsig.
unfold sumtype in Hsig.
so (tr_sigma_formation_invert2 _#5 Hsig) as Hab.
so (tr_generalize _#4 (tr_booltp_intro_btrue _) Hab) as Ha.
simpsubin Ha.
rewrite -> (steps_equiv _#3 (star_one _#4 (step_bite2 _#3))) in Ha.
auto.
Qed.


Lemma sumFormInv2_valid : sumFormInv2_obligation.
Proof.
prepare.
intros G a b ext0 Hsig.
unfold sumtype in Hsig.
so (tr_sigma_formation_invert2 _#5 Hsig) as Hab.
so (tr_generalize _#4 (tr_booltp_intro_bfalse _) Hab) as Hb.
simpsubin Hb.
rewrite -> (steps_equiv _#3 (star_one _#4 (step_bite3 _#3))) in Hb.
auto.
Qed.


Hint Rewrite def_intersect def_pi def_arrow : prepare.


Require Import NatLemmas.


Lemma sumcaseType_valid : sumcaseType_obligation.
Proof.
prepare.
intros G.
unfold Defs.sumcase.
apply tr_intersect_intro; auto using tr_nattp_formation.
simpsub.
apply tr_intersect_intro.
  {
  apply tr_univ_formation.
  unfold pagetp.
  eapply hypothesis; eauto using index_0.
  }
simpsub.
apply tr_intersect_intro.
  {
  apply tr_univ_formation.
  unfold pagetp.
  eapply hypothesis; eauto using index_0, index_S.
  }
simpsub.
apply tr_intersect_intro.
  {
  apply tr_univ_formation.
  unfold pagetp.
  eapply hypothesis; eauto using index_0, index_S.
  }
simpsub.
cbn [Nat.add].
simpsub.
apply tr_pi_intro.
  {
  apply tr_sumtype_formation.
    {
    eapply tr_formation_weaken.
    eapply hypothesis; eauto using index_0, index_S.
    simpsub.
    cbn [Nat.add].
    eauto.
    }

    {
    eapply tr_formation_weaken.
    eapply hypothesis; eauto using index_0, index_S.
    simpsub.
    cbn [Nat.add].
    eauto.
    }
  }
eapply tr_pi_intro.
  {
  eapply tr_pi_formation.
    {
    eapply tr_formation_weaken.
    eapply hypothesis; eauto using index_0, index_S.
    simpsub.
    cbn [Nat.add].
    eauto.
    }
  eapply tr_formation_weaken.
  eapply hypothesis; eauto using index_0, index_S.
  simpsub.
  cbn [Nat.add].
  eauto.
  }
eapply tr_pi_intro.
  {
  eapply tr_pi_formation.
    {
    eapply tr_formation_weaken.
    eapply hypothesis; eauto using index_0, index_S.
    simpsub.
    cbn [Nat.add].
    eauto.
    }
  eapply tr_formation_weaken.
  eapply hypothesis; eauto using index_0, index_S.
  simpsub.
  cbn [Nat.add].
  eauto.
  }
match goal with
| |- tr ?X _ =>
   change (tr X (deq (sumcase (var 2) (app (var 2) (var 0)) (app (var 1) (var 0))) (sumcase (var 2) (app (var 2) (var 0)) (app (var 1) (var 0))) (subst1 (var 2) (var 4))))
end.
eapply tr_sumtype_elim.
  {
  eapply hypothesis; eauto using index_0, index_S.
  simpsub.
  cbn [Nat.add].
  eauto.
  }

  {
  eapply tr_pi_elim'.
    {
    eapply hypothesis; eauto using index_0, index_S.
    simpsub.
    cbn [Nat.add].
    eauto.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
    
    {
    simpsub.
    auto.
    }
  }

  {
  eapply tr_pi_elim'.
    {
    eapply hypothesis; eauto using index_0, index_S.
    simpsub.
    cbn [Nat.add].
    eauto.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
    
    {
    simpsub.
    auto.
    }
  }
Qed.
