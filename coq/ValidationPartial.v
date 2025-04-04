
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
Require Import SumLemmas.
Require Import NatLemmas.

Hint Rewrite def_partial def_halts def_admiss def_uptype def_seq : prepare.


Lemma tr_admiss_eta2 :
  forall G p q m,
    tr G (deq p q (admiss m))
    -> tr G (deq triv triv (admiss m)).
Proof.
intros G p q m Htr.
assert (tr G (deq p triv (admiss m))) as Htr'.
  {
  apply tr_admiss_eta.
  apply (tr_transitivity _ _ q); auto.
  apply tr_symmetry; auto.
  }
apply (tr_transitivity _ _ p); auto.
apply tr_symmetry; auto.
Qed.


Lemma tr_uptype_eta2 :
  forall G p q m,
    tr G (deq p q (uptype m))
    -> tr G (deq triv triv (uptype m)).
Proof.
intros G p q m Htr.
assert (tr G (deq p triv (uptype m))) as Htr'.
  {
  apply tr_uptype_eta.
  apply (tr_transitivity _ _ q); auto.
  apply tr_symmetry; auto.
  }
apply (tr_transitivity _ _ p); auto.
apply tr_symmetry; auto.
Qed.


Lemma partialForm_valid : partialForm_obligation.
Proof.
prepare.
intros G a ext0 Ha.
apply tr_partial_formation; auto.
Qed.


Lemma partialEq_valid : partialEq_obligation.
Proof.
prepare.
intros G a b ext0 Hab.
apply tr_partial_formation; auto.
Qed.


Lemma partialFormUniv_valid : partialFormUniv_obligation.
Proof.
prepare.
intros G a i ext0 Ha.
apply tr_partial_formation_univ; auto.
Qed.


Lemma partialEqUniv_valid : partialEqUniv_obligation.
Proof.
prepare.
intros G a b i ext0 Hab.
apply tr_partial_formation_univ; auto.
Qed.


Lemma partialSub_valid : partialSub_obligation.
Proof.
prepare.
intros G a b ext0 Hab.
apply tr_partial_covariant; auto.
Qed.


Lemma partialStrict_valid : partialStrict_obligation.
Proof.
prepare.
intros G a ext0 Ha.
apply tr_partial_strict; auto.
Qed.


Add Parametric Morphism object : (@partial object)
  with signature equiv ==> equiv
  as equiv_partial.
Proof.
intros m1 m1' H1.
apply equiv_partial; auto.
Qed.


Lemma partialStrictConverse_valid : partialStrictConverse_obligation.
Proof.
prepare.
intros G a ext0 Ha.
apply tr_partial_strict_converse; auto.
Qed.


Lemma partialIdem_valid : partialIdem_obligation.
Proof.
prepare.
intros G a ext0 Ha.
rewrite -> def_eeqtp.
apply tr_prod_intro.
  {
  apply tr_partial_strict_converse; auto.
  }

  {
  apply tr_partial_strict; auto.
  }
Qed.


Lemma haltsForm_valid : haltsForm_obligation.
Proof.
prepare.
intros G a m ext0 Hm.
eapply tr_halts_formation; eauto.
Qed.


Lemma haltsEq_valid : haltsEq_obligation.
Proof.
prepare.
intros G a m n ext0 Hmn.
eapply tr_halts_formation; eauto.
Qed.


Lemma haltsFormUniv_valid : haltsFormUniv_obligation.
Proof.
prepare.
intros G a i m ext1 ext0 Hi Hm.
apply (tr_univ_cumulative _ nzero).
  {
  eapply tr_halts_formation_univ; eauto.
  }

  {
  exact Hi.
  }

  {
  rewrite -> leqpagetp_nzero_equiv.
  apply tr_unittp_intro.
  }
Qed.


Lemma haltsEqUniv_valid : haltsEqUniv_obligation.
Proof.
prepare.
intros G a i m n ext1 ext0 Hi Hmn.
apply (tr_univ_cumulative _ nzero).
  {
  eapply tr_halts_formation_univ; eauto.
  }

  {
  exact Hi.
  }

  {
  rewrite -> leqpagetp_nzero_equiv.
  apply tr_unittp_intro.
  }
Qed.


Lemma partialIntroBottomOf_valid : partialIntroBottomOf_obligation.
Proof.
prepare.
intros G a ext0 Ha.
unfold Defs.bottom.
apply (tr_subtype_elim _ (partial voidtp)).
  {
  apply tr_partial_covariant.
  apply tr_subtype_intro; auto.
    {
    apply (tr_formation_weaken _ nzero).
    apply tr_voidtp_formation_univ.
    }

    {
    apply (tr_voidtp_elim _ (var 0) (var 0)).
    eapply hypothesis; eauto using index_0.
    }
  }
  
  {
  apply tr_bottom_partial_void.
  }
Qed.


Lemma bottomDiverges_valid : bottomDiverges_obligation.
Proof.
prepare.
intros G ext0 H.
apply (tr_voidtp_elim _ Defs.bottom Defs.bottom).
apply tr_partial_elim.
  {
  unfold Defs.bottom.
  apply tr_bottom_partial_void.
  }

  {
  eapply tr_halts_eta2; eauto.
  }
Qed.


Lemma partialExt_valid : partialExt_obligation.
Proof.
prepare.
intros G a m n ext0 p ext2 Ha Hiff Hmn.
rewrite -> def_iff in Hiff.
apply tr_partial_ext; auto.
  {
  eapply tr_pi_formation_invert1.
  apply (tr_inhabitation_formation _ (ppi1 p) (ppi1 p)).
  eapply tr_prod_elim1; eauto.
  }

  {
  eapply tr_pi_formation_invert1.
  apply (tr_inhabitation_formation _ (ppi2 p) (ppi2 p)).
  eapply tr_prod_elim2; eauto.
  }

  {
  apply (tr_halts_eta2 _ (app (ppi1 (subst sh1 p)) (var 0)) (app (ppi1 (subst sh1 p)) (var 0))).
  eapply (tr_pi_elim' _ (subst sh1 (halts m)) (subst (sh 2) (halts n))).
    {
    eapply (tr_prod_elim1 _ _ (subst sh1 (pi (halts n) (subst sh1 (halts m))))).
    eapply (weakening _ [_] []).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      cbn [Nat.add].
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    exact Hiff.
    }

    {
    eapply hypothesis; eauto using index_0.
    }

    {
    simpsub.
    reflexivity.
    }
  }

  {
  apply (tr_halts_eta2 _ (app (ppi2 (subst sh1 p)) (var 0)) (app (ppi2 (subst sh1 p)) (var 0))).
  eapply (tr_pi_elim' _ (subst sh1 (halts n)) (subst (sh 2) (halts m))).
    {
    eapply (tr_prod_elim2 _ (subst sh1 (pi (halts m) (subst sh1 (halts n))))).
    eapply (weakening _ [_] []).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      cbn [Nat.add].
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    exact Hiff.
    }

    {
    eapply hypothesis; eauto using index_0.
    }

    {
    simpsub.
    reflexivity.
    }
  }
Qed.


Lemma partialElimEq_valid : partialElimEq_obligation.
Proof.
prepare.
intros G a m n ext1 ext0 Hmn Hhalt.
apply tr_partial_elim; eauto using tr_halts_eta2.
Qed.


Lemma partialElimOf_valid : partialElimOf_obligation.
Proof.
prepare.
intros G a m ext1 ext0 Hm Hhalt.
apply tr_partial_elim; eauto using tr_halts_eta2.
Qed.


Lemma haltsTrivialize_valid : haltsTrivialize_obligation.
Proof.
prepare.
intros G m ext0 H.
eapply tr_halts_eta2; eauto.
Qed.


Lemma haltsExt_valid : haltsExt_obligation.
Proof.
prepare.
intros G m n p ext1 ext0 Hn Hp.
apply (tr_transitivity _ _ triv).
  {
  eapply tr_halts_eta; eauto.
  }

  {
  apply tr_symmetry.
  eapply tr_halts_eta; eauto.
  }
Qed.


Lemma haltsLeft_valid : haltsLeft_obligation.
Proof.
prepare.
intros G1 G2 c m n H.
unfold Defs.triv in H.
apply tr_halts_eta_hyp; auto.
Qed.


Lemma fixpointInductionEq_valid : fixpointInductionEq_obligation.
Proof.
prepare.
intros G a m n ext1 p Hmn Hadmiss.
rewrite -> def_arrow in Hmn.
assert (tr G (deqtype (partial a) (partial a))) as Heqpa.
  {
  apply tr_partial_formation.
  apply tr_admiss_formation_invert.
  apply (tr_inhabitation_formation _ p p); auto.
  }

apply tr_fixpoint_induction.
  {
  eapply tr_admiss_eta2; eauto.
  }

  {
  apply (tr_eqtype_convert _#3 (pi (partial a) (subst sh1 (partial a)))); auto.
  apply tr_eqtype_symmetry.
  apply tr_tarrow_pi_equal; auto.
  }
Qed.


Lemma fixpointInductionOf_valid : fixpointInductionOf_obligation.
Proof.
prepare.
intros G a m ext1 p Hm Hadmiss.
rewrite -> def_arrow in Hm.
assert (tr G (deqtype (partial a) (partial a))) as Heqpa.
  {
  apply tr_partial_formation.
  apply tr_admiss_formation_invert.
  apply (tr_inhabitation_formation _ p p); auto.
  }
apply tr_fixpoint_induction.
  {
  eapply tr_admiss_eta2; eauto.
  }

  {
  apply (tr_eqtype_convert _#3 (pi (partial a) (subst sh1 (partial a)))); auto.
  apply tr_eqtype_symmetry.
  apply tr_tarrow_pi_equal; auto.
  }
Qed.


Lemma partialFormInv_valid : partialFormInv_obligation.
Proof.
prepare.
intros G a ext0 H.
apply tr_partial_formation_invert; auto.
Qed.


Lemma seqBind_valid : seqBind_obligation.
Proof.
prepare.
intros G a b m n p q ext2 ext1 ext0 Hmn Hpq Hb.
eapply tr_seq_bind; eauto.
Qed.


Lemma activeApp_valid : activeApp_obligation.
Proof.
prepare.
intros G a b m n ext2 ext1 ext0 Hm Hn Hb.
cut (tr G (deq (seq m (app (var 0) (subst sh1 n))) (subst1 m (app (var 0) (subst sh1 n))) (partial b))).
  {
  intro Hseq.
  simpsubin Hseq.
  eapply tr_transitivity; eauto.
  apply tr_symmetry; eauto.
  }
eapply tr_seq_active; eauto.
apply active_app.
apply active_var.
Qed.


Lemma activeAppSeq_valid : activeAppSeq_obligation.
Proof.
prepare.
intros G a b m n ext2 ext1 ext0 Hm Hn Hb.
apply tr_symmetry.
replace (app m n) with (subst1 m (app (var 0) (subst sh1 n))) by (simpsub; auto).
eapply tr_seq_active; eauto.
apply active_app.
apply active_var.
Qed.


Lemma appHaltsInv_valid : appHaltsInv_obligation.
Proof.
prepare.
intros G m n ext0 Hhalt.
apply (tr_active_halts_invert _ _ (app (var 0) (subst sh1 n))).
  {
  simpsub.
  eapply tr_halts_eta2; eauto.
  }

  {
  apply active_app.
  apply active_var.
  }
Qed.


Lemma activePi1_valid : activePi1_obligation.
Proof.
prepare.
intros G a b m ext2 ext1 ext0 Hm Hpi Hb.
cut (tr G (deq (seq m (ppi1 (var 0))) (subst1 m (ppi1 (var 0))) (partial b))).
  {
  intro Hseq.
  simpsubin Hseq.
  eapply tr_transitivity; eauto.
  apply tr_symmetry; eauto.
  }
eapply tr_seq_active; eauto.
apply active_ppi1.
apply active_var.
Qed.


Lemma activePi1Seq_valid : activePi1Seq_obligation.
Proof.
prepare.
intros G a b m ext2 ext1 ext0 Hm Hpi Hb.
apply tr_symmetry.
replace (ppi1 m) with (subst1 m (ppi1 (var 0))) by (simpsub; auto).
eapply tr_seq_active; eauto.
apply active_ppi1.
apply active_var.
Qed.


Lemma pi1HaltsInv_valid : pi1HaltsInv_obligation.
Proof.
prepare.
intros G m ext0 H.
apply (tr_active_halts_invert _ _ (ppi1 (var 0))).
  {
  simpsub.
  eapply tr_halts_eta2; eauto.
  }

  {
  apply active_ppi1.
  apply active_var.
  }
Qed.


Lemma activePi2_valid : activePi2_obligation.
Proof.
prepare.
intros G a b m ext2 ext1 ext0 Hm Hpi Hb.
cut (tr G (deq (seq m (ppi2 (var 0))) (subst1 m (ppi2 (var 0))) (partial b))).
  {
  intro Hseq.
  simpsubin Hseq.
  eapply tr_transitivity; eauto.
  apply tr_symmetry; eauto.
  }
eapply tr_seq_active; eauto.
apply active_ppi2.
apply active_var.
Qed.


Lemma activePi2Seq_valid : activePi2Seq_obligation.
Proof.
prepare.
intros G a b m ext2 ext1 ext0 Hm Hpi Hb.
apply tr_symmetry.
replace (ppi2 m) with (subst1 m (ppi2 (var 0))) by (simpsub; auto).
eapply tr_seq_active; eauto.
apply active_ppi2.
apply active_var.
Qed.


Lemma pi2HaltsInv_valid : pi2HaltsInv_obligation.
Proof.
prepare.
intros G m ext0 H.
apply (tr_active_halts_invert _ _ (ppi2 (var 0))).
  {
  simpsub.
  eapply tr_halts_eta2; eauto.
  }

  {
  apply active_ppi2.
  apply active_var.
  }
Qed.


Lemma prevHaltsInv_valid : prevHaltsInv_obligation.
Proof.
prepare.
intros G m ext0 H.
apply (tr_active_halts_invert _ _ (prev (var 0))).
  {
  simpsub.
  eapply tr_halts_eta2; eauto.
  }

  {
  apply active_prev.
  apply active_var.
  }
Qed.


Lemma activeCase_valid : activeCase_obligation.
Proof.
prepare.
intros G a b m p r ext2 ext1 ext0 Hm Hcase Hb.
rewrite -> def_sum_case in Hcase |- *.
cut (tr G (deq (seq m (sumcase (var 0) (subst (dot (var 0) (sh 2)) p) (subst (dot (var 0) (sh 2)) r))) (subst1 m (sumcase (var 0) (subst (dot (var 0) (sh 2)) p) (subst (dot (var 0) (sh 2)) r))) (partial b))).
  {
  intro Hseq.
  simpsubin Hseq.
  rewrite -> !subst_var0_sh1 in Hseq.
  eapply tr_transitivity; eauto.
  apply tr_symmetry; eauto.
  }
eapply tr_seq_active; eauto.
unfold sumcase.
apply active_bite.
apply active_ppi1.
apply active_var.
Qed.


Lemma activeCaseSeq_valid : activeCaseSeq_obligation.
Proof.
prepare.
intros G a b m p r ext2 ext1 ext0 Hm Hcase Hb.
setoid_rewrite -> def_sum_case at 2.
rewrite -> def_sum_case in Hcase |- *.
replace (sumcase m p r) with (subst1 m (sumcase (var 0) (subst (under 1 sh1) p) (subst (under 1 sh1) r))).
2:{
  simpsub.
  rewrite -> !subst_var0_sh1.
  auto.
  }
apply tr_symmetry.
eapply tr_seq_active; eauto.
unfold sumcase.
apply active_bite.
apply active_ppi1.
apply active_var.
Qed.


Lemma caseHaltsInv_valid : caseHaltsInv_obligation.
Proof.
prepare.
intros G m p r ext0 H.
rewrite -> def_sum_case in H.
apply (tr_active_halts_invert _ _ (sumcase (var 0) (subst (under 1 sh1) p) (subst (under 1 sh1) r))).
  {
  simpsub.
  rewrite -> !subst_var0_sh1.
  eapply tr_halts_eta2; eauto.
  }

  {
  unfold sumcase.
  apply active_bite.
  apply active_ppi1.
  apply active_var.
  }
Qed.


Lemma seqHaltsSequal_valid : seqHaltsSequal_obligation.
Proof.
prepare.
intros G m n ext0 H.
rewrite -> def_sequal.
apply tr_seq_halts_sequal.
eapply tr_halts_eta2; eauto.
Qed.


Lemma seqHaltsInv_valid : seqHaltsInv_obligation.
Proof.
prepare.
intros G m n p H.
apply (tr_active_halts_invert _ _ (seq (var 0) (app (subst (sh 2) n) (var 0)))).
  {
  simpsub.
  unfold Defs.seq in H.
  eapply (tr_halts_eta2 _ p p).
  eapply tr_compute; eauto.
    {
    apply equiv_halts.
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
      apply star_one.
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

    {
    apply equiv_refl.
    }

    {
    apply equiv_refl.
    }
  }

  {
  apply active_seq.
  apply active_var.
  }
Qed.


Lemma totalStrict_valid : totalStrict_obligation.
Proof.
prepare.
intros G a ext1 ext0 Ha Hhalt.
apply tr_total_strict; auto.
eapply tr_halts_eta2; eauto.
Qed.


Lemma voidStrict_valid : voidStrict_obligation.
Proof.
prepare.
intros G.
unfold Defs.void.
apply tr_subtype_intro.
  {
  apply tr_voidtp_istype.
  }

  {
  apply tr_partial_formation.
  apply tr_voidtp_istype.
  }

  {
  apply (tr_voidtp_elim _ (var 0) (var 0)).
  eapply hypothesis; eauto using index_0.
  }
Qed.


Lemma unitTotal_valid : unitTotal_obligation.
Proof.
prepare.
intros G m ext0 H.
unfold Defs.unit in H.
apply tr_unittp_total; auto.
Qed.


Lemma unitStrict_valid : unitStrict_obligation.
Proof.
prepare.
intros G.
unfold Defs.unit.
apply tr_total_strict.
  {
  apply tr_unittp_istype.
  }

  {
  apply tr_unittp_total.
  eapply hypothesis; eauto using index_0.
  }
Qed.


Lemma boolTotal_valid : boolTotal_obligation.
Proof.
prepare.
intros G m ext0 H.
unfold Defs.bool in H.
apply tr_booltp_total; auto.
Qed.


Lemma boolStrict_valid : boolStrict_obligation.
Proof.
prepare.
intro G.
unfold Defs.bool.
apply tr_total_strict.
  {
  apply tr_booltp_istype.
  }

  {
  apply tr_booltp_total.
  eapply hypothesis; eauto using index_0.
  }
Qed.


Lemma forallTotal_valid : forallTotal_obligation.
Proof.
prepare.
intros G a b m ext0 H.
rewrite -> def_pi in H.
eapply tr_pi_total; eauto.
Qed.


Lemma forallStrict_valid : forallStrict_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_pi.
apply tr_total_strict.
  {
  apply tr_pi_formation; auto.
  }

  {
  eapply tr_pi_total.
  eapply hypothesis; eauto using index_0.
  simpsub.
  eauto.
  }
Qed.


Lemma forallfutTotal_valid : forallfutTotal_obligation.
Proof.
prepare.
intros G a b m ext0 H.
rewrite -> def_forallfut in H.
eapply tr_pi_total; eauto.
Qed.


Lemma forallfutStrict_valid : forallfutStrict_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_forallfut.
apply tr_total_strict.
  {
  apply tr_pi_formation; auto.
    {
    apply tr_semifut_formation; auto.
    }

    {
    replace (deqtype b b) with (deqtype (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
    2:{
      simpsub.
      rewrite -> subst_var0_sh1; auto.
      }
    apply (tr_semifut_elim_eqtype _ _ _ (subst sh1 a)).
      {
      eapply hypothesis; eauto using index_0.
      }
  
      {
      cbn.
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
      cbn.
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
      rewrite -> subst_var0_sh1.
      exact Hb.
      }
    }
  }

  {
  eapply tr_pi_total.
  eapply hypothesis; eauto using index_0.
  simpsub.
  eauto.
  }
Qed.


Lemma arrowTotal_valid : arrowTotal_obligation.
Proof.
prepare.
intros G a b M ext0 H.
rewrite -> def_arrow in H.
eapply tr_pi_total; eauto.
Qed.


Lemma arrowStrict_valid : arrowStrict_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_arrow.
apply tr_total_strict.
  {
  apply tr_pi_formation; auto.
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

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  }

  {
  eapply tr_pi_total.
  eapply hypothesis; eauto using index_0.
  simpsub.
  eauto.
  }
Qed.


Lemma parametricTotal_valid : parametricTotal_obligation.
Proof.
prepare.
intros G a b m ext0 H.
rewrite -> def_parametric in H.
eapply tr_pi_total; eauto.
eapply tr_conjoin_elim1; eauto.
Qed.


Lemma parametricStrict_valid : parametricStrict_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_parametric.
apply tr_total_strict.
  {
  apply tr_conjoin_formation.
    {
    apply tr_pi_formation; auto.
    }
    
    {
    apply (tr_formation_weaken _ nzero).
    apply tr_constfn_formation.
    }
  }

  {
  eapply tr_pi_total.
  eapply tr_conjoin_elim1.
  eapply hypothesis; eauto using index_0.
  simpsub.
  eauto.
  }
Qed.


Lemma parametricfutTotal_valid : parametricfutTotal_obligation.
Proof.
prepare.
intros G a b m ext0 H.
rewrite -> def_parametricfut in H.
eapply tr_pi_total; eauto.
eapply tr_conjoin_elim1; eauto.
Qed.


Lemma parametricfutStrict_valid : parametricfutStrict_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_parametricfut.
apply tr_total_strict.
  {
  apply tr_conjoin_formation.
  2:{
    apply (tr_formation_weaken _ nzero).
    apply tr_constfn_formation.
    }
  apply tr_pi_formation; auto.
    {
    apply tr_semifut_formation; auto.
    }

    {
    replace (deqtype b b) with (deqtype (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
    2:{
      simpsub.
      rewrite -> subst_var0_sh1; auto.
      }
    apply (tr_semifut_elim_eqtype _ _ _ (subst sh1 a)).
      {
      eapply hypothesis; eauto using index_0.
      }
  
      {
      cbn.
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
      cbn.
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
      rewrite -> subst_var0_sh1.
      exact Hb.
      }
    }
  }

  {
  eapply tr_pi_total.
  eapply tr_conjoin_elim1.
  eapply hypothesis; eauto using index_0.
  simpsub.
  eauto.
  }
Qed.


Lemma intersectStrict_valid : intersectStrict_obligation.
Proof.
prepare.
intros G a b m ext0 Hm Hb.
rewrite -> def_intersect.
eapply tr_intersect_strict; eauto.
Qed.


Lemma intersectfutStrict_valid : intersectfutStrict_obligation.
Proof.
prepare.
intros G a b m ext0 Hm Hb.
rewrite -> def_intersectfut.
eapply (tr_intersect_strict _#3 m); eauto.
  {
  apply tr_semifut_intro; auto.
  }

  {
  unfold dsubtype.
  replace (deq triv triv (subtype b (partial b))) with (deq (subst1 (var 0) triv) (subst1 (var 0) triv) (subst1 (var 0) (subst (dot (var 0) (sh 2)) (subtype b (partial b))))).
  2:{
    simpsub.
    rewrite -> !subst_var0_sh1.
    auto.
    }
  apply (tr_semifut_elim _#3 (subst sh1 a)).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    eapply tr_inhabitation_formation; eauto.
    }

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
    rewrite -> !subst_var0_sh1.
    exact Hb.
    }
  }
Qed.


Lemma existsTotal_valid : existsTotal_obligation.
Proof.
prepare.
intros G a b m ext0 H.
rewrite -> def_sigma in H.
eapply tr_sigma_total; eauto.
Qed.


Lemma existsStrict_valid : existsStrict_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_sigma.
apply tr_total_strict.
  {
  apply tr_sigma_formation; auto.
  }

  {
  eapply tr_sigma_total.
  eapply hypothesis; eauto using index_0.
  simpsub.
  eauto.
  }
Qed.


Lemma tr_prod_total :
  forall G a b m,
    tr G (deq m m (prod a b))
    -> tr G (deq triv triv (halts m)).
Proof.
intros G a b m H.
apply (tr_sigma_total _ a (subst sh1 b)).
eapply tr_eqtype_convert; eauto.
apply tr_prod_sigma_equal.
  {
  eapply tr_prod_formation_invert1; eauto.
  eapply tr_inhabitation_formation; eauto.
  }

  {
  relquest.
    {
    apply (tr_generalize _ a (ppi1 m) (deqtype (subst sh1 b) (subst sh1 b))).
      {
      eapply tr_prod_elim1; eauto.
      }

      {
      eapply tr_prod_formation_invert2; eauto.
      eapply tr_inhabitation_formation; eauto.
      }
    }

    {
    simpsub.
    reflexivity.
    }
  }
Qed.


Lemma prodTotal_valid : prodTotal_obligation.
Proof.
prepare.
intros G a b M ext0 H.
rewrite -> def_prod in H.
eapply tr_prod_total; eauto.
Qed.


Lemma prodStrict_valid : prodStrict_obligation.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_prod.
apply tr_total_strict.
  {
  apply tr_prod_formation; auto.
  }

  {
  eapply tr_prod_total.
  eapply hypothesis; eauto using index_0.
  simpsub.
  eauto.
  }
Qed.


Lemma dprodTotal_valid : dprodTotal_obligation.
Proof.
prepare.
intros G a b M ext0 H.
rewrite -> def_dprod in H.
eapply tr_sigma_total; eauto.
Qed.


Lemma dprodStrict_valid : dprodStrict_obligation.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_dprod.
apply tr_total_strict.
  {
  apply tr_sigma_formation; auto.
  eapply (weakening _ [_] []).
    {
    simpsub.
    auto.
    }
    
    {
    cbn [length].
    simpsub.
    rewrite <- compose_assoc.
    simpsub.
    auto.
    }
  cbn [length].
  simpsub.
  cbn [List.app].
  exact Hb.
  }

  {
  eapply tr_sigma_total.
  eapply hypothesis; eauto using index_0.
  simpsub.
  eauto.
  }
Qed.


Lemma sumTotal_valid : sumTotal_obligation.
Proof.
prepare.
intros G a b m ext0 H.
rewrite -> def_sum in H.
eapply tr_sum_total; eauto.
Qed.


Lemma sumStrict_valid : sumStrict_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_sum.
apply tr_total_strict.
  {
  apply tr_sumtype_formation; auto.
  }

  {
  eapply tr_sum_total.
  eapply hypothesis; eauto using index_0.
  simpsub.
  eauto.
  }
Qed.


Lemma futureTotal_valid : futureTotal_obligation.
Proof.
prepare.
intros G a m ext0 Hm.
rewrite -> def_fut in Hm.
eapply tr_fut_total; eauto.
Qed.


Lemma futureStrict_valid : futureStrict_obligation.
Proof.
prepare.
intros G a ext0 Ha.
rewrite -> def_fut.
apply tr_total_strict.
  {
  apply tr_fut_formation; eauto.
  }

  {
  eapply tr_fut_total; eauto.
  eapply hypothesis; eauto using index_0.
  simpsub.
  reflexivity.
  }
Qed.


Lemma setStrict_valid : setStrict_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Hb Ha.
rewrite -> def_set.
apply tr_set_strict; auto.
Qed.


Lemma isetStrict_valid : isetStrict_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Hb Ha.
rewrite -> def_iset.
apply tr_iset_strict; auto.
Qed.


Lemma univStrict_valid : univStrict_obligation.
Proof.
prepare.
intros G i ext Hi.
apply tr_total_strict.
  {
  apply tr_univ_formation; auto.
  }

  {
  apply tr_type_halt.
  apply (tr_formation_weaken _ (subst sh1 i)).
  eapply hypothesis; eauto using index_0.
  }
Qed.


Lemma typeHalts_valid : typeHalts_obligation.
Proof.
prepare.
intros G a ext0 Ha.
apply tr_type_halt; auto.
Qed.


Lemma uptypeForm_valid : uptypeForm_obligation.
Proof.
prepare.
intros G a ext0 Ha.
apply tr_uptype_formation; auto.
Qed.


Lemma uptypeEq_valid : uptypeEq_obligation.
Proof.
prepare.
intros G a b ext0 Hab.
apply tr_uptype_formation; auto.
Qed.


Lemma uptypeFormUniv_valid : uptypeFormUniv_obligation.
Proof.
prepare.
intros G a i ext0 Ha.
apply tr_uptype_formation_univ; auto.
Qed.


Lemma uptypeEqUniv_valid : uptypeEqUniv_obligation.
Proof.
prepare.
intros G a b i ext0 Hab.
apply tr_uptype_formation_univ; auto.
Qed.


Lemma uptypeTrivialize_valid : uptypeTrivialize_obligation.
Proof.
prepare.
intros G a ext0 H.
eapply tr_uptype_eta2; eauto.
Qed.


Lemma uptypeExt_valid : uptypeExt_obligation.
Proof.
prepare.
intros G a n p ext1 ext0 Hn Hp.
apply (tr_transitivity _ _ triv).
  {
  eapply tr_uptype_eta; eauto.
  }

  {
  apply tr_symmetry.
  eapply tr_uptype_eta; eauto.
  }
Qed.


Lemma uptypeLeft_valid : uptypeLeft_obligation.
Proof.
prepare.
intros G1 G2 a c m H.
unfold Defs.triv in H.
apply tr_uptype_eta_hyp; auto.
Qed.


Lemma uptypeEeqtp_valid : uptypeEeqtp_obligation.
Proof.
prepare.
intros G a b ext1 m Ha Hab.
rewrite -> def_eeqtp in Hab.
eapply tr_uptype_eeqtp.
  {
  eapply (tr_subtype_eta2 _#3 (ppi1 m) (ppi1 m)).
  eapply tr_prod_elim1; eauto.
  }
  
  {
  eapply (tr_subtype_eta2 _#3 (ppi2 m) (ppi2 m)).
  eapply tr_prod_elim2; eauto.
  }
  
  {
  eapply tr_uptype_eta2; eauto.
  }
Qed.


Lemma uptypeUnitary_valid : uptypeUnitary_obligation.
Proof.
prepare.
intros G a ext0 H.
unfold Defs.unit in H.
apply tr_unitary_uptype; auto.
Qed.


Lemma voidUptype_valid : voidUptype_obligation.
Proof.
prepare.
intros G.
unfold Defs.void.
apply tr_unitary_uptype.
apply tr_subtype_intro; auto using tr_voidtp_istype, tr_unittp_istype.
apply (tr_voidtp_elim _ (var 0) (var 0)).
eapply hypothesis; eauto using index_0.
Qed.


Lemma unitUptype_valid : unitUptype_obligation.
Proof.
prepare.
intros G.
unfold Defs.unit.
apply tr_unitary_uptype.
apply tr_subtype_refl.
apply tr_unittp_istype.
Qed.


Lemma boolUptype_valid : boolUptype_obligation.
Proof.
prepare.
intros G.
unfold Defs.bool.
apply tr_booltp_uptype.
Qed.


Lemma forallUptype_valid : forallUptype_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_pi.
apply tr_pi_uptype; auto.
eapply tr_uptype_eta2; eauto.
Qed.


Lemma forallfutUptype_valid : forallfutUptype_obligation.
Proof.
prepare.
intros G a b ext1 p Ha Hb.
rewrite -> def_forallfut.
apply tr_pi_uptype; auto.
  {
  apply tr_semifut_formation; auto.
  }
  
  {
  eapply tr_uptype_eta2; eauto.
  replace (deq p p (uptype b)) with (deq (subst1 (var 0) (subst (dot (var 0) (sh 2)) p)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) p)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) (uptype b)))).
  2:{
    simpsub.
    rewrite -> !subst_var0_sh1; auto.
    }
  apply (tr_semifut_elim _ _ _ (subst sh1 a)).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    auto.
    }

    {
    simpsub.
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
    rewrite -> !subst_var0_sh1.
    exact Hb.
    }
  }
Qed.


Lemma arrowUptype_valid : arrowUptype_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_arrow.
apply tr_pi_uptype; auto.
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
eapply tr_uptype_eta2; eauto.
Qed.


Lemma tr_conjoin_uptype :
  forall G a b,
    tr G (deq triv triv (uptype a))
    -> tr G (deq triv triv (uptype b))
    -> tr G (deq triv triv (uptype (conjoin a b))).
Proof.
prepare.
intros G a b Ha Hb.
unfold conjoin.
apply tr_intersect_uptype.
  {
  apply tr_booltp_istype.
  }
apply (tr_uptype_eta2 _
         (bite (var 0) (subst (under 0 sh1) triv) (subst (under 0 sh1) triv))
         (bite (var 0) (subst (under 0 sh1) triv) (subst (under 0 sh1) triv))).
apply (tr_booltp_eta_hyp _ []).
  {
  cbn [length].
  simpsub.
  cbn [List.app].
  apply (tr_compute _ _ (uptype a) _ triv _ triv); auto using equiv_refl.
  apply equiv_uptype.
  apply steps_equiv.
  apply star_one.
  apply step_bite2.
  }

  {
  cbn [length].
  simpsub.
  cbn [List.app].
  apply (tr_compute _ _ (uptype b) _ triv _ triv); auto using equiv_refl.
  apply equiv_uptype.
  apply steps_equiv.
  apply star_one.
  apply step_bite3.
  }
Qed.



Lemma intersectUptype_valid : intersectUptype_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_intersect.
apply tr_intersect_uptype; auto.
eapply tr_uptype_eta2; eauto.
Qed.


Lemma intersectfutUptype_valid : intersectfutUptype_obligation.
Proof.
prepare.
intros G a b ext1 p Ha Hb.
rewrite -> def_intersectfut.
apply tr_intersect_uptype; auto.
  {
  apply tr_semifut_formation; auto.
  }
  
  {
  eapply tr_uptype_eta2; eauto.
  replace (deq p p (uptype b)) with (deq (subst1 (var 0) (subst (dot (var 0) (sh 2)) p)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) p)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) (uptype b)))).
  2:{
    simpsub.
    rewrite -> !subst_var0_sh1; auto.
    }
  apply (tr_semifut_elim _ _ _ (subst sh1 a)).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    auto.
    }

    {
    simpsub.
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
    rewrite -> !subst_var0_sh1.
    exact Hb.
    }
  }
Qed.


Lemma existsUptype_valid : existsUptype_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_sigma.
apply tr_sigma_uptype; eauto using tr_uptype_eta2.
Qed.


Lemma prodUptype_valid : prodUptype_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_prod.
apply (tr_eqtype_convert _#3 (uptype (sigma a (subst sh1 b)))).
  {
  apply tr_uptype_formation.
  apply tr_eqtype_symmetry.
  apply tr_prod_sigma_equal.
    {
    apply tr_uptype_formation_invert.
    eapply tr_inhabitation_formation; eauto.
    }

    {
    apply tr_uptype_formation_invert.
    eapply tr_inhabitation_formation; eauto.
    }
  }

  {
  apply tr_sigma_uptype; eauto using tr_uptype_eta2.
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
  eapply tr_uptype_eta2; eauto.
  }
Qed.


Lemma dprodUptype_valid : dprodUptype_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_dprod.
apply tr_sigma_uptype; eauto using tr_uptype_eta2.
Qed.


Lemma tr_sumtype_uptype :
  forall G a b,
    tr G (deq triv triv (uptype a))
    -> tr G (deq triv triv (uptype b))
    -> tr G (deq triv triv (uptype (sumtype a b))).
Proof.
intros G a b Ha Hb.
apply tr_sigma_uptype.
  {
  apply tr_booltp_uptype.
  }
apply (tr_uptype_eta2 _ (bite (var 0) (subst (under 0 sh1) triv) (subst (under 0 sh1) triv)) (bite (var 0) (subst (under 0 sh1) triv) (subst (under 0 sh1) triv))).
apply (tr_booltp_eta_hyp _ []).
  {
  cbn [length].
  simpsub.
  cbn [List.app].
  eapply (tr_compute _ _ (uptype a)); eauto using equiv_refl, tr_uptype_eta2.
  apply equiv_uptype.
  apply steps_equiv.
  apply star_one.
  apply step_bite2.
  }

  {
  cbn [length].
  simpsub.
  cbn [List.app].
  eapply (tr_compute _ _ (uptype b)); eauto using equiv_refl, tr_uptype_eta2.
  apply equiv_uptype.
  apply steps_equiv.
  apply star_one.
  apply step_bite3.
  }
Qed.


Lemma sumUptype_valid : sumUptype_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_sum.
eapply tr_sumtype_uptype; eauto using tr_uptype_eta2.
Qed.


Lemma futureUptype_valid : futureUptype_obligation.
Proof.
prepare.
intros G a ext0 H.
rewrite -> def_fut.
apply tr_fut_uptype.
eapply tr_uptype_eta2; eauto.
Qed.


Lemma eqUptype_valid : eqUptype_obligation.
Proof.
prepare.
intros G a m n ext1 ext0 Hm Hn.
apply tr_unitary_uptype.
apply tr_subtype_intro; auto using tr_unittp_istype.
  {
  apply tr_equal_formation; auto.
  eapply tr_inhabitation_formation; eauto.
  }
simpsub.
apply tr_equal_elim.
replace (@triv obj) with (@subst obj (under 0 sh1) triv) by (simpsub; auto).
apply (tr_equal_eta_hyp _ []).
simpsub.
cbn [List.app].
apply tr_equal_intro.
apply tr_unittp_intro.
Qed.


Lemma ofUptype_valid : ofUptype_obligation.
Proof.
prepare.
intros G a m ext0 Hm.
apply tr_unitary_uptype.
apply tr_subtype_intro; auto using tr_unittp_istype.
  {
  apply tr_equal_formation; auto.
  eapply tr_inhabitation_formation; eauto.
  }
simpsub.
apply tr_equal_elim.
replace (@triv obj) with (@subst obj (under 0 sh1) triv) by (simpsub; auto).
apply (tr_equal_eta_hyp _ []).
simpsub.
cbn [List.app].
apply tr_equal_intro.
apply tr_unittp_intro.
Qed.


Lemma eqtpUptype_valid : eqtpUptype_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_unitary_uptype.
apply tr_subtype_intro; auto using tr_unittp_istype.
  {
  apply tr_eqtype_formation; auto.
  }
simpsub.
apply tr_equal_elim.
replace (@triv obj) with (@subst obj (under 0 sh1) triv) by (simpsub; auto).
apply (tr_eqtype_eta_hyp _ []).
simpsub.
cbn [List.app].
apply tr_equal_intro.
apply tr_unittp_intro.
Qed.


Lemma istpUptype_valid : istpUptype_obligation.
Proof.
prepare.
intros G a ext0 Ha.
apply tr_unitary_uptype.
apply tr_subtype_intro; auto using tr_unittp_istype.
  {
  apply tr_eqtype_formation; auto.
  }
simpsub.
apply tr_equal_elim.
replace (@triv obj) with (@subst obj (under 0 sh1) triv) by (simpsub; auto).
apply (tr_eqtype_eta_hyp _ []).
simpsub.
cbn [List.app].
apply tr_equal_intro.
apply tr_unittp_intro.
Qed.


Lemma subtypeUptype_valid : subtypeUptype_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_unitary_uptype.
apply tr_subtype_intro; auto using tr_unittp_istype.
  {
  apply tr_subtype_formation; auto.
  }
simpsub.
apply tr_equal_elim.
replace (@triv obj) with (@subst obj (under 0 sh1) triv) by (simpsub; auto).
apply (tr_subtype_eta_hyp _ []).
simpsub.
cbn [List.app].
apply tr_equal_intro.
apply tr_unittp_intro.
Qed.


Lemma setUptype_valid : setUptype_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_set.
apply tr_set_uptype; eauto using tr_uptype_eta2.
Qed.


Lemma isetUptype_valid : isetUptype_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_iset.
apply tr_iset_uptype; eauto using tr_uptype_eta2.
Qed.


Lemma muUptype_valid : muUptype_obligation.
Proof.
prepare.
intros G a ext2 ext1 ext0 Ha Huptype Hpos.
rewrite -> def_positive in Hpos.
rewrite -> def_mu.
apply tr_mu_uptype; auto.
  {
  eapply tr_positive_eta2; eauto.
  }

  {
  eapply tr_uptype_eta2; eauto.
  }
Qed.


Lemma muUptypeUniv_valid : muUptypeUniv_obligation.
Proof.
prepare.
intros G a i ext3 ext2 ext1 ext0 Hi Ha Huptype Hpos.
rewrite -> def_positive in Hpos.
rewrite -> def_mu.
eapply tr_mu_uptype_univ; eauto.
  {
  eapply tr_positive_eta2; eauto.
  }

  {
  eapply tr_uptype_eta2; eauto.
  }
Qed.


Lemma recUptype_valid : recUptype_obligation.
Proof.
prepare.
intros G a ext1 ext0 Ha Huptype.
rewrite -> def_rec.
apply tr_rec_uptype.
eapply tr_uptype_eta2; eauto.
Qed.


Lemma recUptypeUniv_valid : recUptypeUniv_obligation.
Proof.
prepare.
intros G a i ext2 ext1 ext0 Hi Ha Huptype.
rewrite -> def_rec.
eapply tr_rec_uptype_univ; eauto.
eapply tr_uptype_eta2; eauto.
Qed.



Lemma uptypeFormInv_valid : uptypeFormInv_obligation.
Proof.
prepare.
intros G a ext0 H.
apply tr_uptype_formation_invert; auto.
Qed.


Lemma admissForm_valid : admissForm_obligation.
Proof.
prepare.
intros G a ext0 Ha.
apply tr_admiss_formation; auto.
Qed.


Lemma admissEq_valid : admissEq_obligation.
Proof.
prepare.
intros G a b ext0 Hab.
apply tr_admiss_formation; auto.
Qed.


Lemma admissFormUniv_valid : admissFormUniv_obligation.
Proof.
prepare.
intros G a i ext0 Ha.
apply tr_admiss_formation_univ; auto.
Qed.


Lemma admissEqUniv_valid : admissEqUniv_obligation.
Proof.
prepare.
intros G a b i ext0 Hab.
apply tr_admiss_formation_univ; auto.
Qed.


Lemma admissTrivialize_valid : admissTrivialize_obligation.
Proof.
prepare.
intros G a ext0 H.
eapply tr_admiss_eta2; eauto.
Qed.


Lemma admissExt_valid : admissExt_obligation.
Proof.
prepare.
intros G a n p ext1 ext0 Hn Hp.
apply (tr_transitivity _ _ triv).
  {
  eapply tr_admiss_eta; eauto.
  }

  {
  apply tr_symmetry.
  eapply tr_admiss_eta; eauto.
  }
Qed.


Lemma admissLeft_valid : admissLeft_obligation.
Proof.
prepare.
intros G1 G2 a c m H.
unfold Defs.triv in H.
apply tr_admiss_eta_hyp; auto.
Qed.


Lemma admissEeqtp_valid : admissEeqtp_obligation.
Proof.
prepare.
intros G a b ext1 m Ha Hab.
rewrite -> def_eeqtp in Hab.
eapply tr_admiss_eeqtp.
  {
  eapply (tr_subtype_eta2 _#3 (ppi1 m) (ppi1 m)).
  eapply tr_prod_elim1; eauto.
  }
  
  {
  eapply (tr_subtype_eta2 _#3 (ppi2 m) (ppi2 m)).
  eapply tr_prod_elim2; eauto.
  }
  
  {
  eapply tr_admiss_eta2; eauto.
  }
Qed.


Lemma uptypeAdmiss_valid : uptypeAdmiss_obligation.
Proof.
prepare.
intros G a ext0 H.
apply tr_uptype_admiss.
eapply tr_uptype_eta2; eauto.
Qed.


Lemma partialAdmiss_valid : partialAdmiss_obligation.
Proof.
prepare.
intros G a ext0 H.
apply tr_partial_admiss.
eapply tr_admiss_eta2; eauto.
Qed.


Lemma voidAdmiss_valid : voidAdmiss_obligation.
Proof.
prepare.
intros G.
unfold Defs.void.
apply tr_uptype_admiss.
apply tr_unitary_uptype.
apply tr_subtype_intro; auto using tr_voidtp_istype, tr_unittp_istype.
apply (tr_voidtp_elim _ (var 0) (var 0)).
eapply hypothesis; eauto using index_0.
Qed.


Lemma unitAdmiss_valid : unitAdmiss_obligation.
Proof.
prepare.
intros G.
unfold Defs.unit.
apply tr_uptype_admiss.
apply tr_unitary_uptype.
apply tr_subtype_refl.
apply tr_unittp_istype.
Qed.


Lemma boolAdmiss_valid : boolAdmiss_obligation.
Proof.
prepare.
intros G.
unfold Defs.bool.
apply tr_uptype_admiss.
apply tr_booltp_uptype.
Qed.


Lemma forallAdmiss_valid : forallAdmiss_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_pi.
apply tr_pi_admiss; auto.
eapply tr_admiss_eta2; eauto.
Qed.


Lemma forallfutAdmiss_valid : forallfutAdmiss_obligation.
Proof.
prepare.
intros G a b ext1 p Ha Hb.
rewrite -> def_forallfut.
apply tr_pi_admiss; auto.
  {
  apply tr_semifut_formation; auto.
  }
  
  {
  eapply tr_admiss_eta2; eauto.
  replace (deq p p (admiss b)) with (deq (subst1 (var 0) (subst (dot (var 0) (sh 2)) p)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) p)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) (admiss b)))).
  2:{
    simpsub.
    rewrite -> !subst_var0_sh1; auto.
    }
  apply (tr_semifut_elim _ _ _ (subst sh1 a)).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    auto.
    }

    {
    simpsub.
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
    rewrite -> !subst_var0_sh1.
    exact Hb.
    }
  }
Qed.


Lemma arrowAdmiss_valid : arrowAdmiss_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_arrow.
apply tr_pi_admiss; auto.
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
eapply tr_admiss_eta2; eauto.
Qed.


Lemma intersectAdmiss_valid : intersectAdmiss_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_intersect.
apply tr_intersect_admiss; auto.
eapply tr_admiss_eta2; eauto.
Qed.


Lemma intersectfutAdmiss_valid : intersectfutAdmiss_obligation.
Proof.
prepare.
intros G a b ext1 p Ha Hb.
rewrite -> def_intersectfut.
apply tr_intersect_admiss; auto.
  {
  apply tr_semifut_formation; auto.
  }
  
  {
  eapply tr_admiss_eta2; eauto.
  replace (deq p p (admiss b)) with (deq (subst1 (var 0) (subst (dot (var 0) (sh 2)) p)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) p)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) (admiss b)))).
  2:{
    simpsub.
    rewrite -> !subst_var0_sh1; auto.
    }
  apply (tr_semifut_elim _ _ _ (subst sh1 a)).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    cbn.
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
    auto.
    }

    {
    simpsub.
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
    rewrite -> !subst_var0_sh1.
    exact Hb.
    }
  }
Qed.


Lemma existsAdmissUptype_valid : existsAdmissUptype_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_sigma.
apply tr_sigma_uptype_admiss; eauto using tr_uptype_eta2, tr_admiss_eta2.
Qed.


Lemma prodAdmiss_valid : prodAdmiss_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_prod.
apply tr_prod_admiss; eauto using tr_admiss_eta2.
Qed.


Lemma dprodAdmissUptype_valid : dprodAdmissUptype_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_dprod.
apply tr_sigma_uptype_admiss; eauto using tr_uptype_eta2, tr_admiss_eta2.
Qed.


Lemma sumAdmiss_valid : sumAdmiss_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
rewrite -> def_sum.
apply tr_sigma_uptype_admiss.
  {
  apply tr_booltp_uptype.
  }
apply (tr_admiss_eta2 _ (bite (var 0) (subst (under 0 sh1) triv) (subst (under 0 sh1) triv)) (bite (var 0) (subst (under 0 sh1) triv) (subst (under 0 sh1) triv))).
apply (tr_booltp_eta_hyp _ []).
  {
  cbn [length].
  simpsub.
  cbn [List.app].
  eapply (tr_compute _ _ (admiss a)); eauto using equiv_refl, tr_admiss_eta2.
  apply equiv_admiss.
  apply steps_equiv.
  apply star_one.
  apply step_bite2.
  }

  {
  cbn [length].
  simpsub.
  cbn [List.app].
  eapply (tr_compute _ _ (admiss b)); eauto using equiv_refl, tr_admiss_eta2.
  apply equiv_admiss.
  apply steps_equiv.
  apply star_one.
  apply step_bite3.
  }
Qed.


Lemma futureAdmiss_valid : futureAdmiss_obligation.
Proof.
prepare.
intros G a ext0 H.
rewrite -> def_fut.
apply tr_fut_admiss.
eapply tr_admiss_eta2; eauto.
Qed.


Lemma eqAdmiss_valid : eqAdmiss_obligation.
Proof.
prepare.
intros G a m n ext1 ext0 Hm Hn.
apply tr_uptype_admiss.
apply tr_unitary_uptype.
apply tr_subtype_intro; auto using tr_unittp_istype.
  {
  apply tr_equal_formation; auto.
  eapply tr_inhabitation_formation; eauto.
  }
simpsub.
apply tr_equal_elim.
replace (@triv obj) with (@subst obj (under 0 sh1) triv) by (simpsub; auto).
apply (tr_equal_eta_hyp _ []).
simpsub.
cbn [List.app].
apply tr_equal_intro.
apply tr_unittp_intro.
Qed.


Lemma ofAdmiss_valid : ofAdmiss_obligation.
Proof.
prepare.
intros G a m ext0 Hm.
apply tr_uptype_admiss.
apply tr_unitary_uptype.
apply tr_subtype_intro; auto using tr_unittp_istype.
  {
  apply tr_equal_formation; auto.
  eapply tr_inhabitation_formation; eauto.
  }
simpsub.
apply tr_equal_elim.
replace (@triv obj) with (@subst obj (under 0 sh1) triv) by (simpsub; auto).
apply (tr_equal_eta_hyp _ []).
simpsub.
cbn [List.app].
apply tr_equal_intro.
apply tr_unittp_intro.
Qed.


Lemma eqtpAdmiss_valid : eqtpAdmiss_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_uptype_admiss.
apply tr_unitary_uptype.
apply tr_subtype_intro; auto using tr_unittp_istype.
  {
  apply tr_eqtype_formation; auto.
  }
simpsub.
apply tr_equal_elim.
replace (@triv obj) with (@subst obj (under 0 sh1) triv) by (simpsub; auto).
apply (tr_eqtype_eta_hyp _ []).
simpsub.
cbn [List.app].
apply tr_equal_intro.
apply tr_unittp_intro.
Qed.


Lemma istpAdmiss_valid : istpAdmiss_obligation.
Proof.
prepare.
intros G a ext0 Ha.
apply tr_uptype_admiss.
apply tr_unitary_uptype.
apply tr_subtype_intro; auto using tr_unittp_istype.
  {
  apply tr_eqtype_formation; auto.
  }
simpsub.
apply tr_equal_elim.
replace (@triv obj) with (@subst obj (under 0 sh1) triv) by (simpsub; auto).
apply (tr_eqtype_eta_hyp _ []).
simpsub.
cbn [List.app].
apply tr_equal_intro.
apply tr_unittp_intro.
Qed.


Lemma subtypeAdmiss_valid : subtypeAdmiss_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_uptype_admiss.
apply tr_unitary_uptype.
apply tr_subtype_intro; auto using tr_unittp_istype.
  {
  apply tr_subtype_formation; auto.
  }
simpsub.
apply tr_equal_elim.
replace (@triv obj) with (@subst obj (under 0 sh1) triv) by (simpsub; auto).
apply (tr_subtype_eta_hyp _ []).
simpsub.
cbn [List.app].
apply tr_equal_intro.
apply tr_unittp_intro.
Qed.


Lemma recAdmiss_valid : recAdmiss_obligation.
Proof.
prepare.
intros G a ext1 ext0 Ha Hadmiss.
rewrite -> def_rec.
apply tr_rec_admiss.
eapply tr_admiss_eta2; eauto.
Qed.


Lemma recAdmissUniv_valid : recAdmissUniv_obligation.
Proof.
prepare.
intros G a i ext2 ext1 ext0 Hi Ha Hadmiss.
rewrite -> def_rec.
eapply tr_rec_admiss_univ; eauto.
eapply tr_admiss_eta2; eauto.
Qed.


Lemma admissFormInv_valid : admissFormInv_obligation.
Proof.
prepare.
intros G a ext0 H.
apply tr_admiss_formation_invert; auto.
Qed.


Lemma partialType_valid : partialType_obligation.
Proof.
prepare.
intros G.
rewrite -> def_intersect.
rewrite -> def_arrow.
simpsub.
cbn [Nat.add].
unfold Defs.partial.
apply tr_intersect_intro.
  {
  apply tr_nattp_formation.
  }
simpsub.
apply tr_pi_intro.
  {
  apply tr_univ_formation.
  unfold pagetp.
  eapply hypothesis; eauto using index_0.
  }
apply tr_partial_formation_univ.
eapply hypothesis; eauto using index_0.
Qed.


Lemma haltsType_valid : haltsType_obligation.
Proof.
prepare.
intro G.
rewrite -> !def_intersect.
rewrite -> def_arrow.
unfold Defs.halts.
apply tr_intersect_intro.
  {
  apply tr_nattp_formation.
  }
simpsub.
apply tr_intersect_intro.
  {
  apply tr_univ_formation.
  eapply hypothesis; eauto using index_0.
  }
simpsub.
apply tr_pi_intro.
  {
  apply tr_partial_formation.
  apply (tr_formation_weaken _ (var 1)).
  eapply hypothesis; eauto using index_0.
  }
rewrite -> def_lzero.
simpsub.
eapply tr_halts_formation_univ; eauto.
eapply hypothesis; eauto using index_0.
simpsub.
eauto.
Qed.



Lemma admissType_valid : admissType_obligation.
Proof.
prepare.
intros G.
rewrite -> def_intersect.
rewrite -> def_arrow.
simpsub.
cbn [Nat.add].
unfold Defs.admiss.
apply tr_intersect_intro.
  {
  apply tr_nattp_formation.
  }
simpsub.
apply tr_pi_intro.
  {
  apply tr_univ_formation.
  unfold pagetp.
  eapply hypothesis; eauto using index_0.
  }
apply tr_admiss_formation_univ.
eapply hypothesis; eauto using index_0.
Qed.


Lemma uptypeType_valid : uptypeType_obligation.
Proof.
prepare.
intros G.
rewrite -> def_intersect.
rewrite -> def_arrow.
simpsub.
cbn [Nat.add].
unfold Defs.uptype.
apply tr_intersect_intro.
  {
  apply tr_nattp_formation.
  }
simpsub.
apply tr_pi_intro.
  {
  apply tr_univ_formation.
  unfold pagetp.
  eapply hypothesis; eauto using index_0.
  }
apply tr_uptype_formation_univ.
eapply hypothesis; eauto using index_0.
Qed.


Lemma seqType_valid : seqType_obligation.
Proof.
prepare.
intro G.
rewrite -> !def_intersect.
rewrite -> !def_arrow.
unfold Defs.seq.
apply tr_intersect_intro.
  {
  apply tr_nattp_formation.
  }
simpsub.
cbn [Nat.add].
apply tr_intersect_intro.
  {
  apply tr_univ_formation.
  eapply hypothesis; eauto using index_0.
  }
simpsub.
cbn [Nat.add].
apply tr_intersect_intro.
  {
  apply tr_univ_formation.
  eapply hypothesis; eauto using index_0, index_S.
  }
simpsub.
cbn [Nat.add].
apply tr_pi_intro.
  {
  apply tr_partial_formation.
  apply (tr_formation_weaken _ (var 2)).
  eapply hypothesis; eauto using index_0, index_S.
  }
apply tr_pi_intro.
  {
  apply tr_pi_formation.
    {
    apply (tr_formation_weaken _ (var 3)).
    eapply hypothesis; eauto using index_S, index_0.
    }
  apply tr_partial_formation.
  apply (tr_formation_weaken _ (var 4)).
  eapply hypothesis; eauto using index_S, index_0.
  }
apply (tr_seq_bind _ (var 3) (var 2)).
  {
  eapply hypothesis; eauto using index_S, index_0.
  }

  {
  simpsub.
  cbn [Nat.add].
  eapply tr_pi_elim'.
    {
    eapply hypothesis; eauto using index_S, index_0.
    simpsub.
    cbn [Nat.add].
    eauto.
    }

    {
    eapply hypothesis; eauto using index_S, index_0.
    }

    {
    simpsub.
    auto.
    }
  }

  {
  apply (tr_formation_weaken _ (var 4)).
  eapply hypothesis; eauto using index_S, index_0.
  }
Qed.


Lemma natTotal_valid : natTotal_obligation.
Proof.
prepare.
intros G m ext0 H.
rewrite -> def_nat in H.
apply tr_nat_total; auto.
Qed.


Lemma natStrict_valid : natStrict_obligation.
Proof.
prepare.
intro G.
rewrite -> def_nat.
apply tr_total_strict.
  {
  apply tr_nattp_formation.
  }

  {
  apply tr_nat_total.
  eapply hypothesis; eauto using index_0.
  }
Qed.


Lemma tr_nattp_uptype :
  forall G, tr G (deq triv triv (uptype nattp)).
Proof.
intros G.
apply tr_mu_uptype.
  {
  apply tr_sumtype_formation.
    {
    apply tr_unittp_istype.
    }
  
    {
    apply tr_hyp_tp.
    apply index_0.
    }
  }

  {
  apply tr_positive_nattp_body.
  }
simpsub.
cbn [Nat.add].
apply tr_sumtype_uptype.
  {
  apply tr_unitary_uptype.
  apply tr_subtype_refl.
  apply tr_unittp_istype.
  }

  {
  eapply (tr_uptype_eta2 _ (var 0) (var 0)).
  eapply hypothesis; eauto using index_0.
  }
Qed.


Lemma natUptype_valid : natUptype_obligation.
Proof.
prepare.
intro G.
rewrite -> def_nat.
apply tr_nattp_uptype.
Qed.


Lemma natAdmiss_valid : natAdmiss_obligation.
Proof.
prepare.
intro G.
rewrite -> def_nat.
apply tr_uptype_admiss.
apply tr_nattp_uptype.
Qed.


Lemma def_total :
  forall a, equiv (app Defs.total a) (sigma (subtype a (partial a)) (pi (subst sh1 a) (halts (var 0)))).
Proof.
intro a.
unfold Defs.total.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Hint Rewrite def_total : prepare.


Lemma total_rhs_formation :
  forall G a,
    tr G (deqtype a a)
    -> tr 
         (hyp_tm (subtype a (partial a)) :: G)
         (deqtype (pi (subst sh1 a) (halts (var 0))) (pi (subst sh1 a) (halts (var 0)))).
Proof.
intros G a Ha.
apply tr_pi_formation.
  {
  eapply (weakening _ [_] []).
    {
    simpsub.
    reflexivity.
    }

    {
    cbn [length].
    simpsub.
    rewrite <- compose_assoc.
    simpsub.
    reflexivity.
    }
  cbn [length].
  simpsub.
  cbn [List.app].
  exact Ha.
  }

  {
  apply (tr_halts_formation _ (subst (sh 2) a)).
  apply (tr_subtype_elim _ (subst (sh 2) a)).
    {
    apply (tr_subtype_eta2 _#3 (var 1) (var 1)).
    eapply hypothesis; eauto using index_S, index_0.
    }

    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }
  }
Qed.


Lemma voidTotal'_valid : voidTotal'_obligation.
Proof.
prepare.
intro G.
unfold Defs.void.
assert (tr (hyp_tm voidtp :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  eapply tr_voidtp_elim.
  eapply hypothesis; eauto using index_0.
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  apply tr_voidtp_istype; auto.
  }

  {
  simpsub.
  apply tr_pi_intro; auto.
  apply tr_voidtp_istype; auto.
  }

  {
  apply total_rhs_formation.
  apply tr_voidtp_istype.
  }
Qed.


Lemma unitTotal'_valid : unitTotal'_obligation.
Proof.
prepare.
intro G.
unfold Defs.unit.
assert (tr (hyp_tm unittp :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  apply tr_unittp_total.
  eapply hypothesis; eauto using index_0.
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  apply tr_unittp_istype; auto.
  }

  {
  simpsub.
  apply tr_pi_intro; auto.
  apply tr_unittp_istype; auto.
  }

  {
  apply total_rhs_formation.
  apply tr_unittp_istype.
  }
Qed.



Lemma boolTotal'_valid : boolTotal'_obligation.
Proof.
prepare.
intro G.
unfold Defs.bool.
assert (tr (hyp_tm booltp :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  apply tr_booltp_total.
  eapply hypothesis; eauto using index_0.
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  apply tr_booltp_istype; auto.
  }

  {
  apply tr_pi_intro; auto.
  apply tr_booltp_istype; auto.
  }

  {
  apply total_rhs_formation.
  apply tr_booltp_istype.
  }
Qed.



Hint Rewrite def_pi : prepare.

Lemma forallTotal'_valid : forallTotal'_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
assert (tr (hyp_tm (pi a b) :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  apply (tr_pi_total _ (subst sh1 a) (subst (under 1 sh1) b)).
  eapply hypothesis; eauto using index_0.
  simpsub.
  reflexivity.
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  apply tr_pi_formation; auto.
  }

  {
  simpsub.
  rewrite -> subst_var0_sh1.
  apply tr_pi_intro; auto.
  apply tr_pi_formation; auto.
  }

  {
  apply total_rhs_formation.
  apply tr_pi_formation; auto.
  }
Qed.


Hint Rewrite def_forallfut : prepare.

Lemma forallfutTotal'_valid : forallfutTotal'_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
assert (tr (hyp_tm (pi (semifut a) b) :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  apply (tr_pi_total _ (subst sh1 (semifut a)) (subst (under 1 sh1) b)).
  eapply hypothesis; eauto using index_0.
  simpsub.
  reflexivity.
  }
assert (tr G (deqtype (pi (semifut a) b) (pi (semifut a) b))) as Hform.
  {
  apply tr_pi_formation; auto.
    {
    apply tr_semifut_formation; auto.
    }
  
    {
    replace (deqtype b b) with (deqtype (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
    2:{
      simpsub.
      rewrite -> subst_var0_sh1; auto.
      }
    apply (tr_semifut_elim_eqtype _ _ _ (subst sh1 a)).
      {
      eapply hypothesis; eauto using index_0.
      }
  
      {
      cbn.
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
      cbn.
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
      rewrite -> subst_var0_sh1.
      exact Hb.
      }
    }
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  }

  {
  simpsub.
  rewrite -> subst_var0_sh1.
  apply tr_pi_intro; auto.
  }

  {
  apply total_rhs_formation; auto.
  }
Qed.


Hint Rewrite def_arrow : prepare.

Lemma arrowTotal'_valid : arrowTotal'_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
assert (tr (hyp_tm (pi a (subst sh1 b)) :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  apply (tr_pi_total _ (subst sh1 a) (subst (sh 2) b)).
  eapply hypothesis; eauto using index_0.
  simpsub.
  reflexivity.
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  apply tr_pi_formation; auto.
  }

  {
  simpsub.
  apply tr_pi_intro; auto.
  apply tr_pi_formation; auto.
  }

  {
  apply total_rhs_formation.
  apply tr_pi_formation; auto.
  }
Qed.


Hint Rewrite def_parametric : prepare.

Lemma parametricTotal'_valid : parametricTotal'_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
assert (tr (hyp_tm (conjoin (pi a b) constfn) :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  apply (tr_pi_total _ (subst sh1 a) (subst (under 1 sh1) b)).
  eapply tr_conjoin_elim1.
  eapply hypothesis; eauto using index_0.
  simpsub.
  reflexivity.
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  apply tr_conjoin_formation.
    {
    apply tr_pi_formation; auto.
    }

    {
    apply (tr_formation_weaken _ nzero).
    apply tr_constfn_formation.
    }
  }

  {
  simpsub.
  rewrite -> subst_var0_sh1.
  apply tr_pi_intro; auto.
  apply tr_conjoin_formation.
    {
    apply tr_pi_formation; auto.
    }

    {
    apply (tr_formation_weaken _ nzero).
    apply tr_constfn_formation.
    }
  }

  {
  apply total_rhs_formation.
  apply tr_conjoin_formation.
    {
    apply tr_pi_formation; auto.
    }

    {
    apply (tr_formation_weaken _ nzero).
    apply tr_constfn_formation.
    }
  }
Qed.


Hint Rewrite def_parametricfut : prepare.

Lemma parametricfutTotal'_valid : parametricfutTotal'_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
assert (tr (hyp_tm (conjoin (pi (semifut a) b) constfn) :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  apply (tr_pi_total _ (subst sh1 (semifut a)) (subst (under 1 sh1) b)).
  eapply tr_conjoin_elim1.
  eapply hypothesis; eauto using index_0.
  simpsub.
  reflexivity.
  }
assert (tr G (deqtype (pi (semifut a) b) (pi (semifut a) b))) as Hform.
  {
  apply tr_pi_formation; auto.
    {
    apply tr_semifut_formation; auto.
    }
  
    {
    replace (deqtype b b) with (deqtype (subst1 (var 0) (subst (dot (var 0) (sh 2)) b)) (subst1 (var 0) (subst (dot (var 0) (sh 2)) b))).
    2:{
      simpsub.
      rewrite -> subst_var0_sh1; auto.
      }
    apply (tr_semifut_elim_eqtype _ _ _ (subst sh1 a)).
      {
      eapply hypothesis; eauto using index_0.
      }
  
      {
      cbn.
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
      cbn.
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
      rewrite -> subst_var0_sh1.
      exact Hb.
      }
    }
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  apply tr_conjoin_formation; auto.
  apply (tr_formation_weaken _ nzero).
  apply tr_constfn_formation.
  }

  {
  simpsub.
  rewrite -> subst_var0_sh1.
  apply tr_pi_intro; auto.
  apply tr_conjoin_formation; auto.
  apply (tr_formation_weaken _ nzero).
  apply tr_constfn_formation.
  }

  {
  apply total_rhs_formation; auto.
  apply tr_conjoin_formation; auto.
  apply (tr_formation_weaken _ nzero).
  apply tr_constfn_formation.
  }
Qed.


Hint Rewrite def_sigma : prepare.

Lemma existsTotal'_valid : existsTotal'_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
assert (tr (hyp_tm (sigma a b) :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  apply (tr_sigma_total _ (subst sh1 a) (subst (under 1 sh1) b)).
  eapply hypothesis; eauto using index_0.
  simpsub.
  reflexivity.
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  apply tr_sigma_formation; auto.
  }

  {
  simpsub.
  rewrite -> subst_var0_sh1.
  apply tr_pi_intro; auto.
  apply tr_sigma_formation; auto.
  }

  {
  apply total_rhs_formation.
  apply tr_sigma_formation; auto.
  }
Qed.


Hint Rewrite def_prod : prepare.

Lemma prodTotal'_valid : prodTotal'_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
assert (tr (hyp_tm (prod a b) :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  apply (tr_prod_total _ (subst sh1 a) (subst sh1 b)).
  eapply hypothesis; eauto using index_0.
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  apply tr_prod_formation; auto.
  }

  {
  simpsub.
  apply tr_pi_intro; auto.
  apply tr_prod_formation; auto.
  }

  {
  apply total_rhs_formation.
  apply tr_prod_formation; auto.
  }
Qed.


Hint Rewrite def_dprod : prepare.

Lemma dprodTotal'_valid : dprodTotal'_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
assert (tr (hyp_tm (sigma a (subst sh1 b)) :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  eapply tr_sigma_total; eauto.
  eapply hypothesis; eauto using index_0.
  simpsub.
  eauto.
  }
assert (tr (hyp_tm a :: G) (deqtype (subst sh1 b) (subst sh1 b))) as Hb'.
  {
  eapply (weakening _ [_] []).
    {
    simpsub.
    auto.
    }
    
    {
    cbn [length].
    simpsub.
    rewrite <- compose_assoc.
    simpsub.
    auto.
    }
  cbn [length].
  simpsub.
  cbn [List.app].
  exact Hb.
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  apply tr_sigma_formation; auto.
  }

  {
  simpsub.
  apply tr_pi_intro; auto.
  apply tr_sigma_formation; auto.
  }

  {
  apply total_rhs_formation.
  apply tr_sigma_formation; auto.
  }
Qed.


Hint Rewrite def_sum : prepare.

Lemma sumTotal'_valid : sumTotal'_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
assert (tr (hyp_tm (sumtype a b) :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  apply (tr_sum_total _ (subst sh1 a) (subst sh1 b)).
  eapply hypothesis; eauto using index_0.
  simpsub.
  reflexivity.
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  apply tr_sumtype_formation; auto.
  }

  {
  simpsub.
  apply tr_pi_intro; auto.
  apply tr_sumtype_formation; auto.
  }

  {
  apply total_rhs_formation.
  apply tr_sumtype_formation; auto.
  }
Qed.


Hint Rewrite def_fut : prepare.

Lemma futureTotal'_valid : futureTotal'_obligation.
Proof.
prepare.
intros G a ext0 Ha.
assert (tr (hyp_tm (fut a) :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  apply (tr_fut_total _ (subst sh1 a)).
  eapply hypothesis; eauto using index_0.
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  apply tr_fut_formation; auto.
  }

  {
  simpsub.
  apply tr_pi_intro; auto.
  apply tr_fut_formation; auto.
  }

  {
  apply total_rhs_formation.
  apply tr_fut_formation; auto.
  }
Qed.


Hint Rewrite def_nat : prepare.

Lemma natTotal'_valid : natTotal'_obligation.
Proof.
prepare.
intro G.
assert (tr (hyp_tm nattp :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  apply tr_nat_total.
  eapply hypothesis; eauto using index_0.
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  apply tr_nattp_formation; auto.
  }

  {
  apply tr_pi_intro; auto.
  apply tr_nattp_formation; auto.
  }

  {
  apply total_rhs_formation.
  apply tr_nattp_formation; auto.
  }
Qed.


Hint Rewrite def_set : prepare.

Lemma setTotal'_valid : setTotal'_obligation.
Proof.
prepare.
intros G a b ext1 m Hb Htot.
assert (tr (hyp_tm (set a b) :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  apply (tr_halts_eta2 _ (app (ppi2 (subst sh1 m)) (var 0)) (app (ppi2 (subst sh1 m)) (var 0))).
  apply (tr_pi_elim' _ (subst sh1 a) (halts (var 0))).
    {
    apply (tr_sigma_elim2' _ (subst sh1 (subtype a (partial a))) (subst (under 1 sh1) (pi (subst sh1 a) (halts (var 0))))).
      {
      eapply (weakening _ [_] []).
        {
        simpsub.
        reflexivity.
        }

        {
        cbn [length].
        simpsub.
        rewrite <- compose_assoc.
        rewrite <- compose_assoc.
        simpsub.
        reflexivity.
        }
      cbn [length].
      simpsub.
      rewrite <- compose_assoc.
      simpsub.
      exact Htot.
      }

      {
      simpsub.
      reflexivity.
      }
    }
    
    {
    apply (tr_set_elim1 _ _ (subst (under 1 sh1) b)).
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    simpsub.
    reflexivity.
    }
  }
assert (tr G (deqtype a a)) as Ha.
  {
  apply (tr_subtype_formation_invert1 _#3 (partial a) (partial a)).
  apply (tr_inhabitation_formation _ (ppi1 m) (ppi1 m)).
  eapply tr_sigma_elim1; eauto.
  }
assert (tr G (deqtype (set a b) (set a b))) as Hset.
  {
  apply (tr_set_formation _#5 (var 0) (var 0)); auto.
    {
    eapply hypothesis; eauto using index_0.
    }
  
    {
    eapply hypothesis; eauto using index_0.
    }
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  }

  {
  simpsub.
  rewrite -> subst_var0_sh1.
  apply tr_pi_intro; auto.
  }

  {
  apply total_rhs_formation; auto.
  }
Qed.


Hint Rewrite def_iset : prepare.

Lemma isetTotal'_valid : isetTotal'_obligation.
Proof.
prepare.
intros G a b ext1 m Hb Htot.
assert (tr (hyp_tm (iset a b) :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  apply (tr_halts_eta2 _ (app (ppi2 (subst sh1 m)) (var 0)) (app (ppi2 (subst sh1 m)) (var 0))).
  apply (tr_pi_elim' _ (subst sh1 a) (halts (var 0))).
    {
    apply (tr_sigma_elim2' _ (subst sh1 (subtype a (partial a))) (subst (under 1 sh1) (pi (subst sh1 a) (halts (var 0))))).
      {
      eapply (weakening _ [_] []).
        {
        simpsub.
        reflexivity.
        }

        {
        cbn [length].
        simpsub.
        rewrite <- compose_assoc.
        rewrite <- compose_assoc.
        simpsub.
        reflexivity.
        }
      cbn [length].
      simpsub.
      rewrite <- compose_assoc.
      simpsub.
      exact Htot.
      }

      {
      simpsub.
      reflexivity.
      }
    }
    
    {
    apply (tr_iset_elim1 _ _ (subst (under 1 sh1) b)).
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    simpsub.
    reflexivity.
    }
  }
assert (tr G (deqtype a a)) as Ha.
  {
  apply (tr_subtype_formation_invert1 _#3 (partial a) (partial a)).
  apply (tr_inhabitation_formation _ (ppi1 m) (ppi1 m)).
  eapply tr_sigma_elim1; eauto.
  }
assert (tr G (deqtype (iset a b) (iset a b))) as Hset.
  {
  apply tr_iset_formation; auto.
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  }

  {
  simpsub.
  rewrite -> subst_var0_sh1.
  apply tr_pi_intro; auto.
  }

  {
  apply total_rhs_formation; auto.
  }
Qed.


Hint Rewrite def_quotient : prepare.


Lemma quotientTotal'_valid : quotientTotal'_obligation.
Proof.
prepare.
intros G a b ext2 ext1 m Hquot Hb Htot.
assert (tr (hyp_tm (quotient a b) :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  apply (tr_quotient_hyp G [] a b triv triv).
    {
    cbn [List.app].
    apply (tr_quotient_hyp_eqtype G [] a b); auto.
    cbn [length].
    simpsub.
    cbn [List.app Nat.add].
    apply (tr_halts_formation_iff _ (subst (sh 3) a)).
      {
      apply (tr_subtype_elim _ (subst (sh 3) a)).
        {
        apply (tr_subtype_eta2 _#3 (ppi1 (subst (sh 3) m)) (ppi1 (subst (sh 3) m))).
        eapply (weakening _ [_; _; _] []).
          {
          simpsub.
          reflexivity.
          }
  
          {
          cbn [length].
          simpsub.
          rewrite <- compose_assoc.
          simpsub.
          reflexivity.
          }
        cbn [length].
        simpsub.
        eapply tr_sigma_elim1; eauto.
        }
      eapply hypothesis; eauto using index_S, index_0.
      }

      {
      apply (tr_subtype_elim _ (subst (sh 3) a)).
        {
        apply (tr_subtype_eta2 _#3 (ppi1 (subst (sh 3) m)) (ppi1 (subst (sh 3) m))).
        eapply (weakening _ [_; _; _] []).
          {
          simpsub.
          reflexivity.
          }
  
          {
          cbn [length].
          simpsub.
          rewrite <- compose_assoc.
          simpsub.
          reflexivity.
          }
        cbn [length].
        simpsub.
        eapply tr_sigma_elim1; eauto.
        }
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      reflexivity.
      }

      {
      simpsub.
      cbn [Nat.add].
      apply (tr_halts_eta2 _ (app (ppi2 (subst (sh 4) m)) (var 2)) (app (ppi2 (subst (sh 4) m)) (var 2))).
      apply (tr_pi_elim' _ (subst (sh 4) a) (halts (var 0))).
        {
        apply (tr_sigma_elim2' _ (subst (sh 4) (subtype a (partial a))) (subst (under 1 (sh 4)) (pi (subst sh1 a) (halts (var 0))))).
          {
          eapply (weakening _ [_; _; _; _] []).
            {
            simpsub.
            reflexivity.
            }
    
            {
            cbn [length].
            simpsub.
            cbn [Nat.add].
            rewrite <- compose_assoc.
            simpsub.
            rewrite <- compose_assoc.
            simpsub.
            reflexivity.
            }
          cbn [length].
          simpsub.
          exact Htot.
          }
    
          {
          simpsub.
          reflexivity.
          }
        }
  
        {
        eapply hypothesis; auto using index_S, index_0.
        simpsub.
        reflexivity.
        }
  
        {
        simpsub.
        reflexivity.
        }
      }

      {
      simpsub.
      cbn [Nat.add].
      apply (tr_halts_eta2 _ (app (ppi2 (subst (sh 4) m)) (var 3)) (app (ppi2 (subst (sh 4) m)) (var 3))).
      apply (tr_pi_elim' _ (subst (sh 4) a) (halts (var 0))).
        {
        apply (tr_sigma_elim2' _ (subst (sh 4) (subtype a (partial a))) (subst (under 1 (sh 4)) (pi (subst sh1 a) (halts (var 0))))).
          {
          eapply (weakening _ [_; _; _; _] []).
            {
            simpsub.
            reflexivity.
            }
    
            {
            cbn [length].
            simpsub.
            cbn [Nat.add].
            rewrite <- compose_assoc.
            simpsub.
            rewrite <- compose_assoc.
            simpsub.
            reflexivity.
            }
          cbn [length].
          simpsub.
          exact Htot.
          }
    
          {
          simpsub.
          reflexivity.
          }
        }
  
        {
        eapply hypothesis; auto using index_S, index_0.
        }
  
        {
        simpsub.
        reflexivity.
        }
      }
    }

    {
    simpsub.
    cbn [List.app].
    apply (tr_halts_eta2 _ (app (ppi2 (subst sh1 m)) (var 0)) (app (ppi2 (subst sh1 m)) (var 0))).
    apply (tr_pi_elim' _ (subst sh1 a) (halts (var 0))).
      {
      apply (tr_sigma_elim2' _ (subst sh1 (subtype a (partial a))) (subst (under 1 sh1) (pi (subst sh1 a) (halts (var 0))))).
        {
        eapply (weakening _ [_] []).
          {
          simpsub.
          reflexivity.
          }
  
          {
          cbn [length].
          simpsub.
          cbn [Nat.add].
          rewrite <- compose_assoc.
          simpsub.
          rewrite <- compose_assoc.
          simpsub.
          reflexivity.
          }
        cbn [length].
        simpsub.
        exact Htot.
        }
  
        {
        simpsub.
        reflexivity.
        }
      }

      {
      eapply hypothesis; auto using index_S, index_0.
      }

      {
      simpsub.
      reflexivity.
      }
    }
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  }

  {
  simpsub.
  cbn [Nat.add].
  simpsub.
  rewrite -> subst_var01_sh2.
  apply tr_pi_intro; auto.
  }

  {
  apply total_rhs_formation; auto.
  }
Qed.


Hint Rewrite def_univ : prepare.

Lemma univTotal'_valid : univTotal'_obligation.
Proof.
prepare.
intros G i ext Hi.
assert (tr (hyp_tm (univ i) :: G) (deq triv triv (halts (var 0)))) as Hhalts.
  {
  apply tr_type_halt.
  apply (tr_formation_weaken _ (subst sh1 i)).
  eapply hypothesis; eauto using index_0.
  }
apply tr_sigma_intro.
  {
  apply tr_total_strict; auto.
  apply tr_univ_formation; auto.
  }

  {
  simpsub.
  apply tr_pi_intro; auto.
  apply tr_univ_formation; auto.
  }

  {
  apply total_rhs_formation.
  apply tr_univ_formation; auto.
  }
Qed.


Hint Rewrite def_sequal : prepare.

Lemma reduceSeqTotal_valid : reduceSeqTotal_obligation.
Proof.
prepare.
intros G a m n ext1 p Hm Ha.
simpsub.
apply tr_seq_halts_sequal.
apply (tr_halts_eta2 _ (app (ppi2 p) m) (app (ppi2 p) m)).
apply (tr_pi_elim' _ a (halts (var 0))); auto.
  {
  apply (tr_sigma_elim2' _ (subtype a (partial a)) (pi (subst sh1 a) (halts (var 0)))); auto.
  simpsub.
  reflexivity.
  }

  {
  simpsub.
  reflexivity.
  }
Qed.


Lemma haltsTotal_valid : haltsTotal_obligation.
Proof.
prepare.
intros G a m ext1 n Hm Ha.
apply (tr_halts_eta2 _ (app (ppi2 n) m) (app (ppi2 n) m)).
eapply tr_pi_elim'.
  {
  eapply tr_sigma_elim2'; eauto.
  simpsub.
  reflexivity.
  }

  {
  auto.
  }

  {
  simpsub.
  reflexivity.
  }
Qed.


Hint Rewrite def_sequal : prepare.

Lemma sequalUnderSeq_valid : sequalUnderSeq_obligation.
Proof.
prepare.
intros G m m' n ext0 Hm.
assert (tr G (deq triv triv (halts m))) as Hhalts.
  {
  apply (tr_active_halts_invert _ _ (seq (var 0) (sequal (var 0) (subst (sh 2) m')))).
    {
    simpsub.
    apply tr_type_halt.
    eapply tr_inhabitation_formation; eauto.
    }

    {
    apply active_seq.
    apply active_var.
    }
  }
assert (tr G (deq triv triv (sequal m m'))) as Hsequal.
  {
  apply (tr_sequal_eta2 _ ext0 ext0).
  apply (tr_eqtype_convert _ _ _ (seq m (sequal (var 0) (subst sh1 m')))); auto.
  apply tr_sequal_eqtype.
  2:{
    eapply tr_inhabitation_formation; eauto.
    }
  replace (sequal m m') with (subst1 m (sequal (var 0) (subst sh1 m'))).
  2:{
    simpsub.
    reflexivity.
    }
  apply tr_seq_halts_sequal; auto.
  }
apply (tr_sequal_trans _ _ (subst1 m n)).
  {
  apply tr_seq_halts_sequal; auto.
  }

  {
  apply tr_sequal_compat; auto.
  }
Qed.
