
Require Import Coq.Lists.List.

Require Import Tactics.
Require Import Syntax.
Require Import Rules.
Require Import MapTerm.
Require Import SimpSub.
Require Import Promote.
Require Import Judgement.
Require Import Hygiene.
Require Import SoundAll.
Require Import SoundEqtype.
Require Import SoundEqual.
Require Import SoundExist.
Require Import SoundFut.
Require Import SoundGuard.
Require Import SoundHyp.
Require Import SoundKuniv.
Require Import SoundMisc.
Require Import SoundMu.
Require Import SoundPi.
Require Import SoundPositive.
Require Import SoundQuotient.
Require Import SoundRec.
Require Import SoundSet.
Require Import SoundSigma.
Require Import SoundSimple.
Require Import SoundSubstitution.
Require Import SoundSubtype.
Require Import SoundStructural.
Require Import SoundUniv.
Require Import SoundWtype.
Require Import Shut.


Theorem soundness :
  forall G J, tr G J -> pseq G J.
Proof.
intros G J H.
induct H.
intros; eapply sound_hyp_tm; eauto; done.
intros; eapply sound_hyp_tp; eauto; done.
intros; eapply sound_pi_formation; eauto; done.
intros; eapply sound_pi_formation_univ; eauto; done.
intros; eapply sound_pi_intro; eauto; done.
intros; eapply sound_pi_elim; eauto; done.
intros; eapply sound_pi_eta; eauto; done.
intros; eapply sound_pi_ext; eauto; done.
intros; eapply sound_arrow_kind_formation; eauto; done.
intros; eapply sound_arrow_formation; eauto; done.
intros; eapply sound_arrow_formation_univ; eauto; done.
intros; eapply sound_arrow_pi_equal; eauto; done.
intros; eapply sound_arrow_pi_equal_univ; eauto; done.
intros; eapply sound_arrow_eta; eauto; done.
intros; eapply sound_karrow_kind_formation; eauto; done.
intros; eapply sound_karrow_formation; eauto; done.
intros; eapply sound_karrow_formation_univ; eauto; done.
intros; eapply sound_karrow_pi_equal; eauto; done.
intros; eapply sound_karrow_pi_equal_univ; eauto; done.
intros; eapply sound_arrow_karrow_equal; eauto; done.
intros; eapply sound_arrow_karrow_equal_univ; eauto; done.
intros; eapply sound_karrow_eta; eauto; done.
intros; eapply sound_pi_formation_invert1; eauto; done.
intros; eapply sound_pi_formation_invert2; eauto; done.
intros; eapply sound_arrow_formation_invert1; eauto; done.
intros; eapply sound_arrow_formation_invert2; eauto; done.
intros; eapply sound_karrow_formation_invert1; eauto; done.
intros; eapply sound_karrow_formation_invert2; eauto; done.
intros; eapply sound_intersect_formation; eauto; done.
intros; eapply sound_intersect_formation_univ; eauto; done.
intros; eapply sound_intersect_intro; eauto; done.
intros; eapply sound_intersect_elim; eauto; done.
intros; eapply sound_intersect_formation_invert1; eauto; done.
intros; eapply sound_intersect_formation_invert2; eauto; done.
intros; eapply sound_sigma_formation; eauto; done.
intros; eapply sound_sigma_formation_univ; eauto; done.
intros; eapply sound_sigma_intro; eauto; done.
intros; eapply sound_sigma_elim1; eauto; done.
intros; eapply sound_sigma_elim2; eauto; done.
intros; eapply sound_sigma_eta; eauto; done.
intros; eapply sound_sigma_eta_hyp; eauto; done.
intros; eapply sound_sigma_ext; eauto; done.
intros; eapply sound_prod_kind_formation; eauto; done.
intros; eapply sound_prod_formation; eauto; done.
intros; eapply sound_prod_formation_univ; eauto; done.
intros; eapply sound_prod_sigma_equal; eauto; done.
intros; eapply sound_prod_sigma_equal_univ; eauto; done.
intros; eapply sound_prod_elim1; eauto; done.
intros; eapply sound_prod_elim2; eauto; done.
intros; eapply sound_sigma_formation_invert1; eauto; done.
intros; eapply sound_sigma_formation_invert2; eauto; done.
intros; eapply sound_prod_formation_invert1; eauto; done.
intros; eapply sound_prod_formation_invert2; eauto; done.
intros; eapply sound_fut_kind_formation; eauto; done.
intros; eapply sound_fut_formation; eauto; done.
intros; eapply sound_fut_formation_univ; eauto; done.
intros; eapply sound_fut_intro; eauto; done.
intros; eapply sound_fut_elim; eauto; done.
intros; eapply sound_fut_elim_eqtype; eauto; done.
intros; eapply sound_fut_eta; eauto; done.
intros; eapply sound_fut_eta_hyp; eauto; done.
intros; eapply sound_fut_ext; eauto; done.
intros; eapply sound_rec_kind_formation; eauto; done.
intros; eapply sound_rec_formation; eauto; done.
intros; eapply sound_rec_formation_univ; eauto; done.
intros; eapply sound_rec_unroll; eauto; done.
intros; eapply sound_rec_unroll_univ; eauto; done.
intros; eapply sound_rec_bisim; eauto; done.
intros; eapply sound_voidtp_formation; eauto; done.
intros; eapply sound_voidtp_elim; eauto; done.
intros; eapply sound_unittp_kind_formation; eauto; done.
intros; eapply sound_unittp_formation; eauto; done.
intros; eapply sound_unittp_intro; eauto; done.
intros; eapply sound_unittp_eta; eauto; done.
intros; eapply sound_unittp_eta_hyp; eauto; done.
intros; eapply sound_booltp_formation; eauto; done.
intros; eapply sound_booltp_intro_btrue; eauto; done.
intros; eapply sound_booltp_intro_bfalse; eauto; done.
intros; eapply sound_booltp_elim; eauto; done.
intros; eapply sound_booltp_elim_eqtype; eauto; done.
intros; eapply sound_booltp_eta_hyp; eauto; done.
intros; eapply sound_wt_formation; eauto; done.
intros; eapply sound_wt_formation_univ; eauto; done.
intros; eapply sound_wt_elim; eauto; done.
intros; eapply sound_wt_subtype_sigma; eauto; done.
intros; eapply sound_wt_sigma_subtype; eauto; done.
intros; eapply sound_wt_formation_inv1; eauto; done.
intros; eapply sound_wt_formation_inv2; eauto; done.
intros; eapply sound_all_formation; eauto; done.
intros; eapply sound_all_formation_univ; eauto; done.
intros; eapply sound_all_intro; eauto; done.
intros; eapply sound_all_elim; eauto; done.
intros; eapply sound_alltp_formation; eauto; done.
intros; eapply sound_alltp_intro; eauto; done.
intros; eapply sound_alltp_elim; eauto; done.
intros; eapply sound_exist_formation; eauto; done.
intros; eapply sound_exist_formation_univ; eauto; done.
intros; eapply sound_exist_intro; eauto; done.
intros; eapply sound_exist_elim; eauto; done.
intros; eapply sound_exist_elim_eqtype; eauto; done.
intros; eapply sound_mu_formation; eauto; done.
intros; eapply sound_mu_formation_univ; eauto; done.
intros; eapply sound_mu_roll; eauto; done.
intros; eapply sound_mu_unroll; eauto; done.
intros; eapply sound_mu_roll_univ; eauto; done.
intros; eapply sound_mu_unroll_univ; eauto; done.
intros; eapply sound_mu_ind; eauto; done.
intros; eapply sound_mu_ind_univ; eauto; done.
intros; eapply sound_positive_algorithm; eauto; done.
intros; eapply sound_positive_eta; eauto; done.
intros; eapply sound_negative_algorithm; eauto; done.
intros; eapply sound_negative_eta; eauto; done.
intros; eapply sound_equal_formation; eauto; done.
intros; eapply sound_equal_formation_univ; eauto; done.
intros; eapply sound_equal_intro; eauto; done.
intros; eapply sound_equal_elim; eauto; done.
intros; eapply sound_equal_eta; eauto; done.
intros; eapply sound_equal_eta_hyp; eauto; done.
intros; eapply sound_equal_formation_invert1; eauto; done.
intros; eapply sound_equal_formation_invert1_univ; eauto; done.
intros; eapply sound_equal_formation_invert2; eauto; done.
intros; eapply sound_equal_formation_invert3; eauto; done.
intros; eapply sound_set_formation; eauto; done.
intros; eapply sound_set_formation_univ; eauto; done.
intros; eapply sound_set_intro; eauto; done.
intros; eapply sound_set_elim1; eauto; done.
intros; eapply sound_set_elim2; eauto; done.
intros; eapply sound_set_hyp_weaken; eauto; done.
intros; eapply sound_set_formation_invert; eauto; done.
intros; eapply sound_squash_idem; eauto; done.
intros; eapply sound_quotient_formation; eauto; done.
intros; eapply sound_quotient_formation_univ; eauto; done.
intros; eapply sound_quotient_intro; eauto; done.
intros; eapply sound_quotient_elim; eauto; done.
intros; eapply sound_quotient_elim_eqtype; eauto; done.
(* For some reason eapply doesn't work on this one. *)
{
intros G a b c m n p.
intros.
apply (sound_descent G a b c m n p); auto.
}
intros; eapply sound_quotient_hyp; eauto; done.
intros; eapply sound_quotient_hyp_with_refl; eauto; done.
intros; eapply sound_quotient_hyp_eqtype; eauto; done.
intros; eapply sound_quotient_hyp_eq; eauto; done.
intros; eapply sound_quotient_hyp_eq_dep; eauto; done.
intros; eapply sound_quotient_formation_invert; eauto; done.
intros; eapply sound_guard_formation; eauto; done.
intros; eapply sound_guard_formation_univ; eauto; done.
intros; eapply sound_guard_sat_eq; eauto; done.
intros; eapply sound_guard_intro; eauto; done.
intros; eapply sound_guard_elim; eauto; done.
intros; eapply sound_univ_kind_formation; eauto; done.
intros; eapply sound_univ_formation; eauto; done.
intros; eapply sound_univ_formation_univ; eauto; done.
intros; eapply sound_univ_cumulative; eauto; done.
intros; eapply sound_formation_weaken; eauto; done.
intros; eapply sound_formation_strengthen; eauto; done.
intros; eapply sound_univ_formation_invert; eauto; done.
intros; eapply sound_kuniv_formation; eauto; done.
intros; eapply sound_kuniv_formation_univ; eauto; done.
intros; eapply sound_kuniv_weaken; eauto; done.
intros; eapply sound_kuniv_formation_invert; eauto; done.
intros; eapply sound_eqtype_formation; eauto; done.
intros; eapply sound_eqtype_formation_univ; eauto; done.
intros; eapply sound_eqtype_convert; eauto; done.
intros; eapply sound_eqtype_convert_hyp; eauto; done.
intros; eapply sound_eqtype_symmetry; eauto; done.
intros; eapply sound_eqtype_transitivity; eauto; done.
intros; eapply sound_eqtype_eta; eauto; done.
intros; eapply sound_eqtype_eta_hyp; eauto; done.
intros; eapply sound_eqtype_formation_invert1; eauto; done.
intros; eapply sound_eqtype_formation_invert2; eauto; done.
intros; eapply sound_subtype_formation; eauto; done.
intros; eapply sound_subtype_formation_univ; eauto; done.
intros; eapply sound_subtype_intro; eauto; done.
intros; eapply sound_subtype_elim; eauto; done.
intros; eapply sound_subtype_eta; eauto; done.
intros; eapply sound_subtype_eta_hyp; eauto; done.
intros; eapply sound_subtype_convert_hyp; eauto; done.
intros; eapply sound_subtype_formation_invert1; eauto; done.
intros; eapply sound_subtype_formation_invert2; eauto; done.
intros; eapply sound_substitution; eauto; done.
intros; eapply sound_substitution_simple; eauto; done.
intros; eapply sound_strengthen_context; eauto; done.
intros; eapply sound_generalize; eauto; done.
intros; eapply sound_generalize_tp; eauto; done.
intros; eapply sound_generalize_eq; eauto; done.
intros; eapply sound_generalize_eq_type; eauto; done.
intros; eapply sound_compute; eauto; done.
intros; eapply sound_compute_hyp; eauto; done.
intros; eapply sound_symmetry; eauto; done.
intros; eapply sound_transitivity; eauto; done.
intros; eapply sound_weakening; eauto; done.
intros; eapply sound_contraction; eauto; done.
intros; eapply sound_exchange; eauto; done.
intros; eapply sound_inhabitation_formation; eauto; done.
Qed.


Corollary consistency :
  forall m n, tr nil (deq m n voidtp) -> False.
Proof.
intros m n Htr.
so (soundness _ _ Htr) as Hseq.
clear Htr.
destruct Hseq as (i & H).
so (H i (le_refl _)) as Hseq; clear H.
cbn in Hseq.
revert m n Hseq.
induct i.

(* 0 *)
{
intros m n Hseq.
cbn in Hseq.
invertc Hseq; intro Hseq.
so (Hseq 0 id id (pwctx_nil _ _)) as (R & Hint & _ & Hmem & _).
simpsubin Hint.
invert (Semantics.basic_value_inv _#6 Dynamic.value_voidtp Hint).
intros <-.
destruct Hmem.
}

(* S *)
{
intros i IH.
intros m n Hseq.
cbn in Hseq.
so (sound_generalize_pre _#4 (sound_unittp_intro_pre _) Hseq) as H.
simpsubin H.
eapply IH; eauto.
}
Qed.
