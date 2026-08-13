
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Tactics.
Require Import Relation.
Require Import Sequence.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.
Require Import Dynamic.
Require Import Promote.
Require Import Hygiene.
Require Import Rules.
Require Import DerivedRules.
Require Defs.
Require Import Obligations.
Require Import Morphism.
Require Import DefsEquiv.
Require Import Equivalence.
Require Import Dots.

Require Import ValidationUtil.
Require Import Equivalences.
Require Import NatLemmas.



Lemma def_symmetrical :
  forall a, equiv (app Defs.symmetrical a) (symmetrical a).
Proof.
intros a.
unfold Defs.symmetrical.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }

  {
  simpsub.
  apply star_refl.
  }
Qed.


Hint Rewrite def_symmetrical def_quotient : prepare.


Lemma tr_symmetrical_eta2 :
  forall G p q m,
    tr G (deq p q (symmetrical m))
    -> tr G (deq triv triv (symmetrical m)).
Proof.
intros G p q m Htr.
assert (tr G (deq p triv (symmetrical m))) as Htr'.
  {
  apply tr_symmetrical_eta.
  apply (tr_transitivity _ _ q); auto.
  apply tr_symmetry; auto.
  }
apply (tr_transitivity _ _ p); auto.
apply tr_symmetry; auto.
Qed.


Lemma symmetricalForm_valid : symmetricalForm_obligation.
Proof.
prepare.
intros G a ext0 Ha.
apply tr_symmetrical_formation; auto.
Qed.


Lemma symmetricalEq_valid : symmetricalEq_obligation.
Proof.
prepare.
intros G a b ext0 Hab.
apply tr_symmetrical_formation; auto.
Qed.


Lemma symmetricalFormUniv_valid : symmetricalFormUniv_obligation.
Proof.
prepare.
intros G a i ext0 Ha.
apply tr_symmetrical_formation_univ; auto.
Qed.


Lemma symmetricalEqUniv_valid : symmetricalEqUniv_obligation.
Proof.
prepare.
intros G a b i ext0 Hab.
apply tr_symmetrical_formation_univ; auto.
Qed.


Lemma symmetricalLeft_valid : symmetricalLeft_obligation.
Proof.
prepare.
intros G1 G2 a c m H.
unfold Defs.triv in H.
apply tr_symmetrical_eta_hyp; auto.
Qed.


Lemma symmetricalTrivialize_valid : symmetricalTrivialize_obligation.
Proof.
prepare.
intros G a ext0 H.
eapply tr_symmetrical_eta2; eauto.
Qed.


Hint Rewrite def_subtype : prepare.

Lemma unitarySymmetrical_valid : unitarySymmetrical_obligation.
Proof.
prepare.
intros G a ext H.
unfold Defs.unit in H.
apply tr_unitary_symmetrical; auto.
Qed.


Lemma unitSymmetrical_valid : unitSymmetrical_obligation.
Proof.
prepare.
unfold Defs.unit.
intro G.
apply tr_unitary_symmetrical.
apply tr_subtype_intro.
  {
  apply tr_unittp_istype.
  }

  {
  apply tr_unittp_istype.
  }

  {
  simpsub.
  eapply hypothesis; eauto using index_0.
  }
Qed.


Lemma voidSymmetrical_valid : voidSymmetrical_obligation.
Proof.
prepare.
unfold Defs.void.
intro G.
apply tr_unitary_symmetrical.
apply tr_subtype_intro.
  {
  apply tr_voidtp_istype.
  }

  {
  apply tr_unittp_istype.
  }

  {
  apply (tr_voidtp_elim _ (var 0) (var 0)).
  eapply hypothesis; eauto using index_0.
  }
Qed.


Lemma integerSymmetrical_valid : integerSymmetrical_obligation.
Proof.
prepare.
unfold Defs.integer.
intro G.
apply tr_nativetp_symmetrical.
Qed.


Lemma symbolSymmetrical_valid : symbolSymmetrical_obligation.
Proof.
prepare.
unfold Defs.symbol.
intro G.
apply tr_nativetp_symmetrical.
Qed.


Lemma natSymmetrical_valid : natSymmetrical_obligation.
Proof.
prepare.
unfold Defs.nat.
intro G.
apply tr_nattp_symmetrical.
Qed.


Lemma boolSymmetrical_valid : boolSymmetrical_obligation.
Proof.
prepare.
unfold Defs.bool.
intro G.
apply tr_booltp_symmetrical.
Qed.


Hint Rewrite def_eq : prepare.

Lemma eqSymmetrical_valid : eqSymmetrical_obligation.
Proof.
prepare.
intros G a m n ext1 ext0 Hm Hn.
apply tr_unitary_symmetrical.
apply tr_subtype_intro.
  {
  apply tr_equal_formation; auto.
  apply (tr_equal_formation_invert1 _#3 m m m m).
  apply (tr_inhabitation_formation _ triv triv).
  apply tr_equal_intro; auto.
  }

  {
  apply tr_unittp_istype.
  }

  {
  simpsub.
  apply tr_equal_elim.
  replace triv with (@subst obj (under 0 sh1) triv) by auto.
  apply (tr_equal_eta_hyp _ []).
  simpsub.
  cbn [List.app].
  apply tr_equal_intro.
  apply tr_unittp_intro.
  }
Qed.


Hint Rewrite def_arrow : prepare.

Lemma arrowSymmetrical_valid : arrowSymmetrical_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply (tr_eqtype_convert _#3 (symmetrical (tarrow a b))).
  {
  apply tr_symmetrical_formation.
  apply tr_tarrow_pi_equal.
    {
    apply tr_symmetrical_formation_invert.
    eapply tr_inhabitation_formation; eauto.
    }

    {
    apply tr_symmetrical_formation_invert.
    eapply tr_inhabitation_formation; eauto.
    }
  }
apply tr_tarrow_symmetrical; eauto using tr_symmetrical_eta2.
Qed.


Hint Rewrite def_pi : prepare.

Lemma forallSymmetrical_valid : forallSymmetrical_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_pi_symmetrical; eauto using tr_symmetrical_eta2.
Qed.


Hint Rewrite def_intersect : prepare.

Lemma intersectSymmetrical_valid : intersectSymmetrical_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_intersect_symmetrical; eauto using tr_symmetrical_eta2.
Qed.


Hint Rewrite def_prod : prepare.

Lemma prodSymmetrical_valid : prodSymmetrical_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_prod_symmetrical; eauto using tr_symmetrical_eta2.
Qed.


Hint Rewrite def_sigma : prepare.

Lemma existsSymmetrical_valid : existsSymmetrical_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_sigma_symmetrical; eauto using tr_symmetrical_eta2.
Qed.


Lemma equiv_symmetrical :
  forall {object} (m m' : @term object),
    equiv m m'
    -> equiv (symmetrical m) (symmetrical m').
Proof.
intros;
apply equiv_compat;
apply mc_oper; repeat2 (apply mcr_cons); [.. | apply mcr_nil]; auto.
Qed.


Hint Rewrite def_sum : prepare.

Lemma sumSymmetrical_valid : sumSymmetrical_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
unfold Defined.sumtype.
apply tr_sigma_symmetrical.
  {
  apply tr_booltp_symmetrical.
  }
apply (tr_symmetrical_eta2 _ (bite (var 0) (subst (under 0 sh1) triv) (subst (under 0 sh1) triv)) (bite (var 0) (subst (under 0 sh1) triv) (subst (under 0 sh1) triv))).
apply (tr_booltp_eta_hyp _ []).
  {
  simpsub.
  cbn [List.app].
  apply (tr_compute _ _ (symmetrical a) _ triv _ triv); auto using equiv_refl.
    {
    apply equiv_symmetrical.
    apply equiv_bite_l.
    }
  eapply tr_symmetrical_eta2; eauto.
  }

  {
  simpsub.
  cbn [List.app].
  apply (tr_compute _ _ (symmetrical b) _ triv _ triv); auto using equiv_refl.
    {
    apply equiv_symmetrical.
    apply equiv_bite_r.
    }
  eapply tr_symmetrical_eta2; eauto.
  }
Qed.


Hint Rewrite def_set : prepare.

Lemma setSymmetrical_valid : setSymmetrical_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_set_symmetrical; eauto using tr_symmetrical_eta2.
Qed.


Hint Rewrite def_quotient : prepare.

Lemma quotientSymmetrical_valid : quotientSymmetrical_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Hquot Hmet.
apply tr_quotient_symmetrical; auto.
eapply tr_symmetrical_eta2; eauto.
Qed.


Hint Rewrite def_partial : prepare.

Lemma partialSymmetrical_valid : partialSymmetrical_obligation.
Proof.
prepare.
intros G a ext H.
apply tr_partial_symmetrical.
eapply tr_symmetrical_eta2; eauto.
Qed.


Lemma tr_tarrow_elim :
  forall G a b m n p q,
    tr G (deq m n (tarrow a b))
    -> tr G (deq p q a)
    -> tr G (deq (app m p) (app n q) b).
Proof.
intros G a b m n p q Hmn Hpq.
apply (tr_pi_elim' _ a (subst sh1 b)); auto.
  {
  apply (tr_eqtype_convert _#3 (tarrow a b)); auto.
  apply tr_tarrow_pi_equal.
    {
    eapply tr_inhabitation_formation; eauto.
    }

    {
    replace (deqtype b b) with (substj (dot p id) (deqtype (subst sh1 b) (subst sh1 b))).
    2:{
      simpsub.
      auto.
      }
    apply (tr_generalize _ a).
      {
      apply (tr_transitivity _ _ q); auto.
      apply tr_symmetry; auto.
      }
    eapply tr_tarrow_formation_invert2; eauto.
    eapply tr_inhabitation_formation; eauto.
    }
  }

  {
  simpsub.
  auto.
  }
Qed.


Hint Rewrite def_pi def_arrow def_eq def_sequal : prepare.


Lemma arrowQuotientCommute_valid : arrowQuotientCommute_obligation.
Proof.
prepare.
unfold Defs.triv.
intros G a b c m n ext9 ext8 ext7 ms mt ext4 ext1 ext0 Ha Hb Hc Hsymm Htrans Htriv Helem Hmn.
assert (tr G (deq m n (quotient 
                         (tarrow a b)
                           (pi (subst (sh 2) a) (subst (dot (app (var 1) (var 0)) (dot (app (var 2) (var 0)) (sh 3))) c))))) as Hmn'.
  {
  apply (tr_arrow_quotient_commute G a b c m n ms mt); auto.
    {
    eapply tr_symmetrical_eta2; eauto.
    }

    {
    eapply tr_symmetrical_eta2; eauto.
    }

    {
    force_exact Htrans.
    f_equal.
    f_equal.
    apply subst_eqsub.
    apply eqsub_dotv.
    apply eqsub_expand_sh.
    }

    {
    eapply tr_sequal_eta2; eauto.
    }
  eapply tr_eqtype_convert; eauto.
    {
    apply tr_eqtype_symmetry.
    apply tr_tarrow_pi_equal; auto.
      {
      apply tr_symmetrical_formation_invert.
      eapply tr_inhabitation_formation; eauto.
      }
    eapply (tr_quotient_formation G b b c c (var 0) (var 0) ms mt); auto.
      {
      apply tr_symmetrical_formation_invert.
      eapply tr_inhabitation_formation; eauto.
      }

      {
      eapply hypothesis; eauto using index_0.
      }
  
      {
      eapply hypothesis; eauto using index_0.
      }
  
      {
      force_exact Htrans.
      f_equal.
      f_equal.
      apply subst_eqsub.
      apply eqsub_dotv.
      apply eqsub_expand_sh.
      }
    }
  }
apply (tr_eqtype_convert _#3 (quotient (tarrow a b) (pi (subst (sh 2) a) (subst (dot (app (var 1) (var 0)) (dot (app (var 2) (var 0)) (sh 3))) c)))); auto.
apply tr_quotient_equal_left.
  {
  apply tr_tarrow_pi_equal; auto.
    {
    apply tr_symmetrical_formation_invert.
    eapply tr_inhabitation_formation; eauto.
    }

    {
    apply tr_symmetrical_formation_invert.
    eapply tr_inhabitation_formation; eauto.
    }
  }

  {
  eapply tr_inhabitation_formation; eauto.
  }
Qed.


Hint Rewrite def_intersect : prepare.


Lemma symmetricalType_valid : symmetricalType_obligation.
Proof.
prepare.
intro G.
unfold Defs.symmetrical.
apply tr_intersect_intro.
  {
  apply tr_nattp_formation.
  }
simpsub.
cbn [Nat.add].
apply tr_pi_intro.
  {
  apply tr_univ_formation.
  unfold Defined.pagetp.
  eapply hypothesis; eauto using index_0.
  }
apply tr_symmetrical_formation_univ.
eapply hypothesis; eauto using index_0.
Qed.
