
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
Require Import SumLemmas.


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


Lemma tr_sumtype_symmetrical :
  forall G a b,
    tr G (deq triv triv (symmetrical a))
    -> tr G (deq triv triv (symmetrical b))
    -> tr G (deq triv triv (symmetrical (Defined.sumtype a b))).
Proof.
intros G a b Ha Hb.
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
  apply equiv_symmetrical.
  apply equiv_bite_l.
  }

  {
  simpsub.
  cbn [List.app].
  apply (tr_compute _ _ (symmetrical b) _ triv _ triv); auto using equiv_refl.
  apply equiv_symmetrical.
  apply equiv_bite_r.
  }
Qed.


Hint Rewrite def_sum : prepare.

Lemma sumSymmetrical_valid : sumSymmetrical_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_sumtype_symmetrical; eauto using tr_symmetrical_eta2.
Qed.


Lemma natSymmetrical_valid : natSymmetrical_obligation.
Proof.
prepare.
unfold Defs.nat.
intro G.
unfold Defined.nattp.
apply tr_mu_symmetrical; auto using tr_positive_nattp_body.
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
simpsub.
cbn [Nat.add].
apply tr_sumtype_symmetrical.
  {
  apply tr_unitary_symmetrical.
  apply tr_subtype_refl.
  apply tr_unittp_istype.
  }

  {
  apply (tr_symmetrical_eta2 _ (var 0) (var 0)).
  eapply hypothesis; eauto using index_0.
  }
Qed.


Hint Rewrite def_set : prepare.

Lemma setSymmetrical_valid : setSymmetrical_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_set_symmetrical; eauto using tr_symmetrical_eta2.
Qed.


Hint Rewrite def_iset : prepare.

Lemma isetSymmetrical_valid : isetSymmetrical_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_iset_symmetrical; eauto using tr_symmetrical_eta2.
Qed.


Hint Rewrite def_quotient : prepare.

Lemma quotientSymmetrical_valid : quotientSymmetrical_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Hquot Hmet.
apply tr_quotient_symmetrical; auto.
eapply tr_symmetrical_eta2; eauto.
Qed.


Hint Rewrite def_fut : prepare.

Lemma futureSymmetrical_valid : futureSymmetrical_obligation.
Proof.
prepare.
intros G a ext H.
apply tr_fut_symmetrical.
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


Hint Rewrite def_mu : prepare.

Lemma muSymmetrical_valid : muSymmetrical_obligation.
Proof.
prepare.
intros G a ext2 ext1 ext0 Ha Hmet Hpos.
rewrite -> def_positive in Hpos.
apply tr_mu_symmetrical; auto.
  {
  eapply tr_positive_eta2; eauto.
  }

  {
  eapply tr_symmetrical_eta2; eauto.
  }
Qed.


Lemma muSymmetricalUniv_valid : muSymmetricalUniv_obligation.
Proof.
prepare.
intros G a i ext3 ext2 ext1 ext0 Hi Ha Hmet Hpos.
rewrite -> def_positive in Hpos.
eapply tr_mu_symmetrical_univ; eauto.
  {
  eapply tr_positive_eta2; eauto.
  }

  {
  eapply tr_symmetrical_eta2; eauto.
  }
Qed.


Hint Rewrite def_rec : prepare.

Lemma recSymmetrical_valid : recSymmetrical_obligation.
Proof.
prepare.
intros G a ext1 ext0 Ha Hmet.
apply tr_rec_symmetrical.
eapply tr_symmetrical_eta2; eauto.
Qed.


Lemma recSymmetricalUniv_valid : recSymmetricalUniv_obligation.
Proof.
prepare.
intros G a i ext2 ext1 ext0 Hi Ha Hmet.
eapply tr_rec_symmetrical_univ; eauto.
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


Lemma tr_quotient_formation_refl :
  forall G a b ms mt,
    tr G (deqtype a a)
    -> tr (hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deqtype b b)
    -> tr (hyp_tm b ::
           hyp_tm (subst sh1 a) ::
           hyp_tm a :: 
           G) 
         (deq ms ms (subst (dot (var 2) (dot (var 1) (sh 3))) b))
    -> tr (hyp_tm (subst (dot (var 1) (dot (var 2) (sh 4))) b) :: 
           hyp_tm (subst sh1 b) ::
           hyp_tm (subst (sh 2) a) :: 
           hyp_tm (subst sh1 a) :: 
           hyp_tm a :: 
           G)
         (deq mt mt (subst (dot (var 2) (dot (var 4) (sh 5))) b))
    -> tr G (deqtype (quotient a b) (quotient a b)).
Proof.
intros G a b ms mt Ha Hb Hsymm Htrans.
apply (tr_quotient_formation _#5 (var 0) (var 0) ms mt); auto.
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  eapply hypothesis; eauto using index_0.
  }
Qed.


Hint Rewrite def_pi def_eq def_sequal : prepare.


Lemma forallQuotientCommute_valid : forallQuotientCommute_obligation.
Proof.
prepare.
unfold Defs.triv.
intros G a b c m n ext7 ext6 ext5 ms mt ext2 ext1 ext0 Ha Hb Hc Hsymm Htrans Htriv Helem Hmn.
assert (tr G (deqtype a a)) as Hwfa.
  {
  apply tr_symmetrical_formation_invert; auto.
  eapply tr_inhabitation_formation; eauto.
  }
assert (tr (hyp_tm a :: G) (deqtype b b)) as Hwfb.
  {
  apply tr_symmetrical_formation_invert; auto.
  eapply tr_inhabitation_formation; eauto.
  }
apply tr_pi_quotient_commute; auto.
  {
  eapply tr_symmetrical_eta2; eauto.
  }

  {
  eapply tr_symmetrical_eta2; eauto.
  }

  {
  apply (tr_quotient_formation _#5 (var 0) (var 0) ms mt); auto.
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

  {
  apply (tr_quotient_formation_refl _#3
           (lam (subst (dot (app (var 1) (var 0))
                          (dot (app (var 2) (var 0))
                             (dot (app (var 3) (var 0))
                                (dot (var 0) (sh 4))))) ms))
           (lam (subst (dot (app (var 1) (var 0))
                          (dot (app (var 2) (var 0))
                             (dot (app (var 3) (var 0))
                                (dot (app (var 4) (var 0))
                                   (dot (app (var 5) (var 0))
                                      (dot (var 0) (sh 6))))))) mt))).
    {
    apply tr_pi_formation; auto.
    }

    {
    apply tr_pi_formation.
      {
      eapply (weakening _ [_; _] []).
        {
        cbn [unlift length].
        simpsub.
        auto.
        }

        {
        cbn [unlift length].
        simpsub.
        auto.
        }
      cbn [unlift length].
      simpsub.
      exact Hwfa.
      }
    unfold deqtype.
    exploit (translate3 G [hyp_tm (subst (sh 2) a); hyp_tm (subst sh1 (pi a b)); hyp_tm (pi a b)] 3
               a (var 0) (var 0)
               b (app (var 2) (var 0)) (app (var 2) (var 0))
               (subst sh1 b) (app (var 1) (var 0)) (app (var 1) (var 0))
               (eqtype c c) triv triv) as H; auto.
      {
      eapply (weakening _ [_] []).
        {
        simpsub.
        auto.
        }

        {
        cbn [length].
        simpsub.
        auto.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      exact Hwfb.
      }

      {
      cbn [List.app].
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      auto.
      }

      {
      cbn [List.app].
      eapply tr_pi_elim'.
        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        auto.
        }

        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        auto.
        }
      simpsub.
      auto.
      }

      {
      cbn [List.app].
      eapply tr_pi_elim'.
        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        auto.
        }

        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        auto.
        }
      simpsub.
      auto.
      }
    }

    {
    simpsub.
    cbn [Nat.add].
    apply tr_pi_intro.
      {
      eapply (weakening _ [_; _; _] []).
        {
        simpsub.
        auto.
        }
  
        {
        cbn [length].
        simpsub.
        auto.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      exact Hwfa.
      }
    exploit (translate4 G 
               [hyp_tm (subst (sh 3) a);
                hyp_tm (pi (subst (sh 2) a) (subst (dot (app (var 1) (var 0)) (dot (app (var 2) (var 0)) (dot (var 0) (sh 3)))) c));
                hyp_tm (subst sh1 (pi a b)); hyp_tm (pi a b)] 4
               a (var 0) (var 0)
               b (app (var 3) (var 0)) (app (var 3) (var 0))
               (subst sh1 b) (app (var 2) (var 0)) (app (var 2) (var 0))
               c (app (var 1) (var 0)) (app (var 1) (var 0))
               (subst (dot (var 2) (dot (var 1) (sh 3))) c) ms ms) as H; auto.
      {
      eapply (weakening _ [_] []).
        {
        simpsub.
        auto.
        }
  
        {
        cbn [length].
        simpsub.
        auto.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      exact Hwfb.
      }
  
      {
      cbn [List.app].
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      auto.
      }
  
      {
      cbn [List.app].
      eapply tr_pi_elim'.
        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        auto.
        }
  
        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        auto.
        }
      simpsub.
      auto.
      }
  
      {
      cbn [List.app].
      eapply tr_pi_elim'.
        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        auto.
        }
  
        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        auto.
        }
      simpsub.
      auto.
      }
  
      {
      cbn [List.app].
      eapply tr_pi_elim'.
        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        auto.
        }
  
        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        auto.
        }
      simpsub.
      auto.
      }
    cbn [List.app] in H.
    simpsubin H.
    exact H.
    }

    {
    simpsub.
    cbn [Nat.add].
    apply tr_pi_intro.
      {
      eapply (weakening _ [_; _; _; _; _] []).
        {
        simpsub.
        auto.
        }
  
        {
        cbn [length].
        simpsub.
        auto.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      exact Hwfa.
      }
    exploit (translate6 G
               [hyp_tm (subst (sh 5) a);
                hyp_tm (pi (subst (sh 4) a) (subst (dot (app (var 2) (var 0)) (dot (app (var 3) (var 0)) (dot (var 0) (sh 5)))) c));
                hyp_tm (pi (subst (sh 3) a) (subst (dot (app (var 2) (var 0)) (dot (app (var 3) (var 0)) (dot (var 0) (sh 4)))) c));
                hyp_tm (pi (subst (sh 2) a) (subst (dot (var 0) (sh 3)) b));
                hyp_tm (pi (subst sh1 a) (subst (dot (var 0) (sh 2)) b));
                hyp_tm (pi a b)] 6
               a (var 0) (var 0)
               b (app (var 5) (var 0)) (app (var 5) (var 0))
               (subst sh1 b) (app (var 4) (var 0)) (app (var 4) (var 0))
               (subst (sh 2) b) (app (var 3) (var 0)) (app (var 3) (var 0))
               (subst sh1 c) (app (var 2) (var 0)) (app (var 2) (var 0))
               (subst (dot (var 1) (dot (var 2) (sh 4))) c) (app (var 1) (var 0)) (app (var 1) (var 0))
               (subst (dot (var 2) (sh 4)) c) mt mt) as H; auto.
      {
      eapply (weakening _ [_] []).
        {
        simpsub.
        auto.
        }
  
        {
        cbn [length].
        simpsub.
        auto.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      exact Hwfb.
      }
  
      {
      eapply (weakening _ [_; _] []).
        {
        simpsub.
        auto.
        }
  
        {
        cbn [length].
        simpsub.
        auto.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      exact Hwfb.
      }
  
      {
      eapply (weakening _ [_] []).
        {
        simpsub.
        auto.
        }
  
        {
        cbn [length].
        simpsub.
        auto.
        }
      cbn [length].
      simpsub.
      cbn [List.app].
      exact Hc.
      }

      {
      unfold deqtype.
      exploit (translate3 G 
                 [hyp_tm (subst sh1 c); hyp_tm (subst (sh 2) b); hyp_tm (subst sh1 b); hyp_tm b; hyp_tm a] 5
                 a (var 4) (var 4)
                 b (var 2) (var 2)
                 (subst sh1 b) (var 1) (var 1)
                 (eqtype c c) triv triv) as H; auto.
        {
        eapply (weakening _ [_] []).
          {
          simpsub.
          auto.
          }
    
          {
          cbn [length].
          simpsub.
          auto.
          }
        cbn [length].
        simpsub.
        cbn [List.app].
        exact Hwfb.
        }

        {
        eapply hypothesis; eauto using index_S, index_0.
        }

        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        setoid_rewrite <- (subst_var0_sh1 _ b) at 2.
        simpsub.
        auto.
        }

        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        setoid_rewrite <- (subst_var0_sh1 _ b) at 2.
        simpsub.
        auto.
        }
      simpsubin H.
      force_exact H.
      f_equal.
      f_equal.
      f_equal.
        {
        apply subst_eqsub.
        apply eqsub_dotv.
        apply eqsub_dotv.
        apply eqsub_symm.
        apply eqsub_expand_sh.
        }

        {
        apply subst_eqsub.
        apply eqsub_dotv.
        apply eqsub_dotv.
        apply eqsub_symm.
        apply eqsub_expand_sh.
        }
      }

      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      auto.
      }

      {
      eapply tr_pi_elim'.
        {
        eapply hypothesis; eauto 6 using index_S, index_0.
        simpsub.
        cbn [Nat.add].
        auto.
        }

        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        cbn [Nat.add].
        auto.
        }
      simpsub.
      auto.
      }

      {
      eapply tr_pi_elim'.
        {
        eapply hypothesis; eauto 6 using index_S, index_0.
        simpsub.
        cbn [Nat.add].
        auto.
        }

        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        cbn [Nat.add].
        auto.
        }
      simpsub.
      auto.
      }

      {
      eapply tr_pi_elim'.
        {
        eapply hypothesis; eauto 6 using index_S, index_0.
        simpsub.
        cbn [Nat.add].
        auto.
        }

        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        cbn [Nat.add].
        auto.
        }
      simpsub.
      auto.
      }

      {
      eapply tr_pi_elim'.
        {
        eapply hypothesis; eauto 6 using index_S, index_0.
        simpsub.
        cbn [Nat.add].
        auto.
        }

        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        cbn [Nat.add].
        auto.
        }
      simpsub.
      auto.
      }

      {
      eapply tr_pi_elim'.
        {
        eapply hypothesis; eauto 6 using index_S, index_0.
        simpsub.
        cbn [Nat.add].
        auto.
        }

        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        cbn [Nat.add].
        auto.
        }
      simpsub.
      auto.
      }
    simpsubin H.
    cbn [List.app] in H.
    exact H.
    }
  }

  {
  apply (tr_sequal_eta2 _ ext1 ext1).
  exact Helem.
  }
Qed.


Hint Rewrite def_prod : prepare.


Lemma quotientStrengthenSequalOf_valid : quotientStrengthenSequalOf_obligation.
Proof.
prepare.
intros G a b c f g m ext5 ext4 ext3 ext2 ext1 ext0 Hb Hc Hab Hf Hg Hfgm.
assert (tr G (deqtype a a)) as Ha.
  {
  apply (tr_quotient_formation_invert _ _ _ b b).
  eapply tr_inhabitation_formation; eauto.
  }
apply tr_quotient_strengthen_sequal; auto.
  {
  apply (tr_eqtype_convert _ _ _ (pi a (subst sh1 c))); auto.
  apply tr_eqtype_symmetry.
  apply tr_tarrow_pi_equal; auto.
  }

  {
  apply (tr_eqtype_convert _ _ _ (pi a (subst sh1 c))); auto.
  apply tr_eqtype_symmetry.
  apply tr_tarrow_pi_equal; auto.
  }

  {
  eapply tr_sequal_eta2; eauto.
  }

  {
  eapply tr_sequal_eta2; eauto.
  }
Qed.


Lemma quotientStrengthenSequalEq_valid : quotientStrengthenSequalEq_obligation.
Proof.
prepare.
intros G a b c f g m n ext6 ext5 ext4 ext3 ext2 ext1 ext0 Hb Hc Hab Hf Hg Hfgm Hfgn.
assert (tr G (deqtype a a)) as Ha.
  {
  apply (tr_quotient_formation_invert _ _ _ b b).
  eapply tr_inhabitation_formation; eauto.
  }
apply tr_quotient_strengthen_sequal; auto.
  {
  apply (tr_eqtype_convert _ _ _ (pi a (subst sh1 c))); auto.
  apply tr_eqtype_symmetry.
  apply tr_tarrow_pi_equal; auto.
  }

  {
  apply (tr_eqtype_convert _ _ _ (pi a (subst sh1 c))); auto.
  apply tr_eqtype_symmetry.
  apply tr_tarrow_pi_equal; auto.
  }

  {
  eapply tr_sequal_eta2; eauto.
  }

  {
  eapply tr_sequal_eta2; eauto.
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
