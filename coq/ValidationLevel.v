
Require Import Coq.Setoids.Setoid.
Require Import Coq.Relations.Relation_Definitions.

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
Require Import DerivedRules.
Require Defs.
Require Import Obligations.
Require Import Morphism.
Require Import DefsEquiv.
Require Import Equivalence.
Require Import Equivalences.
Require Import Dots.

Require Import ValidationUtil.
Require Import Defined.
Require Import SumLemmas.
Require Import NatLemmas.
Require Import LevelLemmas.
Require Import PageCode.



Add Parametric Morphism object : (@natmax object)
  with signature equiv ==> equiv ==> equiv
  as equiv_natmax.
Proof.
intros m1 m1' H1 m2 m2' H2.
unfold natmax.
rewrite H1, H2.
apply equiv_refl.
Qed.



Lemma def_lmax :
  forall m n,
    equiv (app (app Defs.lmax m) n) (natmax m n).
Proof.
intros m n.
unfold Defs.lmax.
unfold natmax.
unfold natcase.
simpsub.
apply equiv_app; auto using equiv_refl.
apply equiv_app; auto using equiv_refl.
apply equiv_app; auto using equiv_refl.
apply equiv_lam.
apply equiv_lam.
apply equiv_lam.
rewrite -> def_inr.
apply equiv_refl.
Qed.


Hint Rewrite def_level def_lzero def_lsucc def_lmax : prepare.



Lemma levelForm_valid : levelForm_obligation.
Proof.
prepare.
intros G.
apply tr_nattp_formation.
Qed.
 

Lemma levelEq_valid : levelEq_obligation.
Proof.
prepare.
intros G.
apply tr_nattp_formation.
Qed.


Lemma levelFormUniv_valid : levelFormUniv_obligation.
Proof.
prepare.
intros G i ext0 Hi.
apply (tr_univ_cumulative _ nzero).
  {
  apply tr_nattp_formation_univ.
  }

  {
  unfold pagetp.
  exact Hi.
  }

  {
  rewrite -> leqpagetp_nzero_equiv.
  apply tr_unittp_intro.
  }
Qed.
 

Lemma levelEqUniv_valid : levelEqUniv_obligation.
Proof.
prepare.
intros G i ext0 Hi.
apply (tr_univ_cumulative _ nzero).
  {
  apply tr_nattp_formation_univ.
  }

  {
  unfold pagetp.
  exact Hi.
  }

  {
  rewrite -> leqpagetp_nzero_equiv.
  apply tr_unittp_intro.
  }
Qed.


Lemma tr_lleq_formation_univ :
  forall G i i' j j',
    tr G (deq i i' nattp)
    -> tr G (deq j j' nattp)
    -> tr G (deq (app (app Defs.lleq i) j) (app (app Defs.lleq i') j') (univ nzero)).
Proof.
intros G i i' j j' Hi Hj.
rewrite -> !def_lleq.
apply tr_intersect2_formation_univ.
  {
  apply tr_leqtp_formation_univ; auto.
  }
apply tr_intersect2_formation_univ.
  {
  apply tr_equal_formation_univ; auto.
  apply tr_nattp_formation_univ.
  }

  {
  apply tr_equal_formation_univ; auto.
  apply tr_nattp_formation_univ.
  }
Qed.


Lemma lleqForm_valid : lleqForm_obligation.
Proof.
prepare.
intros G i j ext1 ext0 Hi Hj.
apply (tr_formation_weaken _ nzero).
apply tr_lleq_formation_univ; auto.
Qed.


Lemma lleqEq_valid : lleqEq_obligation.
Proof.
prepare.
intros G i i' j j' ext1 ext0 Hi Hj.
apply (tr_formation_weaken _ nzero).
apply tr_lleq_formation_univ; auto.
Qed.


Lemma lleqFormUniv_valid : lleqFormUniv_obligation.
Proof.
prepare.
intros G i j k ext2 ext1 ext0 Hi Hj Hk.
apply (tr_univ_cumulative _ nzero).
  {
  apply tr_lleq_formation_univ; auto.
  }

  {
  exact Hk.
  }

  {
  rewrite -> leqpagetp_nzero_equiv.
  apply tr_unittp_intro.
  }
Qed.


Lemma lleqEqUniv_valid : lleqEqUniv_obligation.
Proof.
prepare.
intros G i i' j j' k ext2 ext1 ext0 Hi Hj Hk.
apply (tr_univ_cumulative _ nzero).
  {
  apply tr_lleq_formation_univ; auto.
  }

  {
  exact Hk.
  }

  {
  rewrite -> leqpagetp_nzero_equiv.
  apply tr_unittp_intro.
  }
Qed.


Lemma lzeroLevel_valid : lzeroLevel_obligation.
Proof.
prepare.
intros G.
apply tr_nzero_nattp.
Qed.


Lemma lsuccLevel_valid : lsuccLevel_obligation.
Proof.
prepare.
intros G M ext0 H.
apply tr_nsucc_nattp; auto.
Qed.


Lemma lsuccEq_valid : lsuccEq_obligation.
Proof.
prepare.
intros G M N ext0 H.
apply tr_nsucc_nattp; auto.
Qed.


Lemma unroll_natmax :
  forall m n,
    @equiv obj
      (natmax m n)
      (natcase m
         n
         (natcase (subst sh1 n)
            (subst sh1 m)
            (nsucc (natmax (var 1) (var 0))))).
Proof.
intros m n.
apply steps_equiv.
unfold natmax.
eapply star_trans.
  {
  apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
  eapply star_trans.
    {
    apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
    eapply star_trans.
      {
      apply theta_fix.
      }
    apply star_one.
    apply step_app2.
    }
  simpsub.
  cbn [Nat.add].
  apply star_one.
  apply step_app2.
  }
simpsub.
cbn [Nat.add].
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
cbn [Nat.add].
apply star_refl.
Qed.


Lemma tr_natmax_nattp_of :
  forall G m n,
    tr G (deq m m nattp)
    -> tr G (deq n n nattp)
    -> tr G (deq (natmax m n) (natmax m n) nattp).
Proof.
intros G m n Hm Hn.
apply tr_equal_elim.
apply (tr_equal_eta2 _#4 (app (lam triv) n) (app (lam triv) n)).
apply (tr_pi_elim' _ nattp (equal nattp (natmax (subst sh1 m) (var 0)) (natmax (subst sh1 m) (var 0)))); auto. 
2:{
  simpsub.
  auto.
  }
apply tr_equal_elim.
apply (nat_induction _ (equal (pi nattp (equal nattp (natmax (var 1) (var 0)) (natmax (var 1) (var 0)))) (lam triv) (lam triv)) m); auto.
3:{
  simpsub.
  auto.
  }

  {
  simpsub.
  apply tr_equal_intro.
  apply tr_pi_intro; auto using tr_nattp_formation.
  apply tr_equal_intro.
  rewrite -> unroll_natmax.
  simpsub.
  cbn [Nat.add].
  rewrite -> natcase_zero.
  eapply hypothesis; eauto using index_0.
  }

  {
  simpsub.
  cbn [Nat.add].
  apply tr_equal_intro.
  apply tr_pi_intro; auto using tr_nattp_formation.
  setoid_rewrite -> unroll_natmax at 3 4.
  rewrite -> !natcase_succ.
  simpsub.
  cbn [Nat.add].
  apply (tr_nattp_eta_hyp_triv _ []).
    {
    simpsub.
    cbn [List.app Nat.add].
    apply tr_equal_intro.
    rewrite -> !natcase_zero.
    apply tr_nsucc_nattp.
    apply (tr_subtype_elim _ (var 3)).
      {
      apply (tr_subtype_eta2 _#3 (var 1) (var 1)).
      eapply hypothesis; eauto using index_0, index_S.
      }
    eapply hypothesis; eauto using index_0, index_S.
    }
  cbn [length].
  simpsub.
  cbn [Nat.add List.app].
  rewrite -> natcase_succ.
  simpsub.
  cbn [Nat.add].
  apply tr_equal_intro.
  apply tr_nsucc_nattp.
  apply tr_equal_elim.
  apply (tr_equal_eta2 _#4 (app (lam triv) (var 0)) (app (lam triv) (var 0))).
  apply (tr_pi_elim' _ nattp (equal nattp (natmax (var 4) (var 0)) (natmax (var 4) (var 0)))).
  3:{
    simpsub.
    auto.
    }
  2:{
    eapply hypothesis; eauto using index_0.
    }
  apply tr_equal_elim.
  eapply (tr_equal_eta2 _#4 (app (var 1) (var 3)) (app (var 1) (var 3))).
  eapply tr_pi_elim'.
    {
    eapply hypothesis; eauto using index_0, index_S.
    simpsub.
    cbn [Nat.add].
    reflexivity.
    }

    {
    eapply hypothesis; eauto using index_0, index_S.
    }
    
    {
    simpsub.
    auto.
    }
  }
Qed.


Lemma tr_natmax_nattp :
  forall G m n p q,
    tr G (deq m p nattp)
    -> tr G (deq n q nattp)
    -> tr G (deq (natmax m n) (natmax p q) nattp).
Proof.
intros G m n p q Hmp Hnq.
cut (tr G (deq (app (app (lam (lam (natmax (var 1) (var 0)))) m) n) (app (app (lam (lam (natmax (var 1) (var 0)))) p) q) nattp)).
  {
  intro H.
  rewrite -> equiv_beta in H.
  simpsubin H.
  rewrite -> equiv_beta in H.
  simpsubin H.
  rewrite -> equiv_beta in H.
  simpsubin H.
  rewrite -> equiv_beta in H.
  simpsubin H.
  exact H.
  }
apply (tr_pi_elim2' _ nattp nattp nattp); auto.
apply tr_pi_intro; auto using tr_nattp_formation.
apply tr_pi_intro; auto using tr_nattp_formation.
apply tr_natmax_nattp_of.
  {
  eapply hypothesis; eauto using index_0, index_S.
  }

  {
  eapply hypothesis; eauto using index_0, index_S.
  }
Qed.


Lemma tr_natmax_lub :
  forall G m n p,
    tr G (deq m m nattp)
    -> tr G (deq n n nattp)
    -> tr G (deq p p nattp)
    -> tr G (deq triv triv (app (app leqtp m) p))
    -> tr G (deq triv triv (app (app leqtp n) p))
    -> tr G (deq triv triv (app (app leqtp (natmax m n)) p)).
Proof.
intros G m n p Hm Hn Hp Hmp Hnp.
apply (tr_leqtp_eta2 _ _ _ (app (app (app (app (lam (lam (lam (lam triv)))) n) p) triv) triv) (app (app (app (app (lam (lam (lam (lam triv)))) n) p) triv) triv)); auto.
  {
  apply tr_natmax_nattp; auto.
  }
eapply (tr_pi_elim4' _ nattp nattp (app (app leqtp (subst (sh 2) m)) (var 0)) (app (app leqtp (var 2)) (var 1)) (app (app leqtp (natmax (subst (sh 4) m) (var 3))) (var 2))); auto.
2:{
  simpsub.
  auto.
  }

2:{
  simpsub.
  auto.
  }

2:{
  simpsub.
  auto.
  }
apply tr_equal_elim.
apply (nat_induction _ 
         (equal 
            (pi nattp
               (pi nattp
                  (pi (app (app leqtp (var 2)) (var 0))
                     (pi (app (app leqtp (var 2)) (var 1))
                        (app (app leqtp (natmax (var 4) (var 3))) (var 2))))))
            (lam (lam (lam (lam triv))))
            (lam (lam (lam (lam triv)))))
         m); auto.
3:{
  simpsub.
  auto.
  }

  {
  simpsub.
  apply tr_equal_intro.
  cbn [Nat.add].
  apply tr_pi_intro; auto using tr_nattp_formation.
  apply tr_pi_intro; auto using tr_nattp_formation.
  apply tr_pi_intro.
    {
    apply tr_leqtp_formation; eauto using tr_nzero_nattp, hypothesis, index_0.
    }
  apply tr_pi_intro.
    {
    apply tr_leqtp_formation; eauto using hypothesis, index_0, index_S.
    }
  rewrite -> unroll_natmax.
  rewrite -> natcase_zero.
  eapply (tr_leqtp_eta2 _#3 (var 0)); eauto using hypothesis, index_0, index_S.
  }

  {
  simpsub.
  cbn [Nat.add].
  apply tr_equal_intro.
  apply tr_pi_intro; auto using tr_nattp_formation.
  apply tr_pi_intro; auto using tr_nattp_formation.
  apply tr_pi_intro.
    {
    apply tr_leqtp_formation; eauto using hypothesis, index_0.
    apply tr_nsucc_nattp; auto.
      apply (tr_subtype_elim _ (var 5)).
        {
        apply (tr_subtype_eta2 _#3 (var 3) (var 3)); eauto using hypothesis, index_0, index_S.
        }
      eapply hypothesis; eauto using index_0, index_S.
    }
  apply tr_pi_intro.
    {
    apply tr_leqtp_formation; eauto using hypothesis, index_0, index_S.
    }
  apply (tr_nattp_eta_hyp_triv _ [_; _; _]).
    {
    cbn [length].
    simpsub.
    cbn [Nat.add length].
    simpsub.
    cbn [List.app Nat.add].
    setoid_rewrite -> unroll_natmax at 2.
    rewrite -> natcase_succ.
    simpsub.
    rewrite -> natcase_zero.
    cbn [Nat.add].
    match goal with
    | |- tr ?X _ =>
       assert (tr X (deq (var 5) (var 5) nattp))
    end.
      {
      apply (tr_subtype_elim _ (var 6)).
        {
        apply (tr_subtype_eta2 _#3 (var 4) (var 4)); eauto 7 using hypothesis, index_0, index_S.
        }
      eapply hypothesis; eauto 7 using index_0, index_S.
      }
    apply (tr_leqtp_eta2 _#3 (var 1) (var 1)); eauto using hypothesis, index_0, index_S, tr_nsucc_nattp.
    }

    {
    cbn [length].
    simpsub.
    cbn [Nat.add length].
    simpsub.
    cbn [List.app Nat.add].
    setoid_rewrite -> unroll_natmax at 2.
    rewrite -> natcase_succ.
    simpsub.
    rewrite -> natcase_succ.
    simpsub.
    cbn [Nat.add].
    apply (tr_nattp_eta_hyp_triv _ [_; _]).
      {
      cbn [length].
      simpsub.
      cbn [Nat.add length].
      simpsub.
      cbn [List.app Nat.add].
      apply (tr_voidtp_elim _ (var 0) (var 0)).
      setoid_rewrite -> unroll_leqtp at 1.
      unfold nsucc at 1.
      rewrite -> sumcase_right.
      simpsub.
      unfold nzero at 1.
      rewrite -> sumcase_left.
      simpsub.
      eapply hypothesis; eauto using index_0.
      }
      
      {
      cbn [length].
      simpsub.
      cbn [Nat.add length].
      simpsub.
      cbn [List.app Nat.add].
      setoid_rewrite -> unroll_leqtp at 1 2 6.
      unfold nsucc.
      rewrite -> !sumcase_right.
      simpsub.
      rewrite -> !sumcase_right.
      simpsub.
      cbn [Nat.add].
      match goal with
      | |- tr ?X _ =>
         assert (tr X (deq (var 6) (var 6) nattp))
      end.
        {
        apply (tr_subtype_elim _ (var 7)).
          {
          apply (tr_subtype_eta2 _#3 (var 5) (var 5)); eauto 7 using hypothesis, index_0, index_S.
          }
        eapply hypothesis; eauto 7 using index_0, index_S.
        }
      apply (tr_leqtp_eta2 _#3 (app (app (app (app (lam (lam (lam (lam triv)))) (var 3)) (var 2)) (var 1)) (var 0)) (app (app (app (app (lam (lam (lam (lam triv)))) (var 3)) (var 2)) (var 1)) (var 0))); eauto using hypothesis, index_0, index_S.
        {
        apply tr_natmax_nattp; eauto using hypothesis, index_0, index_S.
        }
      eapply tr_pi_elim4'.
        {
        apply tr_equal_elim.
        apply (tr_equal_eta2 _#4 (app (var 4) (var 6)) (app (var 4) (var 6))).
          {
          eapply tr_pi_elim'.
            {
            eapply hypothesis; eauto using index_0, index_S.
            simpsub.
            cbn [Nat.add].
            reflexivity.
            }

            {
            eapply hypothesis; eauto 7 using index_0, index_S.
            }
            
            {
            simpsub.
            cbn [Nat.add].
            reflexivity.
            }
          }
        }

        {
        eapply hypothesis; eauto using index_0, index_S.
        }

        {
        eapply hypothesis; eauto using index_0, index_S.
        }

        {
        eapply hypothesis; eauto using index_0, index_S.
        }

        {
        eapply hypothesis; eauto using index_0, index_S.
        }

        {
        simpsub.
        auto.
        }
      }
    }
  }
Qed.


Lemma tr_natmax_ub1 :
  forall G m n,
    tr G (deq m m nattp)
    -> tr G (deq n n nattp)
    -> tr G (deq triv triv (app (app leqtp m) (natmax m n))).
Proof.
intros G m n Hm Hn.
apply (tr_leqtp_eta2 _#3 (app (lam triv) n) (app (lam triv) n)); auto.
  {
  apply tr_natmax_nattp; auto.
  }
eapply (tr_pi_elim' _ nattp (app (app leqtp (subst sh1 m)) (natmax (subst sh1 m) (var 0)))); auto.
2:{
  simpsub.
  auto.
  }
apply tr_equal_elim.
apply (nat_induction _
         (equal
            (pi nattp (app (app leqtp (var 1)) (natmax (var 1) (var 0))))
            (lam triv)
            (lam triv))
         m); auto.
3:{
  simpsub.
  auto.
  }

  {
  simpsub.
  apply tr_equal_intro.
  apply tr_pi_intro; auto using tr_nattp_formation.
  rewrite -> leqtp_nzero_equiv.
  apply tr_unittp_intro.
  }

  {
  simpsub.
  cbn [Nat.add].
  apply tr_equal_intro.
  apply tr_pi_intro; auto using tr_nattp_formation.
  apply (tr_nattp_eta_hyp_triv _ []).
    {
    cbn [length].
    simpsub.
    cbn [Nat.add length].
    simpsub.
    cbn [List.app Nat.add].
    setoid_rewrite -> unroll_natmax at 2.
    rewrite -> natcase_succ.
    simpsub.
    rewrite -> natcase_zero.
    cbn [Nat.add].
    apply tr_leqtp_refl.
    apply tr_nsucc_nattp.
    apply (tr_subtype_elim _ (var 3)).
      {
      apply (tr_subtype_eta2 _#3 (var 1) (var 1)); eauto using hypothesis, index_0, index_S.
      }
    eapply hypothesis; eauto using index_0, index_S.
    }

    {
    cbn [length].
    simpsub.
    cbn [Nat.add length].
    simpsub.
    cbn [List.app Nat.add].
    setoid_rewrite -> unroll_natmax at 2.
    rewrite -> natcase_succ.
    simpsub.
    rewrite -> natcase_succ.
    simpsub.
    setoid_rewrite -> unroll_leqtp at 2.
    unfold nsucc.
    rewrite -> sumcase_right.
    simpsub.
    rewrite -> sumcase_right.
    simpsub.
    cbn [Nat.add].
    match goal with
    | |- tr ?X _ =>
       assert (tr X (deq (var 3) (var 3) nattp)) as Hvar
    end.
      {
      apply (tr_subtype_elim _ (var 4)).
        {
        apply (tr_subtype_eta2 _#3 (var 2) (var 2)); eauto using hypothesis, index_0, index_S.
        }
      eapply hypothesis; eauto using index_0, index_S.
      }
    apply (tr_leqtp_eta2 _#3 (app (lam triv) (var 0)) (app (lam triv) (var 0))); auto.
      {
      apply tr_natmax_nattp; eauto using hypothesis, index_0.
      }
    eapply tr_pi_elim'.
      {
      apply tr_equal_elim.
      apply (tr_equal_eta2 _#4 (app (var 1) (var 3)) (app (var 1) (var 3))); auto.
      eapply tr_pi_elim'.
        {
        eapply hypothesis; eauto using index_0, index_S.
        simpsub.
        cbn [Nat.add].
        reflexivity.
        }
  
        {
        eapply hypothesis; eauto using index_0, index_S.
        }
  
        {
        simpsub.
        cbn [Nat.add].
        reflexivity.
        }
      }
    
      {
      eapply hypothesis; eauto using index_0.
      }

      {
      simpsub.
      auto.
      }
    }
  }
Qed.


Lemma tr_natmax_commute :
  forall G m n,
    tr G (deq m m nattp)
    -> tr G (deq n n nattp)
    -> tr G (deq (natmax m n) (natmax n m) nattp).
Proof.
intros G m n Hm Hn.
apply tr_equal_elim.
apply (tr_equal_eta2 _#4 (app (lam triv) n) (app (lam triv) n)).
eapply (tr_pi_elim' _ nattp (equal nattp (natmax (subst sh1 m) (var 0)) (natmax (var 0) (subst sh1 m)))); auto.
2:{
  simpsub.
  auto.
  }
apply tr_equal_elim.
apply (nat_induction _
         (equal
            (pi nattp (equal nattp (natmax (var 1) (var 0)) (natmax (var 0) (var 1))))
            (lam triv) (lam triv))
         m); auto.
3:{
  simpsub.
  auto.
  }

  {
  simpsub.
  apply tr_equal_intro.
  apply tr_pi_intro; auto using tr_nattp_formation.
  apply (tr_nattp_eta_hyp_triv _ []).
    {
    simpsub.
    cbn [List.app].
    apply tr_equal_intro.
    apply tr_natmax_nattp; auto using tr_nzero_nattp.
    }
    
    {
    simpsub.
    cbn [List.app].
    apply tr_equal_intro.
    setoid_rewrite -> unroll_natmax at 2 1.
    rewrite -> natcase_zero.
    rewrite -> natcase_succ.
    simpsub.
    rewrite -> natcase_zero.
    cbn [Nat.add].
    apply tr_nsucc_nattp.
    eapply hypothesis; eauto using index_0.
    }
  }

  {
  simpsub.
  cbn [Nat.add].
  apply tr_equal_intro.
  apply tr_pi_intro; eauto using tr_nattp_formation.
  apply (tr_nattp_eta_hyp_triv _ []).
    {
    simpsub.
    cbn [List.app Nat.add].
    apply tr_equal_intro.
    setoid_rewrite -> unroll_natmax at 4 3.
    rewrite -> natcase_zero.
    rewrite -> natcase_succ.
    simpsub.
    rewrite -> natcase_zero.
    cbn [Nat.add].
    apply tr_nsucc_nattp.
    apply (tr_subtype_elim _ (var 3)).
      {
      apply (tr_subtype_eta2 _#3 (var 1) (var 1)); eauto using hypothesis, index_0, index_S.
      }
    eauto using hypothesis, index_0, index_S.
    }

    {
    simpsub.
    cbn [List.app Nat.add].
    apply tr_equal_intro.
    setoid_rewrite -> unroll_natmax at 4 3.
    rewrite -> !natcase_succ.
    simpsub.
    rewrite -> !natcase_succ.
    simpsub.
    cbn [Nat.add].
    apply tr_nsucc_nattp.
    apply tr_equal_elim.
    eapply (tr_equal_eta2 _#4 (app (lam triv) (var 0)) (app (lam triv) (var 0))).
    eapply tr_pi_elim'.
      {
      apply tr_equal_elim.
      apply (tr_equal_eta2 _#4 (app (var 1) (var 3)) (app (var 1) (var 3))).
      eapply tr_pi_elim'.
        {
        eapply hypothesis; eauto using index_0, index_S.
        simpsub.
        cbn [Nat.add].
        reflexivity.
        }

        {
        eapply hypothesis; eauto using index_0, index_S.
        }

        {
        simpsub.
        cbn [Nat.add].
        reflexivity.
        }
      }

      {
      eapply hypothesis; eauto using index_0.
      }

      {
      simpsub.
      auto.
      }
    }
  }
Qed.


Lemma tr_natmax_ub2 :
  forall G m n,
    tr G (deq m m nattp)
    -> tr G (deq n n nattp)
    -> tr G (deq triv triv (app (app leqtp n) (natmax m n))).
Proof.
intros G m n Hm Hn.
apply (tr_eqtype_convert _#3 (app (app leqtp n) (natmax n m))).
  {
  apply tr_leqtp_formation; auto.
  apply tr_natmax_commute; auto.
  }

  {
  apply tr_natmax_ub1; auto.
  }
Qed.


Lemma lmaxLevel_valid : lmaxLevel_obligation.
Proof.
prepare.
intros G m n ext1 ext0 Hm Hn.
apply tr_natmax_nattp; auto.
Qed.


Lemma lmaxEq_valid : lmaxEq_obligation.
Proof.
prepare.
intros G m n p q ext1 ext0 Hm Hn.
apply tr_natmax_nattp; auto.
Qed.


Lemma lleqRefl_valid : lleqRefl_obligation.
Proof.
prepare.
intros G m ext0 H.
apply lleq_implode; auto.
apply tr_leqtp_refl; auto.
Qed.


Lemma lleqTrans_valid : lleqTrans_obligation.
Proof.
prepare.
intros G m n p ext1 ext0 Hleqmn Hleqnp.
so (lleq_explode _#5 Hleqmn) as (Hleqmn' & Hm & Hn).
so (lleq_explode _#5 Hleqnp) as (Hleqnp' & _ & Hp).
apply lleq_implode; auto.
apply (tr_leqtp_trans _ _ n); auto.
Qed.


Lemma lleqZero_valid : lleqZero_obligation.
Proof.
prepare.
intros G m ext0 H.
apply lleq_implode; auto using tr_nzero_nattp.
rewrite -> leqtp_nzero_equiv.
apply tr_unittp_intro.
Qed.


Lemma lleqSucc_valid : lleqSucc_obligation.
Proof.
prepare.
intros G m n ext0 Hleq.
so (lleq_explode _#5 Hleq) as (Hleq' & Hm & Hn).
apply lleq_implode; auto using tr_nsucc_nattp.
rewrite -> unroll_leqtp.
unfold nsucc.
rewrite -> sumcase_right.
simpsub.
rewrite -> sumcase_right.
simpsub.
auto.
Qed.


Lemma lleqIncrease_valid : lleqIncrease_obligation.
Proof.
prepare.
intros G m n ext0 Hleq.
so (lleq_explode _#5 Hleq) as (Hmn & Hm & Hn).
apply lleq_implode; auto using tr_nsucc_nattp.
apply (tr_leqtp_trans _ _ n); auto using tr_nsucc_nattp.
apply tr_leqtp_succ; auto.
Qed.


Lemma lleqMaxL_valid : lleqMaxL_obligation.
Proof.
prepare.
intros G m n p ext1 ext0 Hleqmp Hleqnp.
so (lleq_explode _#5 Hleqmp) as (Hleqmp' & Hm & Hp).
so (lleq_explode _#5 Hleqnp) as (Hneqnp' & Hn & _).
apply lleq_implode; auto.
2:{
  apply tr_natmax_nattp; auto.
  }
eapply tr_natmax_lub; eauto.
Qed.


Lemma lleqMaxR1_valid : lleqMaxR1_obligation.
Proof.
prepare.
intros G m n p ext1 ext0 Hleq Hp.
so (lleq_explode _#5 Hleq) as (Hleq' & Hm & Hn).
apply lleq_implode; auto.
2:{
  apply tr_natmax_nattp; auto.
  }
apply (tr_leqtp_trans _ _ n); auto.
  {
  apply tr_natmax_nattp; auto.
  }
apply tr_natmax_ub1; auto.
Qed.


Lemma lleqMaxR2_valid : lleqMaxR2_obligation.
Proof.
prepare.
intros G m n p ext1 ext0 Hleq Hn.
so (lleq_explode _#5 Hleq) as (Hleq' & Hm & Hp).
apply lleq_implode; auto.
2:{
  apply tr_natmax_nattp; auto.
  }
apply (tr_leqtp_trans _ _ p); auto.
  {
  apply tr_natmax_nattp; auto.
  }
apply tr_natmax_ub2; auto.
Qed.


Lemma lleqResp_valid : lleqResp_obligation.
Proof.
prepare.
intros G n m p q ext2 ext1 ext0 Hmn Hpq Hleq.
so (lleq_explode _#5 Hleq) as (Hleq' & _).
apply lleq_implode.
  {
  apply (tr_eqtype_convert _#3 (app (app leqtp m) q)); auto.
  apply tr_leqtp_formation; auto.
  }

  {
  eapply tr_eq_reflexivity.
  apply tr_symmetry; eauto.
  }

  {
  eapply tr_eq_reflexivity.
  apply tr_symmetry; eauto.
  }
Qed.


Lemma lsuccMaxDistTrans_valid : lsuccMaxDistTrans_obligation.
Proof.
prepare.
intros G m n p ext0 H.
rewrite -> unroll_natmax in H.
rewrite -> natcase_succ in H.
simpsubin H.
rewrite -> natcase_succ in H.
simpsubin H.
exact H.
Qed.


Lemma lzeroType_valid : lzeroType_obligation.
Proof.
prepare.
intro G.
apply tr_nzero_nattp.
Qed.


Hint Rewrite def_arrow : prepare.


Lemma lsuccType_valid : lsuccType_obligation.
Proof.
prepare.
intro G.
unfold Defs.lsucc.
apply tr_pi_intro; auto using tr_nattp_formation.
rewrite -> def_inr.
fold (@nsucc obj (var 0)).
simpsub.
apply tr_nsucc_nattp.
eapply hypothesis; eauto using index_0.
Qed.


Lemma lmaxType_valid : lmaxType_obligation.
Proof.
prepare.
intro G.
simpsub.
assert (tr G (deq Defs.lmax Defs.lmax (pi voidtp voidtp))) as Hvoid.
  {
  unfold Defs.lmax.
  rewrite -> theta_equiv.
  rewrite -> equiv_beta.
  unfold subst1.
  rewrite -> subst_lam.
  apply tr_pi_intro; auto using tr_voidtp_istype.
  apply (tr_voidtp_elim _ (var 0) (var 0)).
  eapply hypothesis; eauto using index_0.
  }
apply (tr_pi_ext _ _ _ _ _ voidtp voidtp voidtp voidtp); auto using tr_nattp_formation.
simpsub.
replace (subst sh1 Defs.lmax) with Defs.lmax.
2:{
  unfold Defs.lmax.
  simpsub.
  auto.
  }
clear Hvoid.
assert (tr (hyp_tm nattp :: G) (deq (app Defs.lmax (var 0)) (app Defs.lmax (var 0)) (pi voidtp voidtp))) as Hvoid.
  {
  unfold Defs.lmax.
  rewrite -> theta_equiv.
  rewrite -> equiv_beta.
  unfold subst1.
  rewrite -> !subst_lam.
  rewrite -> equiv_beta.
  unfold subst1.
  rewrite -> subst_lam.
  apply tr_pi_intro; auto using tr_voidtp_istype.
  apply (tr_voidtp_elim _ (var 0) (var 0)).
  eapply hypothesis; eauto using index_0.
  }
apply (tr_pi_ext _ _ _ _ _ voidtp voidtp voidtp voidtp); auto using tr_nattp_formation.
simpsub.
cbn [Nat.add].
replace (subst sh1 Defs.lmax) with Defs.lmax.
2:{
  unfold Defs.lmax.
  simpsub.
  auto.
  }
rewrite -> def_lmax.
apply tr_natmax_nattp; eauto using hypothesis, index_0, index_S.
Qed.
