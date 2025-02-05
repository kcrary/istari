
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
Require Import Dots.

Require Import ValidationUtil.
Require Import Defined.


Hint Rewrite def_guard def_coguard def_iff def_squash def_arrow : prepare.


Lemma guardForm_valid : guardForm_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_guard_formation; auto.
Qed.


Lemma guardFormUniv_valid : guardFormUniv_obligation.
Proof.
prepare.
intros G a b lv ext1 ext0 Ha Hb.
apply tr_guard_formation_univ; auto.
Qed.


Lemma guardEq_valid : guardEq_obligation.
Proof.
prepare.
intros G a a' b b' m ext0 Haa Hb.
assert (tr G (deqtype a a)) as Ha.
  {
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation.
  eapply tr_prod_elim1; eauto.
  }
assert (tr G (deqtype a' a')) as Ha'.
  {
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation.
  eapply tr_prod_elim2; eauto.
  }
apply (tr_guard_formation_iff _#5 (app (subst sh1 (ppi1 m)) (var 0)) (app (subst sh1 (ppi2 m)) (var 0))); auto.
  {
  apply (tr_pi_elim' _ (subst sh1 a) (subst (sh 2) a')).
    {
    apply (weakening _ [_] []).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_prod_elim1; eauto.
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
  apply (tr_pi_elim' _ (subst sh1 a') (subst (sh 2) a)).
    {
    apply (weakening _ [_] []).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_prod_elim2; eauto.
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


Lemma tr_guard_formation_univ_iff :
  forall G lv a a' b b' mr ml,
    tr G (deq a a (univ lv))
    -> tr G (deq a' a' (univ lv))
    (* a implies a' *)
    -> tr (hyp_tm a :: G)
         (deq mr mr (subst sh1 a'))
    (* a' implies a *)
    -> tr (hyp_tm a' :: G)
         (deq ml ml (subst sh1 a))
    -> tr (cons (hyp_tm a) G) (deq (subst sh1 b) (subst sh1 b') (univ (subst sh1 lv)))
    -> tr G (deq (guard a b) (guard a' b') (univ lv)).
Proof.
intros G lv a a' b b' mr ml Ha Ha' Hr Hl Hb.
apply tr_formation_strengthen.
  {
  eapply tr_guard_formation_iff; eauto using tr_formation_weaken.
  }

  {
  apply tr_guard_formation_univ; auto.
  eapply tr_eq_reflexivity; eauto.
  }

  {
  apply tr_guard_formation_univ; auto.
  replace (deq (subst sh1 b') (subst sh1 b') (univ (subst sh1 lv))) with (substj (dot ml id) (deq (subst (sh 2) b') (subst (sh 2) b') (univ (subst (sh 2) lv)))) by (simpsub; reflexivity).
  apply (tr_generalize _ (subst sh1 a)); auto.
  apply (weakening _ [_] [_]).
    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  eapply tr_eq_reflexivity.
  apply tr_symmetry; eauto.
  }
Qed.



Lemma guardEqUniv_valid : guardEqUniv_obligation.
Proof.
prepare.
intros G a a' b b' lv ext3 ext2 m ext0 Ha Ha' Haa Hb.
apply (tr_guard_formation_univ_iff _#6 (app (subst sh1 (ppi1 m)) (var 0)) (app (subst sh1 (ppi2 m)) (var 0))); auto.
  {
  apply (tr_pi_elim' _ (subst sh1 a) (subst (sh 2) a')).
    {
    apply (weakening _ [_] []).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_prod_elim1; eauto.
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
  apply (tr_pi_elim' _ (subst sh1 a') (subst (sh 2) a)).
    {
    apply (weakening _ [_] []).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_prod_elim2; eauto.
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


Lemma guardIntroOf_valid : guardIntroOf_obligation.
Proof.
prepare.
intros G a b m ext1 ext0 Ha Hm.
apply tr_guard_intro; auto.
Qed.


Lemma guardIntroEq_valid : guardIntroEq_obligation.
Proof.
prepare.
intros G a b m n ext1 ext0 Ha Hmn.
apply tr_guard_intro; auto.
Qed.


Lemma guardIntro_valid : guardIntro_obligation.
Proof.
prepare.
intros G a b ext0 m Hhide Ha Hm.
apply tr_guard_intro; auto.
simpsub.
replace (subst (dot triv sh1) m) with m; auto.
so (subst_into_absent_single _#3 triv Hhide) as Heq.
simpsubin Heq.
symmetry; auto.
Qed.


Lemma guardElimOf_valid : guardElimOf_obligation.
Proof.
prepare.
intros G a b m ext1 n Hm Hn.
eapply tr_guard_elim; eauto.
Qed.


Lemma guardElimEq_valid : guardElimEq_obligation.
Proof.
prepare.
intros G a b m n ext1 p Hmn Hp.
eapply tr_guard_elim; eauto.
Qed.


Lemma guardElim_valid : guardElim_obligation.
Proof.
prepare.
intros G a b m n Hm Hn.
eapply tr_guard_elim; eauto.
Qed.


Lemma guardSatEq_valid : guardSatEq_obligation.
Proof.
prepare.
intros G a b ext1 m Hb Hm.
eapply tr_guard_sat_eq; eauto.
Qed.


Lemma tr_guard_sub :
  forall G a a' b b' m n,
    tr G (deq m n (pi a' (subst sh1 a)))
    -> tr G (deqtype a a)
    -> tr (hyp_tm a' :: G) (dsubtype (subst sh1 b) (subst sh1 b'))
    -> tr (hyp_tm a :: G) (deqtype (subst sh1 b) (subst sh1 b))
    -> tr G (dsubtype (guard a b) (guard a' b')).
Proof.
intros G a b c d m n Hba Ha Hcd Hc.
assert (tr G (deqtype b b)) as Hb.
  {
  apply (tr_pi_formation_invert1 _ _ _ (subst sh1 a) (subst sh1 a)).
  apply (tr_inhabitation_formation _ m n); auto.
  }
apply tr_subtype_intro.
  {
  apply tr_guard_formation; auto.
  }

  {
  apply tr_guard_formation; auto.
  eapply tr_subtype_istype2; eauto.
  }
simpsub.
apply tr_guard_intro.
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
    cbn [Nat.add].
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  exact Hb.
  }
simpsub.
cbn [Nat.add].
apply (tr_subtype_elim _ (subst (sh 2) c)).
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
    cbn [Nat.add].
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  exact Hcd.
  }
apply (tr_guard_elim _ (subst (sh 2) a) _ _ _ (app (subst (sh 2) m) (var 0)) (app (subst (sh 2) n) (var 0))).
  {
  eapply hypothesis; eauto using index_S, index_0.
  }
eapply (tr_pi_elim' _ (subst (sh 2) b) (subst (sh 3) a)).
  {
  eapply (weakening _ [_; _] []).
    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  
    {
    cbn [length unlift].
    simpsub.
    cbn [Nat.add].
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  exact Hba.
  }

  {
  eapply hypothesis; eauto using index_0.
  simpsub.
  auto.
  }

  {
  simpsub.
  auto.
  }
Qed.


Lemma guardSub_valid : guardSub_obligation.
Proof.
prepare.
intros G a b c d m ext2 ext1 ext0 Hba Ha Hcd Hc.
eapply tr_guard_sub; eauto.
Qed.



Lemma guardSubIntro_valid : guardSubIntro_obligation.
Proof.
prepare.
intros G a b c ext2 ext1 ext0 Ha Hcb Hc.
apply (tr_subtype_trans _ _ (guard a c)).
2:{
  eapply (tr_guard_sub _#5 (lam (var 0)) (lam (var 0))); eauto.
  2:{
    eapply tr_subtype_istype1; eauto.
    }
  apply tr_pi_intro; auto.
  eapply hypothesis; eauto using index_0.
  }
apply tr_subtype_intro; auto.
  {
  apply tr_guard_formation; auto.
  eapply tr_subtype_istype1; eauto.
  }
  simpsub.
apply (tr_guard_intro _ (subst sh1 a)).
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
    cbn [Nat.add].
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  exact Ha.
  }

  {
  simpsub.
  cbn [Nat.add].
  eapply hypothesis; eauto using index_S, index_0.
  }
Qed.


Lemma guardSubElim_valid : guardSubElim_obligation.
Proof.
prepare.
intros G a b c m ext0 Ha Hbc.
apply (tr_subtype_trans _ _ b); auto.
apply tr_subtype_intro.
  {
  apply tr_guard_formation.
    {
    eapply tr_inhabitation_formation; eauto.
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
      cbn [Nat.add].
      auto.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_subtype_istype1; eauto.
    }
  }

  {
  eapply tr_subtype_istype1; eauto.
  }
apply (tr_guard_elim _ (subst sh1 a) _ _ _ (subst sh1 m) (subst sh1 m)).
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
    cbn [Nat.add].
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  exact Ha.
  }
Qed.


Lemma coguardForm_valid : coguardForm_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
apply tr_coguard_formation; auto.
Qed.


Lemma coguardFormUniv_valid : coguardFormUniv_obligation.
Proof.
prepare.
intros G a b lv ext1 ext0 Ha Hb.
apply tr_coguard_formation_univ; auto.
Qed.


Lemma coguardEq_valid : coguardEq_obligation.
Proof.
prepare.
intros G a a' b b' m ext0 Haa Hb.
assert (tr G (deqtype a a)) as Ha.
  {
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation.
  eapply tr_prod_elim1; eauto.
  }
assert (tr G (deqtype a' a')) as Ha'.
  {
  eapply tr_pi_formation_invert1.
  eapply tr_inhabitation_formation.
  eapply tr_prod_elim2; eauto.
  }
apply (tr_coguard_formation_iff _#5 (app (subst sh1 (ppi1 m)) (var 0)) (app (subst sh1 (ppi2 m)) (var 0))); auto.
  {
  apply (tr_pi_elim' _ (subst sh1 a) (subst (sh 2) a')).
    {
    apply (weakening _ [_] []).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_prod_elim1; eauto.
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
  apply (tr_pi_elim' _ (subst sh1 a') (subst (sh 2) a)).
    {
    apply (weakening _ [_] []).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_prod_elim2; eauto.
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


Lemma tr_coguard_formation_univ_iff :
  forall G lv a a' b b' mr ml,
    tr G (deq a a (univ lv))
    -> tr G (deq a' a' (univ lv))
    (* a implies a' *)
    -> tr (hyp_tm a :: G)
         (deq mr mr (subst sh1 a'))
    (* a' implies a *)
    -> tr (hyp_tm a' :: G)
         (deq ml ml (subst sh1 a))
    -> tr (cons (hyp_tm a) G) (deq (subst sh1 b) (subst sh1 b') (univ (subst sh1 lv)))
    -> tr G (deq (coguard a b) (coguard a' b') (univ lv)).
Proof.
intros G lv a a' b b' mr ml Ha Ha' Hr Hl Hb.
apply tr_formation_strengthen.
  {
  eapply tr_coguard_formation_iff; eauto using tr_formation_weaken.
  }

  {
  apply tr_coguard_formation_univ; auto.
  eapply tr_eq_reflexivity; eauto.
  }

  {
  apply tr_coguard_formation_univ; auto.
  replace (deq (subst sh1 b') (subst sh1 b') (univ (subst sh1 lv))) with (substj (dot ml id) (deq (subst (sh 2) b') (subst (sh 2) b') (univ (subst (sh 2) lv)))) by (simpsub; reflexivity).
  apply (tr_generalize _ (subst sh1 a)); auto.
  apply (weakening _ [_] [_]).
    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  eapply tr_eq_reflexivity.
  apply tr_symmetry; eauto.
  }
Qed.



Lemma coguardEqUniv_valid : coguardEqUniv_obligation.
Proof.
prepare.
intros G a a' b b' lv ext3 ext2 m ext0 Ha Ha' Haa Hb.
apply (tr_coguard_formation_univ_iff _#6 (app (subst sh1 (ppi1 m)) (var 0)) (app (subst sh1 (ppi2 m)) (var 0))); auto.
  {
  apply (tr_pi_elim' _ (subst sh1 a) (subst (sh 2) a')).
    {
    apply (weakening _ [_] []).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_prod_elim1; eauto.
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
  apply (tr_pi_elim' _ (subst sh1 a') (subst (sh 2) a)).
    {
    apply (weakening _ [_] []).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_prod_elim2; eauto.
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


Lemma coguardIntroEq_valid : coguardIntroEq_obligation.
Proof.
prepare.
intros G a b m n p ext0 Hp Hmn.
eapply tr_coguard_intro; eauto.
Qed.


Lemma coguardIntroOf_valid : coguardIntroOf_obligation.
Proof.
prepare.
intros G a b m p ext0 Hp Hm.
eapply tr_coguard_intro; eauto.
Qed.


Lemma coguardIntroOfSquash_valid : coguardIntroOfSquash_obligation.
Proof.
prepare.
intros G a b m ext2 p ext0 Ha Hp Hm.
apply (tr_set_elim2 _ unittp (subst sh1 a) p); auto.
  {
  apply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }

    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  exact Ha.
  }
simpsub.
apply (tr_coguard_intro _#3 (var 0) (var 0)).
  {
  eapply hypothesis; eauto using index_0.
  }
apply (weakening _ [_] []).
  {
  cbn [length unlift].
  simpsub.
  reflexivity.
  }

  {
  cbn [length unlift].
  simpsub.
  reflexivity.
  }
cbn [length unlift].
simpsub.
cbn [List.app].
exact Hm.
Qed.


Lemma coguardIntro_valid : coguardIntro_obligation.
Proof.
prepare.
intros G a b p m Hp Hm.
eapply tr_coguard_intro; eauto.
Qed.


Lemma coguardElim1_valid : coguardElim1_obligation.
Proof.
prepare.
intros G a b ext1 m Ha Hm.
eapply tr_coguard_elim1; eauto.
Qed.


Lemma coguardElim2Eq_valid : coguardElim2Eq_obligation.
Proof.
prepare.
intros G a b m n ext0 H.
eapply tr_coguard_elim2; eauto.
Qed.


Lemma coguardElim2Of_valid : coguardElim2Of_obligation.
Proof.
prepare.
intros G a b m ext0 H.
eapply tr_coguard_elim2; eauto.
Qed.


Lemma coguardElim2_valid : coguardElim2_obligation.
Proof.
prepare.
intros G a b m H.
eapply tr_coguard_elim2; eauto.
Qed.


Lemma coguardLeft_valid : coguardLeft_obligation.
Proof.
prepare.
intros G1 G2 a b c ext0 m Hhyg Ha Hc.
assert (tr (G2 ++ hyp_tm (coguard a b) :: G1) (deqtype (subst (sh (S (length G2))) a) (subst (sh (S (length G2))) a))) as Ha'.
  {
  replace (hyp_tm (coguard a b) :: G1) with ([hyp_tm (coguard a b)] ++ G1) by reflexivity.
  rewrite -> app_assoc.
  apply (weakening _ _ []).
    {
    simpsub.
    auto.
    }
   
    {
    rewrite -> app_length.
    cbn [length].
    rewrite -> Nat.add_comm.
    rewrite -> under_zero.
    simpsub.
    rewrite <- compose_assoc.
    rewrite -> compose_sh_unlift.
    simpsub.
    auto.
    }
  rewrite -> app_length.
  cbn [length].
  simpsub.
  cbn [List.app].
  rewrite -> Nat.add_comm.
  rewrite -> compose_sh_unlift.
  simpsub.
  exact Ha.
  }
assert (forall h, tr (h :: G2 ++ hyp_tm (coguard a b) :: G1) (deqtype (subst (sh (S (S (length G2)))) a) (subst (sh (S (S (length G2)))) a))) as Ha''.
  {
  intro h.
  apply (weakening _ [_] []).
    {
    simpsub.
    auto.
    }
    
    {
    cbn [length unlift].
    simpsub.
    do 3 f_equal; omega.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  simpsub.
  exact Ha'.
  }
apply (tr_set_elim2 _ unittp (subst (sh (S (S (length G2)))) a) triv); auto.
  {
  replace (set unittp (subst (sh (S (S (length G2)))) a)) with (squash (subst (sh (S (length G2))) a)).
  2:{
    unfold squash.
    simpsub.
    rewrite -> Nat.add_comm.
    reflexivity.
    }
  apply (tr_coguard_elim1 _ _ (subst (sh (S (length G2))) b) (var (length G2)) (var (length G2))); auto.
  eapply hypothesis.
    {
    apply (index_app_right _#3 0).
    apply index_0.
    }
  simpsub.
  auto.
  }
simpsub.
apply (tr_eqtype_convert_hyp_better _ (_ :: G2) _ b).
  {
  cbn [List.app length].
  simpsub.
  apply tr_eqtype_symmetry.
  apply (tr_coguard_sat_eq _#3 (var 0) (var 0)).
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    rewrite -> Nat.add_comm.
    auto.
    }
    
    {
    apply (tr_inhabitation_formation _ (var (S (length G2))) (var (S (length G2)))).
    apply (tr_coguard_elim2 _ (subst (sh (S (S (length G2)))) a)).
    eapply hypothesis.
      {
      apply index_S.
      apply (index_app_right _ _ _ 0).
      apply index_0.
      }
    simpsub.
    auto.
    }
  }
cbn [List.app].
apply (exchange_1_n _ _ _ []).
  {
  simpsub.
  rewrite <- compose_assoc.
  rewrite -> compose_sh_unlift_ge; auto.
  replace (S (length G2) - length G2) with 1 by omega.
  simpsub.
  auto.
  }
cbn [length].
simpsub.
cbn [List.app].
rewrite <- (compose_sh_sh _ 1).
rewrite <- under_dots.
rewrite <- compose_under.
simpsub.
rewrite -> compose_sh_unlift_ge; [| omega].
replace (1 + length G2 - length G2) with 1 by omega.
rewrite -> subst_into_absent_single; auto.
Qed.


Lemma coguardSatEq_valid : coguardSatEq_obligation.
Proof.
prepare.
intros G a b ext1 m Hb Hm.
eapply tr_coguard_sat_eq; eauto.
Qed.


Lemma tr_coguard_sub :
  forall G a a' b b' m n,
    tr G (deq m n (pi a (subst sh1 a')))
    -> tr G (deqtype a' a')
    -> tr (hyp_tm a :: G) (dsubtype (subst sh1 b) (subst sh1 b'))
    -> tr (hyp_tm a' :: G) (deqtype (subst sh1 b') (subst sh1 b'))
    -> tr G (dsubtype (coguard a b) (coguard a' b')).
Proof.
intros G a b c d m n Hab Hb Hcd Hd.
assert (tr G (deqtype a a)) as Ha.
  {
  apply (tr_pi_formation_invert1 _ _ _ (subst sh1 b) (subst sh1 b)).
  apply (tr_inhabitation_formation _ m n); auto.
  }
apply tr_subtype_intro.
  {
  apply tr_coguard_formation; auto.
  eapply tr_subtype_istype1; eauto.
  }

  {
  apply tr_coguard_formation; auto.
  }
apply (tr_set_elim2 _ unittp (subst sh1 (subst sh1 a)) triv).
  {
  apply (tr_coguard_elim1 _ _ (subst sh1 c) (var 0) (var 0)); auto.
    {
    apply (weakening _ [_] []).
      {
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
  eapply hypothesis; eauto using index_0.
  }

  {
  apply (weakening _ [_; _] []).
    {
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
simpsub.
cbn [Nat.add].
apply (tr_subtype_elim _ (coguard (subst (sh 2) a) (subst (sh 2) c))).
2:{
  eapply hypothesis; eauto using index_S, index_0.
  }
apply (weakening _ [_] [_]).
  {
  cbn [length unlift].
  simpsub.
  auto.
  }

  {
  cbn [length unlift].
  simpsub.
  cbn [Nat.add].
  auto.
  }
cbn [length unlift].
simpsub.
cbn [List.app].
apply (tr_subtype_trans _ _ (subst sh1 c)).
  {
  apply tr_subtype_refl'.
  apply tr_eqtype_symmetry.
  apply (tr_coguard_sat_eq _#3 (var 0) (var 0)).
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    eapply tr_subtype_istype1; eauto.
    }
  }
apply (tr_subtype_trans _ _ (subst sh1 d)); auto.
apply tr_subtype_refl'.
assert (tr (hyp_tm a :: G) (deq (app (subst sh1 m) (var 0)) (app (subst sh1 n) (var 0)) (subst sh1 b))) as Hinh.
  {
  eapply (tr_pi_elim'  _ (subst sh1 a) (subst (sh 2) b)).
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
      cbn [Nat.add].
      auto.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    exact Hab.
    }

    {
    eapply hypothesis; eauto using index_0.
    }

    {
    simpsub.
    auto.
    }
  }
apply (tr_coguard_sat_eq _#3 (app (subst sh1 m) (var 0)) (app (subst sh1 n) (var 0))); auto.
apply (tr_assert _ (subst sh1 b) (app (subst sh1 m) (var 0))); auto.
  {
  eapply tr_eq_reflexivity; eauto.
  }
eapply (weakening _ [_] [_]).
  {
  cbn [length unlift].
  simpsub.
  auto.
  }

  {
  cbn [length unlift].
  simpsub.
  cbn [Nat.add].
  auto.
  }
cbn [length unlift].
simpsub.
cbn [List.app].
exact Hd.
Qed.


Lemma coguardSub_valid : coguardSub_obligation.
Proof.
prepare.
intros G a b c d m ext2 ext1 ext0 Hab Hb Hcd Hd.
eapply tr_coguard_sub; eauto.
Qed.


Lemma coguardSubIntro_valid : coguardSubIntro_obligation.
Proof.
prepare.
intros G a b c m ext0 Ha Hbc.
apply (tr_subtype_trans _ _ b); auto.
apply tr_subtype_intro.
2:{
  apply tr_coguard_formation.
    {
    eapply tr_inhabitation_formation; eauto.
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
      cbn [Nat.add].
      auto.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_subtype_istype2; eauto.
    }
  }

  {
  eapply tr_subtype_istype2; eauto.
  }
simpsub.
apply (tr_coguard_intro _ (subst sh1 a) _ (subst sh1 m) (subst sh1 m)).
2:{
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
    cbn [Nat.add].
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  exact Ha.
  }
Qed.



Lemma coguardSubElim_valid : coguardSubElim_obligation.
Proof.
prepare.
intros G a b c ext2 ext1 ext0 Ha Hbc Hc.
apply (tr_subtype_trans _ _ (coguard a c)).
  {
  eapply (tr_coguard_sub _#5 (lam (var 0)) (lam (var 0))); eauto.
  2:{
    eapply tr_subtype_istype2; eauto.
    }
  apply tr_pi_intro; auto.
  eapply hypothesis; eauto using index_0.
  }
apply tr_subtype_intro; auto.
  {
  apply tr_coguard_formation; auto.
  eapply tr_subtype_istype2; eauto.
  }  
  
  {
  apply (tr_coguard_elim2 _ (subst sh1 a)).
  eapply hypothesis; eauto using index_0.
  }
Qed.
