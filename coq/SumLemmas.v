
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
Require Import Equivalence.
Require Import Equivalences.
Require Import Dots.

Require Import Defined.



Lemma tr_sumtype_formation :
  forall G a a' b b',
    tr G (deqtype a a')
    -> tr G (deqtype b b')
    -> tr G (deqtype (sumtype a b) (sumtype a' b')).
Proof.
intros G a a' b b' Ha Hb.
unfold sumtype.
apply tr_sigma_formation.
  {
  apply tr_booltp_istype.
  }
apply tr_booltp_elim_eqtype.
  {
  eapply hypothesis; eauto using index_0.
  }

  {
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
  auto.
  }

  {
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
  auto.
  }
Qed.


Lemma tr_sumtype_formation_univ :
  forall G lv a a' b b',
    tr G (deq a a' (univ lv))
    -> tr G (deq b b' (univ lv))
    -> tr G (deq (sumtype a b) (sumtype a' b') (univ lv)).
Proof.
intros G lv a a' b b' Ha Hb.
unfold sumtype.
apply tr_sigma_formation_univ.
  {
  apply (tr_univ_cumulative _ nzero).
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
replace (univ (subst sh1 lv)) with (subst1 (var 0) (univ (subst (sh 2) lv))) by (simpsub; auto).
apply tr_booltp_elim.
  {
  eapply hypothesis; eauto using index_0.
  }

  {
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
  auto.
  }

  {
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
  auto.
  }
Qed.


Lemma tr_sumtype_intro1 :
  forall G a b m n,
    tr G (deq m n a)
    -> tr G (deqtype b b)
    -> tr G (deq (sumleft m) (sumleft n) (sumtype a b)).
Proof.
intros G a b m n Hmn Hb.
unfold sumleft, sumtype.
apply tr_sigma_intro.
  {
  apply tr_booltp_intro_btrue.
  }

  {
  simpsub.
  rewrite -> (steps_equiv _#3 (star_one _#4 (step_bite2 _#3))).
  auto.
  }

  {
  apply tr_booltp_elim_eqtype.
    {
    eapply hypothesis; eauto using index_0.
    }
  
    {
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
    eapply tr_inhabitation_formation; eauto.
    }
  
    {
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
    auto.
    }
  }
Qed.


Lemma tr_sumtype_intro2 :
  forall G a b m n,
    tr G (deq m n b)
    -> tr G (deqtype a a)
    -> tr G (deq (sumright m) (sumright n) (sumtype a b)).
Proof.
intros G a b m n Hmn Ha.
unfold sumleft, sumtype.
apply tr_sigma_intro.
  {
  apply tr_booltp_intro_bfalse.
  }

  {
  simpsub.
  rewrite -> (steps_equiv _#3 (star_one _#4 (step_bite3 _#3))).
  auto.
  }

  {
  apply tr_booltp_elim_eqtype.
    {
    eapply hypothesis; eauto using index_0.
    }
  
    {
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
    auto.
    }

    {
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
    eapply tr_inhabitation_formation; eauto.
    }
  }
Qed.


Lemma tr_sumtype_eta_hyp_triv :
  forall G1 G2 a b c,
    tr (substctx (dot (sumleft (var 0)) sh1) G2 ++ hyp_tm a :: G1) 
      (deq triv triv (subst (under (length G2) (dot (sumleft (var 0)) sh1)) c))
    -> tr (substctx (dot (sumright (var 0)) sh1) G2 ++ hyp_tm b :: G1) 
         (deq triv triv (subst (under (length G2) (dot (sumright (var 0)) sh1)) c))
    -> tr (G2 ++ hyp_tm (sumtype a b) :: G1) (deq triv triv c).
Proof.
intros G1 G2 a b c Hl Hr.
unfold sumtype.
replace triv with (@subst obj (under (length G2) (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) sh1))) triv) by (simpsub; auto).
apply tr_sigma_eta_hyp.
set (i := length G2) in * |- *.
replace (substctx (dot (ppair (var 1) (var 0)) (sh 2)) G2 ++ hyp_tm (bite (var 0) (subst sh1 a) (subst sh1 b)) :: hyp_tm booltp :: G1)
   with ((substctx (dot (ppair (var 1) (var 0)) (sh 2)) G2 ++ hyp_tm (bite (var 0) (subst sh1 a) (subst sh1 b)) :: nil) ++ hyp_tm booltp :: G1).
2:{
  rewrite <- app_assoc.
  rewrite <- app_comm_cons.
  cbn.
  reflexivity.
  }
set (j := length (substctx (dot (ppair (var 1) (var 0)) (sh 2)) G2 ++ [hyp_tm (bite (var 0) (subst sh1 a) (subst sh1 b))])).
apply tr_booltp_eta_hyp_triv.
  {
  rewrite -> substctx_append.
  rewrite -> app_length.
  rewrite -> length_substctx.
  cbn [length].
  rewrite <- substctx_compose.
  simpsub.
  rewrite <- app_assoc.
  cbn [List.app].
  rewrite <- under_sum.
  fold i.
  rewrite <- compose_under.
  simpsub.
  fold (@sumleft obj (var 0)).
  apply (tr_compute_hyp _ _ _ (hyp_tm a)); auto.
  apply equivh_tm.
  apply steps_equiv.
  apply star_one.
  apply step_bite2.
  }

  {
  rewrite -> substctx_append.
  rewrite -> app_length.
  rewrite -> length_substctx.
  cbn [length].
  rewrite <- substctx_compose.
  simpsub.
  rewrite <- app_assoc.
  cbn [List.app].
  rewrite <- under_sum.
  fold i.
  rewrite <- compose_under.
  simpsub.
  fold (@sumright obj (var 0)).
  apply (tr_compute_hyp _ _ _ (hyp_tm b)); auto.
  apply equivh_tm.
  apply steps_equiv.
  apply star_one.
  apply step_bite3.
  }
Qed.


Lemma sum_case :
  forall G a b c m d,
    tr (hyp_tm a :: G) (deq triv triv (subst (dot (sumleft (var 0)) (sh 1)) c))
    -> tr (hyp_tm b :: G) (deq triv triv (subst (dot (sumright (var 0)) (sh 1)) c))
    -> tr G (deq m m (sumtype a b))
    -> d = subst1 m c
    -> tr G (deq triv triv d).
Proof.
intros G a b c m d Hleft Hright Hm ->.
replace (deq triv triv (subst1 m c)) with (substj (dot m id) (deq triv triv c)).
2:{
  simpsub.
  auto.
  }
apply (tr_generalize _ (sumtype a b)); auto.
unfold sumtype.
apply tr_equal_elim.
apply (tr_sigma_eta_hyp _ [] _ _ triv triv).
cbn [length].
simpsub.
cbn [List.app].
apply (tr_equal_eta2 _#4 
         (bite (var 1) (subst (under 1 sh1) triv) (subst (under 1 sh1) triv))
         (bite (var 1) (subst (under 1 sh1) triv) (subst (under 1 sh1) triv))).
apply (tr_booltp_eta_hyp _ [_]).
  {
  simpsub.
  cbn [length List.app].
  simpsub.
  apply tr_equal_intro.
  assert (equiv (bite btrue a b) a) as Hequiv.
    {
    apply steps_equiv.
    apply star_one.
    apply step_bite2.
    }
  rewrite -> Hequiv.
  exact Hleft.
  }

  {
  simpsub.
  cbn [length List.app].
  simpsub.
  apply tr_equal_intro.
  assert (equiv (bite bfalse a b) b) as Hequiv.
    {
    apply steps_equiv.
    apply star_one.
    apply step_bite3.
    }
  rewrite -> Hequiv.
  exact Hright.
  }
Qed.


Lemma tr_sumtype_elim :
  forall G a b c m n p q r s,
    tr G (deq m n (sumtype a b))
    -> tr (hyp_tm a :: G) (deq p q (subst (dot (sumleft (var 0)) sh1) c))
    -> tr (hyp_tm b :: G) (deq r s (subst (dot (sumright (var 0)) sh1) c))
    -> tr G (deq
               (sumcase m p r)
               (sumcase n q s)
               (subst1 m c)).
Proof.
intros G a b c m n p q r s Hmn Hpq Hrs.
so (equiv_beta _ (sumcase (var 0) (subst (dot (var 0) (sh 2)) p) (subst (dot (var 0) (sh 2)) r)) m) as H.
simpsubin H.
rewrite -> !subst_var0_sh1 in H.
rewrite <- H; clear H.
so (equiv_beta _ (sumcase (var 0) (subst (dot (var 0) (sh 2)) q) (subst (dot (var 0) (sh 2)) s)) n) as H.
simpsubin H.
rewrite -> !subst_var0_sh1 in H.
rewrite <- H; clear H.
apply (tr_pi_elim' _ (sumtype a b) c); auto.
apply tr_pi_intro.
  {
  eapply tr_inhabitation_formation; eauto.
  }
unfold sumcase.
unfold sumleft in Hpq.
unfold sumright in Hrs.
clear Hmn.
simpsub.
replace (bite (ppi1 (var 0)) (subst (dot (ppi2 (var 0)) sh1) p) (subst (dot (ppi2 (var 0)) sh1) r)) with (subst (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) sh1)) (bite (var 1) (subst (dot (var 0) (sh 2)) p) (subst (dot (var 0) (sh 2)) r))) by (simpsub; auto).
replace (bite (ppi1 (var 0)) (subst (dot (ppi2 (var 0)) sh1) q) (subst (dot (ppi2 (var 0)) sh1) s)) with (subst (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) sh1)) (bite (var 1) (subst (dot (var 0) (sh 2)) q) (subst (dot (var 0) (sh 2)) s))) by (simpsub; auto).
apply (tr_sigma_eta_hyp _ []).
simpsub.
cbn [List.app].
apply (tr_booltp_eta_hyp _ [_]).
  {
  cbn [length].
  simpsub.
  cbn [List.app].
  rewrite -> equiv_bite_l.
  auto.
  }

  {
  cbn [length].
  simpsub.
  cbn [List.app].
  rewrite -> equiv_bite_r.
  auto.
  }
Qed.


Lemma tr_sumtype_elim_eqtype :
  forall G a b c d e f m n,
    tr G (deq m n (sumtype a b))
    -> tr (hyp_tm a :: G) (deqtype c d)
    -> tr (hyp_tm b :: G) (deqtype e f)
    -> tr G (deqtype (sumcase m c e) (sumcase n d f)).
Proof.
intros G a b c d e f m n Hmn Hcd Hef.
replace (sumcase m c e) with (subst1 m (sumcase (var 0) (subst (dot (var 0) (sh 2)) c) (subst (dot (var 0) (sh 2)) e))).
2:{
  simpsub.
  rewrite -> !subst_var0_sh1.
  auto.
  }
replace (sumcase n d f) with (subst1 n (sumcase (var 0) (subst (dot (var 0) (sh 2)) d) (subst (dot (var 0) (sh 2)) f))).
2:{
  simpsub.
  rewrite -> !subst_var0_sh1.
  auto.
  }
eapply tr_functionality; eauto.
apply (tr_sumtype_eta_hyp_triv _ []).
  {
  simpsub.
  cbn [List.app].
  rewrite -> !sumcase_left.
  simpsub.
  rewrite -> !subst_var0_sh1.
  auto.
  }

  {
  simpsub.
  cbn [List.app].
  rewrite -> !sumcase_right.
  simpsub.
  rewrite -> !subst_var0_sh1.
  auto.
  }
Qed.
