
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
Require Import Dots.

Require Import Defined.
Require Import SumLemmas.
Require Import PageType.
Require MuIndExtract.



Lemma tr_positive_nattp_body :
  forall G, tr G (deq triv triv (ispositive (sumtype unittp (var 0)))).
Proof.
intros G.
apply (tr_positive_algorithm _ _ nil nil).
  {
  unfold sumtype.
  apply hpositive_sigma.
    {
    replace booltp with (@subst obj (under 0 sh1) booltp) by (simpsub; auto).
    apply hpositive_const.
    }
  replace (var 0) with (@subst obj (under 1 sh1) (var 0)) by (simpsub; auto).
  apply hpositive_bite.
    {
    simpsub.
    replace unittp with (@subst obj (under 1 sh1) unittp) by (simpsub; auto).
    apply hpositive_const.
    }

    {
    simpsub.
    cbn.
    apply hpositive_var.
    }
  }

  {
  intros x H.
  destruct H.
  }

  {
  intros x H.
  destruct H.
  }
Qed.


Lemma tr_nattp_formation :
  forall G, tr G (deqtype nattp nattp).
Proof.
intros G.
unfold nattp.
apply tr_mu_formation; auto using tr_positive_nattp_body.
apply tr_sumtype_formation.
  {
  apply tr_unittp_istype.
  }

  {
  apply tr_hyp_tp.
  apply index_0.
  }
Qed.


Lemma tr_nzero_nattp :
  forall G, tr G (deq nzero nzero nattp).
Proof.
intros G.
unfold nzero, nattp.
eapply tr_subtype_elim.
  {
  apply tr_mu_roll.
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
  }
simpsub.
apply tr_sumtype_intro1.
  {
  apply tr_unittp_intro.
  }

  {
  apply tr_nattp_formation.
  }
Qed.


Lemma tr_nsucc_nattp :
  forall G m n,
    tr G (deq m n nattp)
    -> tr G (deq (nsucc m) (nsucc n) nattp).
Proof.
intros G m n Hmn.
apply (tr_subtype_elim _ (sumtype unittp nattp)).
  {
  replace (@sumtype obj unittp nattp) with (@subst1 obj nattp (sumtype unittp (var 0))) by (simpsub; auto).
  apply tr_mu_roll.
    {
    apply tr_sumtype_formation.
      {
      apply tr_unittp_istype.
      }

      {
      eapply tr_hyp_tp; eauto using index_0.
      }
    }

    {
    apply tr_positive_nattp_body.
    }
  }

  {
  unfold nsucc.
  apply tr_sumtype_intro2; auto.
  apply tr_unittp_istype.
  }
Qed.


Lemma tr_nattp_formation_univ :
  forall G, tr G (deq nattp nattp (univ nzero)).
Proof.
intros G.
unfold nattp.
apply tr_mu_formation_univ.
  {
  unfold pagetp.
  apply tr_nzero_nattp.
  }

  {
  simpsub.
  apply tr_sumtype_formation_univ.
    {
    apply tr_unittp_formation_univ.
    }
  
    {
    eapply hypothesis; eauto using index_0.
    }
  }

  {
  apply tr_positive_nattp_body.
  }

  {
  apply tr_positive_nattp_body.
  }
Qed.


Lemma tr_nattp_eta_hyp_triv :
  forall G1 G2 c,
    tr (substctx (dot nzero id) G2 ++ G1) 
      (deq triv triv (subst (under (length G2) (dot nzero id)) c))
    -> tr (substctx (dot (nsucc (var 0)) sh1) G2 ++ hyp_tm nattp :: G1) 
         (deq triv triv (subst (under (length G2) (dot (nsucc (var 0)) sh1)) c))
    -> tr (G2 ++ hyp_tm nattp :: G1) (deq triv triv c).
Proof.
intros G1 G2 c Hz Hs.
apply (tr_subtype_convert_hyp _ _ _ (sumtype unittp nattp)).
  {
  simpsub.
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
  cbn [List.app].
  unfold nattp.
  apply tr_mu_unroll.
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
  }

  {
  simpsub.
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
  cbn [List.app].
  unfold nattp.
  replace (sumtype unittp (mu (sumtype unittp (var 0)))) with (@subst1 obj (mu (sumtype unittp (var 0))) (sumtype unittp (var 0))) by (simpsub; auto).
  apply tr_mu_roll.
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
  }
apply tr_sumtype_eta_hyp_triv; auto.
apply tr_unittp_eta_hyp_triv.
rewrite <- substctx_compose.
rewrite -> length_substctx.
rewrite <- subst_compose.
rewrite <- compose_under.
simpsub.
auto.
Qed.




Lemma nat_case :
  forall G b m c,
    tr G (deq triv triv (subst1 nzero b))
    -> tr (hyp_tm nattp :: G) (deq triv triv (subst (dot (nsucc (var 0)) (sh 1)) b))
    -> tr G (deq m m nattp)
    -> c = subst1 m b
    -> tr G (deq triv triv c).
Proof.
intros G b m c Hzero Hsucc Hm ->.
apply (sum_case _ unittp nattp b m).
  {
  replace (@triv obj) with (@subst obj (under 0 sh1) triv) by (simpsub; auto).
  apply (tr_unittp_eta_hyp _ []).
  simpsub.
  cbn [List.app].
  exact Hzero.
  }

  {
  exact Hsucc.
  }

  {
  apply (tr_subtype_elim _ nattp); auto.
  apply tr_mu_unroll.
    {
    apply tr_sumtype_formation.
      {
      apply tr_unittp_istype.
      }

      {
      eapply tr_hyp_tp; eauto using index_0.
      }
    }

    {
    apply tr_positive_nattp_body.
    }
  }

  {
  reflexivity.
  }
Qed.


Lemma nat_induction :
  forall G b m c,
    tr G (deq triv triv (subst1 nzero b))
    -> tr
         (hyp_tm (pi (var 2) (subst (under 1 (sh 3)) b)) ::
          hyp_tm (subtype (var 1) nattp) ::
          hyp_tm (var 0) ::
          hyp_tp :: 
          G)
         (deq triv triv (subst (dot (nsucc (var 2)) (sh 4)) b))
    -> tr G (deq m m nattp)
    -> c = subst1 m b
    -> tr G (deq triv triv c).
Proof.
intros G b m c Hzero Hsucc Hm ->.
apply (tr_mu_ind _ (sumtype unittp (var 0))).
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

2:{
  exact Hm.
  }
replace (mu (subst (under 1 (sh 2)) (sumtype unittp (var 0)))) with (@nattp obj) by (simpsub; auto).
apply (tr_sumtype_eta_hyp_triv _ [_; _]).
  {
  cbn [length].
  simpsub.
  cbn [length Nat.add List.app].
  simpsub.
  cbn [Nat.add].
  replace triv with (@subst obj (under 2 sh1) triv) by (simpsub; auto).
  apply (tr_unittp_eta_hyp _ [_; _]).
  cbn [length].
  simpsub.
  cbn [length Nat.add List.app].
  simpsub.
  cbn [Nat.add].
  fold (@nzero obj).
  apply (weakening _ [_; _; _] []).
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
  cbn [List.app].
  exact Hzero.
  }

  {
  cbn [length].
  simpsub.
  cbn [length Nat.add List.app].
  simpsub.
  cbn [Nat.add].
  exact Hsucc.
  }
Qed.


Lemma subst_leqtp :
  forall object (s : @sub object), subst s leqtp = leqtp.
Proof.
prove_subst.
Qed.



Lemma unroll_leqtp :
  forall m n,
    @equiv obj
      (app (app leqtp m) n)
      (sumcase m
         unittp
         (sumcase (subst sh1 n)
            voidtp
            (app (app leqtp (var 1)) (var 0)))).
Proof.
intros m n.
apply steps_equiv.
unfold leqtp.
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
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
cbn [Nat.add].
apply star_refl.
Qed.


Lemma tr_leqtp_type :
  forall G, tr G (deq leqtp leqtp (pi nattp (pi nattp (univ nzero)))).
Proof.
intros G.
eapply tr_pi_of_ext.
  {
  apply tr_nattp_formation.
  }

2:{
  unfold leqtp.
  rewrite -> theta_equiv.
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
simpsub.
apply tr_equal_elim.
match goal with
| |- tr _ (deq _ _ ?X) => eapply (nat_induction _ (subst (dot (var 0) (sh 2)) X))
end.
3:{
  eapply (hypothesis _ 0); eauto using index_0.
  }

  {
  simpsub.
  apply tr_equal_intro.
  rewrite -> subst_leqtp.
  eapply tr_pi_of_ext.
    {
    apply tr_nattp_formation.
    }
  
  2:{
    unfold leqtp.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
      cbn [Nat.add].
      apply theta_fix.
      }
    eapply star_trans.
      {
      apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
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
    apply star_refl.
    }
  simpsub.
  rewrite -> subst_leqtp.
  rewrite -> unroll_leqtp.
  unfold nzero at 1 2.
  rewrite -> sumcase_left.
  simpsub.
  apply tr_unittp_formation_univ.
  }

  {
  simpsub.
  cbn [Nat.add].
  apply tr_equal_intro.
  rewrite -> subst_leqtp.
  eapply tr_pi_of_ext.
    {
    apply tr_nattp_formation.
    }
  
  2:{
    unfold leqtp.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
      cbn [Nat.add].
      apply theta_fix.
      }
    eapply star_trans.
      {
      apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
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
    apply star_refl.
    }
  simpsub.
  rewrite -> subst_leqtp.
  cbn [Nat.add].
  setoid_rewrite -> unroll_leqtp.
  unfold nsucc.
  rewrite -> sumcase_right.
  simpsub.
  cbn [Nat.add].
  apply tr_equal_elim.
  apply (tr_nattp_eta_hyp_triv _ []).
    {
    cbn [length].
    simpsub.
    cbn [Nat.add length List.app].
    apply tr_equal_intro.
    unfold nzero at 2 4.
    rewrite -> sumcase_left.
    simpsub.
    apply tr_voidtp_formation_univ.
    }

    {
    cbn [length].
    simpsub.
    cbn [Nat.add List.app].
    unfold nsucc.
    rewrite -> sumcase_right.
    simpsub.
    cbn [Nat.add].
    rewrite -> !subst_leqtp.
    apply tr_equal_intro.
    eapply tr_pi_elim'.
    2:{
      eapply hypothesis; eauto using index_0.
      }

      {
      apply tr_equal_elim.
      apply (tr_equal_eta2 _#4 (app (var 1) (var 3)) (app (var 1) (var 3))).
      eapply tr_pi_elim'.
        {
        eapply hypothesis; eauto using index_0, index_S.
        simpsub.
        cbn [Nat.add].
        eauto.
        }
      
        {
        eapply hypothesis; eauto using index_0, index_S.
        }

        {
        simpsub.
        eauto.
        }
      }
    
      {
      simpsub.
      eauto.
      }
    }
  }

  {
  simpsub.
  eauto.
  }
Qed.


Lemma tr_leqtp_formation_univ :
  forall G m m' n n',
    tr G (deq m m' nattp)
    -> tr G (deq n n' nattp)
    -> tr G (deq (app (app leqtp m) n) (app (app leqtp m') n') (univ nzero)).
Proof.
intros G m m' n n' Hm Hn.
eapply tr_pi_elim'.
  {
  eapply tr_pi_elim'.
    {
    apply tr_leqtp_type.
    }

    {
    auto.
    }

    {
    simpsub; eauto.
    }
  }

  {
  auto.
  }

  {
  simpsub; eauto.
  }
Qed.


Lemma tr_leqtp_formation :
  forall G m m' n n',
    tr G (deq m m' nattp)
    -> tr G (deq n n' nattp)
    -> tr G (deqtype (app (app leqtp m) n) (app (app leqtp m') n')).
Proof.
intros G m m' n n' Hm Hn.
apply (tr_formation_weaken _ nzero).
apply tr_leqtp_formation_univ; auto.
Qed.


Lemma tr_leqtp_eta2 :
  forall G m n p q,
    tr G (deq m m nattp)
    -> tr G (deq n n nattp)
    -> tr G (deq p q (app (app leqtp m) n))
    -> tr G (deq triv triv (app (app leqtp m) n)).
Proof.
intros G m n p q Hm Hn Hleqtp.
apply tr_equal_elim.
apply (tr_equal_eta2 _#4 
         (app (app (lam (lam triv)) n) p)
         (app (app (lam (lam triv)) n) q)).
apply (tr_pi_elim2' _
         nattp 
         (app (app leqtp (subst sh1 m)) (var 0))
         (equal (app (app leqtp (subst (sh 2) m)) (var 1)) triv triv)); auto.
2:{
  simpsub.
  unfold subst1.
  rewrite -> subst_leqtp.
  auto.
  }

2:{
  simpsub.
  rewrite -> subst_leqtp.
  reflexivity.
  }
apply tr_equal_elim.
apply (nat_induction _
         (equal
            (pi nattp 
               (pi (app (app leqtp (var 1)) (var 0))
                  (equal (app (app leqtp (var 2)) (var 1)) triv triv)))
            (lam (lam triv))
            (lam (lam triv)))
         m); auto.
3:{
  simpsub.
  rewrite -> !subst_leqtp.
  reflexivity.
  }

(* 0 *)
{
simpsub.
cbn [Nat.add].
rewrite -> !subst_leqtp.
apply tr_equal_intro.
apply tr_pi_intro.
  {
  apply tr_nattp_formation.
  }
apply tr_pi_intro.
  {
  apply tr_leqtp_formation.
    {
    apply tr_nzero_nattp.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }
apply tr_equal_intro.
setoid_rewrite -> unroll_leqtp at 2.
unfold nzero at 2.
rewrite -> sumcase_left.
simpsub.
apply tr_unittp_intro.
}

(* S *)
{
simpsub.
cbn [Nat.add].
rewrite -> !subst_leqtp.
apply tr_equal_intro.
apply tr_pi_intro.
  {
  apply tr_nattp_formation.
  }
apply tr_pi_intro.
  {
  apply tr_leqtp_formation.
    {
    apply tr_nsucc_nattp.
    apply (tr_subtype_elim _ (var 4)).
      {
      apply (tr_subtype_eta2 _ _ _ (var 2) (var 2)).
      eapply hypothesis; eauto using index_S, index_0.
      }
    eapply hypothesis; eauto using index_S, index_0.
    }
  
    {
    eapply hypothesis; eauto using index_0.
    }
  }
apply tr_equal_intro.
setoid_rewrite -> unroll_leqtp at 4.
unfold nsucc at 2.
rewrite -> sumcase_right.
simpsub.
cbn [Nat.add].
rewrite -> subst_leqtp.
apply (tr_nattp_eta_hyp_triv _ [_]).
  {
  cbn [length].
  simpsub.
  cbn [Nat.add List.app].
  unfold subst1.
  rewrite -> !subst_leqtp.
  apply (tr_voidtp_elim _ (var 0) (var 0)).
  rewrite -> unroll_leqtp.
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
  cbn [Nat.add List.app].
  rewrite -> !subst_leqtp.
  unfold nsucc.
  rewrite -> unroll_leqtp at 1.
  rewrite -> !sumcase_right.
  simpsub.
  cbn [Nat.add].
  rewrite -> sumcase_right.
  simpsub.
  cbn [Nat.add].
  unfold subst1.
  rewrite -> !subst_leqtp.
  apply tr_equal_elim.
  apply (tr_equal_eta2 _#4 
           (app (app (lam (lam triv)) (var 1)) (var 0)) 
           (app (app (lam (lam triv)) (var 1)) (var 0))).
  apply (tr_pi_elim2' _ nattp (app (app leqtp (var 5)) (var 0))
           (equal (app (app leqtp (var 6)) (var 1)) triv triv)).
    {
    apply tr_equal_elim.
    apply (tr_equal_eta2 _#4
             (app (var 2) (var 4))
             (app (var 2) (var 4))).
    eapply (tr_pi_elim' _ (var 5) _).
      {
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      rewrite -> !subst_leqtp.
      cbn [Nat.add].
      reflexivity.
      }

      {
      eapply hypothesis; eauto using index_S, index_0.
      }
      
      {
      simpsub.
      cbn [Nat.add].
      rewrite -> !subst_leqtp.
      reflexivity.
      }
    }

    {
    eapply hypothesis; eauto using index_S, index_0.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
    
    {
    simpsub.
    rewrite -> subst_leqtp.
    reflexivity.
    }
  }
}
Qed.
