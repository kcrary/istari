
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
Require Import Equivalence.
Require Import Equivalences.
Require Import DefsEquiv.
Require Import Dots.
Require Import Morphism.

Require Import Defined.
Require Import SumLemmas.
Require Import PageCode.



Definition natcase {object} m n p : term object :=
  sumcase m (subst sh1 n) p.


Lemma def_nat : eq Defs.nat nattp.
Proof.
auto.
Qed.


Lemma def_succ :
  forall n,
    equiv (app Defs.succ n) (nsucc n).
Proof.
intros n.
unfold Defs.succ.
rewrite -> equiv_beta.
simpsub.
unfold Defs.inr.
simpsub.
rewrite -> equiv_beta.
simpsub.
apply equiv_refl.
Qed.


Lemma def_zero :
  equiv Defs.zero nzero.
Proof.
unfold Defs.zero.
unfold Defs.inl.
rewrite -> equiv_beta.
simpsub.
apply equiv_refl.
Qed.


Lemma def_natcase :
  forall m n p,
    equiv (app (app (app Defs.nat_case m) n) (lam p)) (natcase m n p).
Proof.
intros m n p.
unfold Defs.nat_case.
rewrite -> equiv_beta.
simpsub.
rewrite -> equiv_beta.
simpsub.
rewrite -> equiv_beta.
simpsub.
rewrite -> def_sum_case.
rewrite -> equiv_beta.
simpsub.
rewrite -> subst_var0_sh1.
apply equiv_refl.
Qed.



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


Lemma tr_nsucc_nattp_invert :
  forall G m n,
    tr G (deq (nsucc m) (nsucc n) nattp)
    -> tr G (deq m n nattp).
Proof.
intros G m n Hsucc.
cut (tr G (deq (app (lam (sumcase (var 0) nzero (var 0))) (nsucc m)) (app (lam (sumcase (var 0) nzero (var 0))) (nsucc n)) nattp)).
  {
  intro H.
  rewrite -> !equiv_beta in H.
  simpsubin H.
  unfold nsucc in H.
  rewrite -> !sumcase_right in H.
  simpsubin H.
  exact H.
  }
apply (tr_pi_elim' _ nattp nattp); auto.
apply tr_pi_intro; auto using tr_nattp_formation.
apply tr_equal_elim.
eapply (tr_nattp_eta_hyp_triv _ []).
  {
  cbn [length].
  simpsub.
  cbn [List.app].
  apply tr_equal_intro.
  unfold nzero at 1 3.
  rewrite -> sumcase_left.
  simpsub.
  apply tr_nzero_nattp.
  }

  {
  cbn [length].
  simpsub.
  cbn [List.app].
  apply tr_equal_intro.
  unfold nsucc.
  rewrite -> sumcase_right.
  simpsub.
  eapply hypothesis; eauto using index_0.
  }
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
    unfold nzero at 2 3.
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


Lemma tr_nattp_elim_eqtype :
  forall G a b c d m n,
    tr G (deq m n nattp)
    -> tr G (deqtype a b)
    -> tr (hyp_tm nattp :: G) (deqtype c d)
    -> tr G (deqtype (natcase m a c) (natcase n b d)).
Proof.
intros G a b c d m n Hm Hab Hcd.
unfold natcase.
eapply (tr_sumtype_elim_eqtype _ unittp); eauto.
  {
  apply (tr_subtype_elim _ nattp); auto.
  unfold nattp.
  apply tr_mu_unroll.
    {
    apply tr_sumtype_formation.
      {
      apply tr_unittp_istype.
      }

      {
      apply tr_hyp_tp; eauto using index_0.
      }
    }

    {
    apply tr_positive_nattp_body.
    }
  }
unfold deqtype.
exploit (tr_unittp_eta_hyp G [] triv triv (subst sh1 (eqtype a b))) as H.
  {
  simpsub.
  exact Hab.
  }
cbn [length List.app under] in H.
simpsubin H.
exact H.
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
  auto.
  }

2:{
  simpsub.
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
  reflexivity.
  }

(* 0 *)
{
simpsub.
cbn [Nat.add].
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
apply (tr_nattp_eta_hyp_triv _ [_]).
  {
  cbn [length].
  simpsub.
  cbn [Nat.add List.app].
  unfold subst1.
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
  unfold nsucc.
  rewrite -> unroll_leqtp at 1.
  rewrite -> !sumcase_right.
  simpsub.
  cbn [Nat.add].
  rewrite -> sumcase_right.
  simpsub.
  cbn [Nat.add].
  unfold subst1.
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
      cbn [Nat.add].
      reflexivity.
      }

      {
      eapply hypothesis; eauto using index_S, index_0.
      }
      
      {
      simpsub.
      cbn [Nat.add].
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
    reflexivity.
    }
  }
}
Qed.


Lemma equiv_lttp :
  forall i j, @equiv obj (app (app lttp i) j) (app (app leqtp (nsucc i)) j).
Proof.
intros i j.
unfold lttp.
apply equiv_app; auto using equiv_refl.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
unfold subst1.
apply star_refl.  
Qed.


Lemma tr_leqtp_refl :
  forall G n,
    tr G (deq n n nattp)
    -> tr G (deq triv triv (app (app leqtp n) n)).
Proof.
intros G n H.
apply (nat_induction _ (app (app leqtp (var 0)) (var 0)) n); auto.
3:{
  simpsub.
  unfold subst1.
  reflexivity.
  }

  {
  simpsub.
  unfold subst1.
  rewrite -> unroll_leqtp.
  unfold nzero.
  rewrite -> sumcase_left.
  simpsub.
  apply tr_unittp_intro.
  }

  {
  simpsub.
  unfold nsucc.
  setoid_rewrite -> unroll_leqtp at 2.
  rewrite -> sumcase_right.
  simpsub.
  rewrite -> sumcase_right.
  simpsub.
  cbn [Nat.add].
  apply (tr_leqtp_eta2 _#3 (app (var 0) (var 2)) (app (var 0) (var 2))).
    {
    apply (tr_subtype_elim _ (var 3)).
      {
      apply (tr_subtype_eta2 _#3 (var 1) (var 1)).
      eapply hypothesis; eauto using index_0, index_S.
      }

      {
      eapply hypothesis; eauto using index_0, index_S.
      }
    }

    {
    apply (tr_subtype_elim _ (var 3)).
      {
      apply (tr_subtype_eta2 _#3 (var 1) (var 1)).
      eapply hypothesis; eauto using index_0, index_S.
      }

      {
      eapply hypothesis; eauto using index_0, index_S.
      }
    }
  eapply tr_pi_elim'.
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    cbn [Nat.add].
    reflexivity.
    }
    
    {
    eapply hypothesis; eauto using index_0, index_S.
    }

    {
    simpsub.
    unfold subst1.
    reflexivity.
    }
  }
Qed.


Lemma tr_leqtp_succ :
  forall G n,
    tr G (deq n n nattp)
    -> tr G (deq triv triv (app (app leqtp n) (nsucc n))).
Proof.
intros G n Hn.
apply (nat_induction _ (app (app leqtp (var 0)) (nsucc (var 0))) n); auto.
3:{
  simpsub.
  unfold subst1.
  reflexivity.
  }

  {
  simpsub.
  unfold subst1.
  rewrite -> unroll_leqtp.
  unfold nzero.
  rewrite -> sumcase_left.
  simpsub.
  apply tr_unittp_intro.
  }

  {
  simpsub.
  unfold nsucc at 2 3.
  setoid_rewrite -> unroll_leqtp at 2.
  rewrite -> sumcase_right.
  simpsub.
  cbn [Nat.add].
  rewrite -> sumcase_right.
  fold (@nsucc obj (var 2)).
  simpsub.
  cbn [Nat.add].
  apply (tr_leqtp_eta2 _#3 (app (var 0) (var 2)) (app (var 0) (var 2))).
    {
    apply (tr_subtype_elim _ (var 3)).
      {
      apply (tr_subtype_eta2 _#3 (var 1) (var 1)).
      eapply hypothesis; eauto using index_0, index_S.
      }

      {
      eapply hypothesis; eauto using index_0, index_S.
      }
    }

    {
    apply tr_nsucc_nattp.
    apply (tr_subtype_elim _ (var 3)).
      {
      apply (tr_subtype_eta2 _#3 (var 1) (var 1)).
      eapply hypothesis; eauto using index_0, index_S.
      }

      {
      eapply hypothesis; eauto using index_0, index_S.
      }
    }
  eapply tr_pi_elim'.
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    cbn [Nat.add].
    reflexivity.
    }
    
    {
    eapply hypothesis; eauto using index_0, index_S.
    }

    {
    simpsub.
    unfold subst1.
    reflexivity.
    }
  }
Qed.


Lemma tr_leqtp_trans :
  forall G m n p,
    tr G (deq m m nattp)
    -> tr G (deq n n nattp)
    -> tr G (deq p p nattp)
    -> tr G (deq triv triv (app (app leqtp m) n))
    -> tr G (deq triv triv (app (app leqtp n) p))
    -> tr G (deq triv triv (app (app leqtp m) p)).
Proof.
intros G m n p Hm Hn Hp Hmn Hnp.
apply (tr_leqtp_eta2 _ _ _ (app (app (app (app (lam (lam (lam (lam triv)))) n) p) triv) triv) (app (app (app (app (lam (lam (lam (lam triv)))) n) p) triv) triv)); auto.
apply (tr_pi_elim4' _ nattp nattp (app (app leqtp (subst (sh 2) m)) (var 1)) (app (app leqtp (var 2)) (var 1)) (app (app leqtp (subst (sh 4) m)) (var 2))); auto.
4:{
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
apply (nat_induction _ (equal (pi nattp (pi nattp (pi (app (app leqtp (var 2)) (var 1)) (pi (app (app leqtp (var 2)) (var 1)) (app (app leqtp (var 4)) (var 2)))))) (lam (lam (lam (lam triv)))) (lam (lam (lam (lam triv))))) m); auto.
3:{
  simpsub.
  cbn [Nat.add].
  auto.
  }

  {
  simpsub.
  cbn [Nat.add].
  apply tr_equal_intro.
  apply tr_pi_intro; auto using tr_nattp_formation.
  apply tr_pi_intro; auto using tr_nattp_formation.
  apply tr_pi_intro.
    {
    apply tr_leqtp_formation.
      {
      apply tr_nzero_nattp.
      }

      {
      eapply hypothesis; eauto using index_0, index_S.
      }
    }
  apply tr_pi_intro.
    {
    apply tr_leqtp_formation.
      {
      eapply hypothesis; eauto using index_0, index_S.
      }

      {
      eapply hypothesis; eauto using index_0, index_S.
      }
    }
  setoid_rewrite -> unroll_leqtp at 3.
  unfold nzero at 2.
  rewrite -> sumcase_left.
  simpsub.
  apply tr_unittp_intro.
  }

  {
  simpsub.
  cbn [Nat.add].
  apply tr_equal_intro.
  apply tr_pi_intro; auto using tr_nattp_formation.
  apply tr_pi_intro; auto using tr_nattp_formation.
  apply tr_pi_intro.
    {
    apply tr_leqtp_formation.
      {
      apply tr_nsucc_nattp.
      apply (tr_subtype_elim _ (var 5)).
        {
        apply (tr_subtype_eta2 _#3 (var 3) (var 3)).
        eapply hypothesis; eauto using index_0, index_S.
        }

        {
        eapply hypothesis; eauto using index_0, index_S.
        }
      }

      {
      eapply hypothesis; eauto using index_0, index_S.
      }
    }
  apply tr_pi_intro.
    {
    apply tr_leqtp_formation.
      {
      eapply hypothesis; eauto using index_0, index_S.
      }

      {
      eapply hypothesis; eauto using index_0, index_S.
      }
    }
  setoid_rewrite -> unroll_leqtp at 6.
  unfold nsucc at 2.
  rewrite -> sumcase_right.
  simpsub.
  cbn [Nat.add].
  eapply (tr_nattp_eta_hyp_triv _ [_; _; _]).
    {
    simpsub.
    cbn [length].
    simpsub.
    cbn [Nat.add List.app].
    setoid_rewrite -> unroll_leqtp at 2.
    unfold nsucc at 1.
    rewrite -> sumcase_right.
    simpsub.
    unfold nzero at 2.
    rewrite -> sumcase_left.
    simpsub.
    apply (tr_voidtp_elim _ (var 1) (var 1)).
    eapply hypothesis; eauto using index_0, index_S.
    }
  cbn [length].
  simpsub.
  cbn [length].
  simpsub.
  cbn [Nat.add List.app].
  setoid_rewrite -> unroll_leqtp at 2.
  unfold nsucc at 2.
  rewrite -> sumcase_right.
  simpsub.
  rewrite -> sumcase_right.
  simpsub.
  cbn [Nat.add].
  eapply (tr_nattp_eta_hyp_triv _ [_; _]).
    {
    simpsub.
    cbn [length].
    simpsub.
    cbn [Nat.add List.app].
    setoid_rewrite -> unroll_leqtp at 1.
    unfold nsucc at 1.
    rewrite -> sumcase_right.
    simpsub.
    unfold nzero at 1.
    rewrite -> sumcase_left.
    simpsub.
    apply (tr_voidtp_elim _ (var 0) (var 0)).
    eapply hypothesis; eauto using index_0.
    }
  cbn [length].
  simpsub.
  cbn [length].
  simpsub.
  cbn [Nat.add List.app].
  setoid_rewrite -> unroll_leqtp at 1.
  unfold nsucc.
  rewrite -> sumcase_right.
  simpsub.
  rewrite -> sumcase_right.
  simpsub.
  cbn [Nat.add].
  rewrite -> sumcase_right.
  simpsub.
  cbn [Nat.add].
  apply (tr_leqtp_eta2 _#3 (app (app (app (app (lam (lam (lam (lam triv)))) (var 3)) (var 2)) (var 1)) (var 0)) (app (app (app (app (lam (lam (lam (lam triv)))) (var 3)) (var 2)) (var 1)) (var 0))).
    {
    apply (tr_subtype_elim _ (var 7)).
      {
      apply (tr_subtype_eta2 _#3 (var 5) (var 5)).
      eapply hypothesis; eauto 7 using index_0, index_S.
      }
    eapply hypothesis; eauto 7 using index_0, index_S.
    }
  
    {
    eapply hypothesis; eauto using index_0, index_S.
    }
  eapply tr_pi_elim4'; eauto.
    {
    apply tr_equal_elim.
    eapply (tr_equal_eta2 _#4 (app (var 4) (var 6)) (app (var 4) (var 6))).
    eapply tr_pi_elim'; eauto.
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
Qed.


Definition natmax {object} m n : term object :=
  app (app (app theta
              (lam (lam (lam (natcase (var 1) 
                                (var 0)
                                (natcase (var 1)
                                   (var 2)
                                   (nsucc
                                      (app (app (var 4) (var 1)) (var 0)))))))))
         m)
    n.


Lemma subst_natmax :
  forall object s m n,
    @subst object s (natmax m n) = natmax (subst s m) (subst s n).
Proof.
intros object s m n.
unfold natmax.
simpsub.
reflexivity.
Qed.


Lemma subst_natcase :
  forall object s m n p,
    @subst object s (natcase m n p) = natcase (subst s m) (subst s n) (subst (under 1 s) p).
Proof.
intros object s m n p.
unfold natcase.
simpsub.
reflexivity.
Qed.


Hint Rewrite subst_natcase subst_natmax : subst.


Lemma natcase_zero :
  forall n p,
    @equiv obj (natcase nzero n p) n.
Proof.
intros n p.
unfold natcase, nzero.
rewrite -> sumcase_left.
simpsub.
apply equiv_refl.
Qed.


Lemma natcase_succ :
  forall m n p,
    @equiv obj (natcase (nsucc m) n p) (subst1 m p).
Proof.
intros m n p.
unfold natcase, nsucc.
rewrite -> sumcase_right.
apply equiv_refl.
Qed.


Lemma tr_nat_total :
  forall G m,
    tr G (deq m m nattp)
    -> tr G (deq triv triv (halts m)).
Proof.
intros G m Hm.
apply (tr_sum_total _ unittp nattp).
eapply tr_subtype_elim; eauto.
replace (sumtype unittp nattp) with (@subst1 obj nattp (sumtype unittp (var 0))) by (simpsub; reflexivity).
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
Qed.
