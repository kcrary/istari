
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Relation.
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

Require Import Dynamic.
Require ValidationPi.
Require ValidationSigma.



Definition preacc_body (A R : Defs.fterm) : Defs.fterm :=
  sigma (subst sh1 A)
    (pi (subst (sh 2) A)
       (pi
          (app (app (subst (sh 3) R) (var 0)) (var 1))
          (var 3))).


Definition preacc (A R : Defs.fterm) : Defs.fterm :=
  mu (sigma (subst sh1 A)
        (pi (subst (sh 2) A)
           (pi
              (app (app (subst (sh 3) R) (var 0)) (var 1))
              (var 3)))).


Definition wf (A R a x : Defs.fterm) : Defs.fterm :=
  (app
     (app
        (app
           Defined.theta
             (lam
                (lam
                   (lam
                      (sigma 
                         (equal (subst (sh 3) A) (var 0) (ppi1 (var 1)))
                         (pi (subst (sh 4) A)
                            (pi 
                               (app (app (subst (sh 5) R) (var 0)) (var 2))
                               (app
                                  (app 
                                     (var 5)
                                     (app (app (ppi2 (var 4)) (var 1)) (var 0)))
                                  (var 1)))))))))
        a)
     x).


Lemma def_acc :
  forall A R x,
    equiv
      (app (app (app Defs.acc A) R) x)
      (sigma (preacc A R) (wf (subst sh1 A) (subst sh1 R) (var 0) (subst sh1 x))).
Proof.
intros A R x.
unfold Defs.acc, preacc, wf.
apply steps_equiv.
eapply star_trans.
  {
  eapply star_trans.
    {
    apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
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
  apply star_one.
  apply step_app2.
  }
simpsub.
cbn [Nat.add].
apply star_refl.
Qed.



Hint Rewrite def_arrow def_pi def_acc : prepare.



Lemma subst_preacc :
  forall s A R,
    subst s (preacc A R) = preacc (subst s A) (subst s R).
Proof.
intros.
unfold preacc.
simpsub.
auto.
Qed.


Lemma subst_wf :
  forall s A R a x,
    subst s (wf A R a x) = wf (subst s A) (subst s R) (subst s a) (subst s x).
Proof.
intros.
unfold wf.
simpsub.
auto.
Qed.



Hint Rewrite subst_preacc subst_wf : subst.



Lemma wf_unroll :
  forall A R a x,
    equiv
      (wf A R a x)
      (sigma
         (equal A x (ppi1 a))
         (pi (subst sh1 A)
            (pi
               (app (app (subst (sh 2) R) (var 0)) (subst (sh 2) x))
               (wf (subst (sh 3) A) (subst (sh 3) R) 
                  (app (app (ppi2 (subst (sh 3) a)) (var 1)) (var 0))
                  (var 1)))))
.
Proof.
intros A R a x.
unfold wf.
apply steps_equiv.
eapply star_trans.
  {
  apply (star_map' _ _ (fun z => app z _)); auto using step_app1.
  eapply star_trans.
    {
    apply (star_map' _ _ (fun z => app z _)); auto using step_app1.
    apply PageType.theta_fix.
    }
  eapply star_step.
    {
    apply step_app1.
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
  }
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.



Lemma preacc_body_form :
  forall G a r lv,
    tr G (deq a a (univ lv))
    -> tr G (deq r r (pi a (pi (subst sh1 a) (univ (subst (sh 2) lv)))))
    -> tr (hyp_tp :: G) (deqtype (preacc_body a r) (preacc_body a r)).
Proof.
intros G a r lv Ha Hr.
unfold preacc_body.
simpsub.
cbn [Nat.add].
apply tr_sigma_formation.
  {
  eapply (weakening _ [_] []).
    {
    cbn [unlift length].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length].
  simpsub.
  apply (tr_formation_weaken _ lv).
  exact Ha.
  }
apply tr_pi_formation.
  {
  eapply (weakening _ [_; _] []).
    {
    cbn [unlift length].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length].
  simpsub.
  apply (tr_formation_weaken _ lv).
  exact Ha.
  }
apply tr_pi_formation.
  {
  apply (tr_formation_weaken _ (subst (sh 3) lv)).
  eapply (tr_pi_elim2' _ (subst (sh 3) a) (subst (sh 4) a) (univ (subst (sh 5) lv))).
    {
    eapply (weakening _ [_; _; _] []).
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
    eauto.
    }
  
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    auto.
    }

    {
    eapply hypothesis; eauto using index_S, index_0.
    simpsub.
    auto.
    }

    {
    simpsub.
    auto.
    }
  }

  {
  apply tr_hyp_tp.
  eauto using index_S, index_0.
  }
Qed.


Lemma preacc_body_positive :
  forall G a r,
    tr G (deq triv triv (ispositive (preacc_body a r))).
Proof.
intros G a r.
apply (tr_positive_algorithm _ _ [] []).
  {
  unfold preacc_body.
  simpsub.
  cbn [Nat.add].
  apply hpositive_sigma.
    {
    replace (subst sh1 a) with (subst (under 0 sh1) a).
    2:{
      simpsub.
      auto.
      }
    apply hpositive_const.
    }
  apply hpositive_pi.
    {
    replace (subst (sh 2) a) with (subst (under 1 sh1) (subst (sh 1) a)).
    2:{
      simpsub.
      auto.
      }
    apply hnegative_const.
    }
  apply hpositive_pi.
    {
    replace (app (app (subst (sh 3) r) (var 0)) (var 1)) with (subst (under 2 sh1) (app (app (subst (sh 2) r) (var 0)) (var 1))).
    2:{
      simpsub.
      auto.
      }
    apply hnegative_const.
    }
  apply hpositive_var.
  }

  {
  intros l H.
  destruct H.
  }

  {
  intros l H.
  destruct H.
  }
Qed.



Lemma wf_formation :
  forall G a r m x lv,
    tr G (deq a a (univ lv))
    -> tr G (deq r r (pi a (pi (subst sh1 a) (univ (subst (sh 2) lv)))))
    -> tr G (deq m m (preacc a r))
    -> tr G (deq x x a)
    -> tr G (deq (wf a r m x) (wf a r m x) (univ lv)).
Proof.
intros G a r m x lv Ha Hr Hm Hx.
apply tr_equal_elim.
assert (equiv triv ((app (lam triv) x) : Defs.fterm)) as Heq.
  {
  apply equiv_symm.
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
rewrite -> Heq; clear Heq.
eapply (tr_pi_elim' _ a (equal (univ (subst sh1 lv)) (wf (subst sh1 a) (subst sh1 r) (subst sh1 m) (var 0)) (wf (subst sh1 a) (subst sh1 r) (subst sh1 m) (var 0)))).
  {
  apply tr_equal_elim.
  match goal with
  | |- tr _ (deq _ _ ?X) =>
     replace X with
     (subst1 m
        (equal 
           (pi (subst sh1 a)
              (equal
                 (univ (subst (sh 2) lv))
                 (wf (subst (sh 2) a) (subst (sh 2) r) (var 1) (var 0))
                 (wf (subst (sh 2) a) (subst (sh 2) r) (var 1) (var 0))))
           (lam triv) (lam triv)))
  end.
  2:{
    simpsub.
    auto.
    }
  apply (tr_mu_ind _ (preacc_body a r)).
    {
    eapply preacc_body_form; eauto.
    }

    {
    apply preacc_body_positive.
    }

  2:{
    exact Hm.
    }
  simpsub.
  cbn [Nat.add].
  apply tr_equal_intro.
  apply tr_pi_intro.
    {
    eapply (weakening _ [_; _; _; _] []).
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
    eapply tr_formation_weaken; eauto.
    }
  apply tr_equal_intro.
  setoid_rewrite -> wf_unroll at 3 4.
  apply tr_sigma_formation_univ.
    {
    apply tr_equal_formation_univ.
      {
      eapply (weakening _ [_; _; _; _; _] []).
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
      exact Ha.
      }
    
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      auto.
      }

      {
      eapply tr_sigma_elim1.
      eapply hypothesis; eauto using index_S, index_0.
      unfold preacc_body.
      simpsub.
      cbn [Nat.add].
      eauto.
      }
    }

    {
    simpsub.
    cbn [Nat.add].
    apply tr_pi_formation_univ.
      {
      eapply (weakening _ [_; _; _; _; _; _] []).
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
      exact Ha.
      }
    apply tr_pi_formation_univ.
      {
      eapply (tr_pi_elim2' _ (subst (sh 7) a) (subst (sh 8) a) (univ (subst (sh 9) lv))).
        {
        eapply (weakening _ [_; _; _; _; _; _; _] []).
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
        eauto.
        }
      
        {
        eapply hypothesis; eauto using index_0.
        simpsub.
        auto.
        }
  
        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        auto.
        }
  
        {
        simpsub.
        auto.
        }
      }
    simpsub.
    cbn [Nat.add].


    unfold preacc_body.
    set (u := (app
                 (app 
                    (ppi2 (var 6))
                    (var 1))
                 (var 0)) : Defs.fterm).
    match goal with
    | |- tr ?G' _ =>
       assert (tr G' (deq u u (var 7))) as Hofu
    end.
      {
      subst u.
      eapply (tr_pi_elim2' _
                (subst (sh 8) a)
                (app (app (subst (sh 9) r) (var 0)) (var 4))
                (var 9)).
        {
        eapply tr_eqtype_convert.
        2:{
          eapply tr_sigma_elim2.
          eapply hypothesis; eauto 7 using index_S, index_0.
          simpsub.
          cbn [Nat.add].
          eauto.
          }
  
          {
          simpsub.
          cbn [Nat.add].
          apply tr_pi_formation.
            {
            eapply (weakening _ [_; _; _; _; _; _; _; _] []).
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
            cbn [unlift length List.app].
            simpsub.
            cbn [Nat.add List.app].
            apply (tr_formation_weaken _ lv).
            exact Ha.
            }
          apply tr_pi_formation.
            {
            apply (tr_formation_weaken _ (subst (sh 9) lv)).
            eapply (tr_pi_elim2' _
                      (subst (sh 9) a)
                      (subst (sh 10) a)
                      (subst (sh 11) (univ lv))).
              {
              eapply (weakening _ [_; _; _; _; _; _; _; _; _] []).
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
              cbn [unlift length List.app].
              simpsub.
              cbn [Nat.add List.app].
              exact Hr.
              }
              
              {
              eapply hypothesis; eauto using index_0.
              simpsub.
              auto.
              }
  
              {
              simpsub.
              apply tr_symmetry.
              apply tr_equal_elim.
              apply (tr_equal_eta2 _#4 (var 3) (var 3)).
              eapply hypothesis; eauto using index_S, index_0.
              simpsub.
              auto.
              }
              
              {
              simpsub.
              auto.
              }
            }
          
            {
            apply tr_hyp_tp.
            repeat (apply index_S).
            apply index_0.
            }
          }
        }
  
        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        auto.
        }
  
        {
        simpsub.
        eapply hypothesis; eauto using index_0.
        simpsub.
        auto.
        }
  
        {
        simpsub.
        auto.
        }
      }
    apply tr_equal_elim.
    apply (tr_equal_eta2 _#4 (app (lam triv) (var 1)) (app (lam triv) (var 1))).
    eapply (tr_pi_elim' _
              (subst (sh 8) a) 
              (equal (univ (subst (sh 9) lv))
                 (wf (subst (sh 9) a) (subst (sh 9) r) (subst sh1 u) (var 0))
                 (wf (subst (sh 9) a) (subst (sh 9) r) (subst sh1 u) (var 0)))).
      {
      apply tr_equal_elim.
      apply (tr_equal_eta2 _#4 (app (var 4) u) (app (var 4) u)).
      eapply tr_pi_elim'.
        {
        eapply hypothesis; eauto using index_S, index_0.
        simpsub.
        cbn [Nat.add].
        eauto.
        }

        {
        exact Hofu.
        }

        {
        simpsub.
        auto.
        }
      }

      {
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      auto.
      }
      
      {
      simpsub.
      auto.
      }
    }
  }

  {
  exact Hx.
  }

  {
  simpsub.
  auto.
  }
Qed.



Lemma accInd_valid : accInd_obligation.
Proof.
prepare.
intros G a b lv m n r ext3 ext2 p ext1 ext0 Ha Hr Hp Hm Hn.
simpsubin Hr.
simpsubin Hp.
cbn [Nat.add] in Hr, Hp.
match goal with
| |- tr _ (deq (app (app _ ?X) _) _ _) => set (fb := X)
end.
set (f := app Defs.theta fb).
cut (tr (hyp_tm (preacc a r) :: G)
       (deq
          (lam (lam (app (subst (sh 3) f) (var 1))))
          (lam (lam (app (subst (sh 3) f) (var 1))))
          (pi (subst sh1 a)
             (pi (wf (subst (sh 2) a) (subst (sh 2) r) (var 1) (var 0))
                (subst (dot (var 1) (sh 3)) b))))).
  {
  intro Hind.
  assert (equiv
            (app f m)
            (app
               (app
                  (lam (lam (app (subst (sh 2) f) (var 1))))
                  m)
               (ppi2 n))) as Heq.
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_step.
      {
      apply step_app1.
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
  rewrite -> Heq; clear Heq.
  apply (tr_pi_elim2' _ a (wf (subst sh1 a) (subst sh1 r) (ppi1 (subst sh1 n)) (var 0)) (subst (dot (var 1) (sh 2)) b)).
    {
    match goal with
    | |- tr _ ?X =>
       replace X with
       (substj (dot (ppi1 n) id)
          (deq
             (lam (lam (app (subst (sh 3) f) (var 1))))
             (lam (lam (app (subst (sh 3) f) (var 1))))
             (pi (subst sh1 a)
                (pi (wf (subst (sh 2) a) (subst (sh 2) r) (var 1) (var 0))
                   (subst (dot (var 1) (sh 3)) b)))))
    end.
    2:{
      simpsub.
      auto.
      }
    apply (tr_generalize _ (preacc a r)).
      {
      unfold preacc.
      eapply tr_sigma_elim1; eauto.
      }
    exact Hind.
    }

    {
    auto.
    }

    {
    eapply tr_sigma_elim2'; eauto.
    simpsub.
    auto.
    }
    
    {
    simpsub.
    auto.
    }
  }
apply tr_equal_elim.
match goal with
| |- tr _ (deq _ _ ?X) => set (b' := X)
end.
replace b' with (subst1 (var 0) (subst (dot (var 0) (sh 2)) b')).
2:{
  simpsub.
  apply subst_var0_sh1.
  }
apply (tr_mu_ind _ (preacc_body (subst sh1 a) (subst sh1 r)) (subst (dot (var 0) (sh 2)) b') (var 0)).
  {
  eapply (preacc_body_form _ _ _ (subst sh1 lv)).
    {
    (* This idiom happens a LOT. I should have figured out a way to generalize it, rather than cutting and pasting. *)
    eapply (weakening _ [_] []).
      {
      cbn [unlift length].
      simpsub.
      auto.
      }
  
      {
      unfold preacc_body.
      cbn [length unlift].
      simpsub.
      auto.
      }
    cbn [unlift length].
    simpsub.
    exact Ha.
    }

    {
    eapply (weakening _ [_] []).
      {
      cbn [unlift length].
      simpsub.
      auto.
      }
  
      {
      unfold preacc_body.
      cbn [length unlift].
      simpsub.
      auto.
      }
    cbn [unlift length].
    simpsub.
    exact Hr.
    }
  }

  {
  apply preacc_body_positive.
  }

2:{
  eapply hypothesis; eauto using index_0.
  simpsub.
  auto.
  }
unfold preacc_body.
match goal with
| |- tr (_ :: hyp_tm (subtype _ ?X) :: _) _ =>
  replace X with (preacc (subst (sh 3) a) (subst (sh 3) r))
end.
2:{
  unfold preacc.
  simpsub.
  auto.
  }
simpsub.
cbn [Nat.add].
eapply (weakening _ [_] [_; _; _; _]).
  {
  cbn [unlift length].
  simpsub.
  cbn [length List.app Nat.add].
  simpsub.
  cbn [Nat.add].
  auto.
  }

  {
  cbn [unlift length].
  simpsub.
  auto.
  }
cbn [unlift length].
simpsub.
cbn [List.app length Nat.add].
simpsub.
cbn [Nat.add].
unfold b' at 2.
simpsub.
cbn [Nat.add].
apply tr_equal_intro.
apply tr_pi_intro.
  {
  eapply (weakening _ [_; _; _; _] []).
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
  eapply tr_formation_weaken; eauto.
  }
apply tr_pi_intro.
  {
  apply (tr_formation_weaken _ (subst (sh 5) lv)).
  apply wf_formation.
    {
    eapply (weakening _ [_; _; _; _; _] []).
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
    exact Ha.
    }

    {
    eapply (weakening _ [_; _; _; _; _] []).
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
    exact Hr.
    }

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
    cbn [Nat.add List.app].
    simpsub.
    unfold preacc.
    eapply tr_subtype_elim.
      {
      apply tr_mu_roll.
        {
        eapply (preacc_body_form _#3 (subst (sh 3) lv)).
          {
          eapply (weakening _ [_; _; _] []).
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
          exact Ha.
          }

          {
          eapply (weakening _ [_; _; _] []).
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
          exact Hr.
          }
        }

        {
        apply preacc_body_positive.
        }
      }
    match goal with
    | |- tr _ (deq _ _ (subst1 ?X _)) =>
        replace X with (subst (sh 3) (preacc a r))
    end.
    2:{
      unfold preacc.
      simpsub.
      auto.
      }
    simpsub.
    cbn [Nat.add].
    eapply tr_subtype_elim.
    2:{
      apply tr_hyp_tm.
      auto using index_S, index_0.
      }
    simpsub.
    cbn [Nat.add].
    apply ValidationSigma.tr_sigma_sub.
      {
      eapply (weakening _ [_; _; _] []).
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
      apply tr_subtype_refl.
      eapply tr_formation_weaken.
      exact Ha.
      }

      {
      apply ValidationPi.tr_pi_sub.
        {
        eapply (weakening _ [_; _; _; _] []).
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
        apply tr_subtype_refl.
        eapply tr_formation_weaken.
        exact Ha.
        }

        {
        apply ValidationPi.tr_pi_sub.
          {
          apply tr_subtype_refl.
          apply (tr_formation_weaken _ (subst (sh 5) lv)).
          eapply (tr_pi_elim2' _
                    (subst (sh 5) a)
                    (subst (sh 6) a)
                    (subst (sh 7) (univ lv))).
            {
            eapply (weakening _ [_; _; _; _; _] []).
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
            cbn [unlift length List.app].
            simpsub.
            cbn [Nat.add List.app].
            exact Hr.
            }
            
            {
            eapply hypothesis; eauto using index_0.
            simpsub.
            auto.
            }

            {
            simpsub.
            eapply hypothesis; eauto using index_S, index_0.
            simpsub.
            eauto.
            }
  
            {
            simpsub.
            auto.
            }
          }

          {
          apply (tr_subtype_eta2 _#3 (var 3) (var 3)).
          eapply hypothesis; eauto using index_S, index_0.
          simpsub.
          cbn [Nat.add].
          unfold preacc.
          simpsub.
          auto.
          }
  
          {
          apply tr_hyp_tp.
          auto 7 using index_S, index_0.
          }
        }

        {
        apply tr_pi_formation.
          {
          apply (tr_formation_weaken _ (subst (sh 5) lv)).
          eapply (tr_pi_elim2' _ (subst (sh 5) a) (subst (sh 6) a) (univ (subst (sh 7) lv))).
            {
            eapply (weakening _ [_; _; _; _; _] []).
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
            eauto.
            }
          
            {
            eapply hypothesis; eauto using index_0.
            simpsub.
            auto.
            }
      
            {
            eapply hypothesis; eauto using index_S, index_0.
            simpsub.
            auto.
            }
      
            {
            simpsub.
            auto.
            }
          }

          {
          apply tr_hyp_tp.
          auto 6 using index_S, index_0.
          }
        }
      }

      {
      apply tr_pi_formation.
        {
        eapply (weakening _ [_; _; _; _] []).
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
        eapply tr_formation_weaken.
        exact Ha.
        }
      apply tr_pi_formation.
        {
        apply (tr_formation_weaken _ (subst (sh 5) lv)).
        eapply (tr_pi_elim2' _ (subst (sh 5) a) (subst (sh 6) a) (univ (subst (sh 7) lv))).
          {
          eapply (weakening _ [_; _; _; _; _] []).
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
          eauto.
          }
        
          {
          eapply hypothesis; eauto using index_0.
          simpsub.
          auto.
          }
    
          {
          eapply hypothesis; eauto using index_S, index_0.
          simpsub.
          auto.
          }
    
          {
          simpsub.
          auto.
          }
        }
      replace (preacc (subst (sh 6) a) (subst (sh 6) r)) with (mu (preacc_body (subst (sh 6) a) (subst (sh 6) r))).
      2:{
        unfold preacc.
        unfold preacc_body.
        auto.
        }
      apply tr_mu_formation.
        {
        eapply (preacc_body_form _#3 (subst (sh 6) lv)).
          {
          eapply (weakening _ [_; _; _; _; _; _] []).
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
          eauto.
          }

          {
          eapply (weakening _ [_; _; _; _; _; _] []).
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
          eauto.
          }
        }

        {
        apply preacc_body_positive.
        }

        {
        apply preacc_body_positive.
        }
      }
    }

    {
    eapply hypothesis; eauto using index_S, index_0.
    simpsub.
    auto.
    }
  }
assert (equiv f (app fb f)) as Heq.
  {
  unfold f.
  rewrite -> theta_equiv at 1.
  apply equiv_refl.
  }
rewrite -> Heq; clear Heq.
set (f' := (lam (lam (app (subst (sh 8) f) (var 1))))).
unfold fb.
simpsub.
cbn [Nat.add].
match goal with
| |- tr _ (deq ?X _ _) => assert (equiv X (subst (dot f' (dot (var 1) (sh 6))) p)) as Heq
end.
  {
  subst f' fb f.
  simpsub.
  cbn [Nat.add].
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app1.
    apply step_app2.
    }
  simpsub.
  cbn [Nat.add].
  simpsub.
  cbn [Nat.add].
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  cbn [Nat.add].
  apply star_refl.
  }
rewrite -> Heq; clear Heq.
match goal with
| |- tr _ ?X =>
   assert (equivj X (substj (dot f' id)
                      (deq
                         (subst (dot (var 0) (dot (var 2) (sh 7))) p)
                         (subst (dot (var 0) (dot (var 2) (sh 7))) p)
                         (subst (dot (var 2) (sh 7)) b)))) as Heq
end.
  {
  simpsub.
  cbn [Nat.add].
  apply equivj_refl.
  }
rewrite -> Heq; clear Heq.
apply (tr_generalize _ 
         (pi (subst (sh 6) a)
            (pi (app (app (subst (sh 7) r) (var 0)) (var 2))
               (subst (dot (var 1) (sh 8)) b)))).
  {
  subst f'.
  apply tr_pi_intro.
    {
    eapply (weakening _ [_; _; _; _; _; _] []).
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
    eapply tr_formation_weaken; eauto.
    }
  apply tr_pi_intro.
    {
    apply (tr_formation_weaken _ (subst (sh 7) lv)).
    eapply (tr_pi_elim2' _ (subst (sh 7) a) (subst (sh 8) a) (univ (subst (sh 9) lv))).
      {
      eapply (weakening _ [_; _; _; _; _; _; _] []).
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
      eauto.
      }
    
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      auto.
      }

      {
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      auto.
      }

      {
      simpsub.
      auto.
      }
    }
  assert (equiv
            (app (subst (sh 8) f) (var 1))
            (app
               (app
                  (lam (lam (app (subst (sh 10) f) (var 1))))
                  (var 1))
               (app
                  (app (ppi2 (var 2)) (var 1))
                  (var 0)))) as Heq.
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_step.
      {
      apply step_app1.
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
  rewrite -> Heq; clear Heq.
  match goal with
  | |- tr ?X _ => set (G' := X)
  end.
  set (u := (app
               (app 
                  (ppi2 (var 6))
                  (var 1))
               (var 0)) : Defs.fterm).
  assert (tr G' (deq u u (var 7))) as Hofu.
    {
    subst u.
    eapply (tr_pi_elim2' _
              (subst (sh 8) a)
              (app (app (subst (sh 9) r) (var 0)) (var 4))
              (var 9)).
      {
      eapply tr_eqtype_convert.
      2:{
        eapply tr_sigma_elim2.
        eapply hypothesis; eauto 7 using index_S, index_0.
        simpsub.
        cbn [Nat.add].
        eauto.
        }

        {
        simpsub.
        cbn [Nat.add].
        apply tr_pi_formation.
          {
          eapply (weakening _ [_; _; _; _; _; _; _; _] []).
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
          cbn [unlift length List.app].
          simpsub.
          cbn [Nat.add List.app].
          apply (tr_formation_weaken _ lv).
          exact Ha.
          }
        apply tr_pi_formation.
          {
          apply (tr_formation_weaken _ (subst (sh 9) lv)).
          eapply (tr_pi_elim2' _
                    (subst (sh 9) a)
                    (subst (sh 10) a)
                    (subst (sh 11) (univ lv))).
            {
            eapply (weakening _ [_; _; _; _; _; _; _; _; _] []).
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
            cbn [unlift length List.app].
            simpsub.
            cbn [Nat.add List.app].
            exact Hr.
            }
            
            {
            eapply hypothesis; eauto using index_0.
            simpsub.
            auto.
            }

            {
            subst G'.
            simpsub.
            apply tr_symmetry.
            apply tr_equal_elim.
            apply (tr_equal_eta2 _#4 (ppi1 (var 3)) (ppi1 (var 3))).
            eapply tr_sigma_elim1.
            match goal with
            | |- tr ?X _ =>
               eassert (tr X (deq (var 3) (var 3) _)) as H
            end.
              {
              eapply tr_hyp_tm; eauto using index_S, index_0.
              }
            simpsubin H.
            cbn [Nat.add] in H.
            setoid_rewrite -> wf_unroll in H at 2.
            exact H.
            }
            
            {
            simpsub.
            auto.
            }
          }
        
          {
          subst G'.
          apply tr_hyp_tp.
          repeat (apply index_S).
          apply index_0.
          }
        }
      }

      {
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      auto.
      }

      {
      simpsub.
      eapply hypothesis; eauto using index_0.
      simpsub.
      auto.
      }

      {
      simpsub.
      auto.
      }
    }
  eapply (tr_pi_elim2' _ 
           (subst (sh 8) a)
           (wf (subst (sh 9) a) (subst (sh 9) r) (subst sh1 u) (var 0))
           (subst (dot (var 1) (sh 10)) b)).
    {
    apply tr_equal_elim.
    apply (tr_equal_eta2 _#4 (app (var 4) u) (app (var 4) u)).
    eapply tr_pi_elim'.
      {
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      cbn [Nat.add].
      eauto.
      }

      {
      exact Hofu.
      }

      {
      subst b'.
      simpsub.
      cbn [Nat.add].
      auto.
      }
    }
  
    {
    eapply hypothesis; eauto using index_S, index_0.
    simpsub.
    auto.
    }

    {
    simpsub.
    eapply (tr_pi_elim2' _
              (subst (sh 8) a)
              (app (app (subst (sh 9) r) (var 0)) (var 4))
              (wf 
                 (subst (sh 10) a) (subst (sh 10) r)
                 (app (app (ppi2 (var 8)) (var 1)) (var 0))
                 (var 1))).
      {
      eapply tr_sigma_elim2'.
        {
        eassert (tr G' (deq (var 2) (var 2) _)) as H.
          {
          eapply hypothesis; eauto using index_S, index_0.
          }
        simpsubin H.
        cbn [Nat.add] in H.
        rewrite -> wf_unroll in H.
        simpsubin H.
        cbn [Nat.add] in H.
        exact H.
        }
      simpsub.
      auto.
      }
      
      {
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      auto.
      }

      {
      simpsub.
      eapply hypothesis; eauto using index_0.
      simpsub.
      auto.
      }
      
      {
      simpsub.
      auto.
      }
    }

    {
    simpsub.
    auto.
    }
  }
eapply (weakening _ [_] [_]).
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
cbn [unlift length List.app].
simpsub.
cbn [Nat.add List.app].
eapply (weakening _ [_; _; _; _] [_; _]).
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
cbn [unlift length List.app].
simpsub.
cbn [length Nat.add List.app].
simpsub.
cbn [Nat.add].
rewrite -> !subst_var01_sh2.
replace (subst (dot (var 1) (sh 2)) b) with (subst sh1 b).
2:{
  rewrite <- (subst_under_id _ 1 b) at 1.
  simpsub.
  auto.
  }
exact Hp.
Qed.
