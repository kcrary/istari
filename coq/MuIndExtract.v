
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Axioms.
Require Import Tactics.
Require Import Equality.
Require Import Sequence.
Require Import Relation.
Require Import Syntax.
Require Import SimpSub.
Require Import Dynamic.
Require Import Equivalence.
Require Import PageType.
Require Import Equivalences.
Require Import Rules.
Require Import Defined.
Require Import DerivedRules.


Definition sterm := term obj.
Definition shyp := @hyp obj.
Definition scontext := @context obj.
Definition sjudgement := @judgement obj.
Definition ssub := @sub obj.


(* This is tedious. *)
Lemma tr_mu_ind_extract :
  forall G a b m n,
    tr (hyp_tp :: G) (deqtype a a)
    -> tr G (deq triv triv (ispositive a))
    -> tr
         (hyp_tm (pi (var 2) (subst (under 1 (sh 3)) b)) ::
          hyp_tm (subtype (var 1) (mu (subst (under 1 (sh 2)) a))) ::
          hyp_tm a ::
          hyp_tp :: 
          G)
         (deq (subst (under 3 sh1) n) (subst (under 3 sh1) n) (subst (dot (var 2) (sh 4)) b))
    -> tr G (deq m m (mu a))
    -> tr G (deq 
                 (app
                    (app theta
                       (lam (lam
                               (subst (dot (var 1) (dot triv (dot (var 0) (sh 2)))) n))))
                    m)
                 (app
                    (app theta
                       (lam (lam
                               (subst (dot (var 1) (dot triv (dot (var 0) (sh 2)))) n))))
                    m)
                 (subst1 m b)).
Proof.
intros G a b m p Ha Hmono Hn Hm.
set (f := (app theta
             (lam (lam
                     (subst (dot (var 1) (dot triv (dot (var 0) (sh 2)))) p))))).
set (c := equal b (app (subst sh1 f) (var 0)) (app (subst sh1 f) (var 0))).
cut (tr G (deq triv triv (subst1 m c))).
  {
  intro Hseq.
  unfold c in Hseq.
  simpsubin Hseq.
  so (tr_equal_elim _#4 Hseq) as H.
  exact H.
  }
apply (tr_mu_ind _ a); auto.
subst c.
simpsub.
apply tr_equal_intro.
replace (subst (dot (var 2) (sh 4)) b) with (subst1 (var 2) (subst (under 1 (sh 4)) b)).
2:{
  simpsub.
  change (4 + 1) with 5.
  simpsub.
  reflexivity.
  }
apply (tr_pi_elim _ (subst (sh 3) a)).
2:{
  simpsub.
  apply tr_hyp_tm.
  apply index_S.
  apply index_S.
  apply index_0.
  }
cbn [Nat.add].
apply (weakening _ [_] [_; _]).
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
cbn [List.app length unlift].
simpsub.
cbn [List.app length Nat.add].
simpsub.
cbn [Nat.add].
assert (equiv f
          (lam (subst (dot (subst sh1 f) (dot triv (dot (var 0) sh1))) p))) as Hequivf.
  {
  apply steps_equiv.
  eapply star_trans.
    {
    apply theta_fix.
    }
  fold f.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
refine (tr_compute _#7 (equiv_refl _ _) (equiv_subst _ (sh 3) _ _ Hequivf) (equiv_subst _ (sh 3) _ _ Hequivf) _).
simpsub.
cbn [Nat.add].
apply tr_pi_intro.
  {
  apply (weakening _ [_; _] []); auto.
    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  auto.
  }
replace (hyp_tm (subst (sh 2) a)) with (substh sh1 (hyp_tm (subst sh1 a))) by (simpsub; auto).
match goal with
| |- tr _ ?X =>
   replace X with
   (deq 
      (subst (under 0 (dot (var 1) (dot (var 0) (sh 2))))
         (subst (dot (subst (sh 4) f)
                   (dot triv (dot (var 1) (sh 4)))) p))
      (subst (under 0 (dot (var 1) (dot (var 0) (sh 2))))
         (subst (dot (subst (sh 4) f)
                   (dot triv (dot (var 1) (sh 4)))) p))
      (subst (dot (var 0) (sh 4)) b))
end.
2:{
  simpsub.
  reflexivity.
  }
apply (tr_exchange _ []).
cbn [substctx List.app].
simpsub.
cbn [Nat.add].
match goal with
| |- tr (?X :: _ :: ?Y) _ =>
   cut (tr ([X] ++ substh sh1 (hyp_tm a) :: Y)
          (deq
             (subst (under 1 (dot (var 1) (dot (var 0) (sh 2))))
                (subst (dot (subst (sh 4) f)
                          (dot triv (dot (var 2) (sh 4)))) p))
             (subst (under 1 (dot (var 1) (dot (var 0) (sh 2))))
                (subst (dot (subst (sh 4) f)
                          (dot triv (dot (var 2) (sh 4)))) p))
             (subst (dot (var 1) (sh 4)) b)))
end.
  {
  simpsub.
  auto.
  }
apply tr_exchange.
cbn [length substctx List.app].
simpsub.
cbn [Nat.add].
match goal with
| |- tr ?X _ => set (G' := X)
end.
assert (equiv
          (subst (dot (subst (sh 4) f) (dot triv (dot (var 2) (sh 4)))) p)
          (app 
             (app
                (lam (lam (subst (dot (var 0) (dot (var 1) (dot (var 4) (sh 6)))) p)))
                triv)
             (subst (sh 4) f))) as Hequiv.
  {
  apply equiv_symm.
  eapply equiv_trans.
    {
    apply equiv_app; [| apply equiv_refl].
    apply steps_equiv.
    apply star_one.
    apply step_app2.
    }
  simpsub.
  cbn [Nat.add].
  eapply equiv_trans.
    {
    apply steps_equiv.
    apply star_one.
    apply step_app2.
    }
  simpsub.
  apply equiv_refl.
  }
replace (subst (dot (var 2) (sh 4)) b) with (subst1 (subst (sh 4) f) (subst (dot (var 3) (sh 5)) b)).
2:{
  simpsub; reflexivity.
  }
refine (tr_compute _#7 (equiv_refl _ _) Hequiv Hequiv _).
clear Hequiv.
apply (tr_pi_elim _ (pi (var 3) (subst (dot (var 0) (sh 5)) b))).
2:{
  eapply tr_pi_of_ext.
  3:{
    simpsub.
    so (equiv_subst _ (sh 4) _ _ Hequivf) as H.
    simpsubin H.
    exact H.
    }

    {
    subst G'.
    apply tr_hyp_tp.
    repeat (apply index_S).
    apply index_0.
    }
  simpsub.
  cbn [Nat.add].
  apply tr_equal_elim.
  apply (tr_equal_eta2 _#4 (app (var 1) (var 0)) (app (var 1) (var 0))).
  cut (tr (hyp_tm (var 3) :: G')
         (deq (app (var 1) (var 0)) (app (var 1) (var 0))
            (subst1 (var 0)
               (equal
                  (subst (dot (var 0) (sh 6)) b)
                  (app (subst (sh 6) f) (var 0))
                  (app (subst (sh 6) f) (var 0)))))).
    {
    simpsub; auto.
    }
  apply (tr_pi_elim _ (var 4)).
  2:{
    eapply hypothesis.
      {
      apply index_0.
      }
    simpsub; auto.
    }
  subst G'.
  eapply hypothesis.
    {
    apply index_S.
    apply index_0.
    }
  
    {
    simpsub; auto.
    }
  }
replace (pi (pi (var 3) (subst (dot (var 0) (sh 5)) b)) (subst (dot (var 3) (sh 5)) b)) with
  (subst1 triv (pi (pi (var 4) (subst (dot (var 0) (sh 6)) b)) (subst (dot (var 4) (sh 6)) b))).
2:{
  simpsub; reflexivity.
  }
apply (tr_pi_elim _ (subtype (var 3) (subst (sh 4) (mu a)))).
2:{
  apply (tr_subtype_eta2 _#3 (var 1) (var 1)).
  subst G'.
  eapply hypothesis.
    {
    apply index_S.
    apply index_0.
    }
  simpsub; auto.
  }
apply tr_pi_intro.
  {
  apply tr_subtype_formation.
    {
    apply tr_hyp_tp.
    repeat (apply index_S).
    apply index_0.
    }

    {
    apply (weakening _ [_; _; _; _] []); auto.
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift List.app substctx].
    simpsub.
    cbn [Nat.add].
    simpsub.
    rewrite -> subst_var0_sh1.
    apply (tr_inhabitation_formation _ m m).
    auto.
    }
  }
apply tr_pi_intro.
  {
  apply tr_pi_formation.
    {
    subst G'.
    apply tr_hyp_tp.
    repeat (apply index_S).
    apply index_0.
    }

    {
    subst G'.
    apply (tr_inhabitation_formation _ (app (subst (sh 6) f) (var 0)) (app (subst (sh 6) f) (var 0))).
    apply tr_equal_elim.
    apply (tr_equal_eta2 _#4 (app (var 2) (var 0)) (app (var 2) (var 0))).
    match goal with
    | |- tr _ (deq _ _ ?X) =>
       replace X with (subst1 (var 0) (equal
                                         (subst (dot (var 0) (sh 7)) b)
                                         (app (subst (sh 7) f) (var 0))
                                         (app (subst (sh 7) f) (var 0))))
    end.
    2:{
      simpsub; reflexivity.
      }
    apply (tr_pi_elim _ (var 5)).
    2:{
      eapply hypothesis.
        {
        apply index_0.
        }

        {
        simpsub; reflexivity.
        }
      }
    eapply hypothesis.
      {
      repeat (apply index_S).
      apply index_0.
      }
    simpsub; reflexivity.
    }
  }
subst G'.
apply (weakening _ [_; _] [_; _]).
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
cbn [List.app length Nat.add].
simpsub.
cbn [Nat.add].
simpsubin Hn.
exact Hn.
Qed.


(* This is tedious. *)
Lemma tr_mu_ind_univ_extract :
  forall G lv a b m n,
    tr G (deq lv lv pagetp)
    -> tr (hyp_tm (univ lv) :: G) (deq a a (univ (subst sh1 lv)))
    -> tr G (deq triv triv (ispositive a))
    -> tr
         (hyp_tm (pi (var 2) (subst (under 1 (sh 3)) b)) ::
          hyp_tm (subtype (var 1) (mu (subst (under 1 (sh 2)) a))) ::
          hyp_tm a ::
          hyp_tm (univ lv) ::
          G)
         (deq 
            (subst (dot (var 2) (sh 4)) b)
            (subst (dot (var 2) (sh 4)) b)
            (univ (subst (sh 4) lv)))
    -> tr
         (hyp_tm (pi (var 2) (subst (under 1 (sh 3)) b)) ::
          hyp_tm (subtype (var 1) (mu (subst (under 1 (sh 2)) a))) ::
          hyp_tm a ::
          hyp_tm (univ lv) :: 
          G)
         (deq (subst (under 3 sh1) n) (subst (under 3 sh1) n) (subst (dot (var 2) (sh 4)) b))
    -> tr G (deq m m (mu a))
    -> tr G (deq 
                 (app
                    (app theta
                       (lam (lam
                               (subst (dot (var 1) (dot triv (dot (var 0) (sh 2)))) n))))
                    m)
                 (app
                    (app theta
                       (lam (lam
                               (subst (dot (var 1) (dot triv (dot (var 0) (sh 2)))) n))))
                    m)
                 (subst1 m b)).
Proof.
unfold termx.
intros G lv a b m p Hlv Ha Hmono Hb Hn Hm.
set (f := (app theta
             (lam (lam
                     (subst (dot (var 1) (dot triv (dot (var 0) (sh 2)))) p))))).
set (c := equal b (app (subst sh1 f) (var 0)) (app (subst sh1 f) (var 0))).
cut (tr G (deq triv triv (subst1 m c))).
  {
  intro Hseq.
  unfold c in Hseq.
  simpsubin Hseq.
  so (tr_equal_elim _#4 Hseq) as H.
  exact H.
  }
assert (tr
          (hyp_tm (pi (var 2) 
                     (equal
                        (subst (under 1 (sh 3)) b)
                        (app (subst (sh 4) f) (var 0))
                        (app (subst (sh 4) f) (var 0))))
           :: hyp_tm (subtype (var 1) (mu (subst (under 1 (sh 2)) a)))
           :: hyp_tm a
           :: hyp_tm (univ lv)
           :: G)
           (deq
              (app (subst (sh 4) f) (var 2))
              (app (subst (sh 4) f) (var 2))
              (subst (dot (var 2) (sh 4)) b))) as Hof.
  {
  replace (subst (dot (var 2) (sh 4)) b) with (subst1 (var 2) (subst (under 1 (sh 4)) b)).
  2:{
    simpsub.
    cbn.
    reflexivity.
    }
  apply (tr_pi_elim _ (subst (sh 3) a)).
  2:{
    simpsub.
    apply tr_hyp_tm.
    apply index_S.
    apply index_S.
    apply index_0.
    }
  cbn [Nat.add].
  apply (weakening _ [_] [_; _]).
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
  cbn [List.app length unlift].
  simpsub.
  cbn [List.app length Nat.add].
  simpsub.
  cbn [Nat.add].
  assert (equiv f
            (lam (subst (dot (subst sh1 f) (dot triv (dot (var 0) sh1))) p))) as Hequivf.
    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply theta_fix.
      }
    fold f.
    eapply star_step.
      {
      apply step_app2.
      }
    simpsub.
    apply star_refl.
    }
  refine (tr_compute _#7 (equiv_refl _ _) (equiv_subst _ (sh 3) _ _ Hequivf) (equiv_subst _ (sh 3) _ _ Hequivf) _).
  simpsub.
  cbn [Nat.add].
  apply tr_pi_intro.
    {
    apply (weakening _ [_; _] []); auto.
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    eapply tr_formation_weaken; eauto.
    }
  replace (hyp_tm (subst (sh 2) a)) with (substh sh1 (hyp_tm (subst sh1 a))) by (simpsub; auto).
  match goal with
  | |- tr _ ?X =>
     replace X with
     (deq 
        (subst (under 0 (dot (var 1) (dot (var 0) (sh 2))))
           (subst (dot (subst (sh 4) f)
                     (dot triv (dot (var 1) (sh 4)))) p))
        (subst (under 0 (dot (var 1) (dot (var 0) (sh 2))))
           (subst (dot (subst (sh 4) f)
                     (dot triv (dot (var 1) (sh 4)))) p))
        (subst (dot (var 0) (sh 4)) b))
  end.
  2:{
    simpsub.
    reflexivity.
    }
  apply (tr_exchange _ []).
  cbn [substctx List.app].
  simpsub.
  cbn [Nat.add].
  match goal with
  | |- tr (?X :: _ :: ?Y) _ =>
     cut (tr ([X] ++ substh sh1 (hyp_tm a) :: Y)
            (deq
               (subst (under 1 (dot (var 1) (dot (var 0) (sh 2))))
                  (subst (dot (subst (sh 4) f)
                            (dot triv (dot (var 2) (sh 4)))) p))
               (subst (under 1 (dot (var 1) (dot (var 0) (sh 2))))
                  (subst (dot (subst (sh 4) f)
                            (dot triv (dot (var 2) (sh 4)))) p))
               (subst (dot (var 1) (sh 4)) b)))
  end.
    {
    simpsub.
    auto.
    }
  apply tr_exchange.
  cbn [length substctx List.app].
  simpsub.
  cbn [Nat.add].
  match goal with
  | |- tr ?X _ => set (G' := X)
  end.
  assert (equiv
            (subst (dot (subst (sh 4) f) (dot triv (dot (var 2) (sh 4)))) p)
            (app 
               (app
                  (lam (lam (subst (dot (var 0) (dot (var 1) (dot (var 4) (sh 6)))) p)))
                  triv)
               (subst (sh 4) f))) as Hequiv.
    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_app; [| apply equiv_refl].
      apply steps_equiv.
      apply star_one.
      apply step_app2.
      }
    simpsub.
    cbn [Nat.add].
    eapply equiv_trans.
      {
      apply steps_equiv.
      apply star_one.
      apply step_app2.
      }
    simpsub.
    apply equiv_refl.
    }
  replace (subst (dot (var 2) (sh 4)) b) with (subst1 (subst (sh 4) f) (subst (dot (var 3) (sh 5)) b)).
  2:{
    simpsub; reflexivity.
    }
  refine (tr_compute _#7 (equiv_refl _ _) Hequiv Hequiv _).
  clear Hequiv.
  apply (tr_pi_elim _ (pi (var 3) (subst (dot (var 0) (sh 5)) b))).
  2:{
    eapply tr_pi_of_ext.
    3:{
      simpsub.
      so (equiv_subst _ (sh 4) _ _ Hequivf) as H.
      simpsubin H.
      exact H.
      }
  
      {
      subst G'.
      eapply tr_formation_weaken.
      eapply hypothesis.
        {
        repeat (apply index_S).
        apply index_0.
        }
      simpsub.
      reflexivity.
      }
    simpsub.
    cbn [Nat.add].
    apply tr_equal_elim.
    apply (tr_equal_eta2 _#4 (app (var 1) (var 0)) (app (var 1) (var 0))).
    cut (tr (hyp_tm (var 3) :: G')
           (deq (app (var 1) (var 0)) (app (var 1) (var 0))
              (subst1 (var 0)
                 (equal
                    (subst (dot (var 0) (sh 6)) b)
                    (app (subst (sh 6) f) (var 0))
                    (app (subst (sh 6) f) (var 0)))))).
      {
      simpsub; auto.
      }
    apply (tr_pi_elim _ (var 4)).
    2:{
      eapply hypothesis.
        {
        apply index_0.
        }
      simpsub; auto.
      }
    subst G'.
    eapply hypothesis.
      {
      apply index_S.
      apply index_0.
      }
    
      {
      simpsub; auto.
      }
    }
  replace (pi (pi (var 3) (subst (dot (var 0) (sh 5)) b)) (subst (dot (var 3) (sh 5)) b)) with
    (subst1 triv (pi (pi (var 4) (subst (dot (var 0) (sh 6)) b)) (subst (dot (var 4) (sh 6)) b))).
  2:{
    simpsub; reflexivity.
    }
  apply (tr_pi_elim _ (subtype (var 3) (subst (sh 4) (mu a)))).
  2:{
    apply (tr_subtype_eta2 _#3 (var 1) (var 1)).
    subst G'.
    eapply hypothesis.
      {
      apply index_S.
      apply index_0.
      }
    simpsub; auto.
    }
  apply tr_pi_intro.
    {
    apply tr_subtype_formation.
      {
      subst G'.
      eapply tr_formation_weaken.
      eapply hypothesis.
        {
        repeat (apply index_S).
        apply index_0.
        }
      simpsub; reflexivity.
      }
  
      {
      apply (weakening _ [_; _; _; _] []); auto.
        {
        cbn [length unlift].
        simpsub.
        reflexivity.
        }
      cbn [length unlift List.app substctx].
      simpsub.
      cbn [Nat.add].
      simpsub.
      rewrite -> subst_var0_sh1.
      apply (tr_inhabitation_formation _ m m).
      auto.
      }
    }
  apply tr_pi_intro.
    {
    apply tr_pi_formation.
      {
      subst G'.
      eapply tr_formation_weaken.
      eapply hypothesis.
        {
        repeat (apply index_S).
        apply index_0.
        }
      simpsub; reflexivity.
      }
  
      {
      subst G'.
      apply (tr_inhabitation_formation _ (app (subst (sh 6) f) (var 0)) (app (subst (sh 6) f) (var 0))).
      apply tr_equal_elim.
      apply (tr_equal_eta2 _#4 (app (var 2) (var 0)) (app (var 2) (var 0))).
      match goal with
      | |- tr _ (deq _ _ ?X) =>
         replace X with (subst1 (var 0) (equal
                                           (subst (dot (var 0) (sh 7)) b)
                                           (app (subst (sh 7) f) (var 0))
                                           (app (subst (sh 7) f) (var 0))))
      end.
      2:{
        simpsub; reflexivity.
        }
      apply (tr_pi_elim _ (var 5)).
      2:{
        eapply hypothesis.
          {
          apply index_0.
          }
  
          {
          simpsub; reflexivity.
          }
        }
      eapply hypothesis.
        {
        repeat (apply index_S).
        apply index_0.
        }
      simpsub; reflexivity.
      }
    }
  subst G'.
  apply (weakening _ [_; _] [_; _]).
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
  cbn [List.app length Nat.add].
  simpsub.
  cbn [Nat.add].
  simpsubin Hn.
  exact Hn.
  }
subst c.
apply (tr_mu_ind_univ _ lv a); auto.
2:{
  simpsub.
  apply tr_equal_intro.
  auto.
  }
simpsub.
cbn [Nat.add].
apply tr_equal_formation_univ; auto.
eapply (tr_assert _ (pi (var 3) (subst (under 1 (sh 4)) b)) (subst (sh 4) f)).
  {
  eapply tr_pi_of_ext; eauto.
  3:{
    unfold f.
    simpsub.
    eapply equiv_trans.
      {
      apply theta_equiv.
      }
    apply steps_equiv.
    eapply star_step.
      {
      apply step_app2.
      }
    simpsub.
    apply star_refl.
    }
    
    {
    eapply tr_formation_weaken.
    eapply hypothesis.
      {
      repeat (apply index_S).
      apply index_0.
      }
    simpsub.
    reflexivity.
    }
  simpsub.
  cbn [Nat.add].
  apply tr_equal_elim.
  apply (tr_equal_eta2 _#4 (app (var 1) (var 0)) (app (var 1) (var 0))).
  eapply tr_pi_elim'.
    {
    eapply hypothesis.
      {
      apply index_S; apply index_0.
      }
    simpsub.
    reflexivity.
    }

    {
    cbn [Nat.add].
    eapply hypothesis.
      {
      apply index_0.
      }
    simpsub.
    reflexivity.
    }
  simpsub.
  cbn [Nat.add].
  simpsub.
  reflexivity.
  }
eapply (weakening _ [_] [_]).
  {
  cbn [length unlift].
  simpsub.
  cbn.
  auto.
  }

  {
  cbn [length unlift].
  simpsub.
  auto.
  }
cbn [length unlift].
simpsub.
cbn [Nat.add List.app].
auto.
Qed.
