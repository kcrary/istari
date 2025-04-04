
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Tactics.
Require Import Sequence.
Require Import Relation.
Require Import Dynamic.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.
Require Import Promote.
Require Import Hygiene.
Require Import Rules.
Require Import Morphism.
Require Import Equivalence.
Require Import Equivalences.
Require Import Defined.
Require Import PageCode.
Require Import Dots.


(* equivalences *)

Lemma theta_equiv :
  forall object (f : @term object), equiv (app theta f) (app f (app theta f)).
Proof.
intros object f.
apply steps_equiv.
apply theta_fix.
Qed.


Lemma leqtp_nzero_equiv :
  forall object m, @equiv object (app (app leqtp nzero) m) unittp.
Proof.
intros object m.
unfold leqtp.
apply steps_equiv.
eapply star_trans.
  {
  apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
  eapply star_trans.
    {
    apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
    eapply star_trans.
      {
      apply PageCode.theta_fix.
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
unfold sumcase.
eapply star_step.
  {
  apply step_bite1.
  unfold nzero.
  unfold sumleft.
  apply step_ppi12.
  }
eapply star_step.
  {
  apply step_bite2.
  }
simpsub.
apply star_refl.
Qed.


Lemma leqpagetp_nzero_equiv :
  forall object m, @equiv object (leqpagetp nzero m) unittp.
Proof.
intros object m.
unfold leqpagetp.
apply leqtp_nzero_equiv.
Qed.


Lemma sumcase_left :
  forall m n p,
    @equiv obj (sumcase (sumleft m) n p) (subst1 m n).
Proof.
intros m n p.
unfold sumcase, sumleft.
eapply equiv_trans.
  {
  eapply equiv_bite; [| apply equiv_refl | apply equiv_refl].
  apply steps_equiv.
  apply star_one.
  apply step_ppi12.
  }
eapply equiv_trans.
  {
  apply steps_equiv.
  apply star_one.
  apply step_bite2.
  }
apply equiv_funct; auto using equiv_refl.
apply equivsub_dot; auto using equivsub_refl.
apply steps_equiv.
apply star_one.
apply step_ppi22.
Qed.



Lemma sumcase_right :
  forall m n p,
    @equiv obj (sumcase (sumright m) n p) (subst1 m p).
Proof.
intros m n p.
unfold sumcase, sumright.
eapply equiv_trans.
  {
  eapply equiv_bite; [| apply equiv_refl | apply equiv_refl].
  apply steps_equiv.
  apply star_one.
  apply step_ppi12.
  }
eapply equiv_trans.
  {
  apply steps_equiv.
  apply star_one.
  apply step_bite3.
  }
apply equiv_funct; auto using equiv_refl.
apply equivsub_dot; auto using equivsub_refl.
apply steps_equiv.
apply star_one.
apply step_ppi22.
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



(* tools *)

Lemma hypothesis :
  forall G i a a',
    index i G (hyp_tm a')
    -> a = subst (sh (S i)) a'
    -> tr G (deq (var i) (var i) a).
Proof.
intros G i a b Hindex ->.
apply tr_hyp_tm; auto.
Qed.


Lemma weakening :
  forall G1 G2 G3 J,
    G3 = substctx (compose (unlift (length G2)) (sh (length G2))) G3
    -> J = substj (under (length G3) (compose (unlift (length G2)) (sh (length G2)))) J
    -> tr (substctx (unlift (length G2)) G3 ++ G1) (substj (under (length G3) (unlift (length G2))) J)
    -> tr (G3 ++ G2 ++ G1) J.
Proof.
intros G1 G2 G3 J HeqG3 HeqJ Hseq.
rewrite -> HeqG3.
rewrite -> HeqJ.
rewrite -> substctx_compose.
set (G3' := substctx (unlift (length G2)) G3) in Hseq |- *.
rewrite -> compose_under.
rewrite -> substj_compose.
set (J' := substj (under (length G3) (unlift (length G2))) J) in Hseq |- *.
replace (length G3) with (length G3').
2:{
  subst G3'.
  apply length_substctx.
  }
clearbody G3' J'.
clear G3 J HeqG3 HeqJ.
revert G3' J' Hseq.
induct G2.

(* nil *)
{
intros G3 J Hseq.
cbn.
simpsub.
auto.
}

(* cons *)
{
intros h G2 IH G3 J Hseq.
cbn [length List.app].
replace (S (length G2)) with (length G2 + 1) by omega.
rewrite <- compose_sh_sh.
rewrite -> substctx_compose.
rewrite -> compose_under.
rewrite -> substj_compose.
replace (length G3) with (length (substctx (sh (length G2)) G3)).
2:{
  rewrite -> length_substctx.
  auto.
  }
apply tr_weakening.
rewrite -> length_substctx.
apply IH; auto.
}
Qed.


Lemma exchange_1_1 :
  forall G1 h1 h2 G2 J,
    h2 = substh (dot arb sh1) h2
    -> tr 
         (substctx (dot (var 1) (dot (var 0) (sh 2))) G2 ++ substh sh1 h1 :: substh (dot arb id) h2 :: G1)
         (substj (under (length G2) (dot (var 1) (dot (var 0) (sh 2)))) J)
    -> tr (G2 ++ h2 :: h1 :: G1) J.
Proof.
intros G1 h1 h2 G2 J Heq Htr.
replace h2 with (substh sh1 (substh (dot arb id) h2)).
2:{
  rewrite -> Heq at 2.
  simpsub.
  reflexivity.
  }
destruct J as [m n a].
assert (forall (x : @term obj), subst (under (length G2) (dot (var 1) (dot (var 0) (sh 2)))) (subst (under (length G2) (dot (var 1) (dot (var 0) (sh 2)))) x) = x) as Heqsub.
  {
  intro x.
  rewrite <- subst_compose.
  rewrite <- compose_under.
  simpsub.
  setoid_rewrite <- (subst_id _ x) at 2.
  apply subst_eqsub.
  eapply eqsub_trans.
  2:{
    apply (eqsub_under_id _ (length G2)).
    }
  apply eqsub_under.
  eapply eqsub_trans.
  2:{
    apply (eqsub_under_id _ 2).
    }
  simpsub.
  apply eqsub_refl.
  }
rewrite <- (Heqsub m).
rewrite <- (Heqsub n).
clear Heqsub.
apply tr_exchange.
simpsubin Htr.
exact Htr.
Qed.


Lemma exchange_1_n :
  forall G1 G2 h G3 J,
    h = substh (compose (unlift (length G2)) (sh (length G2))) h
    -> tr 
         (substctx (dot (var (length G2)) (dots 0 (length G2) (sh (S (length G2))))) G3
            ++ substctx sh1 G2
            ++ substh (unlift (length G2)) h
            :: G1)
         (substj
            (under (length G3) (dot (var (length G2)) (dots 0 (length G2) (sh (S (length G2))))))
            J)
    -> tr (G3 ++ h :: G2 ++ G1) J.
Proof.
intros G1 G2 h G3 J Heq Htr.
revert G3 h J Heq Htr.
induct G2.

(* nil *)
{
intros G3 h J Heq Htr.
cbn [List.app].
cbn [length dots unlift] in Htr.
rewrite -> substctx_nil in Htr.
cbn [List.app] in Htr.
rewrite -> substh_id in Htr.
force_exact Htr.
f_equal.
  {
  f_equal.
  setoid_rewrite <- substctx_id at 3.
  apply substctx_eqsub.
  apply eqsub_symm.
  apply eqsub_expand_id.
  }

  {
  setoid_rewrite <- substj_id at 3.
  apply substj_eqsub.
  rewrite <- (eqsub_under_id _ (length G3)).
  apply eqsub_under.
  apply eqsub_symm.
  apply eqsub_expand_id.
  }
}

(* cons *)
{
intros h2 G2 IH G3 h J Heq Htr.
cbn [length unlift dots Nat.add] in Htr.
simpsubin Htr.
rewrite <- app_comm_cons.
apply exchange_1_1.
  {
  rewrite -> Heq.
  cbn [length unlift].
  simpsub.
  rewrite -> Nat.add_comm.
  reflexivity.
  }
cut (tr ((substctx (dot (var 1) (dot (var 0) (sh 2))) G3 ++ substh sh1 h2 :: nil) ++ substh (dot arb id) h :: G2 ++ G1) (substj (under (length G3) (dot (var 1) (dot (var 0) (sh 2)))) J)).
  {
  intro H.
  autorewrite with canonlist in H.
  exact H.
  }
cbn [length unlift] in Heq.
apply IH.
  {
  rewrite -> Heq.
  simpsub.
  setoid_rewrite <- compose_assoc at 2.
  rewrite -> compose_sh_unlift.
  simpsub.
  reflexivity.
  }
rewrite -> substctx_append.
cbn [length].
simpsub.
autorewrite with canonlist in Htr |- *.
rewrite -> app_length.
rewrite -> length_substctx.
cbn [length Nat.add].
rewrite <- under_sum.
rewrite <- compose_under.
simpsub.
unfold sh1.
rewrite -> compose_dots_sh_sh.
cbn [Nat.add].
rewrite <- dots_succ.
cbn [dots].
rewrite -> under_dots in Htr.
simpsubin Htr.
exact Htr.
}
Qed.


Lemma exchange :
  forall G1 G2 G3 G4 J,
    G3 = substctx (compose (unlift (length G2)) (sh (length G2))) G3
    -> tr
         (substctx (dots (length G2) (length G3) (dots 0 (length G2) (sh (length G2 + length G3)))) G4
            ++ substctx (sh (length G3)) G2
            ++ substctx (unlift (length G2)) G3
            ++ G1)
         (substj
            (under (length G4) (dots (length G2) (length G3) (dots 0 (length G2) (sh (length G2 + length G3)))))
            J)
    -> tr (G4 ++ G3 ++ G2 ++ G1) J.
Proof.
intros G1 G2 G3 G4 J HeqG3 Htr.
revert G2 G4 J HeqG3 Htr.
induct G3.

(* nil *)
{
intros G2 G4 J _ Htr.
rewrite -> substctx_nil in Htr.
autorewrite with canonlist in Htr |- *.
rewrite -> Nat.add_comm in Htr.
cbn [Nat.add dots length] in Htr.
simpsubin Htr.
rewrite -> (substctx_eqsub _#4 (eqsub_dots_id _ (length G2))) in Htr.
rewrite -> (substj_eqsub _#4 (eqsub_under _ (length G4) _ _ (eqsub_dots_id _ (length G2)))) in Htr.
simpsubin Htr.
exact Htr.
}

(* cons *)
{
intros h G3 IH G2 G4 J Heq Htr.
simpsubin Heq.
injectionc Heq.
intros Heq Heqh.
rewrite <- compose_under in Heqh.
replace (G4 ++ (h :: G3) ++ G2 ++ G1) with ((G4 ++ h :: nil) ++ G3 ++ G2 ++ G1).
2:{
  autorewrite with canonlist.
  reflexivity.
  }
apply IH; auto.
rewrite -> app_length.
cbn [length].
replace (length G4 + 1) with (S (length G4)).
2:{
  rewrite -> Nat.add_comm.
  reflexivity.
  }
simpsub.
rewrite -> substctx_append.
cbn [length].
simpsub.
autorewrite with canonlist.
apply exchange_1_n.
  {
  rewrite -> length_substctx.
  rewrite -> Heqh at 1.
  rewrite <- !substh_compose.
  f_equal.
  rewrite -> under_dots.
  rewrite -> compose_dots_0_eq.
  rewrite -> compose_assoc.
  rewrite -> compose_sh_dots_eq.
  rewrite -> compose_assoc.
  rewrite -> compose_sh_dots_eq.
  rewrite -> compose_dots_stable.
  2:{
    intros i Hi.
    simpsub.
    rewrite -> project_unlift_ge; [| omega].
    simpsub.
    f_equal.
    omega.
    }
  f_equal.
  set (j := length G2).
  set (k := length G3).
  clearbody j k.
  clear G1 h G3 IH G2 G4 J Htr Heq Heqh.
  induct j.
    {
    cbn [unlift Nat.add dots].
    simpsub.
    f_equal.
    omega.
    }
    
    {
    intros j IH.
    cbn [unlift Nat.add].
    rewrite -> dots_succ.
    simpsub.
    f_equal.
    replace (S (j + k)) with ((j + k) + 1) by omega.
    rewrite <- compose_sh_sh.
    rewrite <- compose_assoc.
    rewrite -> IH.
    rewrite <- (compose_dots_sh _ 0 j _ 1).
    simpsub.
    do 3 f_equal.
    omega.
    }
  }
rewrite -> !length_substctx.
cbn [length] in Htr.
cbn [substctx] in Htr.
set (n2 := length G2) in Htr |- *.
set (n3 := length G3) in Htr |- *.
set (n4 := length G4) in Htr |- *.
rewrite <- under_succ.
replace (S n4) with (n4 + 1) by omega.
rewrite <- under_sum.
simpsub.
rewrite <- compose_under.
simpsub.
simpsubin Htr.
replace (n3 + 1) with (S n3) by omega.
autorewrite with canonlist in Htr.
force_exact Htr.
assert (@dots obj (S n2) n3 (dots 0 n2 (sh (n2 + S n3)))
        = compose (dots n2 n3 (dots 0 n2 (sh (n2 + n3)))) (dots 0 n2 (sh (S n2)))) as Heqsub.
  {
  rewrite -> compose_dots_ge; [| auto].
  replace (n2 - n2 + S n2) with (S n2) by omega.
  f_equal.
  rewrite -> compose_dots_le; [| auto].
  cbn [Nat.add].
  f_equal.
  rewrite -> compose_sh_dots_ge; [| omega].
  rewrite -> compose_sh_sh.
  f_equal.
  omega.
  }
f_equal.
  {
  f_equal.
    {
    rewrite -> dots_succ.
    f_equal.
    f_equal.
    auto.
    }

    {
    f_equal.
    f_equal.
    f_equal.
    rewrite -> compose_dots_unlift_ge; [| auto].
    replace (n2 - n2) with 0 by omega.
    rewrite -> compose_dots_unlift_exact; [| omega].
    replace (n2 + n3 - n2) with n3 by omega.
    rewrite -> under_dots.
    reflexivity.
    }
  }

  {
  rewrite -> dots_succ.
  f_equal.
  f_equal.
  f_equal.
  auto.
  }
}
Qed.


Lemma exchange_n_1 :
  forall G1 G2 h G3 J,
    G2 = substctx (dot arb sh1) G2
    -> tr 
         (substctx (dots 1 (length G2) (dot (var 0) (sh (S (length G2))))) G3
            ++ substh (sh (length G2)) h
            :: substctx (dot arb id) G2
            ++ G1)
         (substj
            (under (length G3) (dots 1 (length G2) (dot (var 0) (sh (S (length G2))))))
            J)
    -> tr (G3 ++ G2 ++ h :: G1) J.
Proof.
intros G1 G2 h G3 J Heq Htr.
change (h :: G1) with ((h :: nil) ++ G1).
apply exchange.
  {
  cbn [length unlift].
  simpsub.
  exact Heq.
  }
cbn [length substctx List.app].
exact Htr.
Qed.


Lemma revert :
  forall G a b m n,
    tr G (deq (lam m) (lam n) (pi a b))
    -> tr (hyp_tm a :: G) (deq m n b).
Proof.
intros G a b m n Htr.
apply (tr_compute _ _ (subst1 (var 0) (subst (under 1 sh1) b)) _ (app (lam (subst (under 1 sh1) m)) (var 0)) _ (app (lam (subst (under 1 sh1) n)) (var 0))).
  {
  simpsub.
  rewrite -> subst_var0_sh1.
  apply equiv_refl.
  }

  {
  apply equiv_symm.
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  rewrite -> subst_var0_sh1.
  apply star_refl.
  }

  {
  apply equiv_symm.
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  rewrite -> subst_var0_sh1.
  apply star_refl.
  }
apply (tr_pi_elim _ (subst sh1 a)).
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
    cbn [Nat.add].
    reflexivity.
    }
  cbn [length unlift List.app substctx].
  simpsub.
  rewrite -> !subst_var0_sh1.
  auto.
  }

  {
  eapply hypothesis; eauto using index_0.
  }
Qed.    


Lemma tr_generalize :
  forall G a m J,
    tr G (deq m m a)
    -> tr (cons (hyp_tm a) G) J
    -> tr G (substj (dot m id) J).
Proof.
intros G a m J Hm HJ.
destruct J as [p q b].
simpsub.
eapply tr_functionality_term_term; eauto.
Qed.


Lemma tr_generalize_tp :
  forall G a J,
    tr G (deqtype a a)
    -> tr (cons hyp_tp G) J
    -> tr G (substj (dot a id) J).
Proof.
intros G a J Ha HJ.
destruct J as [p q b].
simpsub.
apply tr_functionality_term_type; auto.
Qed.


Lemma tr_generalize_eq :
  forall G a b m n p q,
    tr G (deq m n a)
    -> tr (cons (hyp_tm a) G) (deq p q b)
    -> tr G (deq (subst1 m p) (subst1 n q) (subst1 m b)).
Proof.
intros G a b m n p q Hmn Hpq.
eapply tr_functionality_term_term; eauto.
Qed.


Lemma tr_generalize_eq_type :
  forall G a b m n p q,
    tr G (deq m n a)
    -> tr (cons (hyp_tm a) G) (deq p q b)
    -> tr G (deqtype (subst1 m b) (subst1 n b)).
Proof.
intros G a b m n p q Hmn Hpq.
eapply tr_functionality_type_term; eauto.
eapply tr_inhabitation_formation; eauto.
Qed.


Lemma tr_subtype_convert_hyp_last :
  forall G a b J,
    tr G (dsubtype a b)
    -> tr (hyp_tm b :: G) J
    -> tr (hyp_tm a :: G) J.
Proof.
intros G a b J Hsub HJ.
replace J with (substj (dot (var 0) id) (substj (dot (var 0) (sh 2)) J)).
2:{
  destruct J as [m n c].
  simpsub.
  rewrite -> !subst_var0_sh1.
  reflexivity.
  }
apply (tr_generalize _ (subst sh1 b) (var 0)).
  {
  apply (tr_subtype_elim _ (subst sh1 a)).
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
    exact Hsub.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }

  {
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
  destruct J as [m n c].
  simpsub.
  rewrite -> !subst_var0_sh1.
  exact HJ.
  }
Qed.


Lemma tr_pi_elim' :
  forall G a b c m n p q,
    tr G (deq m n (pi a b))
    -> tr G (deq p q a)
    -> c = subst1 p b
    -> tr G (deq (app m p) (app n q) c).
Proof.
intros G a b c m n p q H1 H2 ->.
eapply tr_pi_elim; eauto.
Qed.


Lemma tr_pi_elim2' :
  forall G a1 a2 b c m n p1 q1 p2 q2,
    tr G (deq m n (pi a1 (pi a2 b)))
    -> tr G (deq p1 q1 a1)
    -> tr G (deq p2 q2 (subst1 p1 a2))
    -> c = subst (dot p2 (dot p1 id)) b
    -> tr G (deq (app (app m p1) p2) (app (app n q1) q2) c).
Proof.
intros G a1 a2 b c m n p1 q1 p2 q2 H1 H2 H3 ->.
replace (subst (dot p2 (dot p1 id)) b) with (subst (dot p2 id) (subst (under 1 (dot p1 id)) b)).
2:{
  simpsub.
  auto.
  }
eapply (tr_pi_elim _ (subst1 p1 a2)).
  {
  eapply tr_pi_elim'.
    {
    eauto.
    }

    {
    auto.
    }

    {
    simpsub.
    auto.
    }
  }

  {
  auto.
  }
Qed.



Lemma tr_pi_elim3' :
  forall G a1 a2 a3 b c m n p1 q1 p2 q2 p3 q3,
    tr G (deq m n (pi a1 (pi a2 (pi a3 b))))
    -> tr G (deq p1 q1 a1)
    -> tr G (deq p2 q2 (subst1 p1 a2))
    -> tr G (deq p3 q3 (subst (dot p2 (dot p1 id)) a3))
    -> c = subst (dot p3 (dot p2 (dot p1 id))) b
    -> tr G (deq (app (app (app m p1) p2) p3) (app (app (app n q1) q2) q3) c).
Proof.
intros G a1 a2 a3 b c m n p1 q1 p2 q2 p3 q3 H1 H2 H3 H4 ->.
replace (subst (dot p3 (dot p2 (dot p1 id))) b) with (subst (dot p3 id) (subst (under 1 (dot p2 (dot p1 id))) b)).
2:{
  simpsub.
  auto.
  }
eapply (tr_pi_elim _ (subst (dot p2 (dot p1 id)) a3)).
  {
  eapply tr_pi_elim2'.
    {
    eauto.
    }

    {
    auto.
    }

    {
    auto.
    }

    {
    simpsub.
    auto.
    }
  }

  {
  auto.
  }
Qed.


Lemma tr_pi_elim4' :
  forall G a1 a2 a3 a4 b c m n p1 q1 p2 q2 p3 q3 p4 q4,
    tr G (deq m n (pi a1 (pi a2 (pi a3 (pi a4 b)))))
    -> tr G (deq p1 q1 a1)
    -> tr G (deq p2 q2 (subst1 p1 a2))
    -> tr G (deq p3 q3 (subst (dot p2 (dot p1 id)) a3))
    -> tr G (deq p4 q4 (subst (dot p3 (dot p2 (dot p1 id))) a4))
    -> c = subst (dot p4 (dot p3 (dot p2 (dot p1 id)))) b
    -> tr G (deq (app (app (app (app m p1) p2) p3) p4) (app (app (app (app n q1) q2) q3) q4) c).
Proof.
intros G a1 a2 a3 a4 b c m n p1 q1 p2 q2 p3 q3 p4 q4 H1 H2 H3 H4 H5 ->.
replace (subst (dot p4 (dot p3 (dot p2 (dot p1 id)))) b) with (subst (dot p4 id) (subst (under 1 (dot p3 (dot p2 (dot p1 id)))) b)).
2:{
  simpsub.
  auto.
  }
eapply (tr_pi_elim _ (subst (dot p3 (dot p2 (dot p1 id))) a4)).
  {
  eapply tr_pi_elim3'; eauto.
  simpsub.
  auto.
  }

  {
  auto.
  }
Qed.


Lemma tr_pi_elim5' :
  forall G a1 a2 a3 a4 a5 b c m n p1 q1 p2 q2 p3 q3 p4 q4 p5 q5,
    tr G (deq m n (pi a1 (pi a2 (pi a3 (pi a4 (pi a5 b))))))
    -> tr G (deq p1 q1 a1)
    -> tr G (deq p2 q2 (subst1 p1 a2))
    -> tr G (deq p3 q3 (subst (dot p2 (dot p1 id)) a3))
    -> tr G (deq p4 q4 (subst (dot p3 (dot p2 (dot p1 id))) a4))
    -> tr G (deq p5 q5 (subst (dot p4 (dot p3 (dot p2 (dot p1 id)))) a5))
    -> c = subst (dot p5 (dot p4 (dot p3 (dot p2 (dot p1 id))))) b
    -> tr G (deq (app (app (app (app (app m p1) p2) p3) p4) p5) (app (app (app (app (app n q1) q2) q3) q4) q5) c).
Proof.
intros G a1 a2 a3 a4 a5 b c m n p1 q1 p2 q2 p3 q3 p4 q4 p5 q5 H1 H2 H3 H4 H5 H6 ->.
replace (subst (dot p5 (dot p4 (dot p3 (dot p2 (dot p1 id))))) b) with (subst (dot p5 id) (subst (under 1 (dot p4 (dot p3 (dot p2 (dot p1 id))))) b)).
2:{
  simpsub.
  auto.
  }
eapply (tr_pi_elim _ (subst (dot p4 (dot p3 (dot p2 (dot p1 id)))) a5)).
  {
  eapply tr_pi_elim4'; eauto.
  simpsub.
  auto.
  }

  {
  auto.
  }
Qed.


Lemma tr_sigma_elim2' :
  forall G a b c m n,
    tr G (deq m n (sigma a b))
    -> c = subst1 (ppi1 m) b
    -> tr G (deq (ppi2 m) (ppi2 n) c).
Proof.
intros G a b c m n H ->.
eapply tr_sigma_elim2; eauto.
Qed.


Lemma tr_assert :
  forall G a m J,
    tr G (deq m m a)
    -> tr (hyp_tm a :: G) (substj sh1 J)
    -> tr G J.
Proof.
intros G a m J Ha HJ.
replace J with (substj (dot m id) (substj sh1 J)).
2:{
  simpsub.
  reflexivity.
  }
apply (tr_generalize G a m (substj sh1 J)); auto.
Qed.



(* eta2 *)

Lemma tr_equal_eta2 :
  forall G a m n p q,
    tr G (deq p q (equal a m n))
    -> tr G (deq triv triv (equal a m n)).
Proof.
intros G a m n p q Htr.
assert (tr G (deq p triv (equal a m n))) as Htr'.
  {
  apply tr_equal_eta.
  apply (tr_transitivity _ _ q); auto.
  apply tr_symmetry; auto.
  }
apply (tr_transitivity _ _ p); auto.
apply tr_symmetry; auto.
Qed.


Lemma tr_eqtype_eta2 :
  forall G a b p q,
    tr G (deq p q (eqtype a b))
    -> tr G (deq triv triv (eqtype a b)).
Proof.
intros G a b p q Htr.
assert (tr G (deq p triv (eqtype a b))) as Htr'.
  {
  apply tr_eqtype_eta.
  apply (tr_transitivity _ _ q); auto.
  apply tr_symmetry; auto.
  }
apply (tr_transitivity _ _ p); auto.
apply tr_symmetry; auto.
Qed.


Lemma tr_subtype_eta2 :
  forall G a b p q,
    tr G (deq p q (subtype a b))
    -> tr G (deq triv triv (subtype a b)).
Proof.
intros G a b p q Htr.
assert (tr G (deq p triv (subtype a b))) as Htr'.
  {
  apply tr_subtype_eta.
  apply (tr_transitivity _ _ q); auto.
  apply tr_symmetry; auto.
  }
apply (tr_transitivity _ _ p); auto.
apply tr_symmetry; auto.
Qed.


Lemma tr_positive_eta2 :
  forall G a p q,
    tr G (deq p q (ispositive a))
    -> tr G (deq triv triv (ispositive a)).
Proof.
intros G a p q Htr.
assert (tr G (deq p triv (ispositive a))) as Htr'.
  {
  apply tr_positive_eta.
  apply (tr_transitivity _ _ q); auto.
  apply tr_symmetry; auto.
  }
apply (tr_transitivity _ _ p); auto.
apply tr_symmetry; auto.
Qed.


Lemma tr_negative_eta2 :
  forall G a p q,
    tr G (deq p q (isnegative a))
    -> tr G (deq triv triv (isnegative a)).
Proof.
intros G a p q Htr.
assert (tr G (deq p triv (isnegative a))) as Htr'.
  {
  apply tr_negative_eta.
  apply (tr_transitivity _ _ q); auto.
  apply tr_symmetry; auto.
  }
apply (tr_transitivity _ _ p); auto.
apply tr_symmetry; auto.
Qed.


Lemma tr_sequal_eta2 :
  forall G p q m n,
    tr G (deq p q (sequal m n))
    -> tr G (deq triv triv (sequal m n)).
Proof.
intros G p q m n Htr.
assert (tr G (deq p triv (sequal m n))) as Htr'.
  {
  apply tr_sequal_eta.
  apply (tr_transitivity _ _ q); auto.
  apply tr_symmetry; auto.
  }
apply (tr_transitivity _ _ p); auto.
apply tr_symmetry; auto.
Qed.


(* base types *)

Lemma tr_voidtp_istype :
  forall G,
    tr G (deqtype voidtp voidtp).
Proof.
intros G.
apply (tr_formation_weaken _ nzero).
apply tr_voidtp_formation_univ.
Qed.


Lemma tr_unittp_istype :
  forall G,
    tr G (deqtype unittp unittp).
Proof.
intros G.
apply (tr_formation_weaken _ nzero).
apply tr_unittp_formation_univ.
Qed.


Lemma tr_booltp_istype :
  forall G,
    tr G (deqtype booltp booltp).
Proof.
intros G.
apply (tr_formation_weaken _ nzero).
apply tr_booltp_formation_univ.
Qed.


Lemma tr_unittp_eta_hyp_triv :
  forall G1 G2 b,
    tr (substctx (dot triv id) G2 ++ G1) (deq triv triv (subst (under (length G2) (dot triv id)) b))
    -> tr (G2 ++ hyp_tm unittp :: G1) (deq triv triv b).
Proof.
intros G1 G2 b H.
replace triv with (@subst obj (under (length G2) sh1) triv) by (simpsub; auto).
apply tr_unittp_eta_hyp.
auto.
Qed.


Lemma tr_booltp_eta_hyp_triv :
  forall G1 G2 a,
    tr (substctx (dot btrue id) G2 ++ G1) (deq triv triv (subst (under (length G2) (dot btrue id)) a))
    -> tr (substctx (dot bfalse id) G2 ++ G1) (deq triv triv (subst (under (length G2) (dot bfalse id)) a))
    -> tr (G2 ++ cons (hyp_tm booltp) G1) (deq triv triv a).
Proof.
intros G1 G2 a Hl Hr.
apply tr_equal_elim.
set (m := @bite obj (var (length G2)) (subst (under (length G2) sh1) triv) (subst (under (length G2) sh1) triv)).
apply (tr_equal_eta2 _#4 m m).
apply tr_booltp_eta_hyp.
  {
  simpsub.
  apply tr_equal_intro.
  exact Hl.
  }

  {
  simpsub.
  apply tr_equal_intro.
  exact Hr.
  }
Qed.


Lemma tr_voidtp_formation_univ_gen :
  forall G lv,
    tr G (deq lv lv nattp)
    -> tr G (deq voidtp voidtp (univ lv)).
Proof.
intros G lv H.
apply (tr_univ_cumulative _ nzero); auto.
  {
  apply tr_voidtp_formation_univ.
  }

  {
  rewrite -> leqpagetp_nzero_equiv.
  apply tr_unittp_intro.
  }
Qed.


Lemma tr_unittp_formation_univ_gen :
  forall G lv,
    tr G (deq lv lv nattp)
    -> tr G (deq unittp unittp (univ lv)).
Proof.
intros G lv H.
apply (tr_univ_cumulative _ nzero); auto.
  {
  apply tr_unittp_formation_univ.
  }

  {
  rewrite -> leqpagetp_nzero_equiv.
  apply tr_unittp_intro.
  }
Qed.


Lemma tr_booltp_formation_univ_gen :
  forall G lv,
    tr G (deq lv lv nattp)
    -> tr G (deq booltp booltp (univ lv)).
Proof.
intros G lv H.
apply (tr_univ_cumulative _ nzero); auto.
  {
  apply tr_booltp_formation_univ.
  }

  {
  rewrite -> leqpagetp_nzero_equiv.
  apply tr_unittp_intro.
  }
Qed.


(* pi *)

Lemma tr_pi_of_ext :
  forall G a b m l,
    tr G (deqtype a a)
    -> tr (hyp_tm a :: G) (deq (app (subst sh1 m) (var 0)) (app (subst sh1 m) (var 0)) b)
    -> equiv m (lam l)
    -> tr G (deq m m (pi a b)).
Proof.
intros G a b m l Ha Hm Hlam.
apply (tr_pi_ext _#5 voidtp voidtp voidtp voidtp); auto.
  {
  rewrite -> Hlam.
  apply tr_pi_intro.
    {
    apply tr_voidtp_istype.
    }
  apply (tr_voidtp_elim _ (var 0) (var 0)).
  eapply hypothesis; eauto using index_0.
  }

  {
  rewrite -> Hlam.
  apply tr_pi_intro.
    {
    apply tr_voidtp_istype.
    }
  apply (tr_voidtp_elim _ (var 0) (var 0)).
  eapply hypothesis; eauto using index_0.
  }
Qed.



(* prod *)

Lemma tr_prod_intro :
  forall G a b m m' n n',
    tr G (deq m m' a)
    -> tr G (deq n n' b)
    -> tr G (deq (ppair m n) (ppair m' n') (prod a b)).
Proof.
intros G a b m m' n n' Hm Hn.
apply (tr_eqtype_convert _#3 (sigma a (subst sh1 b))).
  {
  apply tr_eqtype_symmetry.
  apply tr_prod_sigma_equal.
    {
    eapply tr_inhabitation_formation; eauto.
    }

    {
    eapply tr_inhabitation_formation; eauto.
    }
  }
apply tr_sigma_intro; auto.
  {
  simpsub.
  auto.
  }

  {
  eapply (weakening _ [_] []).
    {
    cbn [length unlift].
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
Qed.



(* equal *)

Lemma tr_eq_reflexivity:
  forall G m n a,
    tr G (deq m n a) ->
    tr G (deq m m a).
Proof.
  intros  G m n a H0. pose proof (tr_symmetry _#4 H0) as H1.
  apply (tr_transitivity _#5 H0 H1).
Qed.



(* eqtype *)

Lemma deqtype_intro :
  forall G a b m n,
    tr G (deq m n (eqtype a b))
    -> tr G (deqtype a b).
Proof.
intros G a b m n H.
unfold deqtype.
apply (tr_transitivity _ _ m).
  {
  apply tr_symmetry.
  apply tr_eqtype_eta.
  apply (tr_transitivity _ _ n); auto.
  apply tr_symmetry; auto.
  }

  {
  apply tr_eqtype_eta.
  apply (tr_transitivity _ _ n); auto.
  apply tr_symmetry; auto.
  }
Qed.


Lemma tr_eqtype_formation_left :
  forall G a b,
    tr G (deqtype a b)
    -> tr G (deqtype a a).
Proof.
intros G a b H.
eapply tr_eqtype_transitivity; eauto.
apply tr_eqtype_symmetry; auto.
Qed.


Lemma tr_eqtype_formation_right :
  forall G a b,
    tr G (deqtype a b)
    -> tr G (deqtype b b).
Proof.
intros G a b H.
eapply tr_eqtype_formation_left.
apply tr_eqtype_symmetry; eauto.
Qed.



(* Subtype *)

Lemma tr_subtype_refl :
  forall G a,
    tr G (deqtype a a)
    -> tr G (dsubtype a a).
Proof.
intros G a Ha.
apply tr_subtype_intro; auto.
eapply hypothesis; eauto using index_0.
Qed.


Lemma tr_subtype_refl' :
  forall G a b,
    tr G (deqtype a b)
    -> tr G (dsubtype a b).
Proof.
intros G a b Ha.
apply tr_subtype_intro.
  {
  eapply tr_eqtype_formation_left; eauto.
  }

  {
  eapply tr_eqtype_formation_right; eauto.
  }

  {
  apply (tr_eqtype_convert _ _ _ (subst sh1 a)).
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

    {
    eapply hypothesis; eauto using index_0.
    }
  }
Qed.


Lemma tr_subtype_istype1 :
  forall G a b,
    tr G (dsubtype a b)
    -> tr G (deqtype a a).
Proof.
intros G a b Hsub.
eapply tr_subtype_formation_invert1.
eapply tr_inhabitation_formation.
exact Hsub.
Qed.


Lemma tr_subtype_istype2 :
  forall G a b,
    tr G (dsubtype a b)
    -> tr G (deqtype b b).
Proof.
intros G a b Hsub.
eapply tr_subtype_formation_invert2.
eapply tr_inhabitation_formation.
exact Hsub.
Qed.


Lemma tr_subtype_trans :
  forall G a b c,
    tr G (dsubtype a b)
    -> tr G (dsubtype b c)
    -> tr G (dsubtype a c).
Proof.
intros G a b c Hab Hbc.
apply tr_subtype_intro.
  {
  eapply tr_subtype_istype1; eauto.
  }

  {
  eapply tr_subtype_istype2; eauto.
  }

  {
  apply (tr_subtype_elim _ (subst sh1 b)).
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    exact Hbc.
    }
  apply (tr_subtype_elim _ (subst sh1 a)).
    {
    apply (weakening _ [_] []).
      {
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length].
      simpsub.
      rewrite <- !compose_assoc.
      unfold sh1.
      rewrite -> !compose_sh_unlift.
      simpsub.
      reflexivity.
      }
    cbn [length].
    simpsub.
    cbn [List.app].
    exact Hab.
    }
  eapply hypothesis; eauto using index_0.
  }
Qed.


Lemma tr_subtype_convert_hyp' :
  forall G1 G2 a b J,
    tr G1 (dsubtype a b)
    -> tr G1 (dsubtype b a)
    -> tr (G2 ++ hyp_tm b :: G1) J
    -> tr (G2 ++ hyp_tm a :: G1) J.
Proof.
intros G1 G2 a b J Hab Hba HJ.
eapply tr_subtype_convert_hyp; eauto.
  {
  apply (weakening _ [_] []).
    {
    simpsub.
    reflexivity.
    }

    {
    cbn [length].
    simpsub.
    rewrite <- !compose_assoc.
    unfold sh1.
    rewrite -> !compose_sh_unlift.
    simpsub.
    reflexivity.
    }
  cbn [length].
  simpsub.
  cbn [List.app].
  auto.
  }

  {
  apply (weakening _ [_] []).
    {
    simpsub.
    reflexivity.
    }

    {
    cbn [length].
    simpsub.
    rewrite <- !compose_assoc.
    unfold sh1.
    rewrite -> !compose_sh_unlift.
    simpsub.
    reflexivity.
    }
  cbn [length].
  simpsub.
  cbn [List.app].
  auto.
  }
Qed.


Lemma tr_halts_eta2 :
  forall G p q m,
    tr G (deq p q (halts m))
    -> tr G (deq triv triv (halts m)).
Proof.
intros G p q m Htr.
assert (tr G (deq p triv (halts m))) as Htr'.
  {
  apply tr_halts_eta.
  apply (tr_transitivity _ _ q); auto.
  apply tr_symmetry; auto.
  }
apply (tr_transitivity _ _ p); auto.
apply tr_symmetry; auto.
Qed.


Lemma tr_eqtype_convert_hyp_better :
  forall G1 G2 a b c m n,
    tr (G2 ++ hyp_tm a :: G1) (deqtype (subst (sh (S (length G2))) a) (subst (sh (S (length G2))) b))
    -> tr (G2 ++ hyp_tm b :: G1) (deq m n c)
    -> tr (G2 ++ hyp_tm a :: G1) (deq m n c).
Proof.
intros G1 G2 a b c m n Heq Hc.
replace (deq m n c) with (substj (dot triv id) (deq (subst sh1 m) (subst sh1 n) (subst sh1 c))) by (simpsub; reflexivity).
eapply tr_generalize; eauto.
apply (exchange_1_n _ G2 _ nil).
  {
  simpsub.
  rewrite <- !compose_assoc.
  rewrite -> !compose_sh_unlift_ge; [| omega].
  replace (S (length G2) - length G2) with 1 by omega.
  simpsub.
  reflexivity.
  }
simpsub.
cbn [List.app].
rewrite -> !compose_sh_unlift_ge; [| omega].
replace (S (length G2) - length G2) with 1 by omega.
simpsub.
rewrite <- (compose_sh_sh _ 1 (length G2)).
rewrite <- under_dots.
apply exchange_1_1.
  {
  simpsub.
  reflexivity.
  }
simpsub.
rewrite -> length_substctx.
rewrite <- compose_under.
simpsub.
apply (tr_eqtype_convert_hyp (hyp_tm (eqtype a b) :: G1) _ _ (subst sh1 b)).
  {
  unfold deqtype.
  eapply tr_eqtype_eta2.
  eapply hypothesis; eauto using index_0, index_S.
  }

  {
  replace (substctx (dot (var 0) (sh 2)) G2 ++ hyp_tm (subst sh1 b) :: hyp_tm (eqtype a b) :: G1) with ((substctx (dot (var 0) (sh 2)) G2 ++ [hyp_tm (subst sh1 b)]) ++ [hyp_tm (eqtype a b)] ++ G1).
  2:{
    rewrite <- app_assoc.
    cbn [List.app].
    reflexivity.
    }
  apply weakening.
    {
    cbn [length].
    rewrite -> !substctx_append.
    rewrite <- substctx_compose.
    cbn [length].
    replace (dot (var 0) (sh 2)) with (@under obj 1 (sh 1)) by (simpsub; reflexivity).
    rewrite <- compose_under.
    rewrite <- compose_assoc.
    rewrite -> compose_sh_unlift.
    simpsub.
    rewrite <- compose_assoc.
    unfold sh1.
    rewrite -> compose_sh_unlift.
    simpsub.
    reflexivity.
    }

    {
    cbn [length].
    simpsub.
    rewrite -> app_length.
    cbn [length].
    rewrite -> length_substctx.
    replace (dot (var 0) (sh 2)) with (@under obj 1 (sh 1)) by (simpsub; reflexivity).
    rewrite -> under_sum.
    rewrite <- !compose_under.
    rewrite <- compose_assoc.
    rewrite -> compose_sh_unlift.
    simpsub.
    reflexivity.
    }
  cbn [length].
  simpsub.
  rewrite -> !substctx_append.
  rewrite <- substctx_compose.
  rewrite -> app_length.
  cbn [length].
  replace (dot (var 0) (sh 2)) with (@under obj 1 (sh 1)) by (simpsub; reflexivity).
  rewrite -> under_sum.
  rewrite -> length_substctx.
  rewrite <- !compose_under.
  rewrite -> compose_sh_unlift.
  simpsub.
  rewrite <- app_assoc.
  cbn [List.app].
  rewrite -> (substctx_eqsub _ _ id).
    {
    simpsub.
    exact Hc.
    }

    {
    apply eqsub_symm.
    apply eqsub_expand_id.
    }
  }
Qed.


Lemma tr_tighten_better :
  forall G1 G2 a b c m n,
    tr (G2 ++ hyp_tm a :: G1) (dsubtype (subst (sh (S (length G2))) b) (subst (sh (S (length G2))) a))
    -> tr (G2 ++ hyp_tm a :: G1) (deq (var (length G2)) (var (length G2)) (subst (sh (S (length G2))) b))
    -> tr (G2 ++ hyp_tm b :: G1) (deq m n c)
    -> tr (G2 ++ hyp_tm a :: G1) (deq m n c).
Proof.
intros G1 G2 a b c m n Hsub Hof Hc.
apply (tr_assert _ (subst (sh (S (length G2))) (subtype b a)) triv).
  {
  simpsub.
  exact Hsub.
  }
apply (exchange_1_n _ G2 _ nil).
  {
  simpsub.
  rewrite <- !compose_assoc.
  rewrite -> !compose_sh_unlift_ge; [| omega].
  replace (S (length G2) - length G2) with 1 by omega.
  simpsub.
  reflexivity.
  }
simpsub.
cbn [List.app].
rewrite -> !compose_sh_unlift_ge; [| omega].
replace (S (length G2) - length G2) with 1 by omega.
simpsub.
rewrite <- (compose_sh_sh _ 1 (length G2)).
rewrite <- under_dots.
apply exchange_1_1.
  {
  simpsub.
  reflexivity.
  }
simpsub.
rewrite -> length_substctx.
rewrite <- compose_under.
simpsub.
apply (tr_assert _ (equal (subst (sh (2 + length G2)) b) (var (length G2)) (var (length G2))) triv).
  {
  apply tr_equal_intro.
  replace (hyp_tm (subst sh1 a) :: hyp_tm (subtype b a) :: G1) with ([hyp_tm (subst sh1 a)] ++ hyp_tm (subtype b a) :: G1) by reflexivity.
  rewrite -> app_assoc.
  eapply (weakening _ [_] _).
    {
    cbn [length unlift].
    simpsub.
    rewrite -> substctx_append.
    cbn [length].
    simpsub.
    reflexivity.
    }

    {
    cbn [length unlift].
    simpsub.
    rewrite -> app_length.
    rewrite -> length_substctx.
    cbn [length].
    rewrite -> !project_under_lt; [| omega].
    rewrite <- (compose_sh_sh _ 1 (1 + length G2)).
    rewrite -> compose_assoc.
    rewrite -> Nat.add_comm.
    rewrite -> compose_sh_under_eq.
    simpsub.
    reflexivity.
    }
  cbn [length unlift].
  simpsub.
  rewrite -> app_length.
  rewrite -> length_substctx.
  cbn [length].
  rewrite -> !project_under_lt; [| omega].
  rewrite <- (compose_sh_sh _ 1 (1 + length G2)).
  rewrite -> compose_assoc.
  rewrite -> Nat.add_comm.
  rewrite -> compose_sh_under_eq.
  simpsub.
  rewrite -> substctx_append.
  cbn [length].
  simpsub.
  rewrite <- app_assoc.
  cbn [List.app].
  rewrite -> Nat.add_comm.
  rewrite -> (substctx_eqsub _ _ id).
  2:{
    apply eqsub_symm.
    apply eqsub_expand_id.
    }
  simpsub.
  exact Hof.
  }
simpsub.
apply (exchange_1_n _ (substctx (dot (var 0) (sh 2)) G2) _ nil).
  {
  rewrite -> length_substctx.
  simpsub.
  rewrite <- !compose_assoc.
  rewrite -> !compose_sh_unlift_ge; [| omega].
  replace (2 + length G2 - length G2) with 2 by omega.
  simpsub.
  rewrite -> project_unlift_ge; auto.
  replace (length G2 - length G2) with 0 by omega.
  simpsub.
  rewrite -> Nat.add_0_r.
  reflexivity.
  }
rewrite -> length_substctx.
simpsub.
cbn [List.app Nat.add].
rewrite -> !compose_sh_unlift_ge; [| omega].
replace (S (S (length G2)) - length G2) with 2 by omega.
rewrite -> project_unlift_ge; auto.
replace (length G2 - length G2) with 0 by omega.
rewrite <- (compose_sh_sh _ 1 (length G2)).
rewrite <- under_dots.
rewrite <- compose_under.
rewrite <- (compose_sh_sh _ 1 1).
rewrite -> subst_compose.
apply tr_tighten.
  {
  apply (tr_subtype_eta2 _#3 (var 0) (var 0)).
  eapply hypothesis; eauto using index_0.
  }
eapply (weakening _ [_] _).
  {
  cbn [length unlift].
  simpsub.
  reflexivity.
  }

  {
  rewrite -> length_substctx.
  cbn [length unlift].
  simpsub.
  cbn [Nat.add].
  rewrite <- compose_under.
  simpsub.
  reflexivity.
  }
rewrite -> length_substctx.
cbn [length unlift].
simpsub.
cbn [Nat.add].
rewrite <- compose_under.
simpsub.
cbn [Nat.add].
replace (hyp_tm (subst sh1 b) :: hyp_tm (subtype b a) :: G1) with ([hyp_tm (subst sh1 b)] ++ hyp_tm (subtype b a) :: G1) by (simpsub; reflexivity).
rewrite -> app_assoc.
eapply (weakening _ [_] _).
  {
  cbn [length unlift].
  simpsub.
  rewrite -> substctx_append.
  cbn [length].
  simpsub.
  reflexivity.
  }

  {
  rewrite -> app_length.
  rewrite -> length_substctx.
  cbn [length unlift].
  simpsub.
  rewrite <- under_sum.
  rewrite <- compose_under.
  simpsub.
  reflexivity.
  }
cbn [length unlift].
rewrite -> substctx_append.
cbn [length].
simpsub.
rewrite <- app_assoc.
cbn [List.app].
rewrite -> app_length.
cbn [length].
rewrite -> length_substctx.
rewrite <- under_sum.
rewrite <- compose_under.
simpsub.
assert (@eqsub obj (under (length G2) (dot (var 0) sh1)) id) as Heq.
  {
  apply (eqsub_trans _ _ (under (length G2) id)).
    {
    apply eqsub_under.
    apply eqsub_symm.
    apply eqsub_expand_id.
    }

    {
    apply eqsub_under_id.
    }
  }
rewrite -> !(subst_eqsub _#4 Heq).
simpsub.
rewrite -> (substctx_eqsub _ _ id).
2:{
  apply eqsub_symm.
  apply eqsub_expand_id.
  }
simpsub.
exact Hc.
Qed.


(* Nonsense *)

Lemma tr_nonsense_formation :
  forall G,
    tr G (deqtype nonsense nonsense).
Proof.
intro G.
unfold nonsense.
apply tr_guard_formation.
  {
  apply tr_voidtp_istype.
  }

  {
  apply (tr_voidtp_elim _ (var 0) (var 0)).
  eapply hypothesis; eauto using index_0.
  }
Qed.


Lemma tr_nonsense_intro :
  forall G m n,
    tr G (deq m n nonsense).
Proof.
intros G m n.
unfold nonsense.
apply tr_guard_intro.
  {
  apply tr_voidtp_istype.
  }

  {
  apply (tr_voidtp_elim _ (var 0) (var 0)).
  eapply hypothesis; eauto using index_0.
  }
Qed.


(* Conjoin *)

Lemma tr_conjoin_formation :
  forall G a a' b b',
    tr G (deqtype a a')
    -> tr G (deqtype b b')
    -> tr G (deqtype (conjoin a b) (conjoin a' b')).
Proof.
intros G a a' b b' Ha Hb.
apply tr_intersect_formation.
  {
  apply tr_booltp_istype.
  }
apply tr_booltp_elim_eqtype.
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  eapply (weakening _ [_] []).
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
  auto.
  }

  {
  eapply (weakening _ [_] []).
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
  auto.
  }
Qed.


Lemma tr_conjoin_formation_univ :
  forall G a a' b b' lv,
    tr G (deq a a' (univ lv))
    -> tr G (deq b b' (univ lv))
    -> tr G (deq (conjoin a b) (conjoin a' b') (univ lv)).
Proof.
intros G a a' b b' lv Ha Hb.
assert (tr G (deq lv lv pagetp)) as Hlv.
  {
  apply tr_univ_formation_invert.
  eapply tr_inhabitation_formation; eauto.
  }
apply tr_intersect_formation_univ.
  {
  apply (tr_univ_cumulative _ Defined.nzero); auto.
    {
    apply tr_booltp_formation_univ.
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
  eapply (weakening _ [_] []).
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
  auto.
  }

  {
  eapply (weakening _ [_] []).
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
  auto.
  }
Qed.


Lemma tr_conjoin_intro :
  forall G a b m n,
    tr G (deq m n a)
    -> tr G (deq m n b)
    -> tr G (deq m n (conjoin a b)).
Proof.
intros G a b m n Ha Hb.
unfold conjoin.
apply tr_intersect_intro.
  {
  apply tr_booltp_istype.
  }
apply tr_equal_elim.
apply (tr_equal_eta2 _#4 
         (bite (var 0) (subst (under 0 sh1) triv) (subst (under 0 sh1) triv))
         (bite (var 0) (subst (under 0 sh1) triv) (subst (under 0 sh1) triv))).
apply (tr_booltp_eta_hyp _ []).
  {
  cbn [length].
  simpsub.
  cbn [List.app].
  apply tr_equal_intro.
  apply (tr_compute _ _ a _ m _ n); auto using equiv_refl.
  apply steps_equiv.
  apply star_one.
  apply step_bite2.
  }

  {
  cbn [length].
  simpsub.
  cbn [List.app].
  apply tr_equal_intro.
  apply (tr_compute _ _ b _ m _ n); auto using equiv_refl.
  apply steps_equiv.
  apply star_one.
  apply step_bite3.
  }
Qed.


Lemma tr_conjoin_elim1 :
  forall G a b m n,
    tr G (deq m n (conjoin a b))
    -> tr G (deq m n a).
Proof.
intros G a b m n H.
unfold conjoin in H.
apply (tr_compute _ _ (bite btrue a b) _ m _ n); auto using equiv_refl.
  {
  apply equiv_symm.
  apply steps_equiv.
  apply star_one.
  apply step_bite2.
  }
replace (bite btrue a b) with (subst1 btrue (bite (var 0) (subst sh1 a) (subst sh1 b))) by (simpsub; auto).
apply (tr_intersect_elim _ booltp _ _ _ _ btrue); auto.
apply tr_booltp_intro_btrue.
Qed.


Lemma tr_conjoin_elim2 :
  forall G a b m n,
    tr G (deq m n (conjoin a b))
    -> tr G (deq m n b).
Proof.
intros G a b m n H.
unfold conjoin in H.
apply (tr_compute _ _ (bite bfalse a b) _ m _ n); auto using equiv_refl.
  {
  apply equiv_symm.
  apply steps_equiv.
  apply star_one.
  apply step_bite3.
  }
replace (bite bfalse a b) with (subst1 bfalse (bite (var 0) (subst sh1 a) (subst sh1 b))) by (simpsub; auto).
apply (tr_intersect_elim _ booltp _ _ _ _ bfalse); auto.
apply tr_booltp_intro_bfalse.
Qed.


Lemma tr_conjoin_formation_invert1 :
  forall G a a' b b',
    tr G (deqtype (conjoin a b) (conjoin a' b'))
    -> tr G (deqtype a a').
Proof.
intros G a a' b b' H.
unfold conjoin in H.
assert (forall (x y : @term obj), equiv x (bite btrue x y)) as Hequiv.
  {
  intros x y.
  apply equiv_symm.
  apply steps_equiv.
  apply star_one.
  apply step_bite2.
  }
rewrite -> (Hequiv a b).
rewrite -> (Hequiv a' b').
clear Hequiv.
replace (deqtype (bite btrue a b) (bite btrue a' b')) with (substj (dot btrue id) (deqtype (bite (var 0) (subst sh1 a) (subst sh1 b)) (bite (var 0) (subst sh1 a') (subst sh1 b')))) by (simpsub; auto).
apply (tr_generalize _ booltp).
  {
  apply tr_booltp_intro_btrue.
  }
eapply tr_intersect_formation_invert2; eauto.
Qed.


(* Subtyping lemmas *)

Lemma tr_semifut_sub :
  forall G a a',
    tr (promote G) (dsubtype a a')
    -> tr G (dsubtype (semifut a) (semifut a')).
Proof.
intros G a a' Ha.
apply tr_subtype_intro.
  {
  apply tr_semifut_formation.
  eapply tr_subtype_istype1; eauto.
  }

  {
  apply tr_semifut_formation.
  eapply tr_subtype_istype2; eauto.
  }
simpsub.
replace (deq (var 0) (var 0) (semifut (subst sh1 a'))) with (deq (subst1 (var 0) (var 0)) (subst1 (var 0) (var 0)) (subst1 (var 0) (subst (sh 2) (semifut a')))) by (simpsub; auto).
apply (tr_semifut_elim _ _ _ (subst sh1 a)).
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  cbn.
  eapply (weakening _ [_] []).
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
  eapply tr_subtype_istype1; eauto.
  }
simpsub.
eapply (weakening _ [_] [_]).
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
apply tr_semifut_intro.
cbn.
apply (tr_subtype_elim _ (subst sh1 a)).
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
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  exact Ha.
  }

  {
  eapply hypothesis; eauto using index_0.
  }
Qed.


Lemma tr_pi_sub :
  forall G a a' b b',
    tr G (dsubtype a' a)
    -> tr (hyp_tm a' :: G) (dsubtype b b')
    -> tr (hyp_tm a :: G) (deqtype b b)
    -> tr G (dsubtype (pi a b) (pi a' b')).
Proof.
intros G a a' b b' Hsuba Hsubb Hb.
apply tr_subtype_intro.
  {
  apply tr_pi_formation; auto.
  eapply tr_subtype_istype2; eauto.
  }

  {
  apply tr_pi_formation.
    {
    eapply tr_subtype_istype1; eauto.
    }

    {
    eapply tr_subtype_istype2; eauto.
    }
  }
simpsub.
eapply tr_pi_ext; eauto.
3:{
  eapply hypothesis; eauto using index_0.
  simpsub.
  auto.
  }

3:{
  eapply hypothesis; eauto using index_0.
  simpsub.
  auto.
  }

  {
  apply (weakening _ [_] []).
    {
    simpsub.
    auto.
    }
  
    {
    simpsub.
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  eapply tr_subtype_istype1; eauto.
  }

  {
  simpsub.
  cbn [Nat.add].
  apply (tr_subtype_elim _ (subst (dot (var 0) (sh 2)) b)).
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
      auto.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    rewrite -> !subst_var0_sh1; auto.
    }

    {
    eapply tr_pi_elim'.
      {
      eapply hypothesis; eauto using index_S, index_0.
      simpsub; auto.
      }
  
      {
      eapply (tr_subtype_elim _ (subst (sh 2) a')).
        {
        eapply (weakening _ [_; _] []).
          {
          simpsub; auto.
          }
  
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
  
        {
        eapply hypothesis; eauto using index_0.
        simpsub; auto.
        }
      }
      
      {
      simpsub.
      cbn [Nat.add].
      simpsub.
      auto.
      }
    }
  }
Qed.


Lemma tr_intersect_sub :
  forall G a a' b b',
    tr G (dsubtype a' a)
    -> tr (hyp_tm a' :: G) (dsubtype b b')
    -> tr (hyp_tm a :: G) (deqtype b b)
    -> tr G (dsubtype (intersect a b) (intersect a' b')).
Proof.
intros G a a' b b' Hsuba Hsubb Hb.
apply tr_subtype_intro.
  {
  apply tr_intersect_formation; auto.
  eapply tr_subtype_istype2; eauto.
  }

  {
  apply tr_intersect_formation.
    {
    eapply tr_subtype_istype1; eauto.
    }

    {
    eapply tr_subtype_istype2; eauto.
    }
  }
simpsub.
cbn [Nat.add].
apply tr_intersect_intro.
  {
  apply (weakening _ [_] []).
    {
    simpsub.
    auto.
    }
  
    {
    simpsub.
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  eapply tr_subtype_istype1; eauto.
  }

  {
  simpsub.
  cbn [Nat.add].
  apply (tr_subtype_elim _ (subst (dot (var 0) (sh 2)) b)).
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
      auto.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    rewrite -> !subst_var0_sh1; auto.
    }

    {
    replace (subst (dot (var 0) (sh 2)) b) with (subst1 (var 0) (subst (dot (var 0) (sh 3)) b)) by (simpsub; reflexivity).
    apply (tr_intersect_elim _ (subst (sh 2) a) _ _ _ (var 0) (var 0)).
      {
      eapply hypothesis; eauto using index_S, index_0.
      simpsub.
      reflexivity.
      }

      {
      eapply (tr_subtype_elim _ (subst (sh 2) a')).
        {
        eapply (weakening _ [_; _] []).
          {
          simpsub; auto.
          }
  
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
  
        {
        eapply hypothesis; eauto using index_0.
        simpsub; auto.
        }
      }
    }
  }
Qed.


Lemma tr_conjoin_sub_right :
  forall G a b b',
    tr G (dsubtype a b)
    -> tr G (dsubtype a b')
    -> tr G (dsubtype a (conjoin b b')).
Proof.
intros G a b b' Hsub Hsub'.
apply tr_subtype_intro.
  {
  eapply tr_subtype_istype1; eauto.
  }

  {
  apply tr_conjoin_formation.
    {
    eapply tr_subtype_istype2; eauto.
    }

    {
    eapply tr_subtype_istype2; eauto.
    }
  }
simpsub.
apply tr_conjoin_intro.
  {
  apply (tr_subtype_elim _ (subst sh1 a)).
    {
    eapply (weakening _ [_] []).
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
    auto.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }

  {
  apply (tr_subtype_elim _ (subst sh1 a)).
    {
    eapply (weakening _ [_] []).
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
    auto.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }
Qed.


Lemma tr_conjoin_sub_left1 :
  forall G a b,
    tr G (deqtype a a)
    -> tr G (deqtype b b)
    -> tr G (dsubtype (conjoin a b) a).
Proof.
intros G a b Ha Hb.
apply tr_subtype_intro; auto.
  {
  apply tr_conjoin_formation; auto.
  }
apply (tr_conjoin_elim1 _ _ (subst sh1 b)).
eapply hypothesis; eauto using index_0.
simpsub.
auto.
Qed.


Lemma tr_conjoin_sub_left2 :
  forall G a b,
    tr G (deqtype a a)
    -> tr G (deqtype b b)
    -> tr G (dsubtype (conjoin a b) b).
Proof.
intros G a b Ha Hb.
apply tr_subtype_intro; auto.
  {
  apply tr_conjoin_formation; auto.
  }
apply (tr_conjoin_elim2 _ (subst sh1 a)).
eapply hypothesis; eauto using index_0.
simpsub.
auto.
Qed.
