
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
Require Import Defined.
Require Import PageType.


(* equivalences *)

Lemma theta_equiv :
  forall object (f : @term object), equiv (app theta f) (app f (app theta f)).
Proof.
intros object f.
apply steps_equiv.
apply theta_fix.
Qed.


Lemma leqpagetp_nzero_equiv :
  forall object m, @equiv object (leqpagetp nzero m) unittp.
Proof.
intros object m.
unfold leqpagetp.
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
      apply PageType.theta_fix.
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


Fixpoint unlift i : @sub obj :=
  match i with
  | 0 => id
  | S i' => dot arb (unlift i')
  end.


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



(* base types *)

Lemma tr_voidtp_istype :
  forall G,
    tr G (deqtype voidtp voidtp).
Proof.
intros G.
apply (tr_formation_weaken _ nzero).
apply tr_voidtp_formation.
Qed.


Lemma tr_unittp_istype :
  forall G,
    tr G (deqtype unittp unittp).
Proof.
intros G.
apply (tr_formation_weaken _ nzero).
apply tr_unittp_formation.
Qed.


Lemma tr_booltp_istype :
  forall G,
    tr G (deqtype booltp booltp).
Proof.
intros G.
apply (tr_formation_weaken _ nzero).
apply tr_booltp_formation.
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


Lemma tr_eqtype_reflexivity:
  forall G a a',
    tr G (deqtype a a') ->
    tr G (deqtype a a).
Proof.
  intros  G a a' H0. pose proof (tr_eqtype_symmetry _#3 H0) as H1.
  apply (tr_eqtype_transitivity _#4 H0 H1).
Qed.


Lemma tr_eqtype_formation_invert1 :
  forall G a b,
    tr G (deqtype a b)
    -> tr G (deqtype a a).
Proof.
intros G a b H.
eapply tr_eqtype_transitivity; eauto.
apply tr_eqtype_symmetry; auto.
Qed.


Lemma tr_eqtype_formation_invert2 :
  forall G a b,
    tr G (deqtype a b)
    -> tr G (deqtype b b).
Proof.
intros G a b H.
eapply tr_eqtype_formation_invert1.
apply tr_eqtype_symmetry; eauto.
Qed.



(* subtype *)

Lemma tr_subtype_refl :
  forall G a,
    tr G (deqtype a a)
    -> tr G (dsubtype a a).
Proof.
intros G a Ha.
apply tr_subtype_intro; auto.
eapply hypothesis; eauto using index_0.
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
