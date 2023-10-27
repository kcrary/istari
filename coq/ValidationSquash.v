
Require Import Relation.

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

Require Import ValidationSet.


Hint Rewrite def_set def_squash : prepare.



Lemma squashForm_valid : squashForm_obligation.
Proof.
prepare.
intros G a ext0 H.
apply tr_squash_formation1; auto.
Qed.


Lemma squashEq_valid : squashEq_obligation.
Proof.
prepare.
intros G a b ext3 ext2 m n Ha Hb Hm Hn.
assert (tr (hyp_tm unittp :: G) (deqtype (subst sh1 a) (subst sh1 a))) as Ha'.
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
  exact Ha.
  }
assert (tr (hyp_tm unittp :: G) (deqtype (subst sh1 b) (subst sh1 b))) as Hb'.
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
  exact Hb.
  }
apply (tr_set_formation _#5 (subst (under 1 sh1) m) (subst (under 1 sh1) n)); auto using tr_unittp_istype.
  {
  apply (weakening _ [_] [_]).
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
  rewrite -> subst_var0_sh1.
  auto.
  }

  {
  apply (weakening _ [_] [_]).
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
  rewrite -> subst_var0_sh1.
  auto.
  }
Qed.


Require Import NatLemmas.

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


Lemma squashFormUniv_valid : squashFormUniv_obligation.
Proof.
prepare.
intros G a i ext0 H.
unfold squash.
apply (tr_set_formation_univ _#6 (var 0) (var 0)).
  {
  apply tr_unittp_formation_univ_gen.
  apply tr_univ_formation_invert.
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
  simpsub.
  cbn [Nat.add].
  eapply hypothesis; eauto using index_0.
  simpsub.
  auto.
  }

  {
  simpsub.
  cbn [Nat.add].
  eapply hypothesis; eauto using index_0.
  simpsub.
  auto.
  }
Qed.


Lemma squashEqUniv_valid : squashEqUniv_obligation.
Proof.
prepare.
intros G a b i ext3 ext2 m n Ha Hb Hm Hn.
unfold squash.
apply (tr_set_formation_univ _#6 (subst (under 1 sh1) m) (subst (under 1 sh1) n)).
  {
  apply tr_unittp_formation_univ_gen.
  apply tr_univ_formation_invert.
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
  apply (weakening _ [_] [_]).
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
  rewrite -> subst_var0_sh1; auto.
  }

  {
  apply (weakening _ [_] [_]).
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
  rewrite -> subst_var0_sh1; auto.
  }
Qed.


Lemma squashIntroOf_valid : squashIntroOf_obligation.
Proof.
prepare.
intros G a m H.
unfold squash.
apply (tr_set_intro _#5 m).
  {
  apply tr_unittp_intro.
  }

  {
  simpsub.
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
Qed.


Lemma squashIntro_valid : squashIntro_obligation.
Proof.
prepare.
intros G a m H.
unfold squash.
apply (tr_set_intro _#5 m).
  {
  apply tr_unittp_intro.
  }

  {
  simpsub.
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
Qed.


Lemma squashElim_valid : squashElim_obligation.
Proof.
prepare.
intros G a c m ext1 ext0 n Hhyg Hm Ha Hn.
unfold squash in Hm.
refine (tr_set_elim2 _#5 Hm _ _).
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
simpsub.
so (subst_into_absent_single _ _ _ triv Hhyg) as H.
simpsubin H.
rewrite -> H; auto.
Qed.


Lemma squashExt_valid : squashExt_obligation.
Proof.
prepare.
intros G a m n ext2 ext1 ext0 Hm Hn Ha.
unfold squash in * |- *.
refine (tr_set_elim2 _#5 Hm _ _).
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
simpsub.
cbn [Nat.add].
apply (tr_set_intro _#5 (var 0)).
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
  apply (tr_transitivity _ _ triv).
    {
    apply tr_unittp_eta.
    eapply tr_set_elim1; eauto.
    }

    {
    apply tr_symmetry.
    apply tr_unittp_eta.
    eapply tr_set_elim1; eauto.
    }
  }

  {
  simpsub.
  eapply hypothesis; eauto using index_0.
  }

  {
  apply (weakening _ [_; _] []).
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


Lemma squashLeft_valid : squashLeft_obligation.
Proof.
prepare.
intros G1 G2 a c ext0 m Hhyg Ha Hm.
unfold squash.
replace (subst (under (length G2) (dot triv (sh 1))) m) with (subst (under (length G2) (dot triv id)) (subst (under (length G2) (dot (var 0) (sh 2))) m)).
2:{
  rewrite <- subst_compose.
  rewrite <- compose_under.
  simpsub.
  auto.
  }
apply tr_set_left; auto.
  {
  eapply hygiene_subst; eauto.
  intros i Hi.
  cbn in Hi.
  set (k := length G2) in Hi |- *.
  so (Nat.lt_trichotomy i k) as [Hlt | [Heq | Hlt]].
    {
    rewrite -> project_under_lt; auto.
    apply hygiene_var.
    omega.
    }

    {
    contradiction.
    }

    {
    rewrite -> project_under_geq; try omega.
    replace (i - k) with (S (i - k - 1)) by omega.
    simpsub.
    apply hygiene_var.
    omega.
    }
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
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  auto.
  }
match goal with
| |- tr _ ?X =>
   change (tr (substctx sh1 G2 ++ ([hyp_tm (subst sh1 a)] ++ hyp_tm unittp :: G1)) X)
end.
rewrite -> app_assoc.
replace (under (length G2) (dot (var 0) (sh 2))) with (@under obj (length (substctx sh1 G2 ++ [hyp_tm (subst sh1 a)])) sh1).
2:{
  rewrite -> app_length.
  cbn [length].
  rewrite -> length_substctx.
  rewrite <- under_sum.
  auto.
  }
apply tr_unittp_eta_hyp.
rewrite -> app_length.
cbn [length].
rewrite -> length_substctx.
rewrite -> substctx_append.
cbn [length].
simpsub.
rewrite <- app_assoc.
cbn [List.app].
rewrite <- under_sum.
rewrite <- compose_under.
rewrite -> under_succ.
unfold sh1.
rewrite -> compose_sh_dot.
rewrite -> under_zero.
simpsub.
unfold Defs.triv in Hm.
exact Hm.
Qed.


Lemma squashSub_valid : squashSub_obligation.
Proof.
prepare.
intros G a b ext1 m Hb Himp.
rewrite -> def_arrow in Himp.
apply tr_subtype_intro.
  {
  apply tr_squash_formation1.
  eapply tr_pi_formation_invert1; eauto.
  eapply tr_inhabitation_formation; eauto.
  }

  {
  apply tr_squash_formation1; auto.
  }
rewrite -> subst_squash.
unfold squash.
apply (tr_set_elim2 _ unittp (subst (sh 2) a) (var 0)).
  {
  eapply hypothesis; auto using index_0.
  simpsub.
  auto.
  }

  {
  eapply (weakening _ [_; _] []).
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
  eapply tr_pi_formation_invert1; eauto.
  eapply tr_inhabitation_formation; eauto.
  }
simpsub.
cbn [Nat.add].
eapply (tr_set_intro _#5 (app (subst (sh 2) m) (var 0))).
  {
  apply (tr_set_elim1 _ _ (subst (sh 3) a)).
  eapply hypothesis; eauto using index_0, index_S.
  simpsub.
  reflexivity.
  }

  {
  simpsub.
  eapply (tr_pi_elim' _ (subst (sh 2) a) (subst (sh 3) b)).
    {
    eapply (weakening _ [_; _] []).
      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
  
      {
      cbn [length unlift].
      simpsub.
      eauto.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app Nat.add].
    simpsub.
    auto.
    }

    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }
  
    {
    simpsub.
    reflexivity.
    }
  }

  {
  eapply (weakening _ [_; _; _] []).
    {
    cbn [length unlift].
    simpsub.
    reflexivity.
    }

    {
    cbn [length unlift].
    simpsub.
    eauto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  auto.
  }
Qed.
