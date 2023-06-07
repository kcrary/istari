
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


Hint Rewrite def_set def_iset def_squash : prepare.


Lemma subst_squash :
  forall object (s : @sub object) a, subst s (squash a) = squash (subst s a).
Proof.
intros object s a.
unfold squash.
simpsub.
reflexivity.
Qed.


Lemma setForm_valid : setForm_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
eapply (tr_set_formation _#5 (var 0) (var 0)); eauto.
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  eapply hypothesis; eauto using index_0.
  }
Qed.


Lemma isetForm_valid : isetForm_obligation.
Proof.
prepare.
intros G a b ext1 ext0 Ha Hb.
eapply (tr_iset_formation _#5); eauto.
Qed.


Lemma setEq_valid : setEq_obligation.
Proof.
prepare.
intros G a b c d ext4 ext3 ext2 ext1 ext0 Hab Hc Hd Hcd Hdc.
eapply tr_set_formation; eauto.
Qed.


Lemma isetEq_valid : isetEq_obligation.
Proof.
prepare.
intros G a b c d ext1 ext0 Hab Hcd.
eapply tr_iset_formation; eauto.
Qed.


Lemma setFormUniv_valid : setFormUniv_obligation.
Proof.
prepare.
intros G a b i ext1 ext0 Ha Hb.
eapply (tr_set_formation_univ _#6 (var 0) (var 0)); eauto.
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  eapply hypothesis; eauto using index_0.
  }
Qed.


Lemma isetFormUniv_valid : isetFormUniv_obligation.
Proof.
prepare.
intros G a b i ext1 ext0 Ha Hb.
eapply (tr_iset_formation_univ _#6); eauto.
Qed.


Lemma setEqUniv_valid : setEqUniv_obligation.
Proof.
prepare.
intros G a b c d i ext4 ext3 ext2 ext1 ext0 Hab Hc Hd Hcd Hdc.
eapply tr_set_formation_univ; eauto.
Qed.


Lemma isetEqUniv_valid : isetEqUniv_obligation.
Proof.
prepare.
intros G a b c d i ext1 ext0 Hab Hcd.
eapply tr_iset_formation_univ; eauto.
Qed.


Lemma setWeakenOf_valid : setWeakenOf_obligation.
Proof.
prepare.
intros G a b m ext0 H.
eapply tr_set_elim1; eauto.
Qed.


Lemma isetWeakenOf_valid : isetWeakenOf_obligation.
Proof.
prepare.
intros G a b m ext0 H.
eapply tr_iset_elim1; eauto.
Qed.


Lemma setWeakenEq_valid : setWeakenEq_obligation.
Proof.
prepare.
intros G a b m n ext0 H.
eapply tr_set_elim1; eauto.
Qed.


Lemma isetWeakenEq_valid : isetWeakenEq_obligation.
Proof.
prepare.
intros G a b m n ext0 H.
eapply tr_iset_elim1; eauto.
Qed.


Lemma setWeaken_valid : setWeaken_obligation.
Proof.
prepare.
intros G a b m H.
eapply tr_set_elim1; eauto.
Qed.


Lemma isetWeaken_valid : isetWeaken_obligation.
Proof.
prepare.
intros G a b m H.
eapply tr_iset_elim1; eauto.
Qed.


Lemma setIntroOf_valid : setIntroOf_obligation.
Proof.
prepare.
intros G a b m ext2 ext1 ext0 Hb Hm Hmb.
eapply tr_set_intro; eauto.
Qed.


Lemma isetIntroOf_valid : isetIntroOf_obligation.
Proof.
prepare.
intros G a b m ext2 ext1 ext0 Hb Hm Hmb.
eapply tr_iset_intro; eauto.
Qed.


Lemma setIntroEq_valid : setIntroEq_obligation.
Proof.
prepare.
intros G a b m n ext2 ext1 ext0 Hb Hmn Hmb.
eapply tr_set_intro; eauto.
Qed.


Lemma isetIntroEq_valid : isetIntroEq_obligation.
Proof.
prepare.
intros G a b m n ext2 ext1 ext0 Hb Hmn Hmb.
eapply tr_iset_intro; eauto.
Qed.


Lemma setIntro_valid : setIntro_obligation.
Proof.
prepare.
intros G a b m ext2 ext1 ext0 Hb Hm Hmb.
eapply tr_set_intro; eauto.
Qed.


Lemma isetIntro_valid : isetIntro_obligation.
Proof.
prepare.
intros G a b m ext2 ext1 ext0 Hb Hm Hmb.
eapply tr_iset_intro; eauto.
Qed.


Lemma tr_squash_formation1 :
  forall G a,
    tr G (deqtype a a)
    -> tr G (deqtype (squash a) (squash a)).
Proof.
intros G a H.
unfold squash.
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
  exact H.
  }
apply (tr_set_formation _#5 (var 0) (var 0)); auto.
  {
  apply tr_unittp_istype.
  }

  {
  eapply hypothesis; eauto using index_0.
  }

  {
  eapply hypothesis; eauto using index_0.
  }
Qed.    


Lemma setIntroOfSquash_valid : setIntroOfSquash_obligation.
Proof.
prepare.
intros G a b m ext2 ext1 ext0 Hb Hm Hmb.
apply (tr_eqtype_convert _#3 (set a (squash b))).
  {
  apply tr_eqtype_symmetry.
  apply tr_squash_idem.
  eapply (tr_set_formation _#5 (var 0) (var 0)); eauto.
    {
    eapply tr_inhabitation_formation; eauto.
    }
    
    {
    eapply hypothesis; eauto using index_0.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }

  {
  eapply tr_set_intro; eauto.
    {
    unfold subst1.
    rewrite -> subst_squash.
    exact Hmb.
    }

    {
    apply tr_squash_formation1; auto.
    }
  }
Qed.


Lemma squashIntroOfSquash_valid : squashIntroOfSquash_obligation.
Proof.
prepare.
intros G a ext1 m Ha Hm.
apply (tr_eqtype_convert _ _ _ (squash (squash a))).
  {
  unfold squash at 1 3.
  rewrite -> subst_squash.
  apply tr_eqtype_symmetry.
  apply tr_squash_idem.
  fold (squash a).
  eapply tr_inhabitation_formation; eauto.
  }
unfold squash at 1.
eapply tr_set_intro; eauto.
  {
  apply tr_unittp_intro.
  }

  {
  simpsub.
  exact Hm.
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
  eapply tr_inhabitation_formation; eauto.
  }
Qed.


Lemma setElim_valid : setElim_obligation.
Proof.
prepare.
intros G a b c m ext1 ext0 n Hhyg Hb Hm Hn.
eapply tr_set_elim2; eauto.
so (subst_into_absent_single _ 0 n triv Hhyg) as H.
simpsubin H.
simpsub.
rewrite -> H.
auto.
Qed.


Lemma isetElim_valid : isetElim_obligation.
Proof.
prepare.
intros G a b c m ext0 n Hhyg Hm Hn.
eapply tr_iset_elim2; eauto.
so (subst_into_absent_single _ 0 n triv Hhyg) as H.
simpsubin H.
simpsub.
rewrite -> H.
auto.
Qed.


Lemma tr_set_left :
  forall G1 G2 a b c m,
    hygiene (fun i => i <> length G2) m
    -> tr (hyp_tm a :: G1) (deqtype b b)
    -> tr (substctx sh1 G2 ++ hyp_tm b :: hyp_tm a :: G1) (deq m m (subst (under (length G2) sh1) c))
    -> tr (G2 ++ hyp_tm (set a b) :: G1)
         (deq
            (subst (under (length G2) (dot triv id)) m)
            (subst (under (length G2) (dot triv id)) m)
            c).
Proof.
intros G1 G2 a b c m Hhyg Hb Hm.
set (k := length G2) in * |- *.
apply (tr_set_elim2 _ (subst (sh (S k)) a) (subst (under 1 (sh (S k))) b) (var k)).
  {
  eapply hypothesis.
    {
    apply (index_app_right _ G2 _ 0).
    apply index_0.
    }
  simpsub.
  auto.
  }

  {
  eapply (weakening _ G2 [_]).
    {
    cbn [length unlift].
    simpsub.
    rewrite <- compose_assoc.
    rewrite -> compose_sh_unlift_ge; try omega.
    replace (S k - length G2) with 1 by omega.
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    replace (S k + 1) with (S (S k)) by omega.
    simpsub.
    rewrite <- compose_assoc.
    rewrite -> compose_sh_unlift_ge; try omega.
    replace (S k - length G2) with 1 by omega.
    simpsub.
    replace (length G2 + 1) with (S k) by omega.
    auto.
    }
  cbn [length unlift].
  simpsub.
  replace (S k + 1) with (S (S k)) by omega.
  simpsub.
  rewrite <- compose_assoc.
  rewrite -> compose_sh_unlift_ge; try omega.
  replace (S k - length G2) with 1 by omega.
  simpsub.
  cbn [List.app].
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
  rewrite -> subst_var0_sh1.
  auto.
  }

  {
  simpsub.
  replace (S k + 1) with (S (S k)) by omega.
  simpsub.
  apply (exchange_1_n _ G2 _ []).
    {
    simpsub.
    rewrite -> project_unlift_ge; try omega.
    replace (k - length G2) with 0 by omega.
    fold k.
    simpsub.
    replace (k + 0) with k by omega.
    rewrite <- compose_assoc.
    rewrite -> compose_sh_unlift_ge; try omega.
    simpsub.
    replace (S k - k + k) with (S k) by omega.
    auto.
    }
  cbn [length].
  simpsub.
  cbn [List.app].
  rewrite -> project_unlift_ge; try omega.
  replace (k - length G2) with 0 by omega.
  rewrite -> compose_sh_unlift_ge; try omega.
  fold k.
  replace (S k - k) with 1 by omega.
  rewrite -> subst_var0_sh1.
  replace (dots 0 k (sh (S k))) with (@under obj k (sh 1)).
  2:{
    rewrite -> under_dots.
    simpsub.
    reflexivity.
    }
  rewrite <- compose_under.
  simpsub.
  so (subst_into_absent_single _ k m triv Hhyg) as H.
  rewrite -> H.
  apply tr_set_hyp_weaken.
  exact Hm.
  }
Qed.


Lemma tr_iset_left :
  forall G1 G2 a b c m,
    hygiene (fun i => i <> length G2) m
    -> tr (substctx sh1 G2 ++ hyp_tm b :: hyp_tm a :: G1) (deq m m (subst (under (length G2) sh1) c))
    -> tr (G2 ++ hyp_tm (iset a b) :: G1)
         (deq
            (subst (under (length G2) (dot triv id)) m)
            (subst (under (length G2) (dot triv id)) m)
            c).
Proof.
intros G1 G2 a b c m Hhyg Hm.
set (k := length G2) in * |- *.
apply (tr_iset_elim2 _ (subst (sh (S k)) a) (subst (under 1 (sh (S k))) b) (var k)).
  {
  eapply hypothesis.
    {
    apply (index_app_right _ G2 _ 0).
    apply index_0.
    }
  simpsub.
  auto.
  }

  {
  simpsub.
  replace (S k + 1) with (S (S k)) by omega.
  simpsub.
  apply (exchange_1_n _ G2 _ []).
    {
    simpsub.
    rewrite -> project_unlift_ge; try omega.
    replace (k - length G2) with 0 by omega.
    fold k.
    simpsub.
    replace (k + 0) with k by omega.
    rewrite <- compose_assoc.
    rewrite -> compose_sh_unlift_ge; try omega.
    simpsub.
    replace (S k - k + k) with (S k) by omega.
    auto.
    }
  cbn [length].
  simpsub.
  cbn [List.app].
  rewrite -> project_unlift_ge; try omega.
  replace (k - length G2) with 0 by omega.
  rewrite -> compose_sh_unlift_ge; try omega.
  fold k.
  replace (S k - k) with 1 by omega.
  rewrite -> subst_var0_sh1.
  replace (dots 0 k (sh (S k))) with (@under obj k (sh 1)).
  2:{
    rewrite -> under_dots.
    simpsub.
    reflexivity.
    }
  rewrite <- compose_under.
  simpsub.
  so (subst_into_absent_single _ k m triv Hhyg) as H.
  rewrite -> H.
  apply tr_iset_hyp_weaken.
  exact Hm.
  }
Qed.


Lemma isetIntroOfSquash_valid : isetIntroOfSquash_obligation.
Proof.
prepare.
intros G a b m ext2 ext1 ext0 Hb Hm Hmb.
apply (tr_assert _ (squash (subst1 m b)) ext0).
  {
  simpsubin Hmb.
  exact Hmb.
  }
replace (substj sh1 (deq m m (iset a b))) with (deq (subst (under 0 (dot triv id)) (subst (sh 2) m)) (subst (under 0 (dot triv id)) (subst (sh 2) m)) (subst sh1 (iset a b))).
2:{
  simpsub.
  auto.
  }
apply (tr_set_left _ []).
  {
  cbn.
  eapply hygiene_shift'.
  apply (hygiene_weaken _ okay); auto using hygiene_okay.
  intros j Hj.
  omega.
  }

  {
  simpsub.
  eapply (weakening _ [_] []).
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
  apply (tr_generalize _ a m (deqtype b b)); auto.
  }

  {
  simpsub.
  cbn [List.app].
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
  cbn [unlift length].
  simpsub.
  cbn [List.app].
  eapply (tr_iset_intro _#5 (var 0)).
    {
    eapply (weakening _ [_] []).
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
    exact Hm.
    }

    {
    simpsub.
    eapply hypothesis; eauto using index_0.
    simpsub.
    auto.
    }

    {
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
    cbn [unlift length].
    simpsub.
    cbn [List.app].
    rewrite -> subst_var0_sh1.
    exact Hb.
    }
  }
Qed.


Lemma setLeft_valid : setLeft_obligation.
Proof.
prepare.
intros G1 G2 a b c ext0 m Hhyg Hb Hm.
apply tr_set_left; auto.
Qed.


Lemma isetLeft_valid : isetLeft_obligation.
Proof.
prepare.
intros G1 G2 a b c m Hhyg Hm.
apply tr_iset_left; auto.
Qed.


Lemma setSquash_valid : setSquash_obligation.
Proof.
prepare.
intros G a b ext0 H.
apply tr_squash_idem; auto.
Qed.


Lemma setFormInv_valid : setFormInv_obligation.
Proof.
prepare.
intros G a b ext0 H.
eapply tr_set_formation_invert; eauto.
Qed.


Lemma isetFormInv1_valid : isetFormInv1_obligation.
Proof.
prepare.
intros G a b ext0 H.
eapply tr_iset_formation_invert1; eauto.
Qed.


Lemma isetFormInv2_valid : isetFormInv2_obligation.
Proof.
prepare.
intros G a b m ext0 ext1 Hsig Hm.
simpsub.
cut (tr (hyp_tm a :: G) (deqtype b b)).
  {
  intro Hb.
  so (tr_generalize _#4 Hm Hb) as H.
  simpsubin H.
  exact H.
  }
eapply tr_iset_formation_invert2; eauto.
Qed.


Lemma setSubElim_valid : setSubElim_obligation.
Proof.
prepare.
intros G a c b ext1 ext0 Hac Hb.
apply tr_subtype_intro.
  {
  apply (tr_set_formation _#5 (var 0) (var 0)); auto.
    {
    eapply tr_subtype_istype1; eauto.
    }

    {
    eapply hypothesis; eauto using index_0.
    }

    {
    eapply hypothesis; eauto using index_0.
    }
  }

  {
  eapply tr_subtype_istype2; eauto.
  }

  {
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
    exact Hac.
    }

    {
    eapply tr_set_elim1.
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }
  }
Qed.


Lemma isetSubElim_valid : isetSubElim_obligation.
Proof.
prepare.
intros G a c b ext1 ext0 Hac Hb.
apply tr_subtype_intro.
  {
  apply tr_iset_formation; eauto.
    {
    eapply tr_subtype_istype1; eauto.
    }
  }

  {
  eapply tr_subtype_istype2; eauto.
  }

  {
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
    exact Hac.
    }

    {
    eapply tr_iset_elim1.
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }
  }
Qed.
