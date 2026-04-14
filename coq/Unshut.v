
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Tactics.
Require Import Sequence.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.
Require Import Hygiene.
Require Import ContextHygiene.
Require Import System.
Require Import Judgement.

Require Import Shut.
Require Import Subsumption.
Require Import Equivalence.
Require Import Dots.
Require SoundSubstitution.
Require SoundStructural.
Require SoundSimple.


Lemma unshut_one :
  forall G J,
    hygienectx clo G
    -> hygienej (ctxpred G) J
    -> seq (G ++ [hyp_tm unittp]) J
    -> seq G J.
Proof.
intros G J HclG HclJ Hseq.
replace J with (substj (dot triv id) (substj sh1 J)) by (simpsub; reflexivity).
apply (SoundSubstitution.sound_generalize_pre _ unittp).
  {
  apply SoundSimple.sound_unittp_intro_pre.
  }
apply (subsume_seq _ (G ++ [hyp_tm unittp])
         (dots 1 (length G) (dot (var 0) (sh (S (length G)))))
         (dot (var (length G)) (under (length G) sh1))).
  {
  eapply hygienej_subst; eauto.
  intros j Hj.
  cbn in Hj.
  rewrite -> ctxpred_length.
  cbn.
  unfold sh1.
  rewrite -> project_sh.
  unfold varx.
  apply hygiene_var.
  rewrite -> ctxpred_length in Hj.
  omega.
  }

2:{
  rewrite <- substj_compose.
  simpsub.
  erewrite -> substj_into_absent; eauto.
  intros j Hj.
  rewrite -> ctxpred_length in Hj.
  rewrite -> project_under_lt; auto.
  }
clear J HclJ Hseq.
induct HclG.
  {
  cbn.
  cut (subsume [hyp_tm unittp] [hyp_tm unittp] (dot (var 0) (compose id (sh 1))) (dot (var 0) (compose id (sh 1)))).
    {
    simpsub.
    auto.
    }
  apply subsume_under1.
  do2 2 split.
    {
    intro j.
    simpsub.
    split; intro H.
      {
      apply hygiene_var; auto.
      }

      {
      invert H; auto.
      }
    }

    {
    intro j.
    simpsub.
    split; intro H.
      {
      apply hygiene_var; auto.
      }

      {
      invert H; auto.
      }
    }
  intros i s s' Hs.
  simpsub; auto using equivsub_refl.
  }

  {
  intros h G _ IH Hclh.
  cbn [length].
  so (subsume_under1 _ _ (substh sh1 h) _ _ IH) as Hsubsume2.
  so (SoundStructural.sound_exchange_main G h (hyp_tm unittp)) as Hsubsume1.
  simpsubin Hsubsume1.
  so (subsume_compose _#7 Hsubsume1 Hsubsume2) as Hsubsume.
  simpsubin Hsubsume.
  erewrite -> substh_into_absent in Hsubsume; eauto.
  2:{
    intros j Hj.
    cbn in Hj.
    destruct Hj as [Hj | (Hj & Hcl)].
      {
      rewrite -> project_under_lt; auto.
      }

      {
      unfold clo in Hcl.
      destruct Hcl.
      }
    }
  rewrite <- app_comm_cons.
  force_exact Hsubsume.
  f_equal.
  rewrite -> dots_succ.
  f_equal.
  rewrite -> !dots_dotsgen.
  rewrite -> compose_dotsgen.
  apply dotsgen_equal; auto.
    {
    intros j Hj.
    simpsub.
    reflexivity.
    }

    {
    simpsub.
    f_equal.
    f_equal.
    omega.
    }
  }
Qed.


Lemma unshut :
  forall G J n,
    hygienectx clo G
    -> hygienej (ctxpred G) J
    -> seq (G ++ shut n) J
    -> seq G J.
Proof.
intros G J n HclG HclJ.
induct n.
  {
  cbn.
  rewrite -> app_nil_r.
  auto.
  }

  {
  intros n IH H.
  apply IH.
  apply unshut_one.
    {
    clear H IH.
    apply hygienectx_app.
      {
      induct n.
        {
        apply hygienectx_nil.
        }
      intros n IH.
      cbn.
      apply hygienectx_cons; auto.
      apply hygieneh_tm.
      apply hygiene_auto; cbn; trivial.
      }

      {
      eapply hygienectx_weaken; eauto.
      intros j H.
      unfold clo in H.
      destruct H.
      }
    }

    {
    eapply hygienej_weaken; eauto.
    intros j Hj.
    rewrite -> ctxpred_length in Hj |- *.
    rewrite -> app_length.
    omega.
    }

    {
    replace (S n) with (n + 1) in H by omega.
    rewrite -> shut_plus in H.
    cbn in H.
    rewrite <- app_assoc.
    exact H.
    }
  }
Qed.

  
Lemma pseq_elim_with_hygiene :
  forall G J k,
    hygienectx (fun j => j < k) G
    -> hygienej (fun j => j < k + length G) J
    -> pseq G J
    -> forall j,
         k <= j
         -> seq (G ++ shut j) J.
Proof.
intros G J k HhygG HhygJ Hseq j Hkj.
destruct Hseq as (i & Hseqif).
so (le_dec i j) as [Hle | Hnle].
  {
  apply Hseqif; auto.
  }
so (Nat.lt_le_incl _ _ (not_le _ _ Hnle)) as Hji.
so (Hseqif i (le_refl _)) as Hseq.
clear Hseqif Hnle.
replace i with (j + (i - j)) in Hseq by omega.
rewrite -> shut_plus in Hseq.
rewrite -> app_assoc in Hseq.
eapply unshut; eauto.
  {
  clear Hseq Hji.
  apply hygienectx_app.
    {
    clear Hkj.
    induct j.
      {
      apply hygienectx_nil.
      }
    intros j IH.
    cbn.
    apply hygienectx_cons; auto.
    apply hygieneh_tm.
    apply hygiene_auto; cbn; trivial.
    }

    {
    eapply hygienectx_weaken; eauto.
    intros j' H.
    left.
    rewrite -> length_shut.
    omega.
    }
  }

  {
  rewrite -> ctxpred_length.
  eapply hygienej_weaken; eauto.
  intros l H.
  rewrite -> app_length.
  rewrite -> length_shut.
  omega.
  }
Qed.
