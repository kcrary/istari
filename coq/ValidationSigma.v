
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

Require Import ValidationUtil.


Lemma tr_sigma_sub :
  forall G a a' b b',
    tr G (dsubtype a a')
    -> tr (hyp_tm a :: G) (dsubtype b b')
    -> tr (hyp_tm a' :: G) (deqtype b' b')
    -> tr G (dsubtype (sigma a b) (sigma a' b')).
Proof.
intros G a a' b b' Ha Hb Hb'.
apply tr_subtype_intro.
  {
  apply tr_sigma_formation.
    {
    eapply tr_subtype_istype1; eauto.
    }

    {
    eapply tr_subtype_istype1; eauto.
    }
  }

  {
  apply tr_sigma_formation; auto.
  eapply tr_subtype_istype2; eauto.
  }
simpsub.
cbn [Nat.add].
eapply tr_sigma_ext.
  {
  apply (tr_subtype_elim _ (subst sh1 a)).
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
    exact Ha.
    }
  eapply tr_sigma_elim1.
  eapply hypothesis; eauto using index_0.
  simpsub.
  cbn [Nat.add].
  eauto.
  }

  {
  simpsub.
  apply (tr_subtype_elim _ (subst (dot (ppi1 (var 0)) sh1) b)).
    {
    match goal with
    | |- tr _ ?X =>
       replace X with
       (substj (dot (ppi1 (var 0)) id)
          (deq triv triv (subtype
                            (subst (dot (var 0) (sh 2)) b)
                            (subst (dot (var 0) (sh 2)) b'))))
    end.
    2:{
      simpsub.
      auto.
      }
    apply (tr_generalize _ (subst sh1 a)).
      {
      eapply tr_sigma_elim1.
      eapply hypothesis; eauto using index_0.
      simpsub.
      eauto.
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
      rewrite -> !subst_var0_sh1.
      exact Hb.
      }
    }

    {
    eapply tr_sigma_elim2'.
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      cbn [Nat.add].
      eauto.
      }
    simpsub.
    auto.
    }
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
  exact Hb'.
  }

  {
  eapply hypothesis; eauto using index_0.
  simpsub.
  eauto.
  }

  {
  eapply hypothesis; eauto using index_0.
  simpsub.
  eauto.
  }
Qed.
