
Require Import Coq.Lists.List.

Require Import Tactics.
Require Import Axioms.
Require Import Sigma.
Require Import Equality.
Require Import Sequence.
Require Import Relation.
Require Import Ordinal.
Require Import Syntax.
Require Import SimpSub.
Require Import Dynamic.
Require Import Ofe.
Require Import Uniform.
Require Import Intensional.
Require Import Candidate.
Require Import System.
Require Import Semantics.
Require Import SemanticsKnot.
Require Import Judgement.
Require Import Hygiene.
Require Import ProperClosed.
Require Import ProperFun.
Require Import ContextHygiene.
Require Import Equivalence.
Require Import ProperEquiv.
Require Import Shut.

Require Import Equivalence.
Require Import SemanticsProperty.
Require Import ProperDownward.
Require Import Truncate.


Definition subsume G G' ti t :=
  (forall j, ctxpred G j <-> hygiene (ctxpred G') (project t j))
  /\
  (forall j, ctxpred G' j <-> hygiene (ctxpred G) (project ti j))
  /\
  forall i s s',
    pwctx i s s' G
    -> pwctx i (compose ti s) (compose ti s') G'
       /\ equivsub (compose t (compose ti s)) s
       /\ equivsub (compose t (compose ti s')) s'
       /\ (forall j b u,
             smaller j i b
             -> seqctx j (compose ti s) u (qpromote b G')
             -> seqctx j s (compose t u) (qpromote b G))
       /\ (forall j b u,
             smaller j i b
             -> seqctx j u (compose ti s') (qpromote b G')
             -> seqctx j (compose t u) s' (qpromote b G)).


Definition usubsume G G' t :=
  (forall i, ctxpred G' i <-> hygiene (ctxpred G) (project t i))
  /\
  forall i s s',
    pwctx i s s' G
    -> pwctx i (compose t s) (compose t s') G'
       /\ (forall j b u,
             smaller j i b
             -> seqctx j (compose t s) u (qpromote b G')
             -> exists v,
                  seqctx j s (compose v u) (qpromote b G)
                  /\ equivsub (compose t (compose v u)) u)
       /\ (forall j b u,
             smaller j i b
             -> seqctx j u (compose t s') (qpromote b G')
             -> exists v,
                  seqctx j (compose v u) s' (qpromote b G)
                  /\ equivsub (compose t (compose v u)) u).


Lemma subsume_seq_extract :
  forall G G' ti t m m' a,
    hygiene (ctxpred G) a
    -> subsume G G' ti t
    -> seq G' (deq m m' (subst t a))
    -> seq G (deq (subst ti m) (subst ti m') a).
Proof.
intros G G' ti t m p a Hcla (_ & _ & Hsubsume) Hseq.
invertc Hseq; intro Hseq.
apply seq_i.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hsubsume _ _ _ Hs) as (Htis & Heq & Heq' & _).
so (Hseq _#3 Htis) as (A & Hal & Har & Hm & Hp & Hmp).
exists A.
do2 4 split; simpsub; auto.
  {
  simpsubin Hal.
  refine (basic_equiv _#7 _ (equiv_funct _#5 Heq (equiv_refl _ _)) Hal).
  eapply subst_closub; eauto.
  }

  {
  simpsubin Har.
  refine (basic_equiv _#7 _ (equiv_funct _#5 Heq' (equiv_refl _ _)) Har).
  eapply subst_closub; eauto.
  }
Qed.


Lemma subsume_seq :
  forall G G' ti t J,
    hygienej (ctxpred G) J
    -> subsume G G' ti t
    -> seq G' (substj t J)
    -> seq G J.
Proof.
intros G G' ti t J HclJ (_ & _ & Hsubsume) Hseq.
invertc HclJ.
intros m n a Hclm Hcln Hcla <-.
simpsubin Hseq.
invertc Hseq; intro Hseq.
apply seq_i.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hsubsume _ _ _ Hs) as (Htis & Heq & Heq' & _).
so (Hseq _#3 Htis) as (A & Hal & Har & Hm & Hp & Hmp).
exists A.
do2 4 split; simpsub.
  {
  simpsubin Hal.
  refine (basic_equiv _#7 _ (equiv_funct _#5 Heq (equiv_refl _ _)) Hal).
  eapply subst_closub; eauto.
  }

  {
  simpsubin Har.
  refine (basic_equiv _#7 _ (equiv_funct _#5 Heq' (equiv_refl _ _)) Har).
  eapply subst_closub; eauto.
  }

  {
  simpsubin Hm.
  refine (urel_equiv _#7 _ _ (equiv_funct _#5 Heq (equiv_refl _ _)) (equiv_funct _#5 Heq' (equiv_refl _ _)) Hm).
    {
    eapply subst_closub; eauto.
    }

    {
    eapply subst_closub; eauto.
    }
  }

  {
  simpsubin Hp.
  refine (urel_equiv _#7 _ _ (equiv_funct _#5 Heq (equiv_refl _ _)) (equiv_funct _#5 Heq' (equiv_refl _ _)) Hp).
    {
    eapply subst_closub; eauto.
    }

    {
    eapply subst_closub; eauto.
    }
  }

  {
  simpsubin Hmp.
  refine (urel_equiv _#7 _ _ (equiv_funct _#5 Heq (equiv_refl _ _)) (equiv_funct _#5 Heq' (equiv_refl _ _)) Hmp).
    {
    eapply subst_closub; eauto.
    }

    {
    eapply subst_closub; eauto.
    }
  }
Qed.


Lemma usubsume_seq :
  forall G G' t J,
    usubsume G G' t
    -> seq G' J
    -> seq G (substj t J).
Proof.
intros G G' t J (_ & Hsubsume) Hseq.
destruct J as [m p a].
invertc Hseq; intro Hseq.
apply seq_i.
intros i s s' Hs.
so (Hsubsume _ _ _ Hs) as (Hts & _).
cbn in Hts.
so (Hseq _#3 Hts) as (R & Hal & Har & Hm & Hp & Hmp); clear Hseq.
exists R.
do2 4 split; simpsub; auto.
Qed.


Lemma substh_equivsub :
  forall object (s s' : @sub object) h,
    equivsub s s'
    -> equivh (substh s h) (substh s' h).
Proof.
intros object s s' h Hequiv.
cases h; intros; simpsub;
[apply equivh_tpl | apply equivh_tp | apply equivh_tml | apply equivh_tm | apply equivh_emp];
auto using equiv_funct, equiv_refl.
Qed.


Lemma equivh_promote_hyp :
  forall object (h h' : @hyp object),
    equivh h h'
    -> equivh (promote_hyp h) (promote_hyp h').
Proof.
intros object h h' H.
cases H; intros; cbn;
[apply equivh_tp | apply equivh_tp | apply equivh_tm | apply equivh_tm | apply equivh_emp]; auto.
Qed.  


Lemma equivh_qpromote_hyp :
  forall object b (h h' : @hyp object),
    equivh h h'
    -> equivh (qpromote_hyp b h) (qpromote_hyp b h').
Proof.
intros object b h h' H.
cases b; auto.
apply equivh_promote_hyp; auto.
Qed.


Lemma seqhyp_equivh :
  forall i m n h1 h1' h2 h2',
    equivh h1 h1'
    -> equivh h2 h2'
    -> hygieneh clo h1'
    -> hygieneh clo h2'
    -> seqhyp i m n h1 h2
    -> seqhyp i m n h1' h2'.
Proof.
intros i m n h1 h1' h2 h2' Hequiv1 Hequiv2 Hcl1 Hcl2 Hseq.
revert Hequiv1 Hequiv2.
induct Hseq;
try (intros; invertc Hequiv1; invertc Hequiv2; intros; subst; eauto using seqhyp; done).

(* tml *)
{
intros m n a b R Ha Hb Hmn Hclm Hcln _ _ Hequiv1 Hequiv2.
invertc Hequiv1.
intros a' Hequiva <-.
invertc Hequiv2.
intros b' Hequivb <-.
invertc Hcl1.
intros Hcla'.
invertc Hcl2.
intros Hclb'.
cbn in Hcla', Hclb'.
eapply seqhyp_tml; eauto.
  {
  intro Hpos.
  eapply basic_equiv; eauto.
  apply Ha; auto.
  }

  {
  intro Hpos.
  eapply basic_equiv; eauto.
  apply Hb; auto.
  }
}

(* tm *)
{
intros m n a b R Ha Hb Hmn Hequiv1 Hequiv2.
invertc Hequiv1.
intros a' Hequiva <-.
invertc Hequiv2.
intros b' Hequivb <-.
invertc Hcl1.
intros Hcla'.
invertc Hcl2.
intros Hclb'.
cbn in Hcla', Hclb'.
eapply seqhyp_tm; eauto; eapply basic_equiv; eauto.
}
Qed.


Lemma seqhyp_equivh_1 :
  forall i m n h1 h1' h2,
    equivh h1 h1'
    -> hygieneh clo h1'
    -> seqhyp i m n h1 h2
    -> seqhyp i m n h1' h2.
Proof.
intros i m n h1 h1' h2 H1 Hcl1 Hh.
eapply seqhyp_equivh; eauto using equivh_refl.
exact (seqhyp_impl_hygieneh _#5 Hh ander).
Qed.


Lemma seqhyp_equivh_2 :
  forall i m n h1 h2 h2',
    equivh h2 h2'
    -> hygieneh clo h2'
    -> seqhyp i m n h1 h2
    -> seqhyp i m n h1 h2'.
Proof.
intros i m n h1 h2 h2' H2 Hcl2 Hh.
eapply seqhyp_equivh; eauto using equivh_refl.
exact (seqhyp_impl_hygieneh _#5 Hh andel).
Qed.


Lemma relhyp_equiv_1 :
  forall i b h1 h1' h2,
    equivh h1 h1'
    -> hygieneh clo h1'
    -> relhyp i b h1 h2
    -> relhyp i b h1' h2.
Proof.
intros i d h1 h1' h2 Hequiv Hhyg H.
revert Hequiv Hhyg.
cases H;
try (intros; invertc Hequiv; intros; subst; eauto using relhyp; done).

(* tml *)
{
intros a b R Ha Hb _ Hclb Hequiv Hhyg.
invertc Hequiv.
intros c Hequiv <-.
invertc Hhyg.
intros Hclc.
apply (relhyp_tml _#4 R); auto.
intro Hpos.
so (Ha Hpos) as H.
eapply basic_equiv; eauto.
}

(* tm *)
{
intros a b R Ha Hb Hequiv Hhyg.
invertc Hequiv.
intros c Hequiv <-.
invertc Hhyg.
intros Hclc.
apply (relhyp_tm _#4 R); auto.
eapply basic_equiv; eauto.
}
Qed.
    

Lemma relhyp_equiv_2 :
  forall i b h1 h2 h2',
    equivh h2 h2'
    -> hygieneh clo h2'
    -> relhyp i b h1 h2
    -> relhyp i b h1 h2'.
Proof.
intros i b h1 h2 h2' Hequiv Hhug Hrelhyp.
apply relhyp_symm.
eapply relhyp_equiv_1; eauto.
apply relhyp_symm; auto.
Qed.


Lemma subsume_hygiene :
  forall G G' ti t,
    subsume G G' ti t
    -> forall h,
         hygieneh (ctxpred G) h
         -> hygieneh (ctxpred G) (substh (compose t ti) h).
Proof.
intros G G' ti t Hsubsume h Hhyg.
destruct Hsubsume as (Hhygt & Hhygti & _).
eapply hygieneh_subst; eauto.
intros i Hi.
simpsub.
rewrite -> Hhygt in Hi.
eapply hygiene_subst; eauto.
intros.
apply Hhygti; auto.
Qed.


Lemma seqctx_trunc :
  forall i s s' G,
    seqctx i s s' G
    -> exists j,
         trunc (length G) s = sh j
         /\ trunc (length G) s' = sh j.
Proof.
intros i s s' G H.
induct H.

(* nil *)
{
intros n.
exists n.
auto.
}

(* cons *)
{
intros m m' s s' h G _ IH _.
destruct IH as (j & H1 & H2).
exists j.
auto.
}
Qed.


Lemma seqctx_hygiene :
  forall i s s' G,
    seqctx i s s' G
    -> (forall j, hygiene clo (project s j) <-> ctxpred G j)
       /\
       (forall j, hygiene clo (project s' j) <-> ctxpred G j).
Proof.
intros i s s' G Hs.
so (seqctx_trunc _#4 Hs) as (j & Heq & Heq').
so (seqctx_impl_closub _#4 Hs) as (Hcls & Hcls').
split.
  {
  intro k; split.
    {
    intro Hcl.
    rewrite -> ctxpred_length.
    so (le_lt_dec (length G) k) as [Hle | Hlt]; auto.
    exfalso.
    replace k with ((k - length G) + length G) in Hcl by omega.
    unfold project in Hcl.
    rewrite <- trunc_sum in Hcl.
    rewrite -> Heq in Hcl.
    set (l := k - length G) in Hcl.
    destruct l; cbn in Hcl; invert Hcl; intro H; destruct H.
    }

    {
    intro Hk.
    replace (project s k) with (subst s (var k)) by (simpsub; reflexivity).
    eapply subst_closub; eauto.
    apply hygiene_var; auto.
    }
  }

  {
  intro k; split.
    {
    intro Hcl.
    rewrite -> ctxpred_length.
    so (le_lt_dec (length G) k) as [Hle | Hlt]; auto.
    exfalso.
    replace k with ((k - length G) + length G) in Hcl by omega.
    unfold project in Hcl.
    rewrite <- trunc_sum in Hcl.
    rewrite -> Heq' in Hcl.
    set (l := k - length G) in Hcl.
    destruct l; cbn in Hcl; invert Hcl; intro H; destruct H.
    }

    {
    intro Hk.
    replace (project s' k) with (subst s' (var k)) by (simpsub; reflexivity).
    eapply subst_closub; eauto.
    apply hygiene_var; auto.
    }
  }
Qed.


Lemma seqctx_hygieneh_subst :
  forall i s s' G h,
    seqctx i s s' G
    -> (hygieneh clo (substh s h)
        <->
        hygieneh (ctxpred G) h)
       /\
       (hygieneh clo (substh s' h)
        <->
        hygieneh (ctxpred G) h).
Proof.
intros i s s' G h Hs.
so (seqctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (seqctx_hygiene _#4 Hs) as (Hleft & Hright).
split; split.
  {
  intro Hclsm.
  so (hygieneh_subst_invert _#4 Hclsm) as Hm.
  eapply hygieneh_weaken; eauto.
  intros k Hk.
  apply Hleft; auto.
  }

  {
  intros Hclm.
  eapply hygieneh_subst; eauto.
  }

  {
  intro Hclsm.
  so (hygieneh_subst_invert _#4 Hclsm) as Hm.
  eapply hygieneh_weaken; eauto.
  intros k Hk.
  apply Hright; auto.
  }

  {
  intros Hclm.
  eapply hygieneh_subst; eauto.
  }
Qed.


Lemma subsume_under1 :
  forall G G' h ti t,
    subsume G G' ti t
    -> subsume (cons h G) (cons (substh t h) G') (under 1 ti) (under 1 t).
Proof.
intros G G' h ti t Hsubsume.
so (subsume_hygiene _#4 Hsubsume) as Hhygtti.
destruct Hsubsume as (Hhygt & Hhygti & Hsubsume).
do2 2 split.
  {
  intros j.
  destruct j as [| j].
    {
    rewrite -> !ctxpred_length.
    cbn.
    split; try omega.
    intros _.
    apply hygiene_var.
    omega.
    }
  cbn [ctxpred].
  simpsub.
  rewrite <- hygiene_shift_permit_iff.
  rewrite <- Hhygt.
  cbn.
  reflexivity.
  }
  
  {
  destruct j as [| j].
    {
    cbn [ctxpred].
    simpsub.
    split.
      {
      intros _.
      apply hygiene_var; cbn; auto.
      }

      {
      cbn; auto.
      }
    }
  cbn [ctxpred].
  simpsub.
  rewrite <- hygiene_shift_permit_iff.
  rewrite <- Hhygti.
  cbn.
  reflexivity.
  }
intros i ss ss' Hss.
invertc Hss.
intros m p s s' Hs Hmp Hleft Hright <- <-.
so (Hsubsume _ _ _ Hs) as (Htis & Heq & Heq' & Hdown & Hdown').
assert (hygieneh clo (substh (compose t (compose ti s)) h)) as Hclttis.
  {
  rewrite <- compose_assoc.
  rewrite -> substh_compose.
  rewrite -> (seqctx_hygieneh_subst _#5 (pwctx_impl_seqctx _#4 Hs) andel).
  apply Hhygtti.
  rewrite <- (seqctx_hygieneh_subst _#5 (pwctx_impl_seqctx _#4 Hs) andel).
  so (seqhyp_impl_hygieneh _#5 Hmp andel) as H.
  exact H.
  }
assert (hygieneh clo (substh (compose t (compose ti s')) h)) as Hclttis'.
  {
  rewrite <- compose_assoc.
  rewrite -> substh_compose.
  rewrite -> (seqctx_hygieneh_subst _#5 (pwctx_impl_seqctx _#4 Hs) ander).
  apply Hhygtti.
  rewrite <- (seqctx_hygieneh_subst _#5 (pwctx_impl_seqctx _#4 Hs) ander).
  so (seqhyp_impl_hygieneh _#5 Hmp ander) as H.
  exact H.
  }
do2 4 split.
  {
  simpsub.
  apply pwctx_cons; auto.
    {
    eapply seqhyp_equivh; eauto.
      {
      simpsub.
      apply substh_equivsub; auto using equivsub_symm.
      }
  
      {
      simpsub.
      apply substh_equivsub; auto using equivsub_symm.
      }
  
      {
      simpsub.
      auto.
      }
  
      {
      simpsub.
      auto.
      }
    }
  
    {
    intros j b' u Hsmall Hu.
    rewrite <- !substh_qpromote_hyp.
    simpsub.
    apply (relhyp_equiv_1 _ _ (substh s' (qpromote_hyp b' h))).
      {
      apply equivh_symm.
      apply substh_equivsub; auto.
      }
    
      {
      rewrite -> !substh_qpromote_hyp.
      rewrite <- hygieneh_qpromote; auto.
      }
    apply Hleft; auto.
    }
  
    {
    intros j b' u Hsmall Hu.
    rewrite <- !substh_qpromote_hyp.
    simpsub.
    apply (relhyp_equiv_1 _ _ (substh s (qpromote_hyp b' h))).
      {
      apply equivh_symm.
      apply substh_equivsub; auto.
      }
    
      {
      rewrite -> !substh_qpromote_hyp.
      rewrite <- hygieneh_qpromote; auto.
      }
    apply Hright; auto.
    }
  }

  {
  rewrite <- compose_assoc.
  rewrite <- compose_under.
  simpsub.
  apply equivsub_dot; auto using equiv_refl.
  }

  {
  rewrite <- compose_assoc.
  rewrite <- compose_under.
  simpsub.
  apply equivsub_dot; auto using equiv_refl.
  }

  {
  intros j b' uu Hsmall Huu.
  rewrite -> qpromote_cons in Huu |- *.
  invertc Huu.
  intros q u Hu Hmq <-.
  simpsubin Hu.
  simpsubin Hmq.
  simpsub.
  apply seqctx_cons; auto.
  rewrite <- substh_qpromote_hyp in Hmq.
  simpsubin Hmq.
  eapply seqhyp_equivh_1; eauto.
    {
    apply substh_equivsub; auto.
    }

    {
    rewrite -> !substh_qpromote_hyp.
    rewrite <- hygieneh_qpromote.
    so (seqhyp_impl_hygieneh _#5 Hmp andel) as H.
    exact H.
    }
  }

  {
  intros j b' uu Hsmall Huu.
  rewrite -> qpromote_cons in Huu |- *.
  invertc Huu.
  intros q u Hu Hmq <-.
  simpsubin Hu.
  simpsubin Hmq.
  simpsub.
  apply seqctx_cons; auto.
  rewrite <- substh_qpromote_hyp in Hmq.
  simpsubin Hmq.
  eapply seqhyp_equivh_2; eauto.
    {
    apply substh_equivsub; auto.
    }

    {
    rewrite -> !substh_qpromote_hyp.
    rewrite <- hygieneh_qpromote.
    so (seqhyp_impl_hygieneh _#5 Hmp ander) as H.
    exact H.
    }
  }
Qed.


Lemma subsume_under :
  forall G1 G1' G2 ti t,
    subsume G1 G1' ti t
    -> subsume (G2 ++ G1) (substctx t G2 ++ G1') (under (length G2) ti) (under (length G2) t).
Proof.
intros G1 G1' G2.
induct G2; auto.
(* cons *)
intros h G IH ti t Hsubsume.
cbn [length List.app substctx].
simpsub.
apply subsume_under1.
apply IH; auto.
Qed.

    
Lemma usubsume_under1 :
  forall G G' h t,
    usubsume G G' t
    -> usubsume (cons (substh t h) G) (cons h G') (under 1 t).
Proof.
intros G G' h t Hsubsume.
destruct Hsubsume as (Hhygt & Hsubsume).
split.
  {
  intros i.
  destruct i as [| i].
    {
    cbn.
    split; auto.
    intros _.
    apply hygiene_var; cbn; auto.
    }
  cbn [ctxpred].
  simpsub.
  rewrite <- hygiene_shift_permit_iff.
  rewrite <- Hhygt.
  cbn.
  reflexivity.
  }
intros i ss ss' Hss.
invertc Hss.
intros m p s s' Hs Hmp Hleft Hright <- <-.
so (Hsubsume _ _ _ Hs) as (Hts & Hdown & Hdown').
do2 2 split.
  {
  simpsub.
  apply pwctx_cons; auto.
    {
    simpsubin Hmp.
    exact Hmp.
    }

    {
    intros j b u Hsmall Hu.
    so (Hdown _#3 Hsmall Hu) as (v & Hvu & Heq).
    so (Hleft _#3 Hsmall Hvu) as H.
    rewrite <- !substh_qpromote_hyp in H.
    simpsubin H.
    eapply relhyp_equiv_2; eauto; clear H.
      {
      apply substh_equivsub; auto.
      }

      {
      so (seqhyp_impl_hygieneh _#5 Hmp) as (Htsh & _).
      rewrite -> !substh_qpromote_hyp.
      rewrite <- !hygieneh_qpromote.
      simpsubin Htsh.
      so (seqctx_hygieneh_subst _#4 h (seqctx_qdemote _#5 Hu)) as (Hhygts & Hhygu).
      rewrite -> Hhygu.
      rewrite <- Hhygts.
      exact Htsh.
      }
    }

    {
    intros j b' u Hsmall Hu.
    so (Hdown' _#3 Hsmall Hu) as (v & Hvu & Heq).
    so (Hright _#3 Hsmall Hvu) as H.
    rewrite <- !substh_qpromote_hyp in H.
    simpsubin H.
    eapply relhyp_equiv_2; eauto.
      {
      apply substh_equivsub; auto.
      }

      {
      so (seqhyp_impl_hygieneh _#5 Hmp) as (_ & Htsh).
      rewrite -> !substh_qpromote_hyp.
      rewrite <- !hygieneh_qpromote.
      simpsubin Htsh.
      so (seqctx_hygieneh_subst _#4 h (seqctx_qdemote _#5 Hu)) as (Hhygu & Hhygts).
      rewrite -> Hhygu.
      rewrite <- Hhygts.
      exact Htsh.
      }
    }
  }

  {
  intros j b uu Hsmall Huu.
  simpsubin Huu.
  rewrite -> qpromote_cons in Huu.
  invertc Huu.
  intros q u Hu Hmq <-.
  so (Hdown _#3 Hsmall Hu) as (v & Hv & Heq).  
  exists (under 1 v).
  split.
    {
    simpsub.
    rewrite -> qpromote_cons.
    apply seqctx_cons; auto.
    rewrite <- !substh_qpromote_hyp.
    simpsub.
    eapply seqhyp_equivh_2; eauto.
      {
      apply substh_equivsub.
      apply equivsub_symm; auto.
      }

      {
      so (seqhyp_impl_hygieneh _#5 Hmp) as (Htsh & _).
      rewrite -> !substh_qpromote_hyp.
      rewrite <- hygieneh_qpromote.
      simpsubin Htsh.
      so (seqctx_hygieneh_subst _#4 (substh t h) (seqctx_qdemote _#5 Hv)) as (Hhygs & Hhygv).
      rewrite -> substh_compose.
      rewrite -> Hhygv.
      rewrite <- Hhygs.
      simpsub; auto.
      }
    }

    {
    simpsub.
    apply equivsub_dot; auto using equiv_refl.
    }
  }

  {
  intros j b uu Hsmall Huu.
  simpsubin Huu.
  rewrite -> qpromote_cons in Huu.
  invertc Huu.
  intros q u Hu Hmq <-.
  so (Hdown' _#3 Hsmall Hu) as (v & Hv & Heq).  
  exists (under 1 v).
  split.
    {
    simpsub.
    rewrite -> qpromote_cons.
    apply seqctx_cons; auto.
    rewrite <- !substh_qpromote_hyp.
    simpsub.
    eapply seqhyp_equivh_1; eauto.
      {
      apply substh_equivsub.
      apply equivsub_symm; auto.
      }

      {
      so (seqhyp_impl_hygieneh _#5 Hmp) as (_ & Htsh).
      rewrite -> !substh_qpromote_hyp.
      rewrite <- hygieneh_qpromote.
      simpsubin Htsh.
      so (seqctx_hygieneh_subst _#4 (substh t h) (seqctx_qdemote _#5 Hv)) as (Hhygv & Hhygs).
      rewrite -> substh_compose.
      rewrite -> Hhygv.
      rewrite <- Hhygs.
      simpsub; auto.
      }
    }

    {
    simpsub.
    apply equivsub_dot; auto using equiv_refl.
    }
  }
Qed.


Lemma usubsume_under :
  forall G1 G1' G2 t,
    usubsume G1 G1' t
    -> usubsume (substctx t G2 ++ G1) (G2 ++ G1') (under (length G2) t).
Proof.
intros G1 G1' G2.
induct G2; auto.
intros h G IH t Hsubsume.
cbn [length List.app substctx].
simpsub.
apply usubsume_under1.
apply IH; auto.  
Qed.


Local Ltac prove_hygiene :=
  repeat (first [ apply hygiene_shift_permit
                | apply hygiene_auto; cbn; repeat2 split; auto
                ]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1;
  try (apply hygiene_var; cbn; auto; done).


Lemma sound_property_eta_hyp_pre :
  forall G1 G2 a m n b,
    (forall s pg z i R,
       interp pg z i (subst s a) R
       -> exists P HP x,
            R = (property_urel P stop i HP, x))
    -> hygiene (ctxpred (G2 ++ hyp_tm a :: G1)) b
    -> seq (substctx (dot triv id) G2 ++ G1) (deq m n (subst (under (length G2) (dot triv id)) b))
    -> seq (G2 ++ hyp_tm a :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) b).
Proof.
intros G1 G2 a m n b Hprop Hclb Hseq.
eapply subsume_seq_extract; eauto.
apply subsume_under.
clear G2 m n b Hseq Hclb.
do2 2 split.
  {
  intros j.
  split.
    {
    intros Hj.
    destruct j as [| j]; simpsub; auto; try prove_hygiene.
    }

    {
    intros Hj.
    destruct j as [| j]; cbn; auto.
    cbn in Hj.
    simpsubin Hj.
    invert Hj; auto.
    }
  }

  {
  intros j.
  split.
    {
    intros Hj.
    destruct j as [| j]; simpsub; auto; try prove_hygiene.
    }

    {
    intros Hj.
    destruct j as [| j]; simpsubin Hj; invert Hj; auto.
    }
  }

  {
  intros i ss ss' Hss.
  invertc Hss.
  intros m p s s' Hs Hmp Hleft Hright <- <-.
  simpsub.
  simpsubin Hmp.
  invertc Hmp.
  intros R Hintl Hintr Hmp.
  so (Hprop _#5 Hintl) as (P & HP & x & ->).
  assert (forall j k, j <= k -> P k -> P j) as Hdown.
    {
    intros j k Hle.
    induct Hle; auto.
    }
  cbn in Hmp.
  decompose Hmp.
  intros Hsat _ Hclm Hclp Hstepsm Hstepsp.
  do2 4 split; auto.
    {
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm.
    apply steps_equiv; auto.
    }

    {
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm.
    apply steps_equiv; auto.
    }

    {
    intros j b u Hsmall Hu.
    so (smaller_impl_le _#3 Hsmall) as Hj.
    simpsub.
    rewrite -> qpromote_cons.
    rewrite -> qpromote_hyp_tm.
    apply seqctx_cons; auto.
    simpsub.
    so (Hleft j b u Hsmall Hu) as H.
    rewrite -> qpromote_hyp_tm in H.
    simpsubin H.
    invertc H.
    intros R Hintr' Hintu.
    so (basic_fun _#7 (basic_downward _#7 Hj Hintr) Hintr'); subst R.
    apply (seqhyp_tm _#5 (iutruncate (S j) (property_urel P stop i HP, x))); auto.
      {
      eapply basic_downward; eauto.
      }

      {
      split; auto.
      cbn.
      do2 5 split; auto using star_refl; try prove_hygiene.
      }
    }

    {
    intros j b u Hsmall Hu.
    so (smaller_impl_le _#3 Hsmall) as Hj.
    simpsub.
    rewrite -> qpromote_cons.
    rewrite -> qpromote_hyp_tm.
    apply seqctx_cons; auto.
    simpsub.
    so (Hright j b u Hsmall Hu) as H.
    rewrite -> qpromote_hyp_tm in H.
    simpsubin H.
    invertc H.
    intros R Hintl' Hintu.
    so (basic_fun _#7 (basic_downward _#7 Hj Hintl) Hintl'); subst R.
    apply (seqhyp_tm _#5 (iutruncate (S j) (property_urel P stop i HP, x))); auto.
      {
      eapply basic_downward; eauto.
      }

      {
      split; auto.
      cbn.
      do2 5 split; auto using star_refl; try prove_hygiene.
      }
    }
  }
Qed.


Lemma sound_property_eta_hyp :
  forall G1 G2 a m n b,
    (forall s pg z i R,
       interp pg z i (subst s a) R
       -> exists P HP x,
            R = (property_urel P stop i HP, x))
    -> pseq (substctx (dot triv id) G2 ++ G1) (deq m n (subst (under (length G2) (dot triv id)) b))
    -> pseq (G2 ++ hyp_tm a :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) b).
Proof.
intros G1 G2 a m n b Hprop (i1, Hseq).
so (shut_term _ (G2 ++ hyp_tm a :: G1) b) as (i2 & Hclb).
so (upper_bound_all 2 i1 i2) as (i & Hi1 & Hi2 & _).
exists i; intros j Hj.
rewrite <- app_assoc.
rewrite <- app_comm_cons.
apply sound_property_eta_hyp_pre; auto.
  {
  rewrite -> app_comm_cons.
  rewrite -> app_assoc.
  eauto using le_trans.
  }

  {
  rewrite -> app_assoc.
  eauto using le_trans.
  }
Qed.
