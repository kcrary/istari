
Require Import Coq.Lists.List.
Import ListNotations.

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
Require Import Shut.

Require Import Subsumption.
Require Import SoundHyp.
Require Import Equivalence.
Require Import MapTerm.


Lemma sound_symmetry :
  forall G m n a,
    pseq G (deq m n a)
    -> pseq G (deq n m a).
Proof.
intros G m n a.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (A & Hal & Har & Hm & Hn & Hmn).
exists A.
do2 4 split; auto.
eapply urel_zigzag; eauto.
Qed.


Lemma sound_transitivity :
  forall G m n p a,
    pseq G (deq m n a)
    -> pseq G (deq n p a)
    -> pseq G (deq m p a).
Proof.
intros G m n p a.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqmn Hseqnp.
rewrite -> seq_deq in Hseqmn, Hseqnp |- *.
intros i s s' Hs.
so (Hseqmn _#3 Hs) as (A & Hal & Har & Hm & Hn & Hmn).
so (Hseqnp _#3 Hs) as (A' & Hal' & _ & _ & Hp & Hnp).
so (basic_fun _#7 Hal Hal'); subst A'.
exists A.
do2 4 split; auto.
apply (urel_zigzag _#4 (subst s' n) (subst s n)); auto.
Qed.


Lemma index_promote :
  forall object i (G : @context object) h,
    index i G h
    -> index i (promote G) (promote_hyp h).
Proof.
intros object i G h Hindex.
induct Hindex; intros; cbn; eauto using index_0, index_S.
Qed.


Lemma index_qpromote :
  forall object i b (G : @context object) h,
    index i G h
    -> index i (qpromote b G) (qpromote_hyp b h).
Proof.
intros object i b G h H.
destruct b; auto.
apply index_promote; auto.
Qed.


Lemma qpromote_skipn :
  forall object b i (G : @context object),
    qpromote b (skipn i G) = skipn i (qpromote b G).
Proof.
intros object b i G.
revert G.
induct i; auto.
(* S *)
intros i IH G.
destruct G as [| h G].
  {
  rewrite -> !qpromote_nil.
  reflexivity.
  }

  {
  rewrite -> qpromote_cons.
  apply IH.
  }
Qed.


Lemma seqctx_tail :
  forall i s s' G j,
    seqctx i s s' G
    -> seqctx i (compose (sh j) s) (compose (sh j) s') (skipn j G).
Proof.
intros i s s' G j Hs.
revert j.
induct Hs.

(* nil *)
{
intros n j.
simpsub.
cbn.
replace (@skipn (@hyp (Candidate.obj Page.stop)) j nil) with (@nil shyp).
2:{
  destruct j; auto.
  }
apply seqctx_nil.
}

(* cons *)
{
intros m p s s' h G Hs IH Hh j.
destruct j as [| j].
  {
  simpsub.
  cbn [skipn].
  apply seqctx_cons; auto.
  }

  {
  simpsub.
  cbn [skipn].
  apply IH.
  }
}
Qed.


Lemma pwctx_index :
  forall i s s' G k h,
    pwctx i s s' G
    -> index k G h
    -> (forall j b u,
          smaller j i b
          -> seqctx j (compose (sh (S k)) s) u (qpromote b (skipn (S k) G))
          -> relhyp j false (substh (compose (sh (S k)) s') (qpromote_hyp b h)) (substh u (qpromote_hyp b h)))
       /\
       (forall j b u,
          smaller j i b
          -> seqctx j u (compose (sh (S k)) s') (qpromote b (skipn (S k) G))
          -> relhyp j true (substh (compose (sh (S k)) s) (qpromote_hyp b h)) (substh u (qpromote_hyp b h))).
Proof.
intros i s s' G k h Hs Hindex.
revert s s' Hs.
induct Hindex.

(* 0 *)
{
intros h G ss ss' Hss.
invertc Hss.
intros m p s s' _ _ Hleft Hright <- <-.
auto.
}

(* S *)
{
intros k h' G h _ IH ss ss' Hss.
invertc Hss.
intros m p s s' Hs _ _ _ <- <-.
apply IH; auto.
}
Qed.


Lemma sound_weakening :
  forall G1 G2 h J,
    pseq (G2 ++ G1) J
    -> pseq (substctx sh1 G2 ++ cons h G1) (substj (under (length G2) sh1) J).
Proof.
intros G1 G2 h J.
revert G1.
refine (seq_pseq_hyp 0 1 [] _ _ _ [_] _ _); cbn.
intros G Hseq _.
eapply usubsume_seq; eauto.
apply usubsume_under.
split.
  {
  intros i.
  split.
    {
    intro Hi.
    simpsub.
    cbn.
    apply hygiene_var; auto.
    }

    {
    intro Hi.
    simpsubin Hi.
    cbn in Hi.
    invertc Hi; auto.
    }
  }
intros i ss ss' Hss.
invertc Hss.
intros m p s s' Hs Hmp Hleft Hright <- <-.
so (seqhyp_impl_closed _#5 Hmp) as (Hclm & Hclp).
do2 2 split.
  {
  simpsub; auto.
  }

  {
  intros j b u Hsmall Hu.
  exists (dot p id).
  split.
    {
    simpsub.
    rewrite -> subst_into_closed; auto.
    rewrite -> qpromote_cons.
    apply seqctx_cons; auto.
    simpsubin Hu.
    so (seqhyp_smaller _#7 Hsmall Hmp) as Hmp'.
    rewrite <- !substh_qpromote_hyp in Hmp'.
    eapply seqhyp_relhyp_2; eauto.
    }

    {
    simpsub.
    apply equivsub_refl.
    }
  }

  {
  intros j b u Hsmall Hu.
  exists (dot m id).
  split.
    {
    simpsub.
    rewrite -> subst_into_closed; auto.
    rewrite -> qpromote_cons.
    apply seqctx_cons; auto.
    simpsubin Hu.
    so (seqhyp_smaller _#7 Hsmall Hmp) as Hmp'.
    rewrite <- !substh_qpromote_hyp in Hmp'.
    eapply seqhyp_relhyp_1; eauto.
    }

    {
    simpsub.
    apply equivsub_refl.
    }
  }
Qed.


Lemma sound_contraction_main :
  forall G h i,
    index i G h
    -> subsume G (substh (sh (S i)) h :: G) (dot (var i) id) sh1.
Proof.
intros G1 h k Hindex.
do2 2 split.
  {
  cbn.
  intro j.
  simpsub.
  split.
    {
    intro H; apply hygiene_var; auto.
    }

    {
    intro H.
    invert H; auto.
    }
  }
  
  {
  cbn.
  intros j.
  destruct j as [| j].
    {
    simpsub.
    cbn.
    split; auto.
    intros _.
    apply hygiene_var.
    rewrite -> ctxpred_length.
    eapply index_length; eauto.
    }

    {
    simpsub.
    cbn.
    split.
      {
      intro H; apply hygiene_var; auto.
      }

      {
      intro H; invert H; auto.
      }
    }
  }
intros i s s' Hs.
do2 4 split.
  {
  simpsub.
  so (seqctx_index _#6 (pwctx_impl_seqctx _#4 Hs) Hindex) as Hk.
  so (pwctx_index _#6 Hs Hindex) as (Hleft & Hright).
  apply pwctx_cons; auto.
    {
    simpsub.
    exact Hk.
    }

    {
    intros j b' u Hsmall Hu.
    rewrite <- !substh_qpromote_hyp.
    simpsub.
    apply Hleft; auto.
    rewrite -> qpromote_skipn.
    eapply seqctx_tail; eauto.
    }

    {
    intros j b' u Hsmall Hu.
    rewrite <- !substh_qpromote_hyp.
    simpsub.
    apply Hright; auto.
    rewrite -> qpromote_skipn.
    eapply seqctx_tail; eauto.
    }
  }

  {
  simpsub.
  apply equivsub_refl.
  }

  {
  simpsub.
  apply equivsub_refl.
  }

  {
  intros j b' uu Hsmall Huu.
  simpsubin Huu.
  rewrite -> qpromote_cons in Huu.
  invertc Huu.
  intros q u Hu Hq <-.
  simpsub.
  auto.
  }

  {
  intros j b' uu Hsmall Huu.
  simpsubin Huu.
  rewrite -> qpromote_cons in Huu.
  invertc Huu.
  intros q u Hu Hq <-.
  simpsub.
  auto.
  }
Qed.


Lemma sound_contraction_pre :
  forall G1 G2 h i m m' a,
    index i G1 h
    -> hygiene (ctxpred (G2 ++ G1)) a
    -> seq (substctx sh1 G2 ++ substh (sh (S i)) h :: G1) (deq m m' (subst (under (length G2) sh1) a))
    -> seq (G2 ++ G1) (deq (subst (under (length G2) (dot (var i) id)) m) (subst (under (length G2) (dot (var i) id)) m') a).
Proof.
intros G1 G2 h i m n a Hindex Hcla Hseq.
eapply subsume_seq_extract; eauto; clear Hseq.
apply subsume_under.
apply sound_contraction_main; auto.
Qed.


Lemma sound_contraction :
  forall G1 G2 h i m m' a,
    index i G1 h
    -> pseq (substctx sh1 G2 ++ substh (sh (S i)) h :: G1) (deq m m' (subst (under (length G2) sh1) a))
    -> pseq (G2 ++ G1) (deq (subst (under (length G2) (dot (var i) id)) m) (subst (under (length G2) (dot (var i) id)) m') a).
Proof.
intros G1 G2 h k m n a Hindex (i1, Hseq).
so (shut_term _ (G2 ++ G1) a) as (i2, Hcla).
so (upper_bound_all 2 i1 i2) as (i & Hi1 & Hi2 & _).
exists i; intros j Hj.
autorewrite with canonlist.
eapply sound_contraction_pre; try (finish_pseq j).
apply index_app_left; auto.
Qed.


Lemma sound_exchange_main :
  forall G h1 h2,
    subsume (cons (substh sh1 h2) (cons h1 G)) (cons (substh sh1 h1) (cons h2 G)) (dot (var 1) (dot (var 0) (sh 2))) (dot (var 1) (dot (var 0) (sh 2))).
Proof.
intros G h1 h2.
do2 2 split.
  {
  intros j.
  rewrite -> !ctxpred_length.
  destruct j as [|[| j]].
    {
    simpsub.
    cbn.
    split; try omega.
    intros _.
    apply hygiene_var; omega.
    }

    {
    simpsub.
    cbn.
    split; try omega.
    intros _.
    apply hygiene_var; omega.
    }

    {
    simpsub.
    cbn.
    split.
      {
      intro H.
      apply hygiene_var; omega.
      }

      {
      intro H.
      invert H.
      intros; omega.
      }
    }
  }

  {
  intros j.
  rewrite -> !ctxpred_length.
  destruct j as [|[| j]].
    {
    simpsub.
    cbn.
    split; try omega.
    intros _.
    apply hygiene_var; omega.
    }

    {
    simpsub.
    cbn.
    split; try omega.
    intros _.
    apply hygiene_var; omega.
    }

    {
    simpsub.
    cbn.
    split.
      {
      intro H.
      apply hygiene_var; omega.
      }

      {
      intro H.
      invert H.
      intros; omega.
      }
    }
  }
intros i ss ss' Hss.
invertc Hss.
intros m2 p2 ss2 ss2' H Hmp2 Hleft2 Hright2 <- <-.
invertc H.
intros m1 p1 s s' Hs Hmp1 Hleft1 Hright1 <- <-.
simpsubin Hmp2.
do2 4 split.
  {
  simpsub.
  apply pwctx_cons.
    {
    apply pwctx_cons; auto.
      {
      intros j b u Hj Hu.
      exploit (Hleft2 j b (dot p1 u)) as H; auto.
        {
        rewrite -> qpromote_cons.
        apply seqctx_cons; auto.
        rewrite -> !substh_qpromote_hyp.
        eapply seqhyp_relhyp_2.
        2:{
          eapply seqhyp_smaller; eauto.
          }
        rewrite <- !substh_qpromote_hyp.
        apply Hleft1; auto.
        }
      rewrite <- substh_qpromote_hyp in H.
      simpsubin H.
      exact H.
      }

      {
      intros j b u Hj Hu.
      exploit (Hright2 j b (dot m1 u)) as H; auto.
        {
        rewrite -> qpromote_cons.
        apply seqctx_cons; auto.
        rewrite -> !substh_qpromote_hyp.
        eapply seqhyp_relhyp_1.
        2:{
          eapply seqhyp_smaller; eauto.
          }
        rewrite <- !substh_qpromote_hyp.
        apply Hright1; auto.
        }
      rewrite <- substh_qpromote_hyp in H.
      simpsubin H.
      exact H.
      }
    }
  
    {
    simpsub.
    auto.
    }

    {
    intros j b uu Hj Huu.
    rewrite -> qpromote_cons in Huu.
    invertc Huu.
    intros q u Hu Hm2q <-.
    rewrite <- substh_qpromote_hyp.
    simpsub.
    apply Hleft1; auto.
    }

    {
    intros j b uu Hj Huu.
    rewrite -> qpromote_cons in Huu.
    invertc Huu.
    intros q u Hu Hm2q <-.
    rewrite <- substh_qpromote_hyp.
    simpsub.
    apply Hright1; auto.
    }
  }

  {
  simpsub.
  apply equivsub_refl.
  }

  {
  simpsub.
  apply equivsub_refl.
  }

  {
  intros j b uu Hj Huu.
  rewrite -> !qpromote_cons in Huu |- *.
  simpsubin Huu.
  invertc Huu.
  intros q1 u2 H Hmq1 <-.
  invertc H.
  intros q2 u Hu Hmq2 <-.
  simpsub.
  apply seqctx_cons.
    {
    apply seqctx_cons; auto.
      {
      rewrite <- substh_qpromote_hyp in Hmq1.
      simpsubin Hmq1.
      auto.
      }
    }
  
    {
    rewrite <- substh_qpromote_hyp .
    simpsub.
    auto.
    }
  }

  {
  intros j b uu Hj Huu.
  rewrite -> !qpromote_cons in Huu |- *.
  simpsubin Huu.
  invertc Huu.
  intros q1 u2 H Hmq1 <-.
  invertc H.
  intros q2 u Hu Hmq2 <-.
  simpsub.
  apply seqctx_cons.
    {
    apply seqctx_cons; auto.
      {
      rewrite <- substh_qpromote_hyp in Hmq1.
      simpsubin Hmq1.
      auto.
      }
    }
  
    {
    rewrite <- substh_qpromote_hyp .
    simpsub.
    auto.
    }
  }
Qed.
   

Lemma sound_exchange :
  forall G1 G2 h1 h2 m m' a,
    pseq (substctx (dot (var 1) (dot (var 0) (sh 2))) G2 ++ substh sh1 h1 :: h2 :: G1) (deq m m' (subst (under (length G2) (dot (var 1) (dot (var 0) (sh 2)))) a))
    -> pseq (G2 ++ substh sh1 h2 :: h1 :: G1) (deq (subst (under (length G2) (dot (var 1) (dot (var 0) (sh 2)))) m) (subst (under (length G2) (dot (var 1) (dot (var 0) (sh 2)))) m') a).
Proof.
intros G1 G2 h1 h2 m m' a.
revert G1.
refine (seq_pseq_hyp 1 (G2 ++ [substh sh1 h2; h1]) a 1 _ [_; _] _ _ [_; _] _ _); cbn.
intros G1 Hcla Hseq _.
autorewrite with canonlist in Hcla.
eapply subsume_seq_extract; eauto.
apply subsume_under.
apply sound_exchange_main; auto.
Qed.


Lemma sound_exchange' :
  forall G1 G2 h1 h2 m n a,
    pseq (substctx (dot (var 1) (dot (var 0) (sh 2))) G2 ++ substh sh1 h1 :: h2 :: G1) 
      (deq
         (subst (under (length G2) (dot (var 1) (dot (var 0) (sh 2)))) m)
         (subst (under (length G2) (dot (var 1) (dot (var 0) (sh 2)))) n)
         (subst (under (length G2) (dot (var 1) (dot (var 0) (sh 2)))) a))
    -> pseq (G2 ++ substh sh1 h2 :: h1 :: G1) (deq m n a).
Proof.
intros G1 G2 h1 h2 m n a Hseq.
assert (forall (x : @term (Candidate.obj Page.stop)),
          subst (under (length G2) (dot (var 1) (dot (var 0) (sh 2))))
            (subst (under (length G2) (dot (var 1) (dot (var 0) (sh 2)))) x)
            = x) as Heq.
  {
  intro x.
  simpsub.
  rewrite <- compose_under.
  simpsub.
  rewrite -> (subst_eqsub _ _ id); auto using subst_id.
  eapply eqsub_trans.
  2:{
    apply eqsub_under_id.
    }
  apply eqsub_under.
  apply eqsub_symm.
  eapply eqsub_trans.
    {
    apply eqsub_expand_sh.
    }
  apply eqsub_dotv.
  apply eqsub_expand_sh.
  }
so (sound_exchange _#7 Hseq) as Hseq'.
force_exact Hseq'.
clear Hseq Hseq'.
f_equal.
f_equal; auto.
Qed.


Lemma cons_is_append :
  forall A (x : A) l,
    x :: l = (x :: nil) ++ l.
Proof.
intros A x l.
reflexivity.
Qed.


Lemma sound_exchange_multi :
  forall G1 G2 h G3 m n a,
    pseq 
      (substctx (dot (var (length G2)) (under (length G2) sh1)) G3
         ++ substctx sh1 G2 ++ h :: G1) 
      (deq
         (subst (under (length G3) (dot (var (length G2)) (under (length G2) sh1))) m)
         (subst (under (length G3) (dot (var (length G2)) (under (length G2) sh1))) n)
         (subst (under (length G3) (dot (var (length G2)) (under (length G2) sh1))) a))
    -> pseq (G3 ++ substh (sh (length G2)) h :: G2 ++ G1) (deq m n a).
Proof.
intros G1 G2 h G3 m n a Hseq.
revert G3 m n a Hseq.
induct G2.

(* nil *)
{
intros G3 m n a Hseq.
cbn.
cbn in Hseq.
rewrite -> substh_id.
force_exact Hseq.
assert (forall (x : @term (Candidate.obj Page.stop)),
          subst (under (length G3) (dot (var 0) (sh 1))) x = x) as Heq.
  {
  intros x.
  replace x with (subst (under (length G3) id) x).
  2:{
    simpsub.
    auto.
    }
  rewrite <- subst_compose.
  apply subst_eqsub.
  rewrite <- compose_under.
  apply eqsub_under.
  simpsub.
  apply eqsub_symm.
  apply eqsub_expand_id.
  }
f_equal.
  {
  f_equal.
  setoid_rewrite <- substctx_id at 3.
  apply substctx_eqsub.
  apply eqsub_symm.
  apply eqsub_expand_id.
  }
f_equal; auto.
}

(* cons *)
{
intros h2 G2 IH G3 m n a Hseq.
cbn.
replace (S (length G2)) with (length G2 + 1) by omega.
rewrite <- (compose_sh_sh _ (length G2) 1).
rewrite -> substh_compose.
apply sound_exchange'.
rewrite -> cons_is_append.
rewrite -> app_assoc.
apply IH; clear IH.
force_exact Hseq; clear Hseq.
f_equal.
  {
  cbn.
  rewrite -> substctx_append.
  cbn [length].
  rewrite <- substctx_compose.
  rewrite <- app_assoc.
  cbn [substctx List.app].
  f_equal.
    {
    simpsub.
    reflexivity.
    }
  f_equal.
  cbn.
  simpsub.
  reflexivity.
  }
f_equal.
  {
  simpsub.
  rewrite -> app_length.
  rewrite -> length_substctx.
  cbn [length].
  rewrite <- under_sum.
  rewrite <- compose_under.
  simpsub.
  reflexivity.
  }

  {
  simpsub.
  rewrite -> app_length.
  rewrite -> length_substctx.
  cbn [length].
  rewrite <- under_sum.
  rewrite <- compose_under.
  simpsub.
  reflexivity.
  }

  {
  simpsub.
  rewrite -> app_length.
  rewrite -> length_substctx.
  cbn [length].
  rewrite <- under_sum.
  rewrite <- compose_under.
  simpsub.
  reflexivity.
  }
}
Qed.
