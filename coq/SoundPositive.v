
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Axioms.
Require Import Tactics.
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
Require Import System.
Require Import Semantics.
Require Import SemanticsKnot.
Require Import Judgement.
Require Import Hygiene.
Require Import ProperClosed.
Require Import ProperFun.
Require Import Shut.
Require Import Candidate.


Require Import Promote.
Require Import Equivalence.
Require Import SemanticsPositive.
Require Import SemanticsProperty.


Lemma seq_ispositive :
  forall G a,
    hygiene (permit (ctxpred G)) a
    -> seq G (deq triv triv (ispositive a))
       <->
       (forall i s s',
          pwctx i s s' G
          -> positive 0 (subst (under 1 s) a) /\ positive 0 (subst (under 1 s') a)).
Proof.
intros G a Hcla.
split.
  {
  intro Hseq.
  rewrite -> seq_deq in Hseq.
  intros i s s' Hs.
  so (Hseq _#3 Hs) as (R & Hisrobl & Hisrobr & Hinh & _).
  simpsubin Hisrobl.
  simpsubin Hisrobr.
  invert (basic_value_inv _#6 value_ispositive Hisrobl).
  intros _ Heql.
  invert (basic_value_inv _#6 value_ispositive Hisrobr).
  intros _ Heqr.
  simpsubin Hinh.
  so Hinh as H.
  rewrite <- Heql in H.
  cbn in H.
  destruct H as (Hrobl & _).
  rename Hinh into H.
  rewrite <- Heqr in H.
  cbn in H.
  destruct H as (Hrobr & _).
  auto.
  }

  {
  intros Hpositive.
  rewrite -> seq_deq.
  intros i s s' Hs.
  so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
  so (Hpositive _#3 Hs) as (Hrobl & Hrobr).
  exists (iubase (ispositive_urel stop i (subst (under 1 s) a))).
  do2 4 split.
    {
    simpsub.
    apply interp_eval_refl.
    apply interp_ispositive.
    eapply subst_closub_under_permit; eauto.
    }

    {
    replace (ispositive_urel stop i (subst (under 1 s) a)) with (ispositive_urel stop i (subst (under 1 s') a)).
    2:{
      apply property_urel_extensionality; auto.
      intros _ _; split; auto.
      }
    simpsub.
    apply interp_eval_refl.
    apply interp_ispositive.
    eapply subst_closub_under_permit; eauto.
    }

    {
    simpsub.
    do2 5 split; auto using star_refl; try (apply hygiene_auto; cbn; auto; done).
    }

    {
    simpsub.
    do2 5 split; auto using star_refl; try (apply hygiene_auto; cbn; auto; done).
    }

    {
    simpsub.
    do2 5 split; auto using star_refl; try (apply hygiene_auto; cbn; auto; done).
    }
  }
Qed.


Lemma seq_isnegative :
  forall G a,
    hygiene (permit (ctxpred G)) a
    -> seq G (deq triv triv (isnegative a))
       <->
       (forall i s s',
          pwctx i s s' G
          -> negative 0 (subst (under 1 s) a) /\ negative 0 (subst (under 1 s') a)).
Proof.
intros G a Hcla.
split.
  {
  intro Hseq.
  rewrite -> seq_deq in Hseq.
  intros i s s' Hs.
  so (Hseq _#3 Hs) as (R & Hisrobl & Hisrobr & Hinh & _).
  simpsubin Hisrobl.
  simpsubin Hisrobr.
  invert (basic_value_inv _#6 value_isnegative Hisrobl).
  intros _ Heql.
  invert (basic_value_inv _#6 value_isnegative Hisrobr).
  intros _ Heqr.
  simpsubin Hinh.
  so Hinh as H.
  rewrite <- Heql in H.
  cbn in H.
  destruct H as (Hrobl & _).
  rename Hinh into H.
  rewrite <- Heqr in H.
  cbn in H.
  destruct H as (Hrobr & _).
  auto.
  }

  {
  intros Hnegative.
  rewrite -> seq_deq.
  intros i s s' Hs.
  so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
  so (Hnegative _#3 Hs) as (Hrobl & Hrobr).
  exists (iubase (isnegative_urel stop i (subst (under 1 s) a))).
  do2 4 split.
    {
    simpsub.
    apply interp_eval_refl.
    apply interp_isnegative.
    eapply subst_closub_under_permit; eauto.
    }

    {
    replace (isnegative_urel stop i (subst (under 1 s) a)) with (isnegative_urel stop i (subst (under 1 s') a)).
    2:{
      apply property_urel_extensionality; auto.
      intros _ _; split; auto.
      }
    simpsub.
    apply interp_eval_refl.
    apply interp_isnegative.
    eapply subst_closub_under_permit; eauto.
    }

    {
    simpsub.
    do2 5 split; auto using star_refl; try (apply hygiene_auto; cbn; auto; done).
    }

    {
    simpsub.
    do2 5 split; auto using star_refl; try (apply hygiene_auto; cbn; auto; done).
    }

    {
    simpsub.
    do2 5 split; auto using star_refl; try (apply hygiene_auto; cbn; auto; done).
    }
  }
Qed.


Lemma hpositive_hnegative_impl_positive_negative :
  forall object P N,
    Forall (positive 0) P
    -> Forall (negative 0) N
    -> (forall i (a : term object),
          hpositive P N i a
          -> positive i a)
       /\
       (forall i a,
          hnegative P N i a
          -> negative i a).
Proof.
intros object P N HP HN.
exploit (hpositive_hnegative_ind object P N
           (fun i a => positive i a)
           (fun i a => negative i a)) as Hind.

(* goal *)
{
intros i a H.
apply positive_weaken.
rewrite -> Forall_forall in HP.
auto.
}

(* var *)
{
intros i.
apply positive_var.
}

(* const *)
{
intros i a.
apply positive_const.
}

(* prod *)
{
intros i a b _ IH1 _ IH2.
apply positive_prod; auto.
}

(* pi *)
{
intros i a b _ IH1 _ IH2.
apply positive_pi; auto.
}

(* sigma *)
{
intros i a b _ IH1 _ IH2.
apply positive_sigma; auto.
}

(* mu *)
{
intros i a _ IH.
apply positive_mu; auto.
}

(* bite *)
{
intros i m a b _ IH1 _ IH2.
apply positive_bite; auto.
}

(* equiv *)
{
intros i a b Hequiv _ IH.
eapply equiv_positive; eauto.
apply equiv_symm; auto.
}

(* goal *)
{
intros i a H.
apply negative_weaken.
rewrite -> Forall_forall in HN.
auto.
}

(* const *)
{
intros i a.
apply negative_const.
}

(* prod *)
{
intros i a b _ IH1 _ IH2.
apply negative_prod; auto.
}

(* pi *)
{
intros i a b _ IH1 _ IH2.
apply negative_pi; auto.
}

(* sigma *)
{
intros i a b _ IH1 _ IH2.
apply negative_sigma; auto.
}

(* mu *)
{
intros i a _ IH.
apply negative_mu; auto.
}

(* bite *)
{
intros i m a b _ IH1 _ IH2.
apply negative_bite; auto.
}

(* equiv *)
{
intros i a b Hequiv _ IH.
eapply equiv_negative; eauto.
apply equiv_symm; auto.
}

(* epilogue *)
{
destruct Hind.
split; intros; eauto.
}
Qed.


Lemma hpositive_impl_positive :
  forall object P N i (a : term object),
    Forall (positive 0) P
    -> Forall (negative 0) N
    -> hpositive P N i a
    -> positive i a.
Proof.
intros object P N i a HP HN H.
eapply hpositive_hnegative_impl_positive_negative; eauto.
Qed.


Lemma hnegative_impl_negative :
  forall object P N i (a : term object),
    Forall (positive 0) P
    -> Forall (negative 0) N
    -> hnegative P N i a
    -> negative i a.
Proof.
intros object P N i a HP HN H.
eapply hpositive_hnegative_impl_positive_negative; eauto.
Qed.


Lemma subst_hpositive_hnegative :
  forall object P N,
    (forall i s (a : term object),
       hpositive P N i a
       -> hpositive (map (subst (under 1 s)) P) (map (subst (under 1 s)) N) i (subst (under (S i) s) a))
    /\
    (forall i s (a : term object),
       hnegative P N i a
       -> hnegative (map (subst (under 1 s)) P) (map (subst (under 1 s)) N) i (subst (under (S i) s) a)).
Proof.
intros object P N.
exploit (hpositive_hnegative_ind object P N
           (fun i a =>
              forall s,
                hpositive (map (subst (under 1 s)) P) (map (subst (under 1 s)) N) i (subst (under (S i) s) a))
           (fun i a =>
              forall s,
                hnegative (map (subst (under 1 s)) P) (map (subst (under 1 s)) N) i (subst (under (S i) s) a))) as Hind.

(* goal *)
{
intros i a Hin s.
rewrite <- subst_compose.
rewrite -> compose_sh_under_leq; auto.
replace (S i - i) with 1 by omega.
rewrite -> subst_compose.
apply hpositive_goal.
apply in_map; auto.
}

(* var *)
{
intros i s.
rewrite -> subst_var.
rewrite -> project_under_lt; auto.
apply hpositive_var.
}

(* const *)
{
intros i a s.
rewrite <- subst_compose.
rewrite -> subst_under_sh1_more.
rewrite -> subst_compose.
apply hpositive_const.
}

(* prod *)
{
intros i a b _ IH1 _ IH2 s.
simpsub.
apply hpositive_prod; eauto.
}

(* pi *)
{
intros i a b _ IH1 _ IH2 s.
simpsub.
cbn [Nat.add].
apply hpositive_pi.
  {
  apply IH1.
  }
so (IH2 s) as H.
simpsubin H.
exact H.
}

(* sigma *)
{
intros i a b _ IH1 _ IH2 s.
simpsub.
cbn [Nat.add].
apply hpositive_sigma.
  {
  apply IH1.
  }
so (IH2 s) as H.
simpsubin H.
exact H.
}

(* mu *)
{
intros i a _ IH s.
simpsub.
cbn [Nat.add].
apply hpositive_mu.
so (IH s) as H.
rewrite -> !under_succ in H.
simpsubin H.
exact H.
}

(* bite *)
{
intros i m a b _ IH1 _ IH2 s.
rewrite -> SimpSub.subst_bite.
rewrite <- subst_compose.
rewrite -> subst_under_sh1_more.
rewrite -> subst_compose.
apply hpositive_bite; eauto.
}

(* reduce *)
{
intros i a b Hequiv _ IH s.
eapply hpositive_equiv; eauto.
apply equiv_subst; auto.
}

(* goal *)
{
intros i a Hin s.
rewrite <- subst_compose.
rewrite -> compose_sh_under_leq; auto.
replace (S i - i) with 1 by omega.
rewrite -> subst_compose.
apply hnegative_goal.
apply in_map; auto.
}

(* const *)
{
intros i a s.
rewrite <- subst_compose.
rewrite -> subst_under_sh1_more.
rewrite -> subst_compose.
apply hnegative_const.
}

(* prod *)
{
intros i a b _ IH1 _ IH2 s.
simpsub.
apply hnegative_prod; eauto.
}

(* pi *)
{
intros i a b _ IH1 _ IH2 s.
simpsub.
cbn [Nat.add].
apply hnegative_pi.
  {
  apply IH1.
  }
so (IH2 s) as H.
simpsubin H.
exact H.
}

(* sigma *)
{
intros i a b _ IH1 _ IH2 s.
simpsub.
cbn [Nat.add].
apply hnegative_sigma.
  {
  apply IH1.
  }
so (IH2 s) as H.
simpsubin H.
exact H.
}

(* mu *)
{
intros i a _ IH s.
simpsub.
cbn [Nat.add].
apply hnegative_mu.
so (IH s) as H.
rewrite -> !under_succ in H.
simpsubin H.
exact H.
}

(* bite *)
{
intros i m a b _ IH1 _ IH2 s.
rewrite -> SimpSub.subst_bite.
rewrite <- subst_compose.
rewrite -> subst_under_sh1_more.
rewrite -> subst_compose.
apply hnegative_bite; eauto.
}

(* reduce *)
{
intros i a b Hequiv _ IH s.
eapply hnegative_equiv; eauto.
apply equiv_subst; auto.
}

(* epilogue *)
{
destruct Hind; auto.
}
Qed.


Lemma subst_hpositive :
  forall object P N i s (a : term object),
    hpositive P N i a
    -> hpositive (map (subst (under 1 s)) P) (map (subst (under 1 s)) N) i (subst (under (S i) s) a).
Proof.
intros object P N.
exact (subst_hpositive_hnegative object P N andel).
Qed.


Lemma subst_hnegative :
  forall object P N i s (a : term object),
    hnegative P N i a
    -> hnegative (map (subst (under 1 s)) P) (map (subst (under 1 s)) N) i (subst (under (S i) s) a).
Proof.
intros object P N.
exact (subst_hpositive_hnegative object P N ander).
Qed.


Lemma sound_positive_algorithm :
  forall G a P N,
    hpositive P N 0 a
    -> (forall b,
          In b P
          -> pseq G (deq triv triv (ispositive b)))
    -> (forall b,
          In b N
          -> pseq G (deq triv triv (isnegative b)))
    -> pseq G (deq triv triv (ispositive a)).
Proof.
intros G a P N Hhpos Hallpos Hallneg.
so (Forall_forall _#3 ander Hallneg) as H.
revert H.
so (Forall_forall _#3 ander Hallpos) as H.
revert H.
clear Hallpos Hallneg.
revert G.
cut (forall G,
       hygiene (permit (ctxpred G)) a
       -> Forall (fun b => hygiene (ctxpred G) b /\ seq G (deq triv triv (ispositive b))) P
       -> Forall (fun b => hygiene (ctxpred G) b /\ seq G (deq triv triv (isnegative b))) N
       -> seq G (deq triv triv (ispositive a))).
  {
  intros Hprop G Hallpos Hallneg.
  so (shut_term _ G a) as (i1 & Hi1).
  assert (exists i,
            forall j, 
              i <= j
              -> Forall (fun b =>
                           hygiene (ctxpred (G ++ shut j)) b
                           /\ seq (G ++ shut j) (deq triv triv (ispositive b))) P) as (i2 & Hi2).
    {
    clear i1 Hi1 Hprop Hhpos Hallneg.
    induct Hallpos.
      (* nil *)
      {
      exists 0.
      intros j _.
      apply Forall_nil.
      }
  
      (* cons *)
      {
      intros b L Hb _ IH.
      so (shut_term _ G b) as (i1 & Hi1).
      destruct Hb as (i2 & Hi2).
      destruct IH as (i3 & Hi3).
      so (upper_bound_all 3 i1 i2 i3) as H; cbn in H.
      destruct H as (i & Hi1' & Hi2' & Hi3' & _).
      exists i.
      intros j Hj.
      apply Forall_cons.
        {
        split.
          {
          exploit (Hi1 j) as H; [omega |].
          exact H.
          }

          {
          apply Hi2; omega.
          }
        }

        {
        apply Hi3; omega.
        }
      }
    }
  assert (exists i,
            forall j, 
              i <= j
              -> Forall (fun b =>
                           hygiene (ctxpred (G ++ shut j)) b
                           /\ seq (G ++ shut j) (deq triv triv (isnegative b))) N) as (i3 & Hi3).
    {
    clear i1 i2 Hi1 Hi2 Hprop Hhpos Hallpos.
    induct Hallneg.
      (* nil *)
      {
      exists 0.
      intros j _.
      apply Forall_nil.
      }
  
      (* cons *)
      {
      intros b L Hb _ IH.
      so (shut_term _ G b) as (i1 & Hi1).
      destruct Hb as (i2 & Hi2).
      destruct IH as (i3 & Hi3).
      so (upper_bound_all 3 i1 i2 i3) as H; cbn in H.
      destruct H as (i & Hi1' & Hi2' & Hi3' & _).
      exists i.
      intros j Hj.
      apply Forall_cons.
        {
        split.
          {
          exploit (Hi1 j) as H; [omega |].
          exact H.
          }

          {
          apply Hi2; omega.
          }
        }

        {
        apply Hi3; omega.
        }
      }
    }
  so (upper_bound_all 3 i1 i2 i3) as H; cbn in H.
  destruct H as (i & Hi1' & Hi2' & Hi3' & _).
  exists i.
  intros j Hj.
  apply Hprop.
    {
    exploit (Hi1 j) as H; [omega |].
    eapply hygiene_weaken; eauto.
    intros x Hx.
    destruct x as [| x].
      {
      cbn; auto.
      }
    cbn.
    rewrite -> ctxpred_length in Hx |- *.
    omega.
    }

    {
    apply Hi2; omega.
    }

    {
    apply Hi3; omega.
    }
  }
intros G Hcla Hallpos Hallneg.
rewrite -> seq_ispositive; auto.
intros i s s' Hs.
split.
  {
  apply (hpositive_impl_positive _ (map (subst (under 1 s)) P) (map (subst (under 1 s)) N)).
  3:{
    apply subst_hpositive; auto.
    }

    {
    rewrite -> Forall_forall in Hallpos |- *.
    intros b Hb.
    rewrite -> in_map_iff in Hb.
    destruct Hb as (c & <- & Hc).
    so (Hallpos c Hc) as (Hclc & Hseqc).
    rewrite -> seq_ispositive in Hseqc.
      {
      exact (Hseqc _ _ _ Hs andel).
      }
  
      {
      eapply hygiene_weaken; eauto.
      intros x Hx.
      destruct x as [| x].
        {
        cbn; auto.
        }
      cbn.
      rewrite -> ctxpred_length in Hx |- *.
      omega.
      }
    }

    {
    rewrite -> Forall_forall in Hallneg |- *.
    intros b Hb.
    rewrite -> in_map_iff in Hb.
    destruct Hb as (c & <- & Hc).
    so (Hallneg c Hc) as (Hclc & Hseqc).
    rewrite -> seq_isnegative in Hseqc.
      {
      exact (Hseqc _ _ _ Hs andel).
      }
  
      {
      eapply hygiene_weaken; eauto.
      intros x Hx.
      destruct x as [| x].
        {
        cbn; auto.
        }
      cbn.
      rewrite -> ctxpred_length in Hx |- *.
      omega.
      }
    }
  }

  {
  apply (hpositive_impl_positive _ (map (subst (under 1 s')) P) (map (subst (under 1 s')) N)).
  3:{
    apply subst_hpositive; auto.
    }

    {
    rewrite -> Forall_forall in Hallpos |- *.
    intros b Hb.
    rewrite -> in_map_iff in Hb.
    destruct Hb as (c & <- & Hc).
    so (Hallpos c Hc) as (Hclc & Hseqc).
    rewrite -> seq_ispositive in Hseqc; auto.
      {
      exact (Hseqc _ _ _ Hs ander).
      }
  
      {
      eapply hygiene_weaken; eauto.
      intros x Hx.
      destruct x as [| x].
        {
        cbn; auto.
        }
      cbn.
      rewrite -> ctxpred_length in Hx |- *.
      omega.
      }
    }

    {
    rewrite -> Forall_forall in Hallneg |- *.
    intros b Hb.
    rewrite -> in_map_iff in Hb.
    destruct Hb as (c & <- & Hc).
    so (Hallneg c Hc) as (Hclc & Hseqc).
    rewrite -> seq_isnegative in Hseqc; auto.
      {
      exact (Hseqc _ _ _ Hs ander).
      }
  
      {
      eapply hygiene_weaken; eauto.
      intros x Hx.
      destruct x as [| x].
        {
        cbn; auto.
        }
      cbn.
      rewrite -> ctxpred_length in Hx |- *.
      omega.
      }
    }
  }
Qed.


Lemma sound_negative_algorithm :
  forall G a P N,
    hnegative P N 0 a
    -> (forall b,
          In b P
          -> pseq G (deq triv triv (ispositive b)))
    -> (forall b,
          In b N
          -> pseq G (deq triv triv (isnegative b)))
    -> pseq G (deq triv triv (isnegative a)).
Proof.
intros G a P N Hhpos Hallpos Hallneg.
so (Forall_forall _#3 ander Hallneg) as H.
revert H.
so (Forall_forall _#3 ander Hallpos) as H.
revert H.
clear Hallpos Hallneg.
revert G.
cut (forall G,
       hygiene (permit (ctxpred G)) a
       -> Forall (fun b => hygiene (ctxpred G) b /\ seq G (deq triv triv (ispositive b))) P
       -> Forall (fun b => hygiene (ctxpred G) b /\ seq G (deq triv triv (isnegative b))) N
       -> seq G (deq triv triv (isnegative a))).
  {
  intros Hprop G Hallpos Hallneg.
  so (shut_term _ G a) as (i1 & Hi1).
  assert (exists i,
            forall j, 
              i <= j
              -> Forall (fun b =>
                           hygiene (ctxpred (G ++ shut j)) b
                           /\ seq (G ++ shut j) (deq triv triv (ispositive b))) P) as (i2 & Hi2).
    {
    clear i1 Hi1 Hprop Hhpos Hallneg.
    induct Hallpos.
      (* nil *)
      {
      exists 0.
      intros j _.
      apply Forall_nil.
      }
  
      (* cons *)
      {
      intros b L Hb _ IH.
      so (shut_term _ G b) as (i1 & Hi1).
      destruct Hb as (i2 & Hi2).
      destruct IH as (i3 & Hi3).
      so (upper_bound_all 3 i1 i2 i3) as H; cbn in H.
      destruct H as (i & Hi1' & Hi2' & Hi3' & _).
      exists i.
      intros j Hj.
      apply Forall_cons.
        {
        split.
          {
          exploit (Hi1 j) as H; [omega |].
          exact H.
          }

          {
          apply Hi2; omega.
          }
        }

        {
        apply Hi3; omega.
        }
      }
    }
  assert (exists i,
            forall j, 
              i <= j
              -> Forall (fun b =>
                           hygiene (ctxpred (G ++ shut j)) b
                           /\ seq (G ++ shut j) (deq triv triv (isnegative b))) N) as (i3 & Hi3).
    {
    clear i1 i2 Hi1 Hi2 Hprop Hhpos Hallpos.
    induct Hallneg.
      (* nil *)
      {
      exists 0.
      intros j _.
      apply Forall_nil.
      }
  
      (* cons *)
      {
      intros b L Hb _ IH.
      so (shut_term _ G b) as (i1 & Hi1).
      destruct Hb as (i2 & Hi2).
      destruct IH as (i3 & Hi3).
      so (upper_bound_all 3 i1 i2 i3) as H; cbn in H.
      destruct H as (i & Hi1' & Hi2' & Hi3' & _).
      exists i.
      intros j Hj.
      apply Forall_cons.
        {
        split.
          {
          exploit (Hi1 j) as H; [omega |].
          exact H.
          }

          {
          apply Hi2; omega.
          }
        }

        {
        apply Hi3; omega.
        }
      }
    }
  so (upper_bound_all 3 i1 i2 i3) as H; cbn in H.
  destruct H as (i & Hi1' & Hi2' & Hi3' & _).
  exists i.
  intros j Hj.
  apply Hprop.
    {
    exploit (Hi1 j) as H; [omega |].
    eapply hygiene_weaken; eauto.
    intros x Hx.
    destruct x as [| x].
      {
      cbn; auto.
      }
    cbn.
    rewrite -> ctxpred_length in Hx |- *.
    omega.
    }

    {
    apply Hi2; omega.
    }

    {
    apply Hi3; omega.
    }
  }
intros G Hcla Hallpos Hallneg.
rewrite -> seq_isnegative; auto.
intros i s s' Hs.
split.
  {
  apply (hnegative_impl_negative _ (map (subst (under 1 s)) P) (map (subst (under 1 s)) N)).
  3:{
    apply subst_hnegative; auto.
    }

    {
    rewrite -> Forall_forall in Hallpos |- *.
    intros b Hb.
    rewrite -> in_map_iff in Hb.
    destruct Hb as (c & <- & Hc).
    so (Hallpos c Hc) as (Hclc & Hseqc).
    rewrite -> seq_ispositive in Hseqc.
      {
      exact (Hseqc _ _ _ Hs andel).
      }
  
      {
      eapply hygiene_weaken; eauto.
      intros x Hx.
      destruct x as [| x].
        {
        cbn; auto.
        }
      cbn.
      rewrite -> ctxpred_length in Hx |- *.
      omega.
      }
    }

    {
    rewrite -> Forall_forall in Hallneg |- *.
    intros b Hb.
    rewrite -> in_map_iff in Hb.
    destruct Hb as (c & <- & Hc).
    so (Hallneg c Hc) as (Hclc & Hseqc).
    rewrite -> seq_isnegative in Hseqc.
      {
      exact (Hseqc _ _ _ Hs andel).
      }
  
      {
      eapply hygiene_weaken; eauto.
      intros x Hx.
      destruct x as [| x].
        {
        cbn; auto.
        }
      cbn.
      rewrite -> ctxpred_length in Hx |- *.
      omega.
      }
    }
  }

  {
  apply (hnegative_impl_negative _ (map (subst (under 1 s')) P) (map (subst (under 1 s')) N)).
  3:{
    apply subst_hnegative; auto.
    }

    {
    rewrite -> Forall_forall in Hallpos |- *.
    intros b Hb.
    rewrite -> in_map_iff in Hb.
    destruct Hb as (c & <- & Hc).
    so (Hallpos c Hc) as (Hclc & Hseqc).
    rewrite -> seq_ispositive in Hseqc; auto.
      {
      exact (Hseqc _ _ _ Hs ander).
      }
  
      {
      eapply hygiene_weaken; eauto.
      intros x Hx.
      destruct x as [| x].
        {
        cbn; auto.
        }
      cbn.
      rewrite -> ctxpred_length in Hx |- *.
      omega.
      }
    }

    {
    rewrite -> Forall_forall in Hallneg |- *.
    intros b Hb.
    rewrite -> in_map_iff in Hb.
    destruct Hb as (c & <- & Hc).
    so (Hallneg c Hc) as (Hclc & Hseqc).
    rewrite -> seq_isnegative in Hseqc; auto.
      {
      exact (Hseqc _ _ _ Hs ander).
      }
  
      {
      eapply hygiene_weaken; eauto.
      intros x Hx.
      destruct x as [| x].
        {
        cbn; auto.
        }
      cbn.
      rewrite -> ctxpred_length in Hx |- *.
      omega.
      }
    }
  }
Qed.


Lemma sound_positive_eta :
  forall G a p,
    pseq G (deq p p (ispositive a))
    -> pseq G (deq p triv (ispositive a)).
Proof.
intros G a p.
revert G.
refine (seq_pseq 1 [] p 1 [] _ _ _); cbn.
intros G Hclp Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq _#3 Hs) as (R & Hrobl & Hrobr & Htrue & _).
exists R.
do2 2 split; auto.
simpsubin Hrobl; clear Hrobr.
invert (basic_value_inv _#6 value_ispositive Hrobl).
intros _ <-.
destruct Htrue as (Hpositive & _ & Hclsp & Hclsp' & Hp & Hp').
do2 2 split.
  {
  do2 5 split; auto.
  }

  {
  do2 5 split; auto using star_refl; simpsub; apply hygiene_auto; cbn; auto.
  }

  {
  do2 5 split; auto using star_refl; simpsub; apply hygiene_auto; cbn; auto.
  }
Qed.


Lemma sound_negative_eta :
  forall G a p,
    pseq G (deq p p (isnegative a))
    -> pseq G (deq p triv (isnegative a)).
Proof.
intros G a p.
revert G.
refine (seq_pseq 1 [] p 1 [] _ _ _); cbn.
intros G Hclp Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq _#3 Hs) as (R & Hrobl & Hrobr & Htrue & _).
exists R.
do2 2 split; auto.
simpsubin Hrobl; clear Hrobr.
invert (basic_value_inv _#6 value_isnegative Hrobl).
intros _ <-.
destruct Htrue as (Hnegative & _ & Hclsp & Hclsp' & Hp & Hp').
do2 2 split.
  {
  do2 5 split; auto.
  }

  {
  do2 5 split; auto using star_refl; simpsub; apply hygiene_auto; cbn; auto.
  }

  {
  do2 5 split; auto using star_refl; simpsub; apply hygiene_auto; cbn; auto.
  }
Qed.

