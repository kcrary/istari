(* This didn't turn out to be used very widely.  It's used in the soundness of the
   rules tr_sequal_compat_lam, and tr_constfn_intro, neither of which are very
   important.
*)

Require Import Tactics.
Require Import Equality.
Require Import Relation.
Require Import Syntax.
Require Import SimpSub.
Require Import Dynamic.

Require Import Reduction.
Require Import Hygiene.
Require Import Equivalence.

Section object.


Arguments operator {object}.
Arguments term {object}.
Arguments row {object}.
Arguments rw_cons {object i a}.


Variable object : Type.


Lemma subst1_under_form :
  forall i m n a th r,
    subst (under i (dot n id)) m = oper a th r
    -> (m = var i /\ oper a th r = subst (sh i) n)
       \/ (exists r',
             m = oper a th r'
             /\ r = @substr object (under i (dot n id)) a r').
Proof.
intros i m n a th r Hsubst.
destruct m as [j | a' th' r'].
  {
  left.
  simpsubin Hsubst.
  so (Nat.lt_trichotomy j i) as [Hlt | [Heq | Hlt]].
    {
    exfalso.
    rewrite -> project_under_lt in Hsubst; auto.
    discriminate Hsubst.
    }
  
  2:{
    exfalso.
    rewrite -> project_under_geq in Hsubst; [| omega].
    replace (j - i) with (S (j - i - 1)) in Hsubst by omega.
    simpsubin Hsubst.
    discriminate Hsubst.
    }
  
    {
    subst j.
    split; auto.
    rewrite -> project_under_eq in Hsubst.
    simpsubin Hsubst.
    auto.
    }
  }

  {
  right.
  simpsubin Hsubst.
  injection Hsubst.
  intros Heq1 Heq2 ->.
  injectionT Heq2.
  intros ->.
  injectionT Heq1.
  intros <-.
  exists r'; auto.
  }
Qed.


Lemma subst1_marker_under_form :
  forall k i m a th r,
    canon _ th
    -> subst (under i (dot (marker k) id)) m = oper a th r
    -> exists r',
         m = oper a th r'
         /\ r = @substr object (under i (dot (marker k) id)) a r'.
Proof.
intros k i m a th r Hcanon Hsubst.
so (subst1_under_form _#6 Hsubst) as [(-> & Heq) | H].
  {
  exfalso.
  simpsubin Heq.
  unfold marker in Heq.
  injection Heq.
  intros _ Heq1 ->.
  injectionT Heq1.
  intros ->.
  invert Hcanon.
  }
exact H.
Qed.



Lemma value_subst1_marker_under :
  forall k i (m : @term object),
    value (subst (under i (dot (marker k) id)) m)
    -> value m.
Proof.
intros k i m Hval.
invert Hval.
intros a th r Hcanon Hsubst.
destruct m as [j | a' th' r'].
  {
  simpsubin Hsubst.
  so (Nat.lt_trichotomy j i) as [Hlt | [Heq | Hlt]].
    {
    rewrite -> project_under_lt in Hsubst; auto.
    discriminate Hsubst.
    }
  
  2:{
    rewrite -> project_under_geq in Hsubst; [| omega].
    replace (j - i) with (S (j - i - 1)) in Hsubst by omega.
    simpsubin Hsubst.
    discriminate Hsubst.
    }
  subst j.
  rewrite -> project_under_eq in Hsubst.
  simpsubin Hsubst.
  unfold marker in Hsubst.
  injection Hsubst.
  intros _ Heq ->.
  injectionT Heq.
  intros ->.
  invert Hcanon.
  }

  {
  simpsubin Hsubst.
  injection Hsubst.
  intros Heq1 Heq2 <-.
  injectionT Heq2.
  intros <-.
  apply value_i; auto.
  }
Qed.


Lemma reduce_subst_marker_form :
  forall k i m p,
    reduce (subst (under i (dot (marker k) id)) m) p
    -> exists m',
         reduce m m'
         /\ p = @subst object (under i (dot (marker k) id)) m'.
Proof.
intros k i m p.
revert i p.
pattern m.
apply (syntax_ind _ _ (fun a r =>
                         forall i (t : row a),
                           reducer (substr (under i (dot (marker k) id)) r) t
                           -> exists r',
                                reducer r r'
                                /\ t  = substr (under i (dot (marker k) id)) r')).

(* var *)
{
intros j i p Hreduce.
exists (var j).
split.
  {
  apply reduce_var.
  }
simpsubin Hreduce.
simpsub.
so (Nat.lt_trichotomy j i) as [Hlt | [Heq | Hlt]].
  {
  rewrite -> project_under_lt in Hreduce |- *; auto.
  invert Hreduce.
  auto.
  }

2:{
  rewrite -> project_under_geq in Hreduce |- *; [| omega | omega].
  replace (j - i) with (S (j - i - 1)) in Hreduce |- * by omega.
  simpsub.
  simpsubin Hreduce.
  replace (i + (0 + (j - i - 1))) with (j - 1) in Hreduce |- * by omega.
  invert Hreduce.
  auto.
  }

  {
  subst j.
  rewrite -> project_under_eq in Hreduce |- *.
  simpsubin Hreduce.
  simpsub.
  invert Hreduce.
  intros r' Hr' <-.
  so (row_0_invert _ r').
  subst r'.
  fold (@marker object k).
  reflexivity.
  }
}

(* oper *)
{
intros a th r IH i x Hreduce.
simpsubin Hreduce.
invertc Hreduce.
  (* oper *)
  {
  intros y Hreducer <-.
  so (IH _ _ Hreducer) as (r' & Hreducer' & ?).
  subst y.
  exists (oper a th r').
  simpsub.
  split; auto.
  apply reduce_oper; auto.
  }

  (* app beta *)
  {
  intros p p' q q' Hreducep Hreduceq <- Heq1 Heq2 <-.
  injectionT Heq1.
  intros <-.
  injectionT Heq2.
  intro Heq.
  so (row_2_invert _#3 r) as (v & w & ?).
  subst r.
  simpsubin Heq.
  injectionc Heq.
  intros -> Heqlam.
  fold (app v w).
  so (subst1_marker_under_form _#6 (canon_lam _) (eqsymm Heqlam)) as (r & -> & _).
  so (row_1_invert _ _ r) as (t & ->).
  fold (lam t) in Heqlam |- *.
  simpsubin Heqlam.
  injectionc Heqlam.
  rewrite <- under_succ.
  intros ->.
  fold (lam t) in IH.
  exploit (IH i (rw_cons (lam p') (rw_cons q' rw_nil))) as H.
    {
    simpsub.
    rewrite <- under_succ.
    apply reducer_cons.
      {
      apply reduce_oper.
      apply reducer_cons; auto.
      apply reducer_nil.
      }
    apply reducer_cons; auto.
    apply reducer_nil.
    }
  destruct H as (r & Hreducer & Heq).
  so (row_2_invert _#3 r) as (l & w' & ->).
  invertc Hreducer.
  intros Hredlam Hreducer.
  invertc Hreducer.
  intros Hredw _.
  simpsubin Heq.
  invertc Heq.
  intros Heqlam ->.
  so (subst1_marker_under_form _#6 (canon_lam _) (eqsymm Heqlam)) as (r & Heq & _).
  so (row_1_invert _#2 r) as (t' & ->).
  subst l.
  fold (lam t') in Heqlam.
  simpsubin Heqlam.
  injectionc Heqlam.
  rewrite <- under_succ.
  intros ->.
  fold (lam t') in Hredlam.
  invertc Hredlam.
  intros H _.
  invertc H.
  intros Hredt _.
  (* quite easy, when we've finally got all the inversion done *)
  exists (subst1 w' t').
  split.
    {
    apply reduce_app_beta; auto.
    }

    {
    simpsub.
    reflexivity.
    }
  }

  (* prev beta *)
  {
  intros pp Hred <- Heq1 Heq2.
  injectionT Heq1.
  intros <-.
  injectionT Heq2.
  intro Heq.
  so (row_1_invert _ _ r) as (n & ->).
  simpsubin Heq.
  injectionc Heq.
  intro Heq.
  symmetry in Heq.
  so (subst1_marker_under_form _#6 (canon_next _) Heq) as (r & -> & _).
  so (row_1_invert _ _ r) as (n & ->).
  simpsubin Heq.
  fold (next (subst (under i (dot (marker k) id)) n)) in Heq.
  injectionc Heq.
  intros <-.
  exploit (IH i (rw_cons (next x) rw_nil)) as H.
    {
    simpsub.
    apply reducer_cons.
      {
      fold (next (subst (under i (dot (marker k) id)) n)).
      apply reduce_oper.
      apply reducer_cons; auto.
      apply reducer_nil.
      }
    apply reducer_nil.
    }
  destruct H as (r & Hreducer & Heq).
  so (row_1_invert _ _ r) as (p & ->).
  invertc Hreducer.
  fold (next n).
  intros Hred' _.
  fold (prev (next n)).
  simpsubin Heq.
  injectionc Heq.
  intro Heq.
  symmetry in Heq.
  so (subst1_marker_under_form _#6 (canon_next _) Heq) as (r & -> & Heq').
  so (row_1_invert _ _ r) as (p' & ->).
  simpsubin Heq'.
  injectionc Heq'.
  intros ->.
  exists p'.
  split; auto.
  fold (next p') in Hred'.
  invertc Hred'.
  intro Hred'.
  invertc Hred'.
  intros Hred'' _ _.
  apply reduce_prev_beta; auto.
  }

  (* bite_beta1 *)
  {
  intros n n' Hred <- Heq1 Heq2.
  so (row_3_invert _ _ _ _ r) as (u & v & w & ->).
  injectionT Heq1.
  intros <-.
  injectionT Heq2.
  intro Heq.
  fold (bite u v w).
  simpsubin Heq.
  injectionc Heq.
  intros -> -> Heq.
  symmetry in Heq.
  so (subst1_marker_under_form _#6 (canon_btrue _) Heq) as (r & -> & _).
  so (row_0_invert _ r).
  subst r.
  clear Heq.
  exploit (IH i (rw_cons btrue (rw_cons x (rw_cons (subst (under i (dot (marker k) id)) w) rw_nil)))) as H.
    {
    simpsub.
    apply reducer_cons.
      {
      apply reduce_id.
      }
    apply reducer_cons; auto.
    apply reducer_cons.
      {
      apply reduce_id.
      }
    apply reducer_nil.
    }
  destruct H as (r & Hreducer & Heq).
  so (row_3_invert _ _ _ _ r) as (u' & v' & w' & ->).
  invertc Hreducer.
  intros _ Hreducer.
  invertc Hreducer.
  intros Hred' _.
  simpsubin Heq.
  injectionc Heq.
  intros _ -> _.
  exists v'.
  split; auto.
  apply reduce_bite_beta1; auto.
  }

  (* bite_beta2 *)
  {
  intros n n' Hred <- Heq1 Heq2.
  so (row_3_invert _ _ _ _ r) as (u & v & w & ->).
  injectionT Heq1.
  intros <-.
  injectionT Heq2.
  intro Heq.
  fold (bite u v w).
  simpsubin Heq.
  injectionc Heq.
  intros -> -> Heq.
  symmetry in Heq.
  so (subst1_marker_under_form _#6 (canon_bfalse _) Heq) as (r & -> & _).
  so (row_0_invert _ r).
  subst r.
  clear Heq.
  exploit (IH i (rw_cons bfalse (rw_cons (subst (under i (dot (marker k) id)) v) (rw_cons x rw_nil)))) as H.
    {
    simpsub.
    apply reducer_cons.
      {
      apply reduce_id.
      }
    apply reducer_cons.
      {
      apply reduce_id.
      }
    apply reducer_cons; auto.
    apply reducer_nil.
    }
  destruct H as (r & Hreducer & Heq).
  so (row_3_invert _ _ _ _ r) as (u' & v' & w' & ->).
  invertc Hreducer.
  intros _ Hreducer.
  invertc Hreducer.
  intros _ Hreducer.
  invertc Hreducer.
  intros Hred' _.
  simpsubin Heq.
  injectionc Heq.
  intros -> _ _.
  exists w'.
  split; auto.
  apply reduce_bite_beta2; auto.
  }

  (* ppi1_beta *)
  {
  intros n n' Hred <- Heq1 Heq2.
  so (row_1_invert _ _ r) as (p & ->).
  injectionT Heq1.
  intros <-.
  injectionT Heq2.
  intro Heq.
  simpsubin Heq.
  injectionc Heq.
  intro Heq.
  symmetry in Heq.
  so (subst1_marker_under_form _#6 (canon_ppair _) Heq) as (r & -> & Heq').
  so (row_2_invert _ _ _ r) as (u & v & ->).
  clear Heq.
  fold (ppair u v).
  fold (ppi1 (ppair u v)).
  simpsubin Heq'.
  injectionc Heq'.
  intros -> ->.
  exploit (IH i (rw_cons (ppair x (subst (under i (dot (marker k) id)) v)) rw_nil)) as H.
    {
    simpsub.
    apply reducer_cons.
    2:{
      apply reducer_nil.
      }
    fold (ppair (subst (under i (dot (marker k) id)) u) (subst (under i (dot (marker k) id)) v)).
    apply reduce_oper.
    apply reducer_cons; auto.
    apply reducer_id.
    }
  fold (ppair u v) in H.
  destruct H as (r & Hreducer & Heq).
  so (row_1_invert _ _ r) as (p & ->).
  invertc Hreducer.
  intros Hred' _.
  simpsubin Heq.
  injectionc Heq.
  intro Heq.
  symmetry in Heq.
  so (subst1_marker_under_form _#6 (canon_ppair _) Heq) as (r & -> & Heq').
  so (row_2_invert _ _ _ r) as (u' & v' & ->).
  clear Heq.
  simpsubin Heq'.
  invertc Hred'.
  intros Hreducer _.
  invertc Hreducer.
  intros Hredu Hreducer.
  invertc Hreducer.
  intros Hredv _.
  injectionc Heq'.
  intros _ ->.
  exists u'.
  split; auto.
  apply reduce_ppi1_beta; auto.
  }

  (* ppi2_beta *)
  {
  intros n n' Hred <- Heq1 Heq2.
  so (row_1_invert _ _ r) as (p & ->).
  injectionT Heq1.
  intros <-.
  injectionT Heq2.
  intro Heq.
  simpsubin Heq.
  injectionc Heq.
  intro Heq.
  symmetry in Heq.
  so (subst1_marker_under_form _#6 (canon_ppair _) Heq) as (r & -> & Heq').
  so (row_2_invert _ _ _ r) as (u & v & ->).
  clear Heq.
  fold (ppair u v).
  fold (ppi2 (ppair u v)).
  simpsubin Heq'.
  injectionc Heq'.
  intros -> ->.
  exploit (IH i (rw_cons (ppair (subst (under i (dot (marker k) id)) u) x) rw_nil)) as H.
    {
    simpsub.
    apply reducer_cons.
    2:{
      apply reducer_nil.
      }
    fold (ppair (subst (under i (dot (marker k) id)) u) (subst (under i (dot (marker k) id)) v)).
    apply reduce_oper.
    apply reducer_cons.
      {
      apply reduce_id.
      }
    apply reducer_cons; auto.
    apply reducer_nil.
    }
  fold (ppair u v) in H.
  destruct H as (r & Hreducer & Heq).
  so (row_1_invert _ _ r) as (p & ->).
  invertc Hreducer.
  intros Hred' _.
  simpsubin Heq.
  injectionc Heq.
  intro Heq.
  symmetry in Heq.
  so (subst1_marker_under_form _#6 (canon_ppair _) Heq) as (r & -> & Heq').
  so (row_2_invert _ _ _ r) as (u' & v' & ->).
  clear Heq.
  simpsubin Heq'.
  invertc Hred'.
  intros Hreducer _.
  invertc Hreducer.
  intros Hredu Hreducer.
  invertc Hreducer.
  intros Hredv _.
  injectionc Heq'.
  intros -> _.
  exists v'.
  split; auto.
  apply reduce_ppi2_beta; auto.
  }

  (* seq beta *)
  {
  intros mm1 m1' mm2 m2' Hval Hred1 Hred2 <- Heq1 Heq2 <-.
  so (row_2_invert _#3 r) as (m1 & m2 & ->).
  injectionT Heq1.
  intros <-.
  injectionT Heq2.
  intro Heq.
  simpsubin Heq.
  injectionc Heq.
  intros -> ->.
  rewrite <- under_succ in Hred2.
  fold (@seq object m1 m2).
  exploit (IH i (rw_cons m1' (rw_cons m2' rw_nil))) as H.
    {
    simpsub.
    apply reducer_cons; auto.
    apply reducer_cons; auto.
    apply reducer_nil.
    }
  destruct H as (r & Hreducer & Heq).
  so (row_2_invert _#3 r) as (n1 & n2 & ->).
  simpsubin Heq.
  injectionc Heq.
  intros -> ->.
  invert Hreducer.
  intros Hred1' H.
  invert H.
  intros Hred2' _.
  rewrite <- under_succ.
  exists (subst1 n1 n2).
  split.
    {
    apply reduce_seq_beta; auto.
    eapply value_subst1_marker_under; eauto.
    }
  simpsub.
  reflexivity.
  }
}

(* nil *)
{
intros i r _.
so (row_0_invert _ r); subst r.
exists rw_nil.
split.
  {
  apply reducer_nil.
  }

  {
  simpsub.
  reflexivity.
  }
}

(* cons *)
{
clear m.
intros j a m IH1 r IH2 i rr Hrr.
so (row_cons_invert _ _ _ rr) as (p & s & ->).
simpsubin Hrr.
invert Hrr.
intros Hmp Hrs.
so (IH1 (j + i) _ Hmp) as (m' & Hm & ->).
so (IH2 i _ Hrs) as (r' & Hr & ->).
exists (rw_cons m' r').
split.
  {
  apply reducer_cons; auto.
  }

  {
  simpsub.
  reflexivity.
  }
}
Qed.


Lemma reduces_subst_marker_form :
  forall k i m p,
    star reduce (subst (under i (dot (marker k) id)) m) p
    -> exists m',
         star reduce m m'
         /\ p = @subst object (under i (dot (marker k) id)) m'.
Proof.
intros k i m p Hreduces.
remember (subst (under i (dot (marker k) id)) m) as x eqn:Heqx in Hreduces.
revert m Heqx.
induct Hreduces.

(* refl *)
{
intros ? m ->.
exists m.
split; auto.
apply star_refl.
}

(* step *)
{
intros x y z Hxy _ IH m ->.
so (reduce_subst_marker_form _#4 Hxy) as (y' & Hxy' & Heq).
so (IH _ Heq) as (z' & Hyz' & Heq').
exists z'.
split; auto.
eapply star_step; eauto.
}
Qed.


Fixpoint markerin (k : nat) (m : @term object) { struct m } : Prop :=
  (match m with
   | var _ => False
   | oper a th r => 
       (match th with
        | oper_marker _ k' => k = k'
        | _ => False
        end) 
       \/ markerin_row k a r
   end)

with markerin_row (k : nat) (a : list nat) (r : row a) { struct r } : Prop :=
  (match r with
   | rw_nil => False
   | @rw_cons _ j a m r => markerin k m \/ markerin_row k a r
   end)
.


(* Max would be tighter than plus, but tightness doesn't matter and Coq handles plus better. *)
Fixpoint markercap (m : @term object) { struct m } : nat :=
  (match m with
   | var _ => 0
   | oper a th r =>
       (match th with
        | oper_marker _ k => S k
        | _ => 0
        end)
       + markercap_row a r
   end)

with markercap_row (a : list nat) (r : row a) { struct r } : nat :=
  (match r with
   | rw_nil => 0
   | @rw_cons _ j a m r => markercap m + markercap_row a r
   end)
.


Lemma markercap_limit :
  forall m k,
    markerin k m
    -> k < markercap m.
Proof.
intros m k.
pattern m.
revert m.
apply (syntax_ind _ _ (fun a r => markerin_row k a r -> k < markercap_row a r)).

(* var *)
{
intros n Hin.
cbn in Hin.
destruct Hin.
}

(* oper *)
{
intros a th r IH Hin.
cbn in Hin.
destruct Hin as [Hin | Hin].
  {
  destruct th; cbn in Hin; try (destruct Hin; done).
  cbn.
  omega.
  }

  {
  so (IH Hin).
  cbn.
  omega.
  }
}

(* nil *)
{
cbn.
intro H.
destruct H.
}

(* cons *)
{
intros i a th IH1 r IH2 Hin.
cbn.
destruct Hin as [Hin | Hin].
  {
  so (IH1 Hin).
  omega.
  }

  {
  so (IH2 Hin).
  omega.
  }
}
Qed.


Lemma markerin_shift :
  forall k j i m,
    markerin k (subst (under i (sh j)) m)
    -> markerin k m.
Proof.
intros k j i m.
revert i.
pattern m.
revert m.
apply (syntax_ind _ _ (fun a r =>
                         forall i,
                           markerin_row k _ (substr (under i (sh j)) r)
                           -> markerin_row k _ r)).

(* var *)
{
intros n i Hin.
simpsubin Hin.
so (Nat.lt_trichotomy n i) as [Hlt | [Heq | Hlt]].
  {
  rewrite -> project_under_lt in Hin; auto.
  }

  {
  subst n.
  rewrite -> project_under_eq in Hin.
  simpsubin Hin.
  cbn in Hin.
  destruct Hin.
  }

  {
  rewrite -> project_under_geq in Hin; [| omega].
  simpsubin Hin.
  cbn in Hin.
  destruct Hin.
  }
}

(* oper *)
{
intros a th r IH i Hin.
simpsubin Hin.
cbn in Hin.
destruct Hin as [Hin | Hin].
  {
  destruct th; cbn in Hin; try (destruct Hin; done).
  subst k.
  cbn.
  left; auto.
  }

  {
  cbn.
  right.
  apply (IH i); auto.
  }
}

(* nil *)
{
intros i Hin.
cbn in Hin.
destruct Hin.
}

(* cons *)
{
intros l a m IH1 r IH2 i Hin.
simpsubin Hin.
cbn in Hin.
cbn.
destruct Hin as [Hin | Hin].
  {
  left.
  apply (IH1 (l + i)); auto.
  }

  {
  right.
  apply (IH2 i); auto.
  }
}
Qed.



Lemma markerin_subst_under :
  forall k i m n,
    markerin k (subst (under i (dot n id)) m)
    -> markerin k m \/ markerin k n.
Proof.
intros k i m n.
revert i.
pattern m.
revert m.
apply (syntax_ind _ _ (fun a r =>
                         forall i,
                           markerin_row k _ (substr (under i (dot n id)) r)
                           -> markerin_row k _ r \/ markerin k n)).

(* var *)
{
intros j i Hin.
right.
simpsubin Hin.
so (Nat.lt_trichotomy j i) as [Hlt | [Heq | Hlt]].
  {
  rewrite -> project_under_lt in Hin; auto.
  cbn in Hin.
  destruct Hin.
  }

  {
  subst j.
  rewrite -> project_under_eq in Hin.
  simpsubin Hin.
  apply (markerin_shift k i 0); auto.
  }

  {
  rewrite -> project_under_geq in Hin; [| omega].
  replace (j - i) with (S (j - i - 1)) in Hin by omega.
  simpsubin Hin.
  cbn in Hin.
  destruct Hin.
  }
}

(* oper *)
{
intros a th r IH i Hin.
simpsubin Hin.
cbn in Hin.
destruct Hin as [Hin | Hin].
  {
  destruct th; try (cbn in Hin; destruct Hin; done).
  subst k.
  left.
  cbn.
  left.
  reflexivity.
  }

  {
  so (IH _ Hin) as [H | H]; auto.
  left.
  cbn.
  right; auto.
  }
}

(* nil *)
{
intros i Hin.
cbn in Hin.
destruct Hin.
}

(* cons *)
{
intros j a m IH1 r IH2 i Hin.
simpsubin Hin.
cbn in Hin.
destruct Hin as [Hin | Hin].
  {
  so (IH1 (j + i) Hin) as [H | H]; auto.
  left.
  cbn.
  left; auto.
  }

  {
  so (IH2 i Hin) as [H | H]; auto.
  left.
  cbn.
  right; auto.
  }
}
Qed.


Lemma markerin_reduce :
  forall k m n,
    reduce m n
    -> markerin k n
    -> markerin k m.
Proof.
intros k.
exploit
  (reduce_mut_ind _
     (fun m n => markerin k n -> markerin k m)
     (fun a r r' => markerin_row k _ r' -> markerin_row k _ r));
auto.

(* oper *)
{
intros a th r r' _ IH Hin.
cbn in Hin.
cbn.
destruct Hin as [Hin | Hin]; auto.
}

(* app beta *)
{
intros m m' n n' _ IH1 _ IH2 Hin.
cbn.
right.
so (markerin_subst_under k 0 _ _ Hin) as [Hin' | Hin']; auto.
}

{ intros; cbn; auto 6. }
{ intros; cbn; auto 6. }
{ intros; cbn; auto 6. }
{ intros; cbn; auto 6. }
{ intros; cbn; auto 7. }

(* seq beta *)
{
intros m m' n n' Hval _ IH1 _ IH2 Hin.
cbn.
right.
so (markerin_subst_under k 0 _ _ Hin) as [Hin' | Hin']; auto.
}

(* cons *)
{
intros i a m n r s _ IH1 _ IH2 Hin.
cbn in Hin.
cbn.
destruct Hin as [Hin' | Hin']; auto.
}
Qed.


Lemma markerin_reduces :
  forall k m n,
    star reduce m n
    -> markerin k n
    -> markerin k m.
Proof.
intros k m n Hred.
induct Hred; auto.
intros x y z Hred _ IH Hin.
eapply markerin_reduce; eauto.
Qed.


Lemma subst_marker_eq :
  forall k i m n,
    ~ markerin k m
    -> ~ markerin k n
    -> subst (under i (dot (marker k) id)) m = subst (under i (dot (marker k) id)) n
    -> m = n.
Proof.
intros b i m.
revert i.
pattern m.
revert m.
apply (syntax_ind _ _ (fun a r =>
                         forall i r',
                           ~ markerin_row b _ r
                           -> ~ markerin_row b _ r'
                           -> substr (under i (dot (marker b) id)) r = substr (under i (dot (marker b) id)) r'
                           -> r = r')).

(* var *)
{
intros j i n Hnin Hnin' H.
destruct n as [k | a th r].
  {
  simpsubin H.
  so (Nat.lt_trichotomy j i) as [Hltj | [Heqj | Hltj]].
    {
    rewrite -> project_under_lt in H; auto.
    so (Nat.lt_trichotomy k i) as [Hltk | [Heqk | Hltk]].
      {
      rewrite -> project_under_lt in H; auto.
      }

      {
      subst k.
      rewrite -> project_under_eq in H.
      simpsubin H.
      discriminate H.
      }

      {
      rewrite -> project_under_geq in H; [| omega].
      simpsubin H.
      replace (k - i) with (S (k - i - 1)) in H by omega.
      simpsubin H.
      injection H.
      omega.
      }
    }

    {
    subst j.
    rewrite -> project_under_eq in H.
    simpsubin H.
    so (Nat.lt_trichotomy k i) as [Hltk | [Heqk | Hltk]].
      {
      rewrite -> project_under_lt in H; auto.
      discriminate H.
      }

      {
      subst k.
      reflexivity.
      }

      {
      rewrite -> project_under_geq in H; [| omega].
      replace (k - i) with (S (k - i - 1)) in H by omega.
      simpsubin H.
      discriminate H.
      }
    }

    {
    rewrite -> project_under_geq in H; [| omega].
    replace (j - i) with (S (j - i - 1)) in H by omega.
    simpsubin H.
    so (Nat.lt_trichotomy k i) as [Hltk | [Heqk | Hltk]].
      {
      rewrite -> project_under_lt in H; auto.
      f_equal.
      injection H.
      omega.
      }

      {
      subst k.
      rewrite -> project_under_eq in H.
      simpsubin H.
      discriminate H.
      }

      {
      rewrite -> project_under_geq in H; [| omega].
      replace (k - i) with (S (k - i - 1)) in H by omega.
      simpsubin H.
      f_equal.
      injection H.
      omega.
      }
    }
  }

  {
  simpsubin H.
  so (Nat.lt_trichotomy j i) as [Hltj | [Heqj | Hltj]].
    {
    rewrite -> project_under_lt in H; auto.
    discriminate H.
    }

    {
    subst j.
    rewrite -> project_under_eq in H.
    simpsubin H.
    unfold marker in H.
    injectionc H.
    intros _ Heq <-.
    injectionT Heq.
    intros <-.
    cbn in Hnin'.
    destruct Hnin'.
    left.
    reflexivity.
    }

    {
    rewrite -> project_under_geq in H; [| omega].
    replace (j - i) with (S (j - i - 1)) in H by omega.
    simpsubin H.
    discriminate H.
    }
  }
}

(* oper *)
{
intros a th r IH i n Hnin Hnin' H.
destruct n as [k | a' th' r'].
  {
  simpsubin H.
  so (Nat.lt_trichotomy k i) as [Hltk | [Heqk | Hltk]].
    {
    rewrite -> project_under_lt in H; auto.
    discriminate H.
    }

    {
    subst k.
    rewrite -> project_under_eq in H.
    simpsubin H.
    unfold marker in H.
    injectionc H.
    intros _ Heq ->.
    injectionT Heq.
    intros ->.
    cbn in Hnin.
    destruct Hnin.
    left.
    reflexivity.
    }

    {
    rewrite -> project_under_geq in H; [| omega].
    replace (k - i) with (S (k - i - 1)) in H by omega.
    simpsubin H.
    discriminate H.
    }
  }

  {
  simpsubin H.
  injectionc H.
  intros Heq1 Heq2 <-.
  injectionT Heq2.
  intros <-.
  injectionT Heq1.
  intro H.
  f_equal.
  apply (IH i); auto.
    {
    contradict Hnin.
    cbn.
    right; auto.
    }

    {
    contradict Hnin'.
    cbn.
    right; auto.
    }
  }
}

(* nil *)
{
intros i r' _ _ _.
so (row_0_invert _ r').
subst r'.
reflexivity.
}

(* cons *)
{
intros n a m IH1 r IH2 i rr' Hnin Hnin' H.
so (row_cons_invert _ _ _ rr') as (m' & r' & ->).
simpsubin H.
injectionc H.
intros Heq1 Heqm.
injectionT Heq1.
intro Heqr.
f_equal.
  {
  apply (IH1 (n + i)); auto.
    {
    contradict Hnin.
    cbn.
    left; auto.
    }

    {
    contradict Hnin'.
    cbn.
    left; auto.
    }
  }

  {
  apply (IH2 i); auto.
    {
    contradict Hnin.
    cbn.
    right; auto.
    }

    {
    contradict Hnin'.
    cbn.
    right; auto.
    }
  }
}
Qed.



(* Thanks to Rick Statman for suggesting this proof. *)
Lemma subst_closed_equiv :
  forall (m n : @term object),
    (forall p, hygiene clo p -> equiv (subst1 p m) (subst1 p n))
    -> equiv m n.
Proof.
intros m n Hequiv.
set (k := markercap m + markercap n).
assert (~ markerin k m) as Hnin.
  {
  intro Hin.
  so (markercap_limit _ _ Hin) as H.
  unfold k in H.
  omega.
  }
assert (~ markerin k n) as Hnin'.
  {
  intro Hin.
  so (markercap_limit _ _ Hin) as H.
  unfold k in H.
  omega.
  }
clearbody k.
exploit (Hequiv (marker k)) as Hequiv'.
  {
  apply hygiene_auto; cbn.
  auto.
  }
so (church_rosser _#3 Hequiv') as (q & Hredm & Hredn).
so (reduces_subst_marker_form k 0 _ _ Hredm) as (m' & Hredm' & Heqm).
so (reduces_subst_marker_form k 0 _ _ Hredn) as (n' & Hredn' & Heqn).
so (eqtrans (eqsymm Heqm) Heqn) as Heq.
exploit (subst_marker_eq k 0 m' n') as H; auto.
  {
  contradict Hnin.
  eapply markerin_reduces; eauto.
  }

  {
  contradict Hnin'.
  eapply markerin_reduces; eauto.
  }
subst n'.
apply (equiv_trans _ _ m').
  {
  apply reduces_equiv; auto.
  }

  {
  apply equiv_symm.
  apply reduces_equiv; auto.
  }
Qed.


Corollary subst_closed_equiv_impl_closed :
  forall (m : @term object),
    (forall n n', hygiene clo n -> hygiene clo n' -> equiv (subst1 n m) (subst1 n' m))
    -> exists m', equiv m m' /\ hygiene (fun j => j <> 0) m'.
Proof.
intros m Hequiv.
exists (subst (dot triv sh1) m).
split.
2:{
  apply (hygiene_subst _ okay).
    {
    apply hygiene_okay.
    }
  intros j _.
  destruct j as [| j]; simpsub.
    {
    apply hygiene_auto; cbn; auto.
    }
    
    {
    apply hygiene_var.
    omega.
    }
  }
apply subst_closed_equiv.
intros n Hcln.
simpsub.
apply Hequiv; auto.
apply hygiene_auto; cbn.
auto.
Qed.


End object.
