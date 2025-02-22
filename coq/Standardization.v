
Require Import Coq.Logic.Decidable.

Require Import Tactics.
Require Import Relation.
Require Import Syntax.
Require Import SimpSub.
Require Import Dynamic.
Require Export Reduction.
Require Import Equality.



Lemma steps_app :
  forall object (m1 m1' m2 : @term object),
    star step m1 m1'
    -> star step (app m1 m2) (app m1' m2).
Proof.
intros.
apply (star_map' _ _ (fun z => app z _)); auto using step_app1.
Qed.


Lemma steps_prev :
  forall object (m m' : @term object),
    star step m m'
    -> star step (prev m) (prev m').
Proof.
intros.
apply (star_map' _ _ (fun z => prev z)); auto using step_prev1.
Qed.


Lemma steps_bite :
  forall object (m1 m1' m2 m3 : @term object),
    star step m1 m1'
    -> star step (bite m1 m2 m3) (bite m1' m2 m3).
Proof.
intros.
apply (star_map' _ _ (fun z => bite z _ _)); auto using step_bite1.
Qed.


Lemma steps_ppi1 :
  forall object (m m' : @term object),
    star step m m'
    -> star step (ppi1 m) (ppi1 m').
Proof.
intros.
apply (star_map' _ _ (fun z => ppi1 z)); auto using step_ppi11.
Qed.


Lemma steps_ppi2 :
  forall object (m m' : @term object),
    star step m m'
    -> star step (ppi2 m) (ppi2 m').
Proof.
intros.
apply (star_map' _ _ (fun z => ppi2 z)); auto using step_ppi21.
Qed.


Lemma steps_seq :
  forall object (m1 m1' m2 : @term object),
    star step m1 m1'
    -> star step (seq m1 m2) (seq m1' m2).
Proof.
intros.
apply (star_map' _ _ (fun z => seq z _)); auto using step_seq1.
Qed.


Section object.


Variable object : Type.


Inductive ireduce : term object -> term object -> Prop :=
| ireduce_var {i} :
    ireduce (var i) (var i)

| ireduce_canon {a th r s} :
    canon _ th
    -> reducer r s
    -> ireduce (oper a th r) (oper a th s)

| ireduce_app {m1 n1 m2 n2} :
    ireduce m1 n1
    -> reduce m2 n2
    -> ireduce (app m1 m2) (app n1 n2)

| ireduce_prev {m n} :
    ireduce m n
    -> ireduce (prev m) (prev n)

| ireduce_bite {m1 n1 m2 n2 m3 n3} :
    ireduce m1 n1
    -> reduce m2 n2
    -> reduce m3 n3
    -> ireduce (bite m1 m2 m3) (bite n1 n2 n3)

| ireduce_ppi1 {m n} :
    ireduce m n
    -> ireduce (ppi1 m) (ppi1 n)

| ireduce_ppi2 {m n} :
    ireduce m n
    -> ireduce (ppi2 m) (ppi2 n)

| ireduce_seq {m1 n1 m2 n2} :
    ireduce m1 n1
    -> reduce m2 n2
    -> ireduce (seq m1 m2) (seq n1 n2)

| ireduce_marker {x} :
    ireduce (marker x) (marker x)
.


Lemma ireduce_impl_mc_reduce :
  forall m n, ireduce m n -> mc reduce m n.
Proof.
intros m n H.
induct H; eauto using mc_var, mc_oper, reducer_mcr, reduce_compat, mc_app, mc_prev, mc_bite, mc_ppi1, mc_ppi2, mc_seq, mcr_nil.
Qed.


Lemma ireduce_impl_reduce :
  forall m n, ireduce m n -> reduce m n.
Proof.
intros m n H.
apply reduce_compat.
apply ireduce_impl_mc_reduce; auto.
Qed.


Lemma ireduce_id : forall {m}, ireduce m m.
Proof.
intro m.
pattern m.
apply term_row_rect.

(* var *)
{
intro i.
apply ireduce_var.
}

(* oper *)
{
intros a th r IH.
revert r IH.
cases th; try (intros; apply ireduce_canon; auto using reducer_id with dynamic; done).
  (* app *)
  {
  intros r IH.
  so (row_invert_auto _ _ r) as H; cbn in H.
  destruct H as (m1 & m2 & ->).
  fold (app m1 m2) in *.
  invertc IH.
  intros Hm1 Hr.
  invertc Hr.
  intros Hm2 _.
  apply ireduce_app; auto using ireduce_impl_reduce.
  }

  (* prev *)
  {
  intros r IH.
  so (row_invert_auto _ _ r) as H; cbn in H.
  destruct H as (m1 & ->).
  invertc IH.
  intros Hm1 _.
  apply ireduce_prev; auto using ireduce_impl_reduce.
  }

  (* bite *)
  {
  intros r IH.
  so (row_invert_auto _ _ r) as H; cbn in H.
  destruct H as (m1 & m2 & m3 & ->).
  fold (bite m1 m2 m3) in *.
  invertc IH.
  intros Hm1 IH.
  invertc IH.
  intros Hm2 IH.
  invertc IH.
  intros Hm3 _.
  apply ireduce_bite; auto using ireduce_impl_reduce.
  }

  (* ppi1 *)
  {
  intros r IH.
  so (row_invert_auto _ _ r) as H; cbn in H.
  destruct H as (m1 & ->).
  invertc IH.
  intros Hm1 _.
  apply ireduce_ppi1; auto using ireduce_impl_reduce.
  }

  (* ppi2 *)
  {
  intros r IH.
  so (row_invert_auto _ _ r) as H; cbn in H.
  destruct H as (m1 & ->).
  invertc IH.
  intros Hm1 _.
  apply ireduce_ppi2; auto using ireduce_impl_reduce.
  }

  (* seq *)
  {
  intros r IH.
  so (row_invert_auto _ _ r) as H; cbn in H.
  destruct H as (m1 & m2 & ->).
  fold (seq m1 m2) in *.
  invertc IH.
  intros Hm1 Hr.
  invertc Hr.
  intros Hm2 _.
  apply ireduce_seq; auto using ireduce_impl_reduce.
  }

  (* marker *)
  {
  intros x r Hall.
  so (row_invert_auto _ _ r) as H; cbn in H.
  subst r.
  fold (@marker object x).
  apply ireduce_marker.
  }
}
Qed.


Definition sreduce (m n : @term object) : Prop
  :=
  reduce m n
    /\ exists p,
         star step m p
         /\ ireduce p n.


Lemma sreduce_id :
  forall m, sreduce m m.
Proof.
intros m.
split; auto using reduce_id.
exists m.
split; auto using star_refl.
apply ireduce_id.
Qed.


Lemma sreduce_impl_reduce :
  forall m n, sreduce m n -> reduce m n.
Proof.
intros m n H.
destruct H; auto.
Qed.


Lemma sreduce_extend :
  forall m n p,
    reduce m p
    -> step m n
    -> sreduce n p
    -> sreduce m p.
Proof.
intros m n p Hmp Hmn Hnp.
split; auto.
destruct Hnp as (_ & q & Hnq & Hqp).
exists q.
split; auto.
eapply star_step; eauto.
Qed.


Lemma sreduce_app :
  forall m m' n n',
    sreduce m m'
    -> reduce n n'
    -> sreduce (app m n) (app m' n').
Proof.
intros m m' n n' Hm Hn.
destruct Hm as (Hm & p & Hmp & Hpm).
split.
  {
  apply reduce_compat.
  apply mc_app; auto using reduce_id.
  }
exists (app p n).
split.
  {
  apply steps_app; auto.
  }

  {
  apply ireduce_app; auto.
  }
Qed.


Lemma sreduce_prev :
  forall m m',
    sreduce m m'
    -> sreduce (prev m) (prev m').
Proof.
intros m m' Hm.
destruct Hm as (Hm & p & Hmp & Hpm).
split.
  {
  apply reduce_compat.
  apply mc_prev; auto using reduce_id.
  }
exists (prev p).
split.
  {
  apply steps_prev; auto.
  }

  {
  apply ireduce_prev; auto.
  }
Qed.


Lemma sreduce_bite :
  forall m m' n n' p p',
    sreduce m m'
    -> reduce n n'
    -> reduce p p'
    -> sreduce (bite m n p) (bite m' n' p').
Proof.
intros m m' n n' q q' Hm Hn Hq.
destruct Hm as (Hm & p & Hmp & Hpm).
split.
  {
  apply reduce_compat.
  apply mc_bite; auto using reduce_id.
  }
exists (bite p n q).
split.
  {
  apply steps_bite; auto.
  }

  {
  apply ireduce_bite; auto.
  }
Qed.


Lemma sreduce_ppi1 :
  forall m m',
    sreduce m m'
    -> sreduce (ppi1 m) (ppi1 m').
Proof.
intros m m' Hm.
destruct Hm as (Hm & p & Hmp & Hpm).
split.
  {
  apply reduce_compat.
  apply mc_ppi1; auto using reduce_id.
  }
exists (ppi1 p).
split.
  {
  apply steps_ppi1; auto.
  }

  {
  apply ireduce_ppi1; auto.
  }
Qed.


Lemma sreduce_ppi2 :
  forall m m',
    sreduce m m'
    -> sreduce (ppi2 m) (ppi2 m').
Proof.
intros m m' Hm.
destruct Hm as (Hm & p & Hmp & Hpm).
split.
  {
  apply reduce_compat.
  apply mc_ppi2; auto using reduce_id.
  }
exists (ppi2 p).
split.
  {
  apply steps_ppi2; auto.
  }

  {
  apply ireduce_ppi2; auto.
  }
Qed.


Lemma sreduce_seq :
  forall m m' n n',
    sreduce m m'
    -> reduce n n'
    -> sreduce (seq m n) (seq m' n').
Proof.
intros m m' n n' Hm Hn.
destruct Hm as (Hm & p & Hmp & Hpm).
split.
  {
  apply reduce_compat.
  apply mc_seq; auto using reduce_id.
  }
exists (seq p n).
split.
  {
  apply steps_seq; auto.
  }

  {
  apply ireduce_seq; auto.
  }
Qed.


Lemma canon_dec :
  forall a (th : @operator object a),
    decidable (canon _ th).
Proof.
intros a th.
cases th;
try (left; auto using canon; done);
try (right; intro H; invert H; done).
Qed.


Lemma ireduce_sreduce_funct :
  forall m m' n n',
    ireduce m m'
    -> sreduce n n'
    -> sreduce (subst1 n m) (subst1 n' m').
Proof.
intros m m' n n' Hm Hn.
revert m' n n' Hm Hn.
pattern m.
apply term_row_rect.

(* var *)
{
intros i m' n n' Hm Hn.
invertc Hm.
intros <-.
destruct i as [| i].
  {
  simpsub.
  auto.
  }

  {
  simpsub.
  apply sreduce_id.
  }
}
(* oper *)
{
intros a th r IH m' n n' Hm Hn.
invert (ireduce_impl_mc_reduce _ _ Hm).
intros r' Hr <-.
so (canon_dec _ th) as [Hcanon | Hncanon].
  {
  split.
    {
    apply reduce_funct1; auto using sreduce_impl_reduce.
    apply reduce_compat.
    apply mc_oper; auto.
    }
  exists (subst1 n (oper a th r)).
  split; auto using star_refl.
  simpsub.
  apply ireduce_canon; auto.
  apply reducer_funct1; auto using sreduce_impl_reduce.
  apply mcr_reducer; auto.
  }
clear Hr.
revert r r' Hm IH Hncanon.
cases th; try (intros; destruct Hncanon; auto with dynamic; done).
  (* app *)
  {
  intros r r' Hm IH _.
  so (row_invert_auto _ _ r) as (m1 & m2 & ->).
  so (row_invert_auto _ _ r') as (m1' & m2' & ->).
  simpsub.
  fold (app (subst1 n m1) (subst1 n m2)) in *.
  fold (app (subst1 n' m1') (subst1 n' m2')) in *.
  invertc IH.
  intros IH1 IH.
  invertc IH.
  intros IH2 _.
  invertc Hm.
    {
    intros H  _.
    invert H.
    }
  intros Hm1 Hm2.
  apply sreduce_app; auto.
  apply reduce_funct1; auto using sreduce_impl_reduce.
  }

  (* prev *)
  {
  intros r r' Hm IH _.
  so (row_invert_auto _ _ r) as (m1 & ->).
  so (row_invert_auto _ _ r') as (m1' & ->).
  simpsub.
  fold (prev (subst1 n m1)) in *.
  fold (prev (subst1 n' m1')) in *.
  invertc IH.
  intros IH1 _.
  invertc Hm.
    {
    intros H  _.
    invert H.
    }
  intros Hm1.
  apply sreduce_prev; auto.
  }

  (* bite *)
  {
  intros r r' Hm IH _.
  so (row_invert_auto _ _ r) as (m1 & m2 & m3 & ->).
  so (row_invert_auto _ _ r') as (m1' & m2' & m3' & ->).
  simpsub.
  fold (bite (subst1 n m1) (subst1 n m2) (subst1 n m3)) in *.
  fold (bite (subst1 n' m1') (subst1 n' m2') (subst1 n' m3')) in *.
  invertc IH.
  intros IH1 IH.
  invertc IH.
  intros IH2 IH.
  invertc IH.
  intros IH3 _.
  invertc Hm.
    {
    intros H  _.
    invert H.
    }
  intros Hm1 Hm2 Hm3.
  apply sreduce_bite; eauto using reduce_funct1, sreduce_impl_reduce.
  }

  (* ppi1 *)
  {
  intros r r' Hm IH _.
  so (row_invert_auto _ _ r) as (m1 & ->).
  so (row_invert_auto _ _ r') as (m1' & ->).
  simpsub.
  fold (ppi1 (subst1 n m1)) in *.
  fold (ppi1 (subst1 n' m1')) in *.
  invertc IH.
  intros IH1 _.
  invertc Hm.
    {
    intros H  _.
    invert H.
    }
  intros Hm1.
  apply sreduce_ppi1; auto.
  }

  (* ppi2 *)
  {
  intros r r' Hm IH _.
  so (row_invert_auto _ _ r) as (m1 & ->).
  so (row_invert_auto _ _ r') as (m1' & ->).
  simpsub.
  fold (ppi2 (subst1 n m1)) in *.
  fold (ppi2 (subst1 n' m1')) in *.
  invertc IH.
  intros IH1 _.
  invertc Hm.
    {
    intros H  _.
    invert H.
    }
  intros Hm1.
  apply sreduce_ppi2; auto.
  }

  (* seq *)
  {
  intros r r' Hm IH _.
  so (row_invert_auto _ _ r) as (m1 & m2 & ->).
  so (row_invert_auto _ _ r') as (m1' & m2' & ->).
  simpsub.
  fold (seq (subst1 n m1) (subst (dot (var 0) (dot (subst sh1 n) sh1)) m2)).
  fold (seq (subst1 n' m1') (subst (dot (var 0) (dot (subst sh1 n') sh1)) m2')).
  invertc IH.
  intros IH1 IH.
  invertc IH.
  intros IH2 _.
  invertc Hm.
    {
    intros H  _.
    invert H.
    }
  intros Hm1 Hm2.
  apply sreduce_seq; auto.
  apply (reduce_funct1_under _ 1); auto using sreduce_impl_reduce.
  }

  (* marker *)
  {
  intros x r r' Hr IH Hncanon.
  so (row_invert_auto _ _ r) as H; cbn in H.
  subst r.
  so (row_invert_auto _ _ r') as H; cbn in H.
  subst r'.
  fold (@marker object x).
  simpsub.
  apply sreduce_id.
  }
}
Qed.


Lemma ireduce_impl_sreduce :
  forall m m', ireduce m m' -> sreduce m m'.
Proof.
intros m m' Hm.
split.
  {
  apply reduce_compat.
  apply ireduce_impl_mc_reduce; auto.
  }
exists m; auto using star_refl.
Qed.


Lemma sreduce_funct :
  forall m m' n n',
    sreduce m m'
    -> sreduce n n'
    -> sreduce (subst1 n m) (subst1 n' m').
Proof.
intros m m' n n' Hm Hn.
destruct Hm as (Hm & p & Hmp & Hpm).
split.
  {
  apply reduce_funct1; auto using sreduce_impl_reduce.
  }
so (ireduce_sreduce_funct _#4 Hpm Hn) as Hnpm.
destruct Hnpm as (_ & q & Hnpq & Hqnp).
exists q.
split; auto.
eapply star_trans; eauto.
apply subst_steps; auto.
Qed.


Lemma reduce_impl_sreduce :
  forall m n, reduce m n -> sreduce m n.
Proof.
exploit (reduce_mut_ind object
           (fun m n => sreduce m n)
           (fun a r s => mcr sreduce a r s)).

(* var *)
{
intro i.
apply sreduce_id.
}

(* oper *)
{
intros a th r s Hrs IH.
so (canon_dec _ th) as [Hcanon | Hncanon].
  {
  split.
    {
    apply reduce_oper; auto.
    }
  exists (oper a th r).
  split; auto using star_refl.
  apply ireduce_canon; auto.
  }
revert r s Hrs IH Hncanon.
cases th; try (intros; destruct Hncanon; auto with dynamic; done).
  (* app *)
  {
  intros r s Hrs IH Hncanon.
  so (row_invert_auto _ _ r) as (m1 & m2 & ->).
  so (row_invert_auto _ _ s) as (n1 & n2 & ->).
  fold (app m1 m2) in *.
  fold (app n1 n2) in *.
  invertc IH.
  intros IH1 IH.
  invertc IH.
  intros IH2 _.
  apply sreduce_app; auto.
  apply sreduce_impl_reduce; auto.
  }

  (* prev *)
  {
  intros r s Hrs IH Hncanon.
  so (row_invert_auto _ _ r) as (m1 & ->).
  so (row_invert_auto _ _ s) as (n1 & ->).
  fold (prev m1) in *.
  fold (prev n1) in *.
  invertc IH.
  intros IH1 _.
  apply sreduce_prev; auto.
  }

  (* bite *)
  {
  intros r s Hrs IH Hncanon.
  so (row_invert_auto _ _ r) as (m1 & m2 & m3 & ->).
  so (row_invert_auto _ _ s) as (n1 & n2 & n3 & ->).
  fold (bite m1 m2 m3) in *.
  fold (bite n1 n2 n3) in *.
  invertc IH.
  intros IH1 IH.
  invertc IH.
  intros IH2 IH.
  invertc IH.
  intros IH3 _.
  apply sreduce_bite; auto using sreduce_impl_reduce.
  }

  (* ppi1 *)
  {
  intros r s Hrs IH Hncanon.
  so (row_invert_auto _ _ r) as (m1 & ->).
  so (row_invert_auto _ _ s) as (n1 & ->).
  fold (ppi1 m1) in *.
  fold (ppi1 n1) in *.
  invertc IH.
  intros IH1 _.
  apply sreduce_ppi1; auto.
  }

  (* ppi2 *)
  {
  intros r s Hrs IH Hncanon.
  so (row_invert_auto _ _ r) as (m1 & ->).
  so (row_invert_auto _ _ s) as (n1 & ->).
  fold (ppi2 m1) in *.
  fold (ppi2 n1) in *.
  invertc IH.
  intros IH1 _.
  apply sreduce_ppi2; auto.
  }

  (* seq *)
  {
  intros r s Hrs IH _.
  so (row_invert_auto _ _ r) as (m1 & m2 & ->).
  so (row_invert_auto _ _ s) as (n1 & n2 & ->).
  fold (seq m1 m2) in *.
  fold (seq n1 n2) in *.
  invertc IH.
  intros IH1 IH.
  invertc IH.
  intros IH2 _.
  apply sreduce_seq; auto.
  apply sreduce_impl_reduce; auto.
  }

  (* marker *)
  {
  intros x r r' _ _ _.
  so (row_invert_auto _ _ r) as H; cbn in H.
  subst r.
  so (row_invert_auto _ _ r') as H; cbn in H.
  subst r'.
  fold (@marker object x).
  apply sreduce_id.
  }
}

(* app_beta *)
{
intros m m' n n' Hm IH1 Hn IH2.
so (sreduce_funct _#4 IH1 IH2) as Hmn.
eapply sreduce_extend; eauto using step_app2.
apply reduce_app_beta; auto.
}

(* prev_beta *)
{
intros m m' Hm IH1.
eapply sreduce_extend; eauto using step_prev2.
apply reduce_prev_beta; auto.
}

(* bite_beta1 *)
{
intros m m' p Hm IH.
eapply sreduce_extend; eauto using step_bite2.
apply reduce_bite_beta1; auto.
}

(* bite_beta2 *)
{
intros m m' p Hm IH.
eapply sreduce_extend; eauto using step_bite3.
apply reduce_bite_beta2; auto.
}

(* ppi1_beta *)
{
intros m m' Hm IH1.
eapply sreduce_extend; eauto using step_ppi12.
apply reduce_ppi1_beta; auto.
}

(* ppi2_beta *)
{
intros m m' Hm IH1.
eapply sreduce_extend; eauto using step_ppi22.
apply reduce_ppi2_beta; auto.
}

(* seq_beta *)
{
intros m m' n n' Hval Hm IH1 Hn IH2.
so (sreduce_funct _#4 IH2 IH1) as Hmn.
eapply sreduce_extend; eauto using step_seq2.
apply reduce_seq_beta; auto.
}

(* nil *)
{
apply mcr_nil.
}

(* cons *)
{
intros i a m n r s _ IH1 _ IH2.
apply mcr_cons; auto.
}

(* wrapup *)
{
auto.
}
Qed.


Lemma postponement :
  forall (m n p : @term object),
    ireduce m n
    -> step n p
    -> exists q,
         step m q
         /\ reduce q p.
Proof.
intros m n p Hmn Hnp.
revert n p Hmn Hnp.
pattern m.
apply term_row_rect.

(* var *)
{
intros i n p Hmn Hnp.
invert Hmn.
intros <-.
invert Hnp.
}

(* oper *)
{
intros a th r IH n p Hmn Hnp.
invert Hmn.
  (* canon *)
  {
  intros s Hcanon Hrs <-.
  destruct (determinism_value _ _ _ (value_i _#4 Hcanon) Hnp).
  }

  (* app *)
  {
  intros m1 n1 m2 n2 H1 H2 <- Heq Heq' <-.
  injectionT Heq.
  intros <-.
  injectionT Heq'.
  intros <-.
  fold (app m1 m2) in *.
  fold (app n1 n2) in *.
  invertc IH.
  intros IH1 _.
  invert Hnp.
    {
    intros p1 Hstep <-.
    so (IH1 _ _ H1 Hstep) as (q & Hstep' & Hqp).
    exists (app q m2).
    split.
      {
      apply step_app1; auto.
      }
    
      {
      apply reduce_compat.
      apply mc_app; auto.
      }
    }

    {
    intros p1 <- <-.
    invertc Hmn.
      {
      intros H _ _; invert H.
      }
    intros Hmn1 Hmn2.
    destruct m1 as [i | a th r].
      {
      invert Hmn1.
      }
    invertc Hmn1.
    intros _ r' Hr -> Heq Heq'.
    injectionT Heq.
    intros ->.
    injectionT Heq'.
    intros ->.
    so (row_invert_auto _ _ r) as H; cbn in H.
    destruct H as (m3 & ->).
    fold (lam m3) in *.
    invertc Hr.
    intros Hm3p1 _.
    exists (subst1 m2 m3).
    split; auto using step_app2.
    apply reduce_funct1; auto.
    }
  }

  (* prev *)
  {
  intros m1 n1 H1 <- Heq Heq' <-.
  injectionT Heq.
  intros <-.
  injectionT Heq'.
  intros <-.
  fold (prev m1) in *.
  fold (prev n1) in *.
  invertc IH.
  intros IH1 _.
  invert Hnp.
    {
    intros p1 Hstep <-.
    so (IH1 _ _ H1 Hstep) as (q & Hstep' & Hqp).
    exists (prev q).
    split.
      {
      apply step_prev1; auto.
      }
    
      {
      apply reduce_compat.
      apply mc_prev; auto.
      }
    }

    {
    intros <-.
    invertc Hmn.
      {
      intros H _ _; invert H.
      }
    intros Hmn1.
    destruct m1 as [i | a th r].
      {
      invert Hmn1.
      }
    invertc Hmn1.
    intros _ r' Hr -> Heq Heq'.
    injectionT Heq.
    intros ->.
    injectionT Heq'.
    intros ->.
    so (row_invert_auto _ _ r) as H; cbn in H.
    destruct H as (m3 & ->).
    fold (next m3) in *.
    invertc Hr.
    intros Hm3p1 _.
    exists m3.
    split; auto using step_app2.
    apply step_prev2.
    }
  }

  (* bite *)
  {
  intros m1 n1 m2 n2 m3 n3 H1 H2 H3 <- Heq Heq' <-.
  injectionT Heq.
  intros <-.
  injectionT Heq'.
  intros <-.
  fold (bite m1 m2 m3) in *.
  fold (bite n1 n2 n3) in *.
  invertc IH.
  intros IH1 _.
  invert Hnp.
    {
    intros p1 Hstep <-.
    so (IH1 _ _ H1 Hstep) as (q & Hstep' & Hqp).
    exists (bite q m2 m3).
    split.
      {
      apply step_bite1; auto.
      }
    
      {
      apply reduce_compat.
      apply mc_bite; auto.
      }
    }

    {
    intros <- <-.
    invertc Hmn.
      {
      intros H _ _; invert H.
      }
    intros Hmn1 Hmn2 Hmn3.
    destruct m1 as [i | a th r].
      {
      invert Hmn1.
      }
    invertc Hmn1.
    intros _ r' Hr -> Heq Heq'.
    injectionT Heq.
    intros ->.
    injectionT Heq'.
    intros ->.
    so (row_nil_invert _ r); subst r.
    fold (@btrue object) in *.
    exists m2.
    split; auto using step_bite2.
    }

    {
    intros <- <-.
    invertc Hmn.
      {
      intros H _ _; invert H.
      }
    intros Hmn1 Hmn2 Hmn3.
    destruct m1 as [i | a th r].
      {
      invert Hmn1.
      }
    invertc Hmn1.
    intros _ r' Hr -> Heq Heq'.
    injectionT Heq.
    intros ->.
    injectionT Heq'.
    intros ->.
    so (row_nil_invert _ r); subst r.
    fold (@bfalse object) in *.
    exists m3.
    split; auto using step_bite3.
    }
  }

  (* ppi1 *)
  {
  intros m1 n1 H1 <- Heq Heq' <-.
  injectionT Heq.
  intros <-.
  injectionT Heq'.
  intros <-.
  fold (ppi1 m1) in *.
  fold (ppi1 n1) in *.
  invertc IH.
  intros IH1 _.
  invert Hnp.
    {
    intros p1 Hstep <-.
    so (IH1 _ _ H1 Hstep) as (q & Hstep' & Hqp).
    exists (ppi1 q).
    split.
      {
      apply step_ppi11; auto.
      }
    
      {
      apply reduce_compat.
      apply mc_ppi1; auto.
      }
    }

    {
    intros p1 <-.
    invertc Hmn.
      {
      intros H _ _; invert H.
      }
    intros Hmn1.
    destruct m1 as [i | a th r].
      {
      invert Hmn1.
      }
    invertc Hmn1.
    intros _ r' Hr -> Heq Heq'.
    injectionT Heq.
    intros ->.
    injectionT Heq'.
    intros ->.
    so (row_invert_auto _ _ r) as H; cbn in H.
    destruct H as (m3 & m4 & ->).
    fold (ppair m3 m4) in *.
    invertc Hr.
    intros Hm3p1 _.
    exists m3.
    split; auto using step_ppi12.
    }
  }

  (* ppi2 *)
  {
  intros m1 n1 H1 <- Heq Heq' <-.
  injectionT Heq.
  intros <-.
  injectionT Heq'.
  intros <-.
  fold (ppi2 m1) in *.
  fold (ppi2 n1) in *.
  invertc IH.
  intros IH1 _.
  invert Hnp.
    {
    intros p1 Hstep <-.
    so (IH1 _ _ H1 Hstep) as (q & Hstep' & Hqp).
    exists (ppi2 q).
    split.
      {
      apply step_ppi21; auto.
      }
    
      {
      apply reduce_compat.
      apply mc_ppi2; auto.
      }
    }

    {
    intros p1 <-.
    invertc Hmn.
      {
      intros H _ _; invert H.
      }
    intros Hmn1.
    destruct m1 as [i | a th r].
      {
      invert Hmn1.
      }
    invertc Hmn1.
    intros _ r' Hr -> Heq Heq'.
    injectionT Heq.
    intros ->.
    injectionT Heq'.
    intros ->.
    so (row_invert_auto _ _ r) as H; cbn in H.
    destruct H as (m3 & m4 & ->).
    fold (ppair m3 m4) in *.
    invertc Hr.
    intros _ Hr.
    invertc Hr.
    intros Hm4p.
    exists m4.
    split; auto using step_ppi22.
    }
  }

  (* seq *)
  {
  intros m1 n1 m2 n2 H1 H2 <- Heq Heq' <-.
  injectionT Heq.
  intros <-.
  injectionT Heq'.
  intros <-.
  fold (seq m1 m2) in *.
  fold (seq n1 n2) in *.
  invertc IH.
  intros IH1 _.
  invert Hnp.
    {
    intros p1 Hstep <-.
    so (IH1 _ _ H1 Hstep) as (q & Hstep' & Hqp).
    exists (seq q m2).
    split.
      {
      apply step_seq1; auto.
      }
    
      {
      apply reduce_compat.
      apply mc_seq; auto.
      }
    }

    {
    intros Hval <-.
    invertc Hmn.
      {
      intros H _ _; invert H.
      }
    intros Hmn1 Hmn2.
    exists (subst1 m1 m2).
    split.
      {
      apply step_seq2.
      invert H1; intros; subst; try (invert Hval; intro H; invert H; done).
      invert Hval.
      intro.
      apply value_i; auto.
      }

      {
      apply reduce_funct1; auto.
      apply ireduce_impl_reduce; auto.
      }
    }
  }

  (* marker *)
  {
  intros x <- Heq1 Heq2 <-.
  injectionT Heq1.
  intros <-.
  injectionT Heq2.
  intros <-.
  fold (@marker object x).
  exists p.
  split; auto.
  apply reduce_id.
  }
} 
Qed.


Lemma postponement' :
  forall (m n p : @term object),
    ireduce m n
    -> step n p
    -> exists q,
         star step m q
         /\ ireduce q p.
Proof.
intros m n p Hmn Hnp.
so (postponement _#3 Hmn Hnp) as (q & Hmq & Hqp).
so (reduce_impl_sreduce _ _ Hqp) as (_ & r & Hqr & Hrp).
exists r.
split; auto.
eapply star_step; eauto.
Qed.


Lemma bifurcation :
  forall (m n : @term object),
    star reduce m n
    -> exists p,
         star step m p
         /\ star ireduce p n.
Proof.
intros m n H.
induct H.

(* refl *)
{
intro m.
exists m.
split; auto using star_refl, ireduce_id.
}

(* step *)
{
intros m n p Hmn _ IH.
destruct IH as (q & Hnq & Hqp).
so (reduce_impl_sreduce _ _ Hmn) as (_ & r & Hmr & Hrn).
cut (exists s, star step r s /\ star ireduce s q).
  {
  intros (s & Hrs & Hsq).
  exists s.
  split; eauto using star_trans.
  }
clear m p Hmn Hmr Hqp.
revert r Hrn.
induct Hnq.
  (* refl *)
  {
  intros n r Hrn.
  exists r.
  split; auto using star_one, star_refl.
  }

  (* step *)
  {
  intros n s q Hns _ IH r Hrn.
  so (postponement' _#3 Hrn Hns) as (t & Hrt & Hts).
  so (IH _ Hts) as (u & Htu & Huq).
  exists u.
  split; eauto using star_trans.
  }
}
Qed.


Lemma standardization :
  forall (m n : @term object),
    star reduce m n
    -> exists p,
         star step m p
         /\ star (mc reduce) p n.
Proof.
intros m n Hmn.
so (bifurcation _ _ Hmn) as (p & Hmp & Hpn).
exists p.
split; auto.
refine (star_mono _#3 _ _ _ Hpn).
apply ireduce_impl_mc_reduce.
Qed.


End object.
