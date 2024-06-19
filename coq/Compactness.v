
Require Import Axioms.

Require Import Tactics.
Require Import Equality.
Require Import Relation.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.
Require Import Dynamic.
Require Import Hygiene.
Require Import Reduction.
Require Import Approximation.
Require Import Defined.
Require Import PageCode.
Require Import MapTerm.


Section object.


Variable object : Type.


Lemma bottom_closed : hygiene clo (@bottom object).
Proof.
unfold bottom.
apply hygiene_auto; cbn.
do2 2 split; auto.
  {
  apply theta_closed.
  }
apply hygiene_auto; cbn.
split; auto.
apply hygiene_var.
split.
Qed.


Fixpoint afix (i : nat) (f : @term object) { struct i } : @term object :=
  match i with
  | O => bottom
  | S i' => app f (afix i' f)
  end.


Lemma afix_closed :
  forall i m, hygiene clo m -> hygiene clo (afix i m).
Proof.
intros i m Hcl.
induct i.

(* 0 *)
{
cbn.
apply bottom_closed.
}

(* S *)
{
intros i IH.
cbn.
apply hygiene_auto; cbn; auto.
}
Qed.


Local Ltac prove_hygiene :=
  repeat (first [ apply hygiene_subst1
                | apply hygiene_auto; cbn; repeat2 split; auto]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', theta_closed, bottom_closed, afix_closed;
  try (apply hygiene_var; cbn; auto; done).


Lemma bottom_diverge :
  forall (v : @term object), eval bottom v -> False.
Proof.
intros v Heval.
destruct Heval as (Hsteps & Hval).
assert (star step (@bottom object) bottom) as H.
  {
  unfold bottom.
  eapply star_trans.
    {
    apply theta_fix.
    }
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
revert Hsteps H Hval.
remember bottom as m eqn:Heq in * at 1 2.
clear Heq.
intro Hsteps.
induct Hsteps.

(* refl *)
{
intros m Hsteps Hval.
so (star_plus _#4 Hsteps) as [Heq | (n & Hstep & _)].
  {
  subst m.
  unfold bottom in Hval.
  invert Hval.
  intro H.
  invert H.
  }

  {
  eapply determinism_value; eauto.
  }
}

(* step *)
{
intros m n v Hstep _ IH Hbottom Hval.
so (star_plus _#4 Hbottom) as [Heq | (n' & Hstep' & Hbottom')].
  {
  subst m.
  apply IH; auto.
  so (theta_fix object (lam (var 0))) as Hsteps.
  fold (@bottom object) in Hsteps.
  so (star_plus _#4 Hsteps) as [Heq | (n' & Hstep' & Hsteps')].
    {
    discriminate Heq.
    }
  so (determinism_step _#4 Hstep Hstep').
  subst n'.
  eapply star_trans; eauto.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }

  {
  so (determinism_step _#4 Hstep Hstep').
  subst n'.
  apply IH; auto.
  }
}
Qed.


Lemma bottom_approx :
  forall (m : @term object),
    hygiene clo m
    -> approx bottom m.
Proof.
intros m Hclm.
rewrite <- approx_fixpoint.
do2 2 split; auto using bottom_closed.
intros v Heval.
destruct (bottom_diverge _ Heval).
Qed.


Lemma afix_approx :
  forall m i j,
    hygiene clo m
    -> i <= j
    -> approx (afix i m) (afix j m).
Proof.
intros m i j Hcl.
revert i j.
assert (forall i, approx (afix i m) (afix (S i) m)) as Happrox.
  {
  intro i.
  induct i.
    (* 0 *)
    {
    cbn.
    apply bottom_approx.
    apply hygiene_auto; cbn; auto using bottom_closed.
    }

    (* S *)
    {
    intros i IH.
    change (approx (app m (afix i m)) (app m (afix (S i) m))).
    apply approx_compat; try prove_hygiene.
    apply mc_oper.
    repeat (apply mcr_cons); auto using mcr_nil.
      {
      apply ci_approx_refl.
      }
    apply ci_approx_from_approx; auto.
    }
  }
intros i j Hle.
induct Hle.
  {
  apply approx_refl.
  apply afix_closed; auto.
  }

  {
  intros j _ IH.
  eapply approx_trans; eauto.
  }
Qed.



Lemma afix_fix_approx :
  forall m i,
    hygiene clo m
    -> approx (afix i m) (app theta m).
Proof.
intros m i Hclm.
induct i.

(* 0 *)
{
cbn.
apply bottom_approx.
apply hygiene_auto; cbn; auto using theta_closed.
}

(* S *)
{
intros i IH.
cbn.
apply (approx_trans _ _ (app m (app theta m))).
  {
  apply approx_compat; try prove_hygiene.
  apply mc_oper.
  repeat (apply mcr_cons); auto using mcr_nil.
    {
    apply ci_approx_refl.
    }

    {
    apply ci_approx_from_approx; auto.
    }
  }

  {
  apply anti_steps_approx; try prove_hygiene.
  apply theta_fix.
  }
}
Qed.


Lemma lam_subst_form :
  forall (m1 : @term object) p n,
    lam m1 = subst1 p n
    -> (n = var 0) \/ (exists n1, n = lam n1).
Proof.
intros m1 p n Heq.
destruct n as [i | a th r].
  {
  left.
  destruct i as [| i].
    {
    auto.
    }

    {
    simpsubin Heq.
    discriminate Heq.
    }
  }

  {
  right.
  simpsubin Heq.
  unfold lam in Heq.
  injectionc Heq.
  intros _ Heqth <-.
  injectionT Heqth.
  intros <-.
  so (row_1_invert _ _ r) as (n1 & ->).
  exists n1.
  reflexivity.
  }
Qed.


Lemma app_subst_form :
  forall (m1 m2 : @term object) p n,
    app m1 m2 = subst1 p n
    -> (n = var 0) \/ (exists n1 n2, n = app n1 n2).
Proof.
intros m1 m2 p n Heq.
destruct n as [i | a th r].
  {
  left.
  destruct i as [| i].
    {
    auto.
    }

    {
    simpsubin Heq.
    discriminate Heq.
    }
  }

  {
  right.
  simpsubin Heq.
  unfold app in Heq.
  injectionc Heq.
  intros _ Heqth <-.
  injectionT Heqth.
  intros <-.
  so (row_2_invert _#3 r) as (n1 & n2 & ->).
  exists n1, n2.
  reflexivity.
  }
Qed.


Lemma next_subst_form :
  forall (m1 : @term object) p n,
    next m1 = subst1 p n
    -> (n = var 0) \/ (exists n1, n = next n1).
Proof.
intros m1 p n Heq.
destruct n as [i | a th r].
  {
  left.
  destruct i as [| i].
    {
    auto.
    }

    {
    simpsubin Heq.
    discriminate Heq.
    }
  }

  {
  right.
  simpsubin Heq.
  unfold app in Heq.
  injectionc Heq.
  intros _ Heqth <-.
  injectionT Heqth.
  intros <-.
  so (row_1_invert _#2 r) as (n1 & ->).
  exists n1.
  reflexivity.
  }
Qed.


Lemma prev_subst_form :
  forall (m1 : @term object) p n,
    prev m1 = subst1 p n
    -> (n = var 0) \/ (exists n1, n = prev n1).
Proof.
intros m1 p n Heq.
destruct n as [i | a th r].
  {
  left.
  destruct i as [| i].
    {
    auto.
    }

    {
    simpsubin Heq.
    discriminate Heq.
    }
  }

  {
  right.
  simpsubin Heq.
  unfold app in Heq.
  injectionc Heq.
  intros _ Heqth <-.
  injectionT Heqth.
  intros <-.
  so (row_1_invert _#2 r) as (n1 & ->).
  exists n1.
  reflexivity.
  }
Qed.


Lemma btrue_subst_form :
  forall (p n : @term object),
    btrue = subst1 p n
    -> (n = var 0) \/ (n = btrue).
Proof.
intros p n Heq.
destruct n as [i | a th r].
  {
  left.
  destruct i as [| i].
    {
    auto.
    }

    {
    simpsubin Heq.
    discriminate Heq.
    }
  }

  {
  right.
  simpsubin Heq.
  unfold app in Heq.
  injectionc Heq.
  intros _ Heqth <-.
  injectionT Heqth.
  intros <-.
  cases r.
  reflexivity.
  }
Qed.


Lemma bfalse_subst_form :
  forall (p n : @term object),
    bfalse = subst1 p n
    -> (n = var 0) \/ (n = bfalse).
Proof.
intros p n Heq.
destruct n as [i | a th r].
  {
  left.
  destruct i as [| i].
    {
    auto.
    }

    {
    simpsubin Heq.
    discriminate Heq.
    }
  }

  {
  right.
  simpsubin Heq.
  unfold app in Heq.
  injectionc Heq.
  intros _ Heqth <-.
  injectionT Heqth.
  intros <-.
  cases r.
  reflexivity.
  }
Qed.


Lemma bite_subst_form :
  forall (m1 m2 m3 : @term object) p n,
    bite m1 m2 m3 = subst1 p n
    -> (n = var 0) \/ (exists n1 n2 n3, n = bite n1 n2 n3).
Proof.
intros m1 m2 m3 p n Heq.
destruct n as [i | a th r].
  {
  left.
  destruct i as [| i].
    {
    auto.
    }

    {
    simpsubin Heq.
    discriminate Heq.
    }
  }

  {
  right.
  simpsubin Heq.
  unfold app in Heq.
  injectionc Heq.
  intros _ Heqth <-.
  injectionT Heqth.
  intros <-.
  cases r.
  intros j a n1 r h.
  injection h.
  intros -> ->.
  substrefl h.
  cases r.
  intros j a n2 r h.
  injection h.
  intros -> ->.
  substrefl h.
  cases r.
  intros j a n3 r h.
  injection h.
  intros -> ->.
  substrefl h.
  cases r.
  exists n1, n2, n3.
  reflexivity.
  }
Qed.


Lemma ppair_subst_form :
  forall (m1 m2 : @term object) p n,
    ppair m1 m2 = subst1 p n
    -> (n = var 0) \/ (exists n1 n2, n = ppair n1 n2).
Proof.
intros m1 m2 p n Heq.
destruct n as [i | a th r].
  {
  left.
  destruct i as [| i].
    {
    auto.
    }

    {
    simpsubin Heq.
    discriminate Heq.
    }
  }

  {
  right.
  simpsubin Heq.
  unfold app in Heq.
  injectionc Heq.
  intros _ Heqth <-.
  injectionT Heqth.
  intros <-.
  so (row_2_invert _#3 r) as (n1 & n2 & ->).
  exists n1, n2.
  reflexivity.
  }
Qed.


Lemma ppi1_subst_form :
  forall (m1 : @term object) p n,
    ppi1 m1 = subst1 p n
    -> (n = var 0) \/ (exists n1, n = ppi1 n1).
Proof.
intros m1 p n Heq.
destruct n as [i | a th r].
  {
  left.
  destruct i as [| i].
    {
    auto.
    }

    {
    simpsubin Heq.
    discriminate Heq.
    }
  }

  {
  right.
  simpsubin Heq.
  unfold app in Heq.
  injectionc Heq.
  intros _ Heqth <-.
  injectionT Heqth.
  intros <-.
  so (row_1_invert _#2 r) as (n1 & ->).
  exists n1.
  reflexivity.
  }
Qed.


Lemma ppi2_subst_form :
  forall (m1 : @term object) p n,
    ppi2 m1 = subst1 p n
    -> (n = var 0) \/ (exists n1, n = ppi2 n1).
Proof.
intros m1 p n Heq.
destruct n as [i | a th r].
  {
  left.
  destruct i as [| i].
    {
    auto.
    }

    {
    simpsubin Heq.
    discriminate Heq.
    }
  }

  {
  right.
  simpsubin Heq.
  unfold app in Heq.
  injectionc Heq.
  intros _ Heqth <-.
  injectionT Heqth.
  intros <-.
  so (row_1_invert _#2 r) as (n1 & ->).
  exists n1.
  reflexivity.
  }
Qed.


Lemma seq_subst_form :
  forall (m1 m2 : @term object) p n,
    seq m1 m2 = subst1 p n
    -> (n = var 0) \/ (exists n1 n2, n = seq n1 n2).
Proof.
intros m1 m2 p n Heq.
destruct n as [i | a th r].
  {
  left.
  destruct i as [| i].
    {
    auto.
    }

    {
    simpsubin Heq.
    discriminate Heq.
    }
  }

  {
  right.
  simpsubin Heq.
  unfold app in Heq.
  injectionc Heq.
  intros _ Heqth <-.
  injectionT Heqth.
  intros <-.
  so (row_2_invert _#3 r) as (n1 & n2 & ->).
  exists n1, n2.
  reflexivity.
  }
Qed.


(* The main work for compactness is here. *)
Lemma factor_step :
  forall (t m n : @term object),
    ~ (value t)
    -> step (subst1 t m) n
    -> (exists q,
          forall t', step (subst1 t' m) (subst1 t' q))
       \/
       (exists p,
          m = subst1 (var 0) p
          /\ forall t' t'',
               plus step t t'
               -> plus step (subst (dot t (dot t'' id)) p) (subst (dot t' (dot t'' id)) p)).
Proof.
intros t m n Hnval Hstep.
remember (subst1 t m) as p eqn:Heqp.
revert m Heqp.
induct Hstep.

(* app1 *)
{
intros m1 m1' m2 _ IH m Heq.
so (app_subst_form _#4 Heq) as [-> | (n1 & n2 & Heq')].
  {
  right.
  exists (var 0).
  simpsub.
  split; auto.
  intros t1 t2 Hsteps.
  simpsub.
  auto.
  }
subst m.
simpsubin Heq.
injectionc Heq.
intros -> ->.
so (IH n1 eq_refl) as [(q & Hsteps) | (p & Heq & Hsteps)].
  {
  left.
  exists (app q n2).
  intros t'.
  simpsub.
  apply step_app1; auto.
  }

  {
  right.
  exists (app p (subst sh1 n2)).
  simpsub.
  split.
    {
    f_equal; auto.
    }
  intros t1 t2 Hstepst.
  simpsub.
  apply (plus_map' _ _ (fun z => app z (subst1 t2 n2))); auto using step_app1.
  }
}

(* app2 *)
{
intros m1 m2 m Heq.
so (app_subst_form _#4 Heq) as [-> | (n1 & n2 & Heq')].
  {
  right.
  exists (var 0).
  simpsub.
  split; auto.
  intros t1 t2 Hsteps.
  simpsub.
  auto.
  }
subst m.
simpsubin Heq.
injectionc Heq.
intros -> Heq.
so (lam_subst_form _#3 Heq) as [-> | (n3 & Heq')].
  {
  simpsubin Heq.
  subst t.
  destruct Hnval.
  apply value_lam.
  }
subst n1.
simpsubin Heq.
injectionc Heq.
intros ->.
left.
exists (subst1 n2 n3).
intros t'.
simpsub.
relquest.
  {
  apply step_app2.
  }
simpsub.
reflexivity.
}

(* prev1 *)
{
intros m1 m1' _ IH m Heq.
so (prev_subst_form _#3 Heq) as [-> | (n1 & Heq')].
  {
  right.
  exists (var 0).
  simpsub.
  split; auto.
  intros t1 t2 Hsteps.
  simpsub.
  auto.
  }
subst m.
simpsubin Heq.
injectionc Heq.
intros ->.
so (IH n1 eq_refl) as [(q & Hsteps) | (p & Heq & Hsteps)].
  {
  left.
  exists (prev q).
  intros t'.
  simpsub.
  apply step_prev1; auto.
  }

  {
  right.
  exists (prev p).
  simpsub.
  split.
    {
    f_equal; auto.
    }
  intros t1 t2 Hstepst.
  simpsub.
  apply (plus_map' _ _ prev); auto using step_prev1.
  }
}

(* prev2 *)
{
intros m1 m Heq.
so (prev_subst_form _#3 Heq) as [-> | (n1 & Heq')].
  {
  right.
  exists (var 0).
  simpsub.
  split; auto.
  intros t1 t2 Hsteps.
  simpsub.
  auto.
  }
subst m.
simpsubin Heq.
injectionc Heq.
intros Heq.
so (next_subst_form _#3 Heq) as [-> | (n3 & Heq')].
  {
  simpsubin Heq.
  subst t.
  destruct Hnval.
  apply value_next.
  }
subst n1.
simpsubin Heq.
injectionc Heq.
intros ->.
left.
exists (n3).
intros t'.
simpsub.
apply step_prev2.
}

(* bite1 *)
{
intros m1 m1' m2 m3 _ IH m Heq.
so (bite_subst_form _#5 Heq) as [-> | (n1 & n2 & n3 & Heq')].
  {
  right.
  exists (var 0).
  simpsub.
  split; auto.
  intros t1 t2 Hsteps.
  simpsub.
  auto.
  }
subst m.
simpsubin Heq.
injectionc Heq.
intros -> -> ->.
so (IH n1 eq_refl) as [(q & Hsteps) | (p & Heq & Hsteps)].
  {
  left.
  exists (bite q n2 n3).
  intros t'.
  simpsub.
  apply step_bite1; auto.
  }

  {
  right.
  exists (bite p (subst sh1 n2) (subst sh1 n3)).
  simpsub.
  split.
    {
    f_equal; auto.
    }
  intros t1 t2 Hstepst.
  simpsub.
  apply (plus_map' _ _ (fun z => bite z (subst1 t2 n2) (subst1 t2 n3))); auto using step_bite1.
  }
}

(* bite2 *)
{
intros m1 m2 m Heq.
so (bite_subst_form _#5 Heq) as [-> | (n0 & n2 & n3 & Heq')].
  {
  right.
  exists (var 0).
  simpsub.
  split; auto.
  intros t1 t2 Hsteps.
  simpsub.
  auto.
  }
subst m.
simpsubin Heq.
injectionc Heq.
intros -> -> Heq.
so (btrue_subst_form _ _ Heq) as [-> | ->].
  {
  simpsubin Heq.
  subst t.
  destruct Hnval.
  apply value_btrue.
  }
left.
exists n2.
intros t'.
simpsub.
apply step_bite2.
}

(* bite3 *)
{
intros m1 m2 m Heq.
so (bite_subst_form _#5 Heq) as [-> | (n0 & n2 & n3 & Heq')].
  {
  right.
  exists (var 0).
  simpsub.
  split; auto.
  intros t1 t2 Hsteps.
  simpsub.
  auto.
  }
subst m.
simpsubin Heq.
injectionc Heq.
intros -> -> Heq.
so (bfalse_subst_form _ _ Heq) as [-> | ->].
  {
  simpsubin Heq.
  subst t.
  destruct Hnval.
  apply value_bfalse.
  }
left.
exists n3.
intros t'.
simpsub.
apply step_bite3.
}

(* ppi11 *)
{
intros m1 m1' _ IH m Heq.
so (ppi1_subst_form _#3 Heq) as [-> | (n1 & Heq')].
  {
  right.
  exists (var 0).
  simpsub.
  split; auto.
  intros t1 t2 Hsteps.
  simpsub.
  auto.
  }
subst m.
simpsubin Heq.
injectionc Heq.
intros ->.
so (IH n1 eq_refl) as [(q & Hsteps) | (p & Heq & Hsteps)].
  {
  left.
  exists (ppi1 q).
  intros t'.
  simpsub.
  apply step_ppi11; auto.
  }

  {
  right.
  exists (ppi1 p).
  simpsub.
  split.
    {
    f_equal; auto.
    }
  intros t1 t2 Hstepst.
  simpsub.
  apply (plus_map' _ _ ppi1); auto using step_ppi11.
  }
}

(* ppi12 *)
{
intros m1 m2 m Heq.
so (ppi1_subst_form _#3 Heq) as [-> | (n1 & Heq')].
  {
  right.
  exists (var 0).
  simpsub.
  split; auto.
  intros t1 t2 Hsteps.
  simpsub.
  auto.
  }
subst m.
simpsubin Heq.
injectionc Heq.
intros Heq.
so (ppair_subst_form _#4 Heq) as [-> | (n2 & n3 & Heq')].
  {
  simpsubin Heq.
  subst t.
  destruct Hnval.
  apply value_ppair.
  }
subst n1.
simpsubin Heq.
injectionc Heq.
intros -> ->.
left.
exists (n2).
intros t'.
simpsub.
apply step_ppi12.
}

(* ppi21 *)
{
intros m1 m1' _ IH m Heq.
so (ppi2_subst_form _#3 Heq) as [-> | (n1 & Heq')].
  {
  right.
  exists (var 0).
  simpsub.
  split; auto.
  intros t1 t2 Hsteps.
  simpsub.
  auto.
  }
subst m.
simpsubin Heq.
injectionc Heq.
intros ->.
so (IH n1 eq_refl) as [(q & Hsteps) | (p & Heq & Hsteps)].
  {
  left.
  exists (ppi2 q).
  intros t'.
  simpsub.
  apply step_ppi21; auto.
  }

  {
  right.
  exists (ppi2 p).
  simpsub.
  split.
    {
    f_equal; auto.
    }
  intros t1 t2 Hstepst.
  simpsub.
  apply (plus_map' _ _ ppi2); auto using step_ppi21.
  }
}

(* ppi22 *)
{
intros m1 m2 m Heq.
so (ppi2_subst_form _#3 Heq) as [-> | (n1 & Heq')].
  {
  right.
  exists (var 0).
  simpsub.
  split; auto.
  intros t1 t2 Hsteps.
  simpsub.
  auto.
  }
subst m.
simpsubin Heq.
injectionc Heq.
intros Heq.
so (ppair_subst_form _#4 Heq) as [-> | (n2 & n3 & Heq')].
  {
  simpsubin Heq.
  subst t.
  destruct Hnval.
  apply value_ppair.
  }
subst n1.
simpsubin Heq.
injectionc Heq.
intros -> ->.
left.
exists (n3).
intros t'.
simpsub.
apply step_ppi22.
}

(* seq1 *)
{
intros m1 m1' m2 _ IH m Heq.
so (seq_subst_form _#4 Heq) as [-> | (n1 & n2 & Heq')].
  {
  right.
  exists (var 0).
  simpsub.
  split; auto.
  intros t1 t2 Hsteps.
  simpsub.
  auto.
  }
subst m.
simpsubin Heq.
injectionc Heq.
intros -> ->.
so (IH n1 eq_refl) as [(q & Hsteps) | (p & Heq & Hsteps)].
  {
  left.
  exists (seq q n2).
  intros t'.
  simpsub.
  apply step_seq1; auto.
  }

  {
  right.
  exists (seq p (subst (dot (var 0) (sh 2)) n2)).
  simpsub.
  split.
    {
    f_equal; auto.
    rewrite -> subst_var0_sh1.
    reflexivity.
    }
  intros t1 t2 Hstepst.
  simpsub.
  apply (plus_map' _ _ (fun z => seq z (subst (under 1 (dot t2 id)) n2))); auto using step_seq1.
  }
}

(* seq2 *)
{
intros m1 m2 Hval m Heq.
so (seq_subst_form _#4 Heq) as [-> | (n1 & n2 & Heq')].
  {
  right.
  exists (var 0).
  simpsub.
  split; auto.
  intros t1 t2 Hsteps.
  simpsub.
  auto.
  }
subst m.
simpsubin Heq.
injectionc Heq.
intros -> Heq.
left.
exists (subst1 n1 n2).
intros t'.
simpsub.
relquest.
  {
  apply step_seq2.
  subst m1.
  apply subst_value.
  destruct n1 as [k | a th r].
    {
    destruct k as [| k].
      {
      simpsubin Hval.
      contradiction.
      }

      {
      simpsubin Hval.
      invert Hval.
      }
    }

    {
    simpsubin Hval.
    invert Hval.
    intro H.
    apply value_i; auto.
    }
  }
simpsub.
reflexivity.
}
Qed.



Lemma simulation1 :
  forall f m n,
    hygiene clo f
    -> hygiene (permit clo) m
    -> step (subst1 (app theta f) m) n
    -> exists j q,
         star step n (subst1 (app theta f) q)
         /\ forall k,
              j <= k
              -> approx (subst1 (afix (k - j) f) q) (subst1 (afix k f) m).
Proof.
intros f m n Hclf Hclm Hstep.
exploit (factor_step (app theta f) m n) as H; auto.
  {
  intro H.
  invertc H.
  intro H.
  invert H.
  }
destruct H as [(q & Hfactor) | (p & Heq & Hfactor)].
  {
  exists 0, q.
  split.
    {
    so (Hfactor (app theta f)) as H.
    apply star_refl'.
    exact (determinism_step _#4 Hstep H).
    }

    {
    intros k _.
    replace (k - 0) with k by omega.
    apply anti_steps_approx; try prove_hygiene.
    apply star_one.
    apply Hfactor.
    }
  }

  {
  exists 1.
  exists (subst1 (app f (var 0)) p).
  split.
    {
    simpsub.
    unfold subst1.
    rewrite -> (subst_into_closed _ _ f); auto.
    exploit (Hfactor (app f (app theta f)) (app theta f)) as Hsteps.
      {
      apply theta_fix'.
      }
    subst m.
    simpsubin Hstep.
    destruct Hsteps as (q & Hstep' & Hsteps').
    so (determinism_step _#4 Hstep Hstep').
    subst q.
    auto.
    }

    {
    intros k Hk.
    simpsub.
    unfold subst1.
    rewrite -> (subst_into_closed _ _ f); auto.
    subst m.
    simpsub.
    assert (hygiene (permit (permit clo)) p) as Hclp.
      {
      so (hygiene_subst_invert _#4 Hclm) as H.
      eapply hygiene_weaken; eauto.
      intros i Hi.
      destruct i as [|[|i]]; cbn; auto.
      simpsubin Hi.
      invert Hi.
      intro H'.
      cbn in H'.
      auto.
      }
    apply closed_ci.
      {
      eapply subst_closub; eauto.
      apply closub_dot.
        {
        apply closub_dot.
          {
          intros j H.
          destruct H.
          }
        prove_hygiene.
        }
      prove_hygiene.
      }
      
      {
      eapply subst_closub; eauto.
      apply closub_dot.
        {
        apply closub_dot.
          {
          intros j H.
          destruct H.
          }
        prove_hygiene.
        }
      prove_hygiene.
      }
    apply ci_approx_funct.
      {
      intro i.
      destruct i as [|[|i]].
        {
        simpsub.
        replace k with (S (k - 1)) at 2 by omega.
        cbn.
        apply ci_approx_refl.
        }
        
        {
        simpsub.
        apply ci_from_closed; try prove_hygiene.
        apply afix_approx; try prove_hygiene.
        omega.
        }
        
        {
        simpsub.
        apply ci_approx_refl.
        }
      }

      {
      apply ci_approx_refl.
      }
    }
  }
Qed.

          
Lemma simulation :
  forall f m n,
    hygiene clo f
    -> hygiene (permit clo) m
    -> star step (subst1 (app theta f) m) n
    -> exists j q,
         star step n (subst1 (app theta f) q)
         /\ forall k,
              j <= k
              -> approx (subst1 (afix (k - j) f) q) (subst1 (afix k f) m).
Proof.
intros f m n Hclf Hclm Hsteps.
remember (subst1 (app theta f) m) as p eqn:Heqp.
assert (star step p (subst1 (app theta f) m)) as Hstart.
  {
  apply star_refl'; auto.
  }
clear Heqp.
revert m Hstart Hclm.
induct Hsteps.

(* refl *)
{
intros x m Hstart Hclm.
exists 0, m.
split; auto.
intros k _.
replace (k - 0) with k by omega.
apply approx_refl.
prove_hygiene.
}

(* step *)
{
intros x n z Hstep _ IH m Hstart Hclm.
so (star_plus _#4 Hstart) as [Heq | (y & Hxy & Hstart')].
2:{
  so (determinism_step _#4 Hstep Hxy).
  subst y.
  apply IH; auto.
  }
subst x.
so (simulation1 _#3 Hclf Hclm Hstep) as (j & q & Hsteps & Happrox).
exploit (IH q) as (j' & r & Hsteps' & Happrox'); auto.
  {
  exploit (steps_hygiene _ clo (subst1 (app theta f) m) (subst1 (app theta f) q)) as Hhyg.
    {
    eapply star_step; eauto.
    }

    {
    apply hygiene_subst1; prove_hygiene.
    }
  so (hygiene_subst_invert _#4 Hhyg) as H.
  eapply hygiene_weaken; eauto.
  intros i Hi.
  destruct i as [|i]; cbn; auto.
  simpsubin Hi.
  invert Hi.
  auto.
  }
exists (j + j'), r.
split; auto.
intros k Hk.
eapply approx_trans.
  {
  replace (k - (j + j')) with (k - j - j') by omega.
  apply Happrox'.
  omega.
  }

  {
  apply Happrox.
  omega.
  }
}
Qed.


Lemma compactness :
  forall f m,
    hygiene clo f
    -> hygiene (permit clo) m
    -> converges (subst1 (app theta f) m)
    -> exists i, converges (subst1 (afix i f) m).
Proof.
intros f m Hclf Hclm (v & (Hsteps & Hvalv)).
so (simulation _#3 Hclf Hclm Hsteps) as (j & w & Hsteps' & Happrox).
exists j.
so (star_plus _#4 Hsteps') as [Heq | (x & Hstepsx & _)].
2:{
  destruct (determinism_value _#3 Hvalv Hstepsx).
  }
subst v.
assert (value w) as Hvalw.
  {
  destruct w as [k | a th r].
    {
    destruct k as [| k].
      {
      simpsubin Hvalv.
      invert Hvalv.
      intro H.
      invert H.
      }
  
      {
      simpsubin Hvalv.
      invert Hvalv.
      }
    }

    {
    simpsubin Hvalv.
    invert Hvalv.
    apply value_i.
    }
  }
exploit (Happrox j) as H.
  {
  apply le_refl.
  }
eapply approx_converges; eauto.
eexists.
split; [apply star_refl |].
apply subst_value; auto.
Qed.


End object.


Arguments afix {object}.


Lemma map_afix :
  forall A B (f : A -> B) i m,
    map_term f (afix i m) = afix i (map_term f m).
Proof.
intros A B f i m.
induct i.

(* 0 *)
{
cbn [afix].
unfold bottom.
simpmap.
reflexivity.
}

(* S *)
{
intros i IH.
cbn [afix].
simpmap.
f_equal.
auto.
}
Qed.

Hint Rewrite map_afix : map.
