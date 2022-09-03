
Require Import Axioms.
Require Import Tactics.
Require Import Relation.
Require Import Equality.
Require Export Subst.
Require Import SimpSub.
Require Import Dynamic.
Require Import Reduction.


Section object.


Arguments operator {object}.
Arguments term {object}.
Arguments row {object}.


Variable object : Type.


(* General hygiene *)


Definition hpred := nat -> Prop.


Inductive hygiene : hpred -> @term object -> Prop :=
| hygiene_var :
    forall (P : nat -> Prop) i,
      P i
      -> hygiene P (var i)

| hygiene_oper :
    forall P a th r,
      hygiene_row P a r
      -> hygiene P (oper a th r)

with hygiene_row : hpred -> forall a, row a -> Prop :=
| hygiene_nil :
    forall P,
      hygiene_row P nil rw_nil 

| hygiene_cons :
    forall P i a m r,
      hygiene (fun j => j < i \/ (j >= i /\ P (j - i))) m
      -> hygiene_row P a r
      -> hygiene_row P (cons i a) (rw_cons i a m r)
.


Scheme hygiene_mut_ind := Minimality for hygiene Sort Prop
with   hygiene_row_mut_ind := Minimality for hygiene_row Sort Prop.
Combined Scheme hygiene_term_and_row_ind from hygiene_mut_ind, hygiene_row_mut_ind.


Definition hincl (P Q : hpred) : Prop :=
  forall i, P i -> Q i.


Lemma hincl_refl :
  forall P, hincl P P.
Proof.
intros P i H; auto.
Qed.


Lemma hincl_trans :
  forall P Q R, hincl P Q -> hincl Q R -> hincl P R.
Proof.
intros P Q R H1 H2.
intros i H; auto.
Qed.


Lemma hygiene_weaken_term_and_row :
  (forall (P Q : hpred) m,
     hincl P Q
     -> hygiene P m
     -> hygiene Q m)
  /\
  (forall (P Q : hpred) a r,
     hincl P Q
     -> hygiene_row P a r
     -> hygiene_row Q a r).
Proof.
exploit
  (hygiene_term_and_row_ind
     (fun P m =>
        forall (Q : hpred),
          (forall i, P i -> Q i)
          -> hygiene Q m)
     (fun P a r =>
        forall (Q : hpred),
          (forall i, P i -> Q i)
          -> hygiene_row Q a r)) as H; eauto using hygiene, hygiene_row.

(* cons *)
{
intros P j a m r _ IH1 _ IH2 Q HPQ.
apply hygiene_cons; auto.
apply IH1.
intros i H.
destruct H as [| H]; auto.
right.
destruct H; auto.
}

(* epilogue *)
{
destruct H; split; intros; eauto.
}
Qed.


Lemma hygiene_weaken :
  forall (P Q : nat -> Prop) m,
    hincl P Q
    -> hygiene P m
    -> hygiene Q m.
Proof.
exact (hygiene_weaken_term_and_row andel).
Qed.


Lemma hygiene_row_weaken :
  forall (P Q : hpred) a r,
    hincl P Q
    -> hygiene_row P a r
    -> hygiene_row Q a r.
Proof.
exact (hygiene_weaken_term_and_row ander).
Qed.


Lemma hygiene_conjoin :
  forall P Q m,
    hygiene P m
    -> hygiene Q m
    -> hygiene (fun i => P i /\ Q i) m.
Proof.
intros P Q m HPm HQm.
revert Q HQm.
induct HPm
  using (fun X => hygiene_mut_ind X
           (fun P a r =>
              forall Q,
                hygiene_row Q a r
                -> hygiene_row (fun i => P i /\ Q i) a r)).

(* var *)
{
intros P i HPi Q HQvar.
invert HQvar.
intros HQi.
apply hygiene_var; auto.
}

(* oper *)
{
intros P a th r _ IH Q HQm.
invert HQm.
intros HQr.
apply hygiene_oper.
apply IH; auto.
}

(* nil *)
{
intros P Q H.
apply hygiene_nil.
}

(* cons *)
{
intros P i a m r _ IH1 _ IH2 Q HQmr.
invert HQmr.
intros HQm HQr.
apply hygiene_cons; auto.
refine (hygiene_weaken _#3 _ (IH1 _ HQm)).
intros j Hie.
destruct Hie as ([Hji | (Hji & HPe)] & [Hji' | (Hji' & HQe)]); try omega.
  {
  left; auto.
  }

  {
  right; auto.
  }
}
Qed.


Lemma hygiene_shift_under :
  forall P i j m,
    hygiene P m
    -> hygiene (fun k => (k < i /\ P k) \/ (k >= i + j /\ P (k - j))) (subst (under i (sh j)) m).
Proof.
intros P i j m H.
revert i.
induct H
  using (fun Z => hygiene_mut_ind Z
           (fun P a r =>
              forall i,
                hygiene_row (fun k => (k < i /\ P k) \/ (k >= i + j /\ P (k - j))) a (substr (under i (sh j)) r))); eauto using hygiene, hygiene_row.

(* var *)
{
intros P k H i.
simpsub.
so (lt_dec k i) as [Hlt | Hge].
  {
  rewrite -> project_under_lt; auto.
  apply hygiene_var; auto.
  }

  {
  rewrite -> project_under_geq; [| omega].
  simpsub.
  apply hygiene_var.
  right.
  split; [omega |].
  force_exact H.
  f_equal.
  omega.
  }
}

(* cons *)
{
intros P k a m r _ IH1 _ IH2 i.
simpsub.
apply hygiene_cons; auto.
eapply hygiene_weaken.
2:{
  apply IH1.
  }
intros l H.
cbn in H.
destruct H as [H | H].
  {
  destruct H as (Hl_ki & H).
  destruct H as [H | H].
    {
    left; auto.
    }
  right.
  destruct H as (Hlk & H).
  split; auto.
  left.
  split; auto.
  omega.
  }

  {
  destruct H as (H_kij & H).
  destruct H as [H | H].
    {
    left; omega.
    }
  destruct H as (? & HH).
  right.
  split; [omega |].
  right.
  split; [omega |].
  force_exact HH.
  f_equal.
  omega.
  }
}
Qed.


Lemma hygiene_shift :
  forall P i m,
    hygiene P m
    -> hygiene (fun j => j >= i /\ P (j - i)) (subst (sh i) m).
Proof.
intros P i m Hm.
rewrite <- (under_zero _ (sh i)).
eapply hygiene_weaken; [| eapply hygiene_shift_under; eauto].
intros j H.
cbn in H.
destruct H as [H | H]; auto.
destruct H; omega.
Qed.


Lemma hygiene_shift' :
  forall P i m,
    hygiene (fun j => P (i + j)) m
    -> hygiene P (subst (sh i) m).
Proof.
intros P i m Hhyg.
refine (hygiene_weaken _#3 _ (hygiene_shift _ i _ Hhyg)).
intros j H.
destruct H as (Hji & H).
force_exact H; f_equal.
omega.
Qed.


Lemma hygiene_shift_under' :
  forall P i j m,
    hygiene (fun k => (k < i /\ P k) \/ (k >= i /\ P (k + j))) m
    -> hygiene P (subst (under i (sh j)) m).
Proof.
intros P i j m Hhyg.
refine (hygiene_weaken _#3 _ (hygiene_shift_under _ i j _ Hhyg)).
intros k Hk.
destruct Hk as [Hk | Hk].
  {
  destruct Hk as (Hk & H).
  destruct H as [(_ & H) | H]; auto.
  exfalso.
  omega.
  }

  {
  destruct Hk as (Hk & H).
  destruct H as [H | (_ & H)].
    {
    exfalso.
    omega.
    }
  replace (k - j + j) with k in H by omega.
  exact H.
  }
Qed.


Lemma hygiene_subst :
  forall P Q s m,
    hygiene P m
    -> (forall i, P i -> hygiene Q (project s i))
    -> hygiene Q (subst s m).
Proof.
intros P Q s m Hm Hs.
revert Q s Hs.
induct Hm
  using (fun X => hygiene_mut_ind X
           (fun P a r =>
              forall Q s,
                (forall i, P i -> hygiene Q (project s i))
                -> hygiene_row Q a (substr s r))).

(* var *)
{
intros P i Hi Q s Hs.
simpsub.
exact (Hs _ Hi).
}

(* oper *)
{
intros P a th r _ IH Q s Hs.
simpsub.
apply hygiene_oper.
apply IH.
intros i Hi.
apply Hs; auto.
}

(* nil *)
{
intros P Q s H.
simpsub.
apply hygiene_nil.
}

(* cons *)
{
intros P i a m r _ IH1 _ IH2 Q s Hs.
simpsub.
apply hygiene_cons; auto.
apply IH1.
intros j H.
destruct H as [H | H].
  {
  rewrite -> project_under_lt; auto.
  apply hygiene_var.
  left; auto.
  }
destruct H as (Hji & Hj).
rewrite -> project_under_geq; [| omega].
so (hygiene_shift _ i _ (Hs _ Hj)) as Hproj.
refine (hygiene_weaken _#3 _ Hproj).
intros k H.
right; auto.
}
Qed.


Lemma hygiene_unshift_under :
  forall P i j m,
    hygiene P (subst (under i (sh j)) m)
    -> hygiene (fun k => (k < i /\ P k) \/ (k >= i /\ P (k + j))) m.
Proof.
intros P i j m.
revert P i j.
induct m
  using (fun X => term_mut_ind _ X
           (fun a r =>
              forall P i j,
                hygiene_row P _ (substr (under i (sh j)) r)
                -> hygiene_row (fun k => (k < i /\ P k) \/ (k >= i /\ P (k + j))) _ r)).

(* var *)
{
intros k P i j Hhyg.
simpsubin Hhyg.
apply hygiene_var.
so (le_lt_dec i k) as [Hik | Hki].
  {
  rewrite -> project_under_geq in Hhyg; auto.
  simpsubin Hhyg.
  invert Hhyg.
  intro H.
  replace (i + (j + (k - i))) with (k + j) in H by omega.
  right; auto.
  }

  {
  rewrite -> project_under_lt in Hhyg; auto.
  invert Hhyg.
  intro H.
  left; auto.
  }
}

(* oper *)
{
intros a th r IH P i j Hhyg.
simpsubin Hhyg.
invertc Hhyg.
intro Hhyg.
apply hygiene_oper.
exact (IH _#3 Hhyg).
}

(* nil *)
{
intros P i j _.
apply hygiene_nil.
}

(* cons *)
{
intros k a m IH1 r IH2 P i j Hhyg.
simpsubin Hhyg.
invertc Hhyg.
intros Hm Hr.
apply hygiene_cons; auto.
refine (hygiene_weaken _#3 _ (IH1 _ _ _ Hm)).
intros l Hle.
destruct Hle as [H | H].
  {
  destruct H as (Hlki & [H | H]).
    {
    left; auto.
    }

    {
    destruct H as (Hlk & Hlke).
    right.
    split; auto.
    left.
    split; auto; omega.
    }
  }

  {
  destruct H as (Hlki & [H | H]).
    {
    destruct H; exfalso; omega.
    }

    {
    destruct H as (Hljk & Hljke).
    right.
    split; [omega |].
    right.
    split; [omega |].
    force_exact Hljke.
    f_equal; omega.
    }
  }
}
Qed.


Lemma hygiene_unshift :
  forall P i m,
    hygiene P (subst (sh i) m)
    -> hygiene (fun j => P (i + j)) m.
Proof.
intros P i m Hhyg.
rewrite <- (under_zero _ (sh i)) in Hhyg.
refine (hygiene_weaken _#3 _ (hygiene_unshift_under _#4 Hhyg)).
intros j H.
destruct H as [H | H].
  {
  destruct H; omega.
  }

  {
  destruct H; auto.
  rewrite -> plus_comm; auto.
  }
Qed.


Lemma hygiene_subst_under_invert :
  forall P i s m,
    hygiene P (subst (under i s) m)
    -> hygiene (fun j => (j < i /\ P j) \/ (j >= i /\ hygiene (fun k => P (k + i)) (project s (j - i)))) m.
Proof.
intros P i s m.
revert P i s.
induct m
  using (fun X => term_mut_ind _ X
           (fun a r =>
              forall P i s,
                hygiene_row P _ (substr (under i s) r)
                -> hygiene_row (fun j => (j < i /\ P j) \/ (j >= i /\ hygiene (fun k => P (k + i)) (project s (j - i)))) _ r)).

(* var *)
{
intros n P i s Hhyg.
apply hygiene_var.
simpsubin Hhyg.
so (le_lt_dec i n) as [Hin | Hni].
  {
  right.
  split; auto.
  rewrite -> project_under_geq in Hhyg; eauto.
  refine (hygiene_weaken _#3 _ (hygiene_unshift _#3 Hhyg)).
  intros j Hje.
  rewrite -> plus_comm.
  exact Hje.
  }

  {
  left.
  split; auto.
  rewrite -> project_under_lt in Hhyg; auto.
  invert Hhyg; auto.
  }
}

(* oper *)
{
intros a th r IH P i s Hhyg.
simpsubin Hhyg.
invertc Hhyg.
intros Hhyg.
apply hygiene_oper.
apply IH; auto.
}

(* nil *)
{
intros P i s _.
apply hygiene_nil.
}

(* cons *)
{
intros j a m IH1 r IH2 P i s Hhyg.
simpsubin Hhyg.
invertc Hhyg.
intros Hm Hr.
apply hygiene_cons; auto.
refine (hygiene_weaken _#3 _
          (IH1 (fun k => k < j \/ (k >= j /\ P (k - j))) (j + i) s Hm)).
intros k Hke.
destruct Hke as [H | H].
  {
  destruct H as (Hk & [H | H]).
    {
    left; auto.
    }
    
    {
    destruct H as (Hkj & Hkje).
    right.
    split; auto.
    left.
    split; auto; omega.
    }
  }

  {
  destruct H as (Hkji & Hhyg').
  right.
  split; [omega |].
  right.
  split; [omega |].
  replace (k - j - i) with (k - (j + i)) by omega.
  refine (hygiene_weaken _#3 _ Hhyg').
  intros l Hle.
  destruct Hle as [H | H].
    {
    omega.
    }

    {
    destruct H as (_ & H).
    force_exact H.
    f_equal.
    omega.
    }
  }
}
Qed.


Lemma hygiene_subst1_under_invert :
  forall i j (m n : @term object),
    hygiene (fun k => k < i + j) (subst (under i (dot n id)) m)
    -> hygiene (fun k => k < S (i + j)) m.
Proof.
intros i j m n Hhyg.
so (hygiene_subst_under_invert _#4 Hhyg) as Hhyg'.
eapply hygiene_weaken; eauto.
intros k Hk.
destruct Hk as [(Hk & _) | (Hkmin & Hk)].
  {
  omega.
  }
so (lt_dec i k) as [Hlt | Hnlt].
  {
  replace (k - i) with (S (pred (k - i))) in Hk by omega.
  simpsubin Hk.
  cbn in Hk.
  invert Hk.
  intro; omega.
  }

  {
  omega.
  }
Qed.


Lemma hygiene_subst_invert :
  forall P s m,
    hygiene P (subst s m)
    -> hygiene (fun j => hygiene P (project s j)) m.
Proof.
intros P s m Hhyg.
rewrite <- (under_zero _ s) in Hhyg.
so (hygiene_subst_under_invert _#4 Hhyg) as Hhyg'.
refine (hygiene_weaken _#3 _ Hhyg').
intros j H.
destruct H as [H | H].
  {
  destruct H; omega.
  }

  {
  destruct H as (_ & H).
  replace (j - 0) with j in H by omega.
  refine (hygiene_weaken _#3 _ H).
  intros k H'.
  replace (k + 0) with k in H' by omega.
  auto.
  }
Qed.


Lemma hygiene_specific :
  forall P m,
    hygiene P m
    -> forall i, P i \/ hygiene (fun j => j <> i /\ P j) m.
Proof.
intros P m H.
induct H
  using (fun X => hygiene_mut_ind X
           (fun P a r =>
              forall i,
                P i \/ hygiene_row (fun j => j <> i /\ P j) a r)).

(* var *)
{
intros P j Hj i.
so (eq_nat_dec j i) as [Heq | Hneq].
  {
  subst j.
  left; eauto.
  }

  {
  right.
  apply hygiene_var.
  auto.
  }
}

(* oper *)
{
intros P a th r _ IH i.
so (IH i) as [H | H].
  {
  left; auto.
  }

  {
  right.
  apply hygiene_oper; auto.
  }
}

(* nil *)
{
intros P i.
right.
apply hygiene_nil.
}

(* cons *)
{
intros P j a m r _ IH1 _ IH2 i.
so (IH1 (i + j)) as [Hyes | Hno1].
  {
  destruct Hyes as [H | H]; [omega |].
  destruct H as (_ & H).
  left.
  force_exact H.
  f_equal.
  omega.
  }
so (IH2 i) as [Hyes | Hno2].
  {
  left; auto.
  }
right.
apply hygiene_cons; auto.
refine (hygiene_weaken _#3 _ Hno1).
intros k H.
destruct H as (Hneq & H).
destruct H as [H | H]; auto.
right.
destruct H as (Hkj & H).
do2 2 split; auto.
omega.
}
Qed.


(* Hygiene predicate combinators *)

Definition clo : hpred := fun _ => False.


Definition okay : hpred := fun _ => True.


Definition absent (P : hpred) : hpred :=
  fun i =>
    match i with
    | 0 => False
    | S i' => P i'
    end.


Definition permit (P : hpred) : hpred :=
  fun i =>
    match i with
    | 0 => True
    | S i' => P i'
    end.


Lemma clo_min :
  forall P, hincl clo P.
Proof.
intros P i H'.
destruct H'.
Qed.


Lemma okay_max :
  forall P, hincl P okay.
Proof.
intros P i H'.
exact I.
Qed.


Lemma permit_compat :
  forall P Q,
    hincl P Q
    -> hincl (permit P) (permit Q).
Proof.
unfold permit.
intros P Q HPQ k H.
destruct k as [| k]; auto.
Qed.


Lemma hygiene_auto :
  forall P a (th : operator a) r,
    (row_rect object (fun _ _ => Prop)
       True
       (fun i a m _ Q =>
          hygiene
            (nat_rect (fun _ => hpred)
               P
               (fun _ => permit)
               i)
            m
          /\ Q)
       a r)
    -> hygiene P (oper a th r).
Proof.
intros P a th r Hcond.
apply hygiene_oper.
revert Hcond.
cbn.
clear th.
induct r.

(* nil *)
{
intros _.
apply hygiene_nil.
}

(* cons *)
{
intros i a m r IH Hcond.
cbn in Hcond.
destruct Hcond as (Hm & Hr).
apply hygiene_cons; auto.
clear IH Hr.
refine (hygiene_weaken _#3 _ Hm).
clear a m r Hm.
intros j Hcond.
revert j Hcond.
induct i.
  (* 0 *)
  {
  intros j Hcond.
  cbn in Hcond.
  right.
  split; [omega |].
  rewrite -> Nat.sub_0_r; auto.
  }

  (* S *)
  {
  intros i IH j Hcond.
  cbn in Hcond.
  destruct j as [| j].
    {
    left.
    omega.
    }
  exploit (IH j) as H; auto.
  destruct H as [H | H].
    {
    left.
    destruct H; omega.
    }

    {
    right.
    destruct H.
    split; auto; omega.
    }
  }
}
Qed.


Lemma hygiene_invert_auto :
  forall P a (th : operator a) r,
    hygiene P (oper a th r)
    -> (row_rect object (fun _ _ => Prop)
          True
          (fun i a m _ Q =>
             hygiene
               (nat_rect (fun _ => hpred)
                  P
                  (fun _ => permit)
                  i)
               m
             /\ Q)
          a r).
Proof.
intros P a th r Hcond.
invertc Hcond.
clear th.
induct r.

(* nil *)
{
intros _.
cbn.
trivial.
}

(* cons *)
{
intros i a m r IH Hcond.
invertc Hcond.
intros Hm Hr.
cbn.
split; auto.
clear IH Hr.
refine (hygiene_weaken _#3 _ Hm).
clear a m r Hm.
intros j Hcond.
revert j Hcond.
induct i.
  (* 0 *)
  {
  intros j Hcond.
  cbn.
  destruct Hcond as [H | H].
    {
    omega.
    }
  destruct H as (_ & Hcond).
  rewrite -> Nat.sub_0_r in Hcond; auto.
  }

  (* S *)
  {
  intros i IH j Hcond.
  cbn.
  destruct j as [| j].
    {
    cbn.
    trivial.
    }
  exploit (IH j) as Hcond'; auto.
  destruct Hcond as [H | H].
    {
    left.
    omega.
    }

    {
    destruct H as (Hsjsi & Hcond).
    right.
    split; auto.
    omega.
    }
  }
}
Qed.               


(* Substitutions on hygiene *)

Lemma hygiene_shift_absent :
  forall P m,
    hygiene P m
    -> hygiene (absent P) (subst sh1 m).
Proof.
intros P m Hm.
so (hygiene_shift _ 1 _ Hm) as H.
refine (hygiene_weaken _#3 _ H).
intros i Hcond.
destruct i as [| i].
  {
  omega.
  }
cbn.
cbn in Hcond.
rewrite -> Nat.sub_0_r in Hcond.
destruct Hcond; auto.
Qed.


Lemma hygiene_shift_permit_iff :
  forall P m,
    hygiene P m <-> hygiene (permit P) (subst sh1 m).
Proof.
intros P m.
split.
  {
  intro Hhyg.
  apply hygiene_shift'.
  refine (hygiene_weaken _#3 _ Hhyg).
  intros j H.
  cbn; auto.
  }

  {
  intro Hhyg.
  so (hygiene_unshift _#3 Hhyg) as Hhyg'.
  cbn in Hhyg'.
  refine (hygiene_weaken _#3 _ Hhyg').
  intro; intros; eauto.
  }
Qed.


Lemma hygiene_shift_permit :
  forall P m,
    hygiene P m
    -> hygiene (permit P) (subst sh1 m).
Proof.
intros P m.
exact (hygiene_shift_permit_iff P m andel).
Qed.


Lemma hygiene_subst1 :
  forall P m n,
    hygiene P m
    -> hygiene (permit P) n
    -> hygiene P (subst1 m n).
Proof.
intros P m n Hm Hn.
apply (hygiene_subst (permit P)); auto.
intros i Hie.
destruct i as [| i].
  {
  simpsub; auto.
  }

  {
  simpsub.
  cbn.
  apply hygiene_var.
  exact Hie.
  }
Qed.


(* Substitutions using hygiene *)

Lemma subst_into_absent_term_and_row :
  (forall P s m,
     hygiene P m
     -> (forall i, P i -> project s i = var i)
     -> subst s m = m)
  /\
  (forall P s a (r : row a),
     hygiene_row P a r
     -> (forall i, P i -> project s i = var i)
     -> substr s r = r).
Proof.
exploit
  (hygiene_term_and_row_ind
     (fun P m =>
        forall s,
          (forall i, P i -> project s i = var i)
          -> subst s m = m)
     (fun P a r =>
        forall s,
          (forall i, P i -> project s i = var i)
          -> substr s r = r)) as H; eauto.


(* var *)
{
intros P j Hj s HP.
simpsub.
apply HP; auto.
}

(* oper *)
{
intros P a th r _ IH s HP.
simpsub.
f_equal.
apply IH; eauto.
}

(* cons *)
{
intros P k a m r _ IH1 _ IH2 s HP.
simpsub.
f_equal; auto.
apply IH1.
intros i H.
destruct H as [H | H].
  {
  rewrite -> project_under_lt; auto.
  }
destruct H as (Hki & H).
rewrite -> project_under_geq; auto.
rewrite -> HP; auto.
simpsub.
f_equal; omega.
}

(* epilogue *)
{
destruct H; eauto.
}
Qed.  


Lemma subst_into_absent :
  forall P s m,
    hygiene P m
    -> (forall i, P i -> project s i = var i)
    -> subst s m = m.
Proof.
exact (subst_into_absent_term_and_row andel).
Qed.


Lemma subst_into_closed :
  forall s m,
    hygiene clo m
    -> subst s m = m.
Proof.
intros s m Hcl.
eapply subst_into_absent; eauto.
intros i H.
destruct H.
Qed.


Lemma subst_into_absent_single :
  forall i m n,
    hygiene (fun j => j <> i) m
    -> subst (under i (dot n sh1)) m = m.
Proof.
intros i m n Hhyg.
eapply subst_into_absent; eauto.
intros j Hj.
so (lt_eq_lt_dec j i) as [[Hlt | Heq] | Hlt].
  {
  rewrite -> project_under_lt; auto.
  }

  {
  destruct Hj; auto.
  }

  {
  rewrite -> project_under_geq; [| omega].
  replace (j - i) with (S (j - S i)) by omega.
  simpsub.
  f_equal; omega.
  }
Qed.


(* Inverting closed substitution results *)

Lemma hygiene_clo_subst_invert :
  forall s m,
    hygiene clo (subst s m)
    -> hygiene (fun i => hygiene clo (project s i)) m.
Proof.
intros s m Hhyg.
so (hygiene_subst_invert _#3 Hhyg) as Hhyg'.
refine (hygiene_weaken _#3 _ Hhyg').
intros j Hje.
refine (hygiene_weaken _#3 _ Hje).
intros k Hke.
destruct Hke.
Qed.


Lemma hygiene_clo_subst1_invert :
  forall m n,
    hygiene clo (subst1 m n)
    -> hygiene clo m \/ hygiene clo n.
Proof.
intros m n Hmn.
so (hygiene_clo_subst_invert _ _ Hmn) as Hn.
so (hygiene_specific _ _ Hn 0) as [Hie | Hn'].
  {
  left.
  simpsubin Hie.
  exact Hie.
  }

  {
  right.
  refine (hygiene_weaken _#3 _ Hn').
  intros i (Hneq & Hi).
  destruct i as [| i].
    {
    destruct Hneq; auto.
    }
  simpsubin Hi.
  cbn in Hi.
  invert Hi.
  intro H'.
  destruct H'.
  }
Qed.


Lemma hygiene_subst1_invert :
  forall P (m n : @term object),
    hygiene P (subst1 m n)
    -> hygiene (permit P) n.
Proof.
intros P m n Hhyg.
so (hygiene_subst_invert _#3 Hhyg) as Hhyg'.
eapply hygiene_weaken; eauto.
intros i Hi.
destruct i as [| i].
  {
  exact I.
  }
cbn.
simpsubin Hi.
invert Hi; auto.
Qed.


Lemma hygiene_clo_subst1_invert_permit :
  forall (m n : @term object),
    hygiene clo (subst1 m n)
    -> hygiene (permit clo) n.
Proof.
intros m n H.
eapply hygiene_subst1_invert; eauto.
Qed.


(* Closed substitutions *)

Definition closub (P : hpred) s : Prop :=
  forall j,
    P j
    -> hygiene clo (project s j).


Lemma subst_closub :
  forall P s m,
    closub P s
    -> hygiene P m
    -> hygiene clo (subst s m).
Proof.
intros P s m Hs Hm.
refine (hygiene_subst _#4 Hm _).
intros i Hie.
apply (hygiene_weaken clo); auto using clo_min.
Qed.


Lemma subst_closub_under_permit :
  forall P m s,
    hygiene (permit P) m
    -> closub P s
    -> hygiene (permit clo) (subst (under 1 s) m).
Proof.
intros P m s Hm Hs.
apply (hygiene_subst (permit P)); auto.
intros j H.
destruct j as [| j].
  {
  simpsub.
  apply hygiene_var.
  auto.
  }

  {
  simpsub.
  cbn in H.
  apply hygiene_shift'.
  so (Hs j H).
  cbn.
  eapply hygiene_weaken; eauto.
  intros j' H'.
  destruct H'.
  }
Qed.


Lemma closub_dot :
  forall P (m : @term object) s,
    closub P s
    -> hygiene clo m
    -> closub (permit P) (dot m s).
Proof.
intros P m s Hs Hm.
intros i Hi.
destruct i as [| i]; simpsub; auto.
Qed.


(* Evaluation and reduction *)

Lemma reduce_hygiene :
  forall P m n,
    reduce m n
    -> hygiene P m
    -> hygiene P n.
Proof.
intros P m n Hmn Hm.
revert P Hm.
induct Hmn
  using (fun X => reduce_mut_ind _ X
           (fun a r r' =>
              forall P, hygiene_row P a r -> hygiene_row P a r')); eauto.

(* oper *)
{
intros a th r s _ IH P H.
apply hygiene_oper.
invertc H.
intro H.
auto.
}

(* tapp_beta *)
{
intros m m' n n' _ IH1 _ IH2 P Hhyg.
so (hygiene_invert_auto _#4 Hhyg) as H; cbn in H.
destruct H as (Hlam & Hn & _).
so (hygiene_invert_auto _#4 Hlam) as H; cbn in H.
destruct H as (Hm & _).
apply hygiene_subst1; auto.
}

(* prev_beta *)
{
intros m m' _ IH P Hhyg.
so (hygiene_invert_auto _#4 Hhyg) as H; cbn in H.
destruct H as (Hnext & _).
so (hygiene_invert_auto _#4 Hnext) as H; cbn in H.
destruct H as (Hm & _).
auto.
}

(* bite_beta1 *)
{
intros m m' n _ IH P Hhyg.
so (hygiene_invert_auto _#4 Hhyg) as H; cbn in H.
destruct H as (_ & Hm & Hn & _).
apply IH; auto.
}

(* bite_beta2 *)
{
intros m m' n _ IH P Hhyg.
so (hygiene_invert_auto _#4 Hhyg) as H; cbn in H.
destruct H as (_ & Hm & Hn & _).
apply IH; auto.
}

(* ppi1_beta *)
{
intros m m' n _ IH P Hhyg.
so (hygiene_invert_auto _#4 Hhyg) as H; cbn in H.
destruct H as (Hpair & _).
so (hygiene_invert_auto _#4 Hpair) as H; cbn in H.
destruct H as (Hm & Hn & _).
apply IH; auto.
}

(* ppi2_beta *)
{
intros m m' n _ IH P Hhyg.
so (hygiene_invert_auto _#4 Hhyg) as H; cbn in H.
destruct H as (Hpair & _).
so (hygiene_invert_auto _#4 Hpair) as H; cbn in H.
destruct H as (Hm & Hn & _).
apply IH; auto.
}

(* cons *)
{
intros i a m n r s _ IH1 _ IH2 P Hhyg.
invertc Hhyg.
intros Hm Hr.
apply hygiene_cons; auto.
}
Qed.


Lemma step_hygiene :
  forall P (m n : @term object),
    step m n
    -> hygiene P m
    -> hygiene P n.
Proof.
intros.
eapply reduce_hygiene; eauto.
apply step_reduce; auto.
Qed.


Lemma steps_hygiene :
  forall P (m n : @term object),
    star step m n
    -> hygiene P m
    -> hygiene P n.
Proof.
intros P m n Hsteps Hhyg.
revert Hhyg.
induct Hsteps; eauto using step_hygiene.
Qed.


Lemma reduces_hygiene :
  forall P (m n : @term object),
    star reduce m n
    -> hygiene P m
    -> hygiene P n.
Proof.
intros P m n Hsteps Hhyg.
revert Hhyg.
induct Hsteps; eauto using reduce_hygiene.
Qed.


Lemma hygiene_sumbool :
  forall P A B (c : {A} + {B}) (m n : @term object),
    hygiene P m
    -> hygiene P n
    -> hygiene P (if c then m else n).
Proof.
intros P A B c m n H H0.
destruct c; auto.
Qed.   


Lemma hygiene_okay :
  forall m,
    hygiene okay m.
Proof.
exploit (syntax_ind _ 
           (fun m => hygiene (fun _ => True) m)
           (fun a r => hygiene_row (fun _ => True) a r)) as Hind;
eauto using hygiene, hygiene_nil.

(* cons *)
{
intros i a m IH1 r IH2.
apply hygiene_cons; auto.
refine (hygiene_weaken _#3 _ IH1).
intros j _.
so (lt_dec j i) as [H | H]; auto.
right; split; auto.
omega.
}

(* wrapup *)
{
destruct Hind; auto.
}
Qed.


Lemma reduce_sh1_under_form :
  forall i (m n : @term object),
    reduce (subst (under i sh1) m) n
    -> exists m', n = subst (under i sh1) m' /\ reduce m m'.
Proof.
intros i m n Hreduces.
assert (hygiene (fun j => j <> i) (subst (under i sh1) m)) as Hhyg.
  {
  apply hygiene_shift_under'.
  refine (hygiene_weaken _#3 _ (hygiene_okay m)).
  intros k _.
  omega.
  }
so (reduce_hygiene _#3 Hreduces Hhyg) as Hhyg'.
exists (subst (under i (dot arb id)) n).
split.
2:{
  so (reduce_subst _ (under i (dot arb id)) _ _ Hreduces) as Hreduces'.
  simpsubin Hreduces'.
  rewrite <- compose_under in Hreduces'.
  unfold sh1 in Hreduces'.
  rewrite -> compose_sh_dot in Hreduces'.
  simpsubin Hreduces'.
  exact Hreduces'.
  }
simpsub.
symmetry.
rewrite <- compose_under.
simpsub.
apply (subst_into_absent_single i); auto.
Qed.


Lemma reduce_sh1_form :
  forall (m n : @term object),
    reduce (subst sh1 m) n
    -> exists m', n = subst sh1 m' /\ reduce m m'.
Proof.
intros m n H.
apply (reduce_sh1_under_form 0 m n); auto.
Qed.


Lemma reduce_sh_form :
  forall i (m n : @term object),
    reduce (subst (sh i) m) n
    -> exists m', n = subst (sh i) m' /\ reduce m m'.
Proof.
intros i.
induct i.

(* 0 *)
{
intros m n H.
exists n.
split.
  {
  simpsub.
  auto.
  }

  {
  simpsubin H.
  exact H.
  }
}

(* S *)
{
intros i IH m n Hred.
replace (S i) with (i + 1) in Hred by omega.
rewrite <- compose_sh_sh in Hred.
rewrite -> subst_compose in Hred.
so (reduce_sh1_form _#2 Hred) as (m' & -> & Hred').
so (IH _ _ Hred') as (m'' & -> & Hred'').
exists m''.
split; auto.
simpsub.
replace (i + 1) with (S i) by omega.
reflexivity.
}
Qed.


Lemma reduces_sh1_under_form :
  forall i (m n : @term object),
    star reduce (subst (under i sh1) m) n
    -> exists m', n = subst (under i sh1) m' /\ star reduce m m'.
Proof.
intros i m n Hreduces.
assert (hygiene (fun j => j <> i) (subst (under i sh1) m)) as Hhyg.
  {
  apply hygiene_shift_under'.
  refine (hygiene_weaken _#3 _ (hygiene_okay m)).
  intros k _.
  omega.
  }
so (reduces_hygiene _#3 Hreduces Hhyg) as Hhyg'.
exists (subst (under i (dot arb id)) n).
split.
2:{
  so (reduces_subst _ (under i (dot arb id)) _ _ Hreduces) as Hreduces'.
  simpsubin Hreduces'.
  rewrite <- compose_under in Hreduces'.
  unfold sh1 in Hreduces'.
  rewrite -> compose_sh_dot in Hreduces'.
  simpsubin Hreduces'.
  exact Hreduces'.
  }
simpsub.
symmetry.
rewrite <- compose_under.
simpsub.
apply (subst_into_absent_single i); auto.
Qed.


Lemma reduces_sh1_form :
  forall (m n : @term object),
    star reduce (subst sh1 m) n
    -> exists m', n = subst sh1 m' /\ star reduce m m'.
Proof.
intros m n H.
apply (reduces_sh1_under_form 0 m n); auto.
Qed.


Lemma reduces_sh_form :
  forall i (m n : @term object),
    star reduce (subst (sh i) m) n
    -> exists m', n = subst (sh i) m' /\ star reduce m m'.
Proof.
intros i.
induct i.

(* 0 *)
{
intros m n H.
exists n.
split.
  {
  simpsub.
  auto.
  }

  {
  simpsubin H.
  exact H.
  }
}

(* S *)
{
intros i IH m n Hred.
replace (S i) with (i + 1) in Hred by omega.
rewrite <- compose_sh_sh in Hred.
rewrite -> subst_compose in Hred.
so (reduces_sh1_form _#2 Hred) as (m' & -> & Hred').
so (IH _ _ Hred') as (m'' & -> & Hred'').
exists m''.
split; auto.
simpsub.
replace (i + 1) with (S i) by omega.
reflexivity.
}
Qed.


Inductive hygienej P : @judgement object -> Prop :=
| hygienej_deq :
    forall m n a,
      hygiene P m
      -> hygiene P n
      -> hygiene P a
      -> hygienej P (deq m n a).


Lemma hygienej_weaken :
  forall P Q (J : @judgement object),
    hincl P Q
    -> hygienej P J
    -> hygienej Q J.
Proof.
intros P Q J Hincl HJ.
induct HJ; intros.
apply hygienej_deq; eauto using hygiene_weaken.
Qed.


End object.


Arguments hygiene {object}.
Arguments hygienej {object}.
Arguments hygiene_row {object} P {a}.
Arguments closub {object}.
