
Require Import Axioms.
Require Import Tactics.
Require Import Sigma.
Require Import Equality.
Require Import Relation.
Require Import Syntax.
Require Import Dynamic.
Require Import Hygiene.
Require Import Equivalence.
Require Import MapTerm.
Require Import Reduction.
Require Import Standardization.


Inductive robust {object} : nat -> term object -> Prop :=
| robust_var :
    forall i,
      robust i (var i)

| robust_const :
    forall i a,
      robust i (subst (under i sh1) a)

| robust_prod :
    forall i a b,
      robust i a
      -> robust i b
      -> robust i (prod a b)

| robust_pi :
    forall i a b,
      robust i a
      -> robust (S i) b
      -> robust i (pi a b)

| robust_sigma :
    forall i a b,
      robust i a
      -> robust (S i) b
      -> robust i (sigma a b)

| robust_mu :
    forall i a,
      robust (S i) a
      -> robust i (mu a)

(* It's true without assuming m is closed wrt the variable, but we would have to show
   that candidates cannot influence evaluation, which doesn't seem worth the trouble.
*)
| robust_bite :
    forall i m a b,
      robust i a
      -> robust i b
      -> robust i (bite (subst (under i sh1) m) a b)

(* Really should allow you to pick and choose with variables to drop, but this is
   all we need.
*)
| robust_weaken :
    forall i a,
      robust 0 a
      -> robust i (subst (sh i) a)

| robust_reduce :
    forall i a b,
      reduce a b
      -> robust i b
      -> robust i a
.


Lemma subst_under_sh1_more :
  forall object i (s : @sub object),
    compose (under i sh1) (under (S i) s)
    =
    compose (under i s) (under i sh1).
Proof.
intros object i s.
replace (S i) with (i + 1) by omega.
rewrite <- under_sum.
rewrite <- compose_under.
unfold sh1.
rewrite -> compose_sh_under_eq.
rewrite -> compose_under.
reflexivity.
Qed.


Lemma subst_robust :
  forall object i s (a : term object),
    robust i a
    -> robust i (subst (under (S i) s) a).
Proof.
intros object i s a H.
revert s.
induct H.

(* var *)
{
intros i s.
rewrite -> subst_var.
rewrite -> project_under_lt; auto.
apply robust_var.
}

(* const *)
{
intros i a s.
rewrite <- subst_compose.
rewrite -> subst_under_sh1_more.
rewrite -> subst_compose.
apply robust_const.
}

(* prod *)
{
intros i a b _ IH1 _ IH2 s.
simpsub.
apply robust_prod; eauto.
}

(* pi *)
{
intros i a b _ IH1 _ IH2 s.
simpsub.
cbn [Nat.add].
apply robust_pi.
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
apply robust_sigma.
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
apply robust_mu.
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
apply robust_bite; eauto.
}

(* weaken *)
{
intros i a _ IH s.
rewrite <- subst_compose.
rewrite -> compose_sh_under_leq; auto.
replace (S i - i) with 1 by omega.
rewrite -> subst_compose.
apply robust_weaken; auto.
}

(* reduce *)
{
intros i a b Hred _ IH s.
apply (robust_reduce _ _ (subst (under (S i) s) b)); auto.
apply reduce_subst; auto.
}
Qed.


Lemma reduce_robust :
  forall object i (m n : term object),
    reduce m n
    -> robust i m
    -> robust i n.
Proof.
intros object i m n Hred Hrobust.
revert n Hred.
induct Hrobust.

(* var *)
{
intros i n Hred.
invert Hred.
intros <-.
apply robust_var.
}

(* const *)
{
intros i m n Hred.
so (reduces_sh1_under_form _ i _ _ (star_one _#4 Hred)) as (n' & -> & _).
apply robust_const.
}

(* prod *)
{
intros i a b _ IH1 _ IH2 n Hred.
invert Hred.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros b' r3 Hb Hr3 <-.
invertc Hr3.
intros <-.
fold (prod a' b').
apply robust_prod; auto.
}

(* pi *)
{
intros i a b _ IH1 _ IH2 n Hred.
invert Hred.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros b' r3 Hb Hr3 <-.
invertc Hr3.
intros <-.
fold (pi a' b').
apply robust_pi; auto.
}

(* sigma *)
{
intros i a b _ IH1 _ IH2 n Hred.
invert Hred.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros b' r3 Hb Hr3 <-.
invertc Hr3.
intros <-.
fold (sigma a' b').
apply robust_sigma; auto.
}

(* mu *)
{
intros i a _ IH n Hred.
invert Hred.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros <-.
fold (mu a').
apply robust_mu; auto.
}

(* bite *)
{
intros i m a b _ IH1 _ IH2 n Hred.
invert Hred.
  {
  intros r1 Hr1 <-.
  invertc Hr1.
  intros m' r2 Hm Hr2 <-.
  invertc Hr2.
  intros a' r3 Ha Hr3 <-.
  invertc Hr3.
  intros b' r4 Hb Hr4 <-.
  invertc Hr4.
  intros <-.
  fold (bite m' a' b').
  so (reduces_sh1_under_form _ i _ _ (star_one _#4 Hm)) as (m'' & -> & _).
  apply robust_bite; auto.
  }

  {
  intros Ha _.
  apply IH1; auto.
  }

  {
  intros Hb _.
  apply IH2; auto.
  }
}

(* weaken *)
{
intros i a _ IH n Hred.
so (reduce_sh_form _#4 Hred) as (n' & -> & Hred').
apply robust_weaken.
apply IH; auto.
}

(* reduce *)
{
intros i a b Hab _ IH c Hac.
so (diamond _#4 Hab Hac) as (d & Hbd & Hcd).
eapply robust_reduce; eauto.
}
Qed.


Lemma reduces_robust :
  forall object i (m n : term object),
    star reduce m n
    -> robust i m
    -> robust i n.
Proof.
intros object i a b Hab Hb.
revert Hb.
induct Hab; auto.
(* step *)
intros a b c Hab _ IH Hc.
apply IH.
eapply reduce_robust; eauto.
Qed.


Lemma robust_reduces :
  forall {object} i (a b : term object),
    star reduce a b
    -> robust i b
    -> robust i a.
Proof.
intros object i a b Hab Hb.
revert Hb.
induct Hab; auto.
(* step *)
intros a b c Hab _ IH Hc.
eapply robust_reduce; eauto.
Qed.


Lemma equiv_robust :
  forall object i (m n : term object),
    equiv m n
    -> robust i m
    -> robust i n.
Proof.
intros object i a b Hequiv Hb.
so (church_rosser _#3 Hequiv) as (c & Hac & Hbc).
eapply robust_reduces; eauto.
apply (reduces_robust _ _ a); auto.
Qed.


Lemma map_robust :
  forall A B i (f : A -> B) (m : term A),
    robust i m
    -> robust i (map_term f m).
Proof.
intros A B i f m Hrobust.
induct Hrobust;
try (intros;
     simpmap;
     first [apply robust_var | apply robust_const | apply robust_prod | apply robust_pi | apply robust_sigma | apply robust_mu | apply robust_weaken | apply robust_bite];
     auto;
     done).
(* reduce *)
intros i a b Hab _ IH.
eapply robust_reduce; eauto.
apply map_reduce; auto.
Qed.


Lemma map_robust_conv :
  forall A B i (f : A -> B) (m : term A),
    robust i (map_term f m)
    -> robust i m.
Proof.
intros A B i f a Hrobust.
remember (map_term f a) as b eqn:Heq.
symmetry in Heq.
revert a Heq.
induct Hrobust.

(* var *)
{
intros i a Heq.
revert Heq.
cases a; try (intros; simpmapin Heq; discriminate Heq).
intros n Heq.
simpmapin Heq.
injection Heq.
intros ->.
apply robust_var.
}

(* const *)
{
intros i a b Heq.
so (map_term_sh1_under_form _#6 Heq) as (a' & -> & ->).
apply robust_const.
}

(* prod *)
{
intros i a b _ IH1 _ IH2 c Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr).
so (map_operator_same _#6 Heqth) as H.
invertc H.
intros <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (a' & b' & ->).
fold (prod a' b').
invertc Heqr.
intros <- <-.
apply robust_prod; auto.
}

(* pi *)
{
intros i a b _ IH1 _ IH2 c Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr); clear Heq.
so (map_operator_same _#6 Heqth) as H; clear Heqth.
invertc H.
intros <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (a' & b' & ->).
fold (pi a' b').
invertc Heqr.
intros Heqa Heqb.
apply robust_pi; auto.
}

(* sigma *)
{
intros i a b _ IH1 _ IH2 c Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr); clear Heq.
so (map_operator_same _#6 Heqth) as H; clear Heqth.
invertc H.
intros <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (a' & b' & ->).
fold (sigma a' b').
invertc Heqr.
intros Heqa Heqb.
apply robust_sigma; auto.
}

(* mu *)
{
intros i a _ IH c Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr); clear Heq.
so (map_operator_same _#6 Heqth) as H; clear Heqth.
invertc H.
intros <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (a' & ->).
fold (mu a').
invertc Heqr.
intros Heqa.
apply robust_mu; auto.
}

(* bite *)
{
intros i m a b _ IH1 _ IH2 c Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr); clear Heq.
so (map_operator_same _#6 Heqth) as H; clear Heqth.
invertc H.
intros <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (m' & a' & b' & ->).
fold (bite m' a' b').
invertc Heqr.
intros Heq <- <-.
so (map_term_sh1_under_form _#6 Heq) as (m'' & -> & ->).
apply robust_bite; auto.
}

(* weaken *)
{
intros i a _ IH c Heq.
so (map_term_sh_form _#6 Heq) as (d & -> & ->).
apply robust_weaken; auto.
}

(* reduce *)
{
intros i a b Hred _ IH c <-.
so (map_reduce_form _#5 Hred) as (d & -> & Hred').
apply (robust_reduce _ _ d); auto.
}
Qed.


Inductive positive {object} : nat -> term object -> Prop :=
| positive_var :
    forall i,
      positive i (var i)

| positive_const :
    forall i a,
      positive i (subst (under i sh1) a)

| positive_prod :
    forall i a b,
      positive i a
      -> positive i b
      -> positive i (prod a b)

| positive_pi :
    forall i a b,
      negative i a
      -> positive (S i) b
      -> positive i (pi a b)

| positive_sigma :
    forall i a b,
      positive i a
      -> positive (S i) b
      -> positive i (sigma a b)

| positive_mu :
    forall i a,
      positive (S i) a
      -> positive i (mu a)

| positive_bite :
    forall i m a b,
      positive i a
      -> positive i b
      -> positive i (bite (subst (under i sh1) m) a b)

(* Really should allow you to pick and choose with variables to drop, but this is
   all we need.
*)
| positive_weaken :
    forall i a,
      positive 0 a
      -> positive i (subst (sh i) a)

| positive_reduce :
    forall i a b,
      reduce a b
      -> positive i b
      -> positive i a

with negative {object} : nat -> term object -> Prop :=
| negative_const :
    forall i a,
      negative i (subst (under i sh1) a)

| negative_prod :
    forall i a b,
      negative i a
      -> negative i b
      -> negative i (prod a b)

| negative_pi :
    forall i a b,
      positive i a
      -> negative (S i) b
      -> negative i (pi a b)

| negative_sigma :
    forall i a b,
      negative i a
      -> negative (S i) b
      -> negative i (sigma a b)

| negative_mu :
    forall i a,
      negative (S i) a
      -> negative i (mu a)

| negative_bite :
    forall i m a b,
      negative i a
      -> negative i b
      -> negative i (bite (subst (under i sh1) m) a b)

| negative_weaken :
    forall i a,
      negative 0 a
      -> negative i (subst (sh i) a)

| negative_reduce :
    forall i a b,
      reduce a b
      -> negative i b
      -> negative i a
.


Scheme positive_mut_ind := Minimality for positive Sort Prop
with   negative_mut_ind := Minimality for negative Sort Prop.
Combined Scheme positive_negative_ind from positive_mut_ind, negative_mut_ind.


Lemma subst_positive_negative :
  forall object,
    (forall i s (a : term object),
       positive i a
       -> positive i (subst (under (S i) s) a))
    /\
    (forall i s (a : term object),
       negative i a
       -> negative i (subst (under (S i) s) a)).
Proof.
intros object.
exploit (positive_negative_ind object
           (fun i a =>
              forall s,
                positive i (subst (under (S i) s) a))
           (fun i a =>
              forall s,
                negative i (subst (under (S i) s) a))) as Hind.

(* var *)
{
intros i s.
rewrite -> subst_var.
rewrite -> project_under_lt; auto.
apply positive_var.
}

(* const *)
{
intros i a s.
rewrite <- subst_compose.
rewrite -> subst_under_sh1_more.
rewrite -> subst_compose.
apply positive_const.
}

(* prod *)
{
intros i a b _ IH1 _ IH2 s.
simpsub.
apply positive_prod; eauto.
}

(* pi *)
{
intros i a b _ IH1 _ IH2 s.
simpsub.
cbn [Nat.add].
apply positive_pi.
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
apply positive_sigma.
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
apply positive_mu.
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
apply positive_bite; eauto.
}

(* weaken *)
{
intros i a _ IH s.
rewrite <- subst_compose.
rewrite -> compose_sh_under_leq; auto.
replace (S i - i) with 1 by omega.
rewrite -> subst_compose.
apply positive_weaken; auto.
}

(* reduce *)
{
intros i a b Hequiv _ IH s.
eapply positive_reduce; eauto.
apply reduce_subst; auto.
}

(* const *)
{
intros i a s.
rewrite <- subst_compose.
rewrite -> subst_under_sh1_more.
rewrite -> subst_compose.
apply negative_const.
}

(* prod *)
{
intros i a b _ IH1 _ IH2 s.
simpsub.
apply negative_prod; eauto.
}

(* pi *)
{
intros i a b _ IH1 _ IH2 s.
simpsub.
cbn [Nat.add].
apply negative_pi.
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
apply negative_sigma.
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
apply negative_mu.
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
apply negative_bite; eauto.
}

(* weaken *)
{
intros i a _ IH s.
rewrite <- subst_compose.
rewrite -> compose_sh_under_leq; auto.
replace (S i - i) with 1 by omega.
rewrite -> subst_compose.
apply negative_weaken; auto.
}

(* reduce *)
{
intros i a b Hequiv _ IH s.
eapply negative_reduce; eauto.
apply reduce_subst; auto.
}

(* epilogue *)
{
destruct Hind; auto.
}
Qed.


Lemma subst_positive :
  forall object i s (a : term object),
    positive i a
    -> positive i (subst (under (S i) s) a).
Proof.
intros object.
exact (subst_positive_negative object andel).
Qed.


Lemma subst_negative :
  forall object i s (a : term object),
    negative i a
    -> negative i (subst (under (S i) s) a).
Proof.
intros object.
exact (subst_positive_negative object ander).
Qed.


Lemma positive_impl_robust :
  forall object i (a : term object),
    positive i a
    -> robust i a.
Proof.
intros object i a Hpos.
pattern i, a.
revert Hpos.
apply (positive_mut_ind _ _ (fun i a => robust i a));
clear i a.

(* var *)
{
intros i.
apply robust_var.
}

(* const *)
{
intros i a.
apply robust_const.
}

(* prod *)
{
intros i a b _ IH1 _ IH2.
apply robust_prod; auto.
}

(* pi *)
{
intros i a b _ IH1 _ IH2.
apply robust_pi; auto.
}

(* sigma *)
{
intros i a b _ IH1 _ IH2.
apply robust_sigma; auto.
}

(* mu *)
{
intros i a _ IH.
apply robust_mu; auto.
}

(* bite *)
{
intros i m a b _ IH1 _ IH2.
apply robust_bite; auto.
}

(* weaken *)
{
intros i a _ IH.
apply robust_weaken; auto.
}

(* reduce *)
{
intros i a b Hequiv _ IH.
eapply robust_reduce; eauto.
}

(* const *)
{
intros i a.
apply robust_const.
}

(* prod *)
{
intros i a b _ IH1 _ IH2.
apply robust_prod; auto.
}

(* pi *)
{
intros i a b _ IH1 _ IH2.
apply robust_pi; auto.
}

(* sigma *)
{
intros i a b _ IH1 _ IH2.
apply robust_sigma; auto.
}

(* mu *)
{
intros i a _ IH.
apply robust_mu; auto.
}

(* bite *)
{
intros i m a b _ IH1 _ IH2.
apply robust_bite; auto.
}

(* weaken *)
{
intros i a _ IH.
apply robust_weaken; auto.
}

(* reduce *)
{
intros i a b Hequiv _ IH.
eapply robust_reduce; eauto.
}
Qed.


Lemma reduce_positive_negative :
  forall object,
    (forall i (m n : term object),
       reduce m n
       -> positive i m
       -> positive i n)
    /\
    (forall i (m n : term object),
       reduce m n
       -> negative i m
       -> negative i n).
Proof.
intros object.
exploit (positive_negative_ind object
           (fun i m => forall n, reduce m n -> positive i n)
           (fun i m => forall n, reduce m n -> negative i n)) as Hind.

(* var *)
{
intros i n Hred.
invert Hred.
intros <-.
apply positive_var.
}

(* const *)
{
intros i m n Hred.
so (reduces_sh1_under_form _ i _ _ (star_one _#4 Hred)) as (n' & -> & _).
apply positive_const.
}

(* prod *)
{
intros i a b _ IH1 _ IH2 n Hred.
invert Hred.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros b' r3 Hb Hr3 <-.
invertc Hr3.
intros <-.
fold (prod a' b').
apply positive_prod; auto.
}

(* pi *)
{
intros i a b _ IH1 _ IH2 n Hred.
invert Hred.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros b' r3 Hb Hr3 <-.
invertc Hr3.
intros <-.
fold (pi a' b').
apply positive_pi; auto.
}

(* sigma *)
{
intros i a b _ IH1 _ IH2 n Hred.
invert Hred.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros b' r3 Hb Hr3 <-.
invertc Hr3.
intros <-.
fold (sigma a' b').
apply positive_sigma; auto.
}

(* mu *)
{
intros i a _ IH n Hred.
invert Hred.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros <-.
fold (mu a').
apply positive_mu; auto.
}

(* bite *)
{
intros i m a b _ IH1 _ IH2 n Hred.
invert Hred.
  {
  intros r1 Hr1 <-.
  invertc Hr1.
  intros m' r2 Hm Hr2 <-.
  invertc Hr2.
  intros a' r3 Ha Hr3 <-.
  invertc Hr3.
  intros b' r4 Hb Hr4 <-.
  invertc Hr4.
  intros <-.
  fold (bite m' a' b').
  so (reduces_sh1_under_form _ i _ _ (star_one _#4 Hm)) as (m'' & -> & _).
  apply positive_bite; auto.
  }

  {
  intros Ha _.
  apply IH1; auto.
  }

  {
  intros Hb _.
  apply IH2; auto.
  }
}

(* weaken *)
{
intros i a _ IH n Hred.
so (reduce_sh_form _#4 Hred) as (n' & -> & Hred').
apply positive_weaken.
apply IH; auto.
}

(* reduce *)
{
intros i a b Hab _ IH c Hac.
so (diamond _#4 Hab Hac) as (d & Hbd & Hcd).
eapply positive_reduce; eauto.
}

(* const *)
{
intros i m n Hred.
so (reduces_sh1_under_form _ i _ _ (star_one _#4 Hred)) as (n' & -> & _).
apply negative_const.
}

(* prod *)
{
intros i a b _ IH1 _ IH2 n Hred.
invert Hred.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros b' r3 Hb Hr3 <-.
invertc Hr3.
intros <-.
fold (prod a' b').
apply negative_prod; auto.
}

(* pi *)
{
intros i a b _ IH1 _ IH2 n Hred.
invert Hred.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros b' r3 Hb Hr3 <-.
invertc Hr3.
intros <-.
fold (pi a' b').
apply negative_pi; auto.
}

(* sigma *)
{
intros i a b _ IH1 _ IH2 n Hred.
invert Hred.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros b' r3 Hb Hr3 <-.
invertc Hr3.
intros <-.
fold (sigma a' b').
apply negative_sigma; auto.
}

(* mu *)
{
intros i a _ IH n Hred.
invert Hred.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros <-.
fold (mu a').
apply negative_mu; auto.
}

(* bite *)
{
intros i m a b _ IH1 _ IH2 n Hred.
invert Hred.
  {
  intros r1 Hr1 <-.
  invertc Hr1.
  intros m' r2 Hm Hr2 <-.
  invertc Hr2.
  intros a' r3 Ha Hr3 <-.
  invertc Hr3.
  intros b' r4 Hb Hr4 <-.
  invertc Hr4.
  intros <-.
  fold (bite m' a' b').
  so (reduces_sh1_under_form _ i _ _ (star_one _#4 Hm)) as (m'' & -> & _).
  apply negative_bite; auto.
  }

  {
  intros Ha _.
  apply IH1; auto.
  }

  {
  intros Hb _.
  apply IH2; auto.
  }
}

(* weaken *)
{
intros i a _ IH n Hred.
so (reduce_sh_form _#4 Hred) as (n' & -> & Hred').
apply negative_weaken.
apply IH; auto.
}

(* reduce *)
{
intros i a b Hab _ IH c Hac.
so (diamond _#4 Hab Hac) as (d & Hbd & Hcd).
eapply negative_reduce; eauto.
}

(* epilogue *)
{
destruct Hind; split; intros; eauto.
}
Qed.


Lemma reduce_positive :
  forall object i (m n : term object),
    reduce m n
    -> positive i m
    -> positive i n.
Proof.
intro object.
apply reduce_positive_negative.
Qed.


Lemma reduce_negative :
  forall object i (m n : term object),
    reduce m n
    -> negative i m
    -> negative i n.
Proof.
intro object.
apply reduce_positive_negative.
Qed.


Lemma reduces_positive :
  forall object i (m n : term object),
    star reduce m n
    -> positive i m
    -> positive i n.
Proof.
intros object i a b Hab Hb.
revert Hb.
induct Hab; auto.
(* step *)
intros a b c Hab _ IH Hc.
apply IH.
eapply reduce_positive; eauto.
Qed.


Lemma reduces_negative :
  forall object i (m n : term object),
    star reduce m n
    -> negative i m
    -> negative i n.
Proof.
intros object i a b Hab Hb.
revert Hb.
induct Hab; auto.
(* step *)
intros a b c Hab _ IH Hc.
apply IH.
eapply reduce_negative; eauto.
Qed.


Lemma positive_reduces :
  forall {object} i (a b : term object),
    star reduce a b
    -> positive i b
    -> positive i a.
Proof.
intros object i a b Hab Hb.
revert Hb.
induct Hab; auto.
(* step *)
intros a b c Hab _ IH Hc.
eapply positive_reduce; eauto.
Qed.


Lemma negative_reduces :
  forall {object} i (a b : term object),
    star reduce a b
    -> negative i b
    -> negative i a.
Proof.
intros object i a b Hab Hb.
revert Hb.
induct Hab; auto.
(* step *)
intros a b c Hab _ IH Hc.
eapply negative_reduce; eauto.
Qed.


Lemma equiv_positive :
  forall object i (m n : term object),
    equiv m n
    -> positive i m
    -> positive i n.
Proof.
intros object i a b Hequiv Hb.
so (church_rosser _#3 Hequiv) as (c & Hac & Hbc).
eapply positive_reduces; eauto.
apply (reduces_positive _ _ a); auto.
Qed.


Lemma equiv_negative :
  forall object i (m n : term object),
    equiv m n
    -> negative i m
    -> negative i n.
Proof.
intros object i a b Hequiv Hb.
so (church_rosser _#3 Hequiv) as (c & Hac & Hbc).
eapply negative_reduces; eauto.
apply (reduces_negative _ _ a); auto.
Qed.


Lemma map_positive_negative :
  forall A B (f : A -> B),
    (forall i m,
       positive i m
       -> positive i (map_term f m))
    /\
    (forall i m,
       negative i m
       -> negative i (map_term f m)).
Proof.
intros A B f.
exploit (positive_negative_ind A
           (fun i m => positive i (map_term f m))
           (fun i m => negative i (map_term f m))) as Hind;
try (intros;
     simpmap;
     first [apply positive_var | apply positive_const | apply positive_prod | apply positive_pi | apply positive_sigma | apply positive_mu | apply positive_weaken | apply positive_bite | apply negative_const | apply negative_prod | apply negative_pi | apply negative_sigma | apply negative_mu | apply negative_weaken | apply negative_bite];
     auto;
     done).

(* reduce *)
{
intros i a b Hab _ IH.
eapply positive_reduce; eauto.
apply map_reduce; auto.
}

(* reduce *)
{
intros i a b Hab _ IH.
eapply negative_reduce; eauto.
apply map_reduce; auto.
}

(* epilogue *)
{
destruct Hind.
split; intros; eauto.
}
Qed.


Lemma map_positive :
  forall A B i (f : A -> B) (m : term A),
    positive i m
    -> positive i (map_term f m).
Proof.
intros A B i f.
revert i.
exact (map_positive_negative A B f andel).
Qed.


Lemma map_negative :
  forall A B i (f : A -> B) (m : term A),
    negative i m
    -> negative i (map_term f m).
Proof.
intros A B i f.
revert i.
exact (map_positive_negative A B f ander).
Qed.


Lemma map_positive_negative_conv :
  forall A B (f : A -> B),
    (forall i m,
       positive i (map_term f m)
       -> positive i m)
    /\
    (forall i m,
       negative i (map_term f m)
       -> negative i m).
Proof.
intros A B f.
exploit (positive_negative_ind B
           (fun i b => forall a, map_term f a = b -> positive i a)
           (fun i b => forall a, map_term f a = b -> negative i a)) as Hind.

(* var *)
{
intros i a Heq.
revert Heq.
cases a; try (intros; simpmapin Heq; discriminate Heq).
intros n Heq.
simpmapin Heq.
injection Heq.
intros ->.
apply positive_var.
}

(* const *)
{
intros i a b Heq.
so (map_term_sh1_under_form _#6 Heq) as (a' & -> & ->).
apply positive_const.
}

(* prod *)
{
intros i a b _ IH1 _ IH2 c Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr).
so (map_operator_same _#6 Heqth) as H.
invertc H.
intros <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (a' & b' & ->).
fold (prod a' b').
invertc Heqr.
intros <- <-.
apply positive_prod; auto.
}

(* pi *)
{
intros i a b _ IH1 _ IH2 c Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr); clear Heq.
so (map_operator_same _#6 Heqth) as H; clear Heqth.
invertc H.
intros <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (a' & b' & ->).
fold (pi a' b').
invertc Heqr.
intros Heqa Heqb.
apply positive_pi; auto.
}

(* sigma *)
{
intros i a b _ IH1 _ IH2 c Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr); clear Heq.
so (map_operator_same _#6 Heqth) as H; clear Heqth.
invertc H.
intros <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (a' & b' & ->).
fold (sigma a' b').
invertc Heqr.
intros Heqa Heqb.
apply positive_sigma; auto.
}

(* mu *)
{
intros i a _ IH c Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr); clear Heq.
so (map_operator_same _#6 Heqth) as H; clear Heqth.
invertc H.
intros <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (a' & ->).
fold (mu a').
invertc Heqr.
intros Heqa.
apply positive_mu; auto.
}

(* bite *)
{
intros i m a b _ IH1 _ IH2 c Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr); clear Heq.
so (map_operator_same _#6 Heqth) as H; clear Heqth.
invertc H.
intros <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (m' & a' & b' & ->).
fold (bite m' a' b').
invertc Heqr.
intros Heq <- <-.
so (map_term_sh1_under_form _#6 Heq) as (m'' & -> & ->).
apply positive_bite; auto.
}

(* weaken *)
{
intros i a _ IH c Heq.
so (map_term_sh_form _#6 Heq) as (d & -> & ->).
apply positive_weaken; auto.
}

(* reduce *)
{
intros i a b Hred _ IH c <-.
so (map_reduce_form _#5 Hred) as (d & -> & Hred').
apply (positive_reduce _ _ d); auto.
}

(* const *)
{
intros i a b Heq.
so (map_term_sh1_under_form _#6 Heq) as (a' & -> & ->).
apply negative_const.
}

(* prod *)
{
intros i a b _ IH1 _ IH2 c Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr).
so (map_operator_same _#6 Heqth) as H.
invertc H.
intros <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (a' & b' & ->).
fold (prod a' b').
invertc Heqr.
intros <- <-.
apply negative_prod; auto.
}

(* pi *)
{
intros i a b _ IH1 _ IH2 c Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr); clear Heq.
so (map_operator_same _#6 Heqth) as H; clear Heqth.
invertc H.
intros <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (a' & b' & ->).
fold (pi a' b').
invertc Heqr.
intros Heqa Heqb.
apply negative_pi; auto.
}

(* sigma *)
{
intros i a b _ IH1 _ IH2 c Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr); clear Heq.
so (map_operator_same _#6 Heqth) as H; clear Heqth.
invertc H.
intros <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (a' & b' & ->).
fold (sigma a' b').
invertc Heqr.
intros Heqa Heqb.
apply negative_sigma; auto.
}

(* mu *)
{
intros i a _ IH c Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr); clear Heq.
so (map_operator_same _#6 Heqth) as H; clear Heqth.
invertc H.
intros <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (a' & ->).
fold (mu a').
invertc Heqr.
intros Heqa.
apply negative_mu; auto.
}

(* bite *)
{
intros i m a b _ IH1 _ IH2 c Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr); clear Heq.
so (map_operator_same _#6 Heqth) as H; clear Heqth.
invertc H.
intros <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (m' & a' & b' & ->).
fold (bite m' a' b').
invertc Heqr.
intros Heq <- <-.
so (map_term_sh1_under_form _#6 Heq) as (m'' & -> & ->).
apply negative_bite; auto.
}

(* weaken *)
{
intros i a _ IH c Heq.
so (map_term_sh_form _#6 Heq) as (d & -> & ->).
apply negative_weaken; auto.
}

(* reduce *)
{
intros i a b Hred _ IH c <-.
so (map_reduce_form _#5 Hred) as (d & -> & Hred').
apply (negative_reduce _ _ d); auto.
}

(* epilogue *)
{
destruct Hind.
split; intros; eauto.
}
Qed.


Lemma map_positive_conv :
  forall A B i (f : A -> B) (m : term A),
    positive i (map_term f m)
    -> positive i m.
Proof.
intros A B i f.
revert i.
exact (map_positive_negative_conv A B f andel).
Qed.


Lemma map_negative_conv :
  forall A B i (f : A -> B) (m : term A),
    negative i (map_term f m)
    -> negative i m.
Proof.
intros A B i f.
revert i.
exact (map_positive_negative_conv A B f ander).
Qed.


Require Import Candidate.
Require Import Page.
Require Import SemanticsProperty.


Definition ispositive_urel w i (a : wterm stop) : wurel w :=
  property_urel (fun _ => positive 0 a) w i (fun _ h => h).

Definition isnegative_urel w i (a : wterm stop) : wurel w :=
  property_urel (fun _ => negative 0 a) w i (fun _ h => h).
