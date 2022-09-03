
Require Import Tactics.
Require Import Equality.
Require Import Relation.
Require Import Syntax.
Require Import SimpSub.
Require Import Dynamic.


Section object.


Arguments operator {object}.
Arguments term {object}.
Arguments row {object}.

Arguments rw_cons {object i a}.


Variable object : Type.


(* mapped through compatibility *)

Inductive mcr (R : relation (@term object)) : forall {a}, relation (row a) :=
| mcr_nil :
    mcr R rw_nil rw_nil

| mcr_cons {i a m m' r r'} :
    R m m'
    -> mcr R r r'
    -> mcr R (@rw_cons _ i a m r) (@rw_cons _ i a m' r')
.


Inductive mc (R : relation term) : relation term :=
| mc_var {i} :
    mc R (var i) (var i)

| mc_oper {a} {t : operator a} {r r' : row a} :
    mcr R r r'
    -> mc R (oper a t r) (oper a t r')
.


Lemma mc_reverse :
  forall (R R' : @term object -> term -> Prop),
    (forall x y, R x y -> R' y x)
    -> forall x y, mc R x y -> mc R' y x.
Proof.
intros R R' Hrev x y Hxy.
cases Hxy.

(* var *)
{
intro; apply mc_var.
}

(* oper *)
{
intros a th r s H.
apply mc_oper.
induct H; auto using mcr_nil, mcr_cons.
}
Qed.


Lemma mc_mono :
  forall (R R' : @term object -> term -> Prop),
    (forall x y, R x y -> R' x y)
    -> forall x y, mc R x y -> mc R' x y.
Proof.
intros R R' Hmono x y Hxy.
apply (mc_reverse (fun x y => R y x)); auto.
apply (mc_reverse R); auto.
Qed.


Lemma mc_refl :
  forall (R : @term object -> term -> Prop),
    reflexive _ R
    -> reflexive _ (mc R).
Proof.
intros R Hrefl x.
cases x; auto using mc_var.
intros a th r.
apply mc_oper.
induct r; auto using mcr_nil, mcr_cons.
Qed.


Lemma mc_trans :
  forall (R : @term object -> term -> Prop),
    transitive _ R
    -> transitive _ (mc R).
Proof.
intros R Htrans x y z Hxy Hyz.
revert z Hyz.
cases Hxy.

(* var *)
{
intros i z Hyz.
invert Hyz.
intros <-.
apply mc_var.
}

(* oper *)
{
intros a th r s Hrs z Hyz.
invert Hyz.
intros t Hst <-.
apply mc_oper.
clear Hyz.
revert t Hst.
clear th.
induct Hrs; auto using mcr_nil.
intros i a m n r s Hmn _ IH tt Htt.
invert Htt.
intros p t Hnp Hst <-.
apply mcr_cons; auto.
eapply Htrans; eauto.
}
Qed.


Lemma star_mc_impl_mc_star :
  forall (R : @term object -> term -> Prop),
    forall m n,
      star (mc R) m n
      -> mc (star R) m n.
Proof.
intros R m n H.
induct H.

(* refl *)
{
intro x.
apply mc_refl.
intro; apply star_refl.
}

(* step *)
{
intros x y z Hxy _ Hyz.
eapply mc_trans; eauto.
  {
  intro.
  apply star_trans.
  }

  {
  apply (mc_mono R); auto.
  intros; apply star_one; auto.
  }
}
Qed.


Lemma star_mc_impl_mc :
  forall (R : @term object -> term -> Prop),
    reflexive _ R
    -> transitive _ R
    -> forall m n,
         star (mc R) m n
         -> mc R m n.
Proof.
intros R Hrefl Htrans m n Hmn.
so (star_mc_impl_mc_star _#3 Hmn) as H.
apply (mc_mono (star R)); eauto.
eapply star_of_refl_trans; eauto.
Qed.


Lemma mc_value :
  forall R v m,
    mc R v m
    -> value v
    -> value m.
Proof.
intros R v m Hmc Hval.
invertc Hmc.
  {
  intros i <- <-.
  invert Hval; done.
  }

  {
  intros a t r r' _ <- <-.
  invert Hval; [].
  intro Hcanon.
  apply value_i; auto.
  }
Qed.


Lemma mcr_refl :
  forall (P : relation term),
    (forall m, P m m)
    -> forall a (r : row a), mcr P r r.
Proof.
intros P Hrefl a r.
induct r; eauto using mcr.
Qed.


Lemma mc_app :
  forall (P : relation term) m m' n n',
    P m m'
    -> P n n'
    -> mc P (app m n) (app m' n').
Proof.
intros.
apply mc_oper.
eauto using mcr.
Qed.


Lemma mc_lam :
  forall (P : relation term) m m',
    P m m'
    -> mc P (lam m) (lam m').
Proof.
intros.
apply mc_oper.
eauto using mcr.
Qed.


Lemma mc_next :
  forall (P : relation term) m m',
    P m m'
    -> mc P (next m) (next m').
Proof.
intros.
apply mc_oper.
eauto using mcr.
Qed.


Lemma mc_prev :
  forall (P : relation term) m m',
    P m m'
    -> mc P (prev m) (prev m').
Proof.
intros.
apply mc_oper.
eauto using mcr.
Qed.


Lemma mc_bite :
  forall (P : relation term) m m' n n' p p',
    P m m'
    -> P n n'
    -> P p p'
    -> mc P (bite m n p) (bite m' n' p').
Proof.
intros.
apply mc_oper.
eauto using mcr.
Qed.


Lemma mc_ppair :
  forall (P : relation term) m m' n n',
    P m m'
    -> P n n'
    -> mc P (ppair m n) (ppair m' n').
Proof.
intros.
apply mc_oper.
eauto using mcr.
Qed.


Lemma mc_ppi1 :
  forall (P : relation term) m m',
    P m m'
    -> mc P (ppi1 m) (ppi1 m').
Proof.
intros.
apply mc_oper.
eauto using mcr.
Qed.


Lemma mc_ppi2 :
  forall (P : relation term) m m',
    P m m'
    -> mc P (ppi2 m) (ppi2 m').
Proof.
intros.
apply mc_oper.
eauto using mcr.
Qed.


Lemma star_mcr :
  forall R a (r s : @row object a),
    star (mcr R) r s
    -> mcr (star R) r s.
Proof.
intros R a r s Hrs.
induct Hrs.

(* refl *)
{
intros r.
apply mcr_refl.
intro m.
apply star_refl.
}

(* step *)
{
intros r s t Hrs _ IH.
revert t IH.
induct Hrs.
  {
  intros t H.
  invert H.
  intros <-.
  apply mcr_nil.
  }

  {
  intros i a m n r s Hmn _ IH tt Htt.
  invert Htt.
  intros p t Hnp Hst <-.
  so (IH t Hst) as Hrt.
  apply mcr_cons; auto.
  eapply star_step; eauto.
  }
}
Qed.


Inductive reduce : @term object -> @term object -> Prop :=
| reduce_var {i} :
    reduce (var i) (var i)

| reduce_oper {a th r s} :
    reducer r s
    -> reduce (oper a th r) (oper a th s)

| reduce_app_beta {m m' n n'} :
    reduce m m'
    -> reduce n n'
    -> reduce (app (lam m) n) (subst1 n' m')

| reduce_prev_beta {m m'} :
    reduce m m'
    -> reduce (prev (next m)) m'

| reduce_bite_beta1 {n n' p} :
    reduce n n'
    -> reduce (bite btrue n p) n'

| reduce_bite_beta2 {p p' n} :
    reduce p p'
    -> reduce (bite bfalse n p) p'

| reduce_ppi1_beta {m m' n} :
    reduce m m'
    -> reduce (ppi1 (ppair m n)) m'

| reduce_ppi2_beta {n n' m} :
    reduce n n'
    -> reduce (ppi2 (ppair m n)) n'


with reducer : forall {a}, row a -> row a -> Prop :=
| reducer_nil :
    reducer rw_nil rw_nil

| reducer_cons {i a m n r s} :
    reduce m n
    -> reducer r s
    -> reducer (@rw_cons _ i a m r) (@rw_cons _ i a n s)
.


Scheme reduce_mut_ind := Minimality for reduce Sort Prop
with   reducer_mut_ind := Minimality for reducer Sort Prop.


Lemma mcr_reducer :
  forall a (r s : row a),
    mcr reduce r s
    -> reducer r s.
Proof.
intros a r s H.
induct H; eauto using reducer_nil, reducer_cons.
Qed.


Lemma reducer_mcr :
  forall a (r s : row a),
    reducer r s
    -> mcr reduce r s.
Proof.
intros a r s H.
induct H; eauto using mcr_nil, mcr_cons.
Qed.


Lemma reduce_id : forall {m}, reduce m m.
Proof.
intro m.
induct m using
  (fun z => term_mut_ind _ z (fun a r => reducer r r)); eauto using reduce, reducer_nil, reducer_cons.
Qed.


Lemma reduce_compat :
  forall m n,
    mc reduce m n
    -> reduce m n.
Proof.
intros m n H.
induct H; eauto using reduce_id, reduce_oper, mcr_reducer.
Qed.


Lemma reducer_id :
  forall a (r : row a),
    reducer r r.
Proof.
intros a r.
apply mcr_reducer.
apply mcr_refl.
intro; apply reduce_id.
Qed.


Lemma reduce_value_impl :
  forall m n,
    reduce m n
    -> value m
    -> mc reduce m n.
Proof.
intros m n Hreduce Hvalue.
revert Hvalue.
cases Hreduce;
try (intros;
     invert Hvalue;
     intros;
     match goal with
     | H : canon _ _ |- _ => invert H; done
     end).
(* oper *)
intros a th r s H Hvalue.
apply mc_oper.
apply reducer_mcr; auto.
Qed.


Lemma reduces_value_impl :
  forall m n,
    star reduce m n
    -> value m
    -> mc (star reduce) m n.
Proof.
intros m n Hreduce.
induct Hreduce.

(* refl *)
{
intros m _.
apply mc_refl.
intro; apply star_refl.
}

(* trans *)
{
intros m n p Hmn _ IH Hvalm.
so (reduce_value_impl _#2 Hmn Hvalm) as Hmn'.
so (mc_value _#3 Hmn' Hvalm) as Hvaln.
so (IH Hvaln) as Hnp'.
eapply mc_trans; eauto.
  {
  intro; intros.
  eapply star_trans; eauto.
  }

  {
  apply (mc_mono reduce); auto.
  intros x y H.
  apply star_one; auto.
  }
}
Qed.


Lemma step_reduce :
  forall m n,
    step m n
    -> reduce m n.
Proof.
intros m n H.
induct H.

(* app1 *)
{
intros m1 m1' m2 _ IH.
apply reduce_compat.
apply mc_app; auto using reduce_id.
}

(* app2 *)
{
intros m1 m2.
apply reduce_app_beta; auto using reduce_id.
}

(* prev1 *)
{
intros.
apply reduce_compat.
apply mc_prev; auto.
}

(* prev2 *)
{
intros.
apply reduce_prev_beta; auto using reduce_id.
}

(* bite1 *)
{
intros m1 m1' m2 m3 _ IH.
apply reduce_compat.
apply mc_bite; auto using reduce_id.
}

(* bite2 *)
{
intros m1 m2.
apply reduce_bite_beta1.
apply reduce_id.
}

(* bite3 *)
{
intros m1 m2.
apply reduce_bite_beta2.
apply reduce_id.
}

(* ppi11 *)
{
intros.
apply reduce_compat.
apply mc_ppi1; auto.
}

(* ppi12 *)
{
intros.
apply reduce_ppi1_beta.
apply reduce_id.
}

(* ppi21 *)
{
intros.
apply reduce_compat.
apply mc_ppi2; auto.
}

(* ppi22 *)
{
intros.
apply reduce_ppi2_beta.
apply reduce_id.
}
Qed.


Lemma row_1_invert :
  forall i (r : @row object (cons i nil)),
    exists m,
      r = rw_cons m rw_nil.
Proof.
intros i r.
so (row_cons_invert _#3 r) as (m & r1 & ->).
so (row_nil_invert _ r1); subst r1.
eauto.
Qed.

Lemma row_2_invert :
  forall i j (r : @row object (cons i (cons j nil))),
    exists m n,
      r = rw_cons m (rw_cons n rw_nil).
Proof.
intros i j r.
so (row_cons_invert _#3 r) as (m & r1 & ->).
so (row_cons_invert _#3 r1) as (n & r2 & ->).
so (row_nil_invert _ r2); subst r2.
eauto.
Qed.


Lemma reduce_subst :
  forall s m m',
    reduce m m'
    -> reduce (subst s m) (subst s m').
Proof.
intros s m n H.
revert s.
induct H
  using (fun z => reduce_mut_ind z
           (fun a r t =>
              forall s,
                reducer (substr s r) (substr s t))).

(* var *)
{
intros i s.
apply reduce_id.
}

(* oper *)
{
intros a th r t _ IH s.
simpsub.
apply reduce_oper; auto.
}

(* app_beta *)
{
intros m m' n n' _ IH1 _ IH2 s.
simpsub.
relquest.
  {
  eapply reduce_app_beta; eauto.
  }
simpsub.
reflexivity.
}

(* prev_beta *)
{
intros m m' _ IH s.
simpsub.
apply reduce_prev_beta; auto.
}

(* bite_beta1 *)
{
intros n n' p _ IH s.
simpsub.
eapply reduce_bite_beta1; eauto.
}

(* bite_beta2 *)
{
intros n n' p _ IH s.
simpsub.
eapply reduce_bite_beta2; eauto.
}

(* ppi1_beta *)
{
intros.
simpsub.
eapply reduce_ppi1_beta; auto.
}

(* ppi1_beta *)
{
intros.
simpsub.
eapply reduce_ppi2_beta; auto.
}

(* nil *)
{
intros s.
apply reducer_nil.
}

(* cons *)
{
intros i a m m' r r' _ IH1 _ IH2 s.
simpsub.
apply reducer_cons; auto.
}
Qed.


Lemma reduces_subst :
  forall s m m',
    star reduce m m'
    -> star reduce (subst s m) (subst s m').
Proof.
intros s m m' Hreduces.
eapply star_map'; eauto.
intros; eapply reduce_subst; eauto.
Qed.


Combined Scheme reduce_reducer_ind from reduce_mut_ind, reducer_mut_ind.


Lemma reduce_reducer_funct1_under :
  forall n n',
    reduce n n'
    -> (forall i m m',
          reduce m m'
          -> reduce (subst (under i (dot n id)) m) (subst (under i (dot n' id)) m'))
       /\
       (forall i a (r r' : row a),
          reducer r r'
          -> reducer (substr (under i (dot n id)) r) (substr (under i (dot n' id)) r')).
Proof.
intros n n' Hn.
exploit (reduce_reducer_ind
           (fun m m' => forall i, reduce (subst (under i (dot n id)) m) (subst (under i (dot n' id)) m'))
           (fun a r r' => forall i, reducer (substr (under i (dot n id)) r) (substr (under i (dot n' id)) r'))) as Hind; try (intros; simpsub; eauto using reduce, reducer_nil, reducer_cons; done).

(* var *)
{
intros i j.
simpsub.
so (lt_eq_lt_dec i j) as [[Hij | Heq] | Hji].
  {
  rewrite -> !project_under_lt; try omega.
  apply reduce_id.
  }

  {
  subst j.
  rewrite -> !project_under_eq.
  simpsub.
  apply reduce_subst; auto.
  }

  {
  rewrite -> !project_under_geq; try omega.
  replace (i - j) with (S (pred (i - j))) by omega.
  simpsub.
  apply reduce_id.
  }
}

(* app_beta *)
{
intros m m' p p' _ IH1 _ IH2 i.
simpsub.
relquest.
  {
  eapply reduce_app_beta; auto.
  rewrite <- under_succ.
  apply IH1.
  }
simpsub.
reflexivity.
}

(* wrapup *)
{
destruct Hind.
split; intros; eauto.
}
Qed.


Lemma reduce_funct1_under :
  forall i n n' m m',
    reduce n n'
    -> reduce m m'
    -> reduce (subst (under i (dot n id)) m) (subst (under i (dot n' id)) m').
Proof.
intros i n n' m m' Hn Hm.
revert i m m' Hm.
exact (reduce_reducer_funct1_under n n' Hn andel).
Qed.


Lemma reducer_funct1_under :
  forall i a n n' (r r' : row a),
    reduce n n'
    -> reducer r r'
    -> reducer (substr (under i (dot n id)) r) (substr (under i (dot n' id)) r').
Proof.
intros i a n n' m m' Hn Hm.
revert i a m m' Hm.
exact (reduce_reducer_funct1_under n n' Hn ander).
Qed.


Lemma reduce_funct1 :
  forall n n' m m',
    reduce n n'
    -> reduce m m'
    -> reduce (subst1 n m) (subst1 n' m').
Proof.
intros n n' m m' Hn Hm.
unfold subst1.
rewrite <- (under_zero _ (dot n id)).
rewrite <- (under_zero _ (dot n' id)).
apply reduce_funct1_under; auto.
Qed.


Lemma reducer_funct1 :
  forall a n n' (r r' : row a),
    reduce n n'
    -> reducer r r'
    -> reducer (substr (dot n id) r) (substr (dot n' id) r').
Proof.
intros a n n' m m' Hn Hm.
rewrite <- (under_zero _ (dot n id)).
rewrite <- (under_zero _ (dot n' id)).
apply reducer_funct1_under; auto.
Qed.


Lemma diamond :
  forall m n p,
    reduce m n
    -> reduce m p
    -> exists q,
         reduce n q
         /\ reduce p q.
Proof.
intros m n p Hmn Hmp.
revert p Hmp.
induct Hmn using
  (fun z => reduce_mut_ind z
     (fun a r s => forall t, reducer r t -> exists u, reducer s u /\ reducer t u)).

(* var *)
{
intros i p Hmp.
exists p.
split; auto using reduce_id.
}

(* oper *)
{
intros a th r s Hrs IH p Hmp.
invertc Hmp.
  {
  intros t Hrt <-.
  so (IH _ Hrt) as (u & Hsu & Htu).
  exists (oper a th u).
  split; auto using reduce_oper.
  }

  (* oper / app_beta *)
  {
  intros m m2 n n2 Hm2 Hn2 <- Heqth Heqr <-.
  so (eq_dep_impl_eq_snd _#5 Heqth); subst th.
  so (eq_dep_impl_eq_snd _#5 Heqr); subst r.
  clear Heqth Heqr.
  invertc Hrs.
  intros a r1 Ha Hr1 <-.
  invertc Hr1.
  intros n1 r2 Hn1 Hr2 <-.
  invertc Hr2.
  intros <-.
  invertc Ha.
  intros r1 Hr1 <-.
  invertc Hr1.
  intros m1 r2 Hm1 Hr2 <-.
  invertc Hr2.
  intros <-.
  fold (lam m1) in *.
  fold (app (lam m1) n1) in *.
  so (IH _ (reducer_cons (reduce_compat _ _ (mc_lam _#3 Hm2)) (reducer_cons Hn2 reducer_nil))) as (u & Hsu & Htu).
  invertc Htu.
  intros a r1 Ha Hr1 <-.
  invertc Hr1.
  intros q r2 Hq2 Hr2 <-.
  invertc Hr2.
  intros <-.
  invertc Ha.
  intros r1 Hr1 <-.
  invertc Hr1.
  intros p r2 Hp2 Hr2 <-.
  invertc Hr2.
  intros <-.
  fold (lam p) in Hsu.
  invertc Hsu.
  intros Ha Hr1.
  invertc Hr1.
  intros Hq1 _.
  invertc Ha.
  intros Hr1 _.
  invertc Hr1.
  intros Hp1 _.
  exists (subst1 q p).
  split.
    {
    apply reduce_app_beta; auto.
    }

    {
    apply reduce_funct1; auto.
    }
  }

  (* oper / prev_beta *)
  {
  intros m Hmp <- Heqth Heqr.
  so (eq_dep_impl_eq_snd _#5 Heqth); subst th.
  so (eq_dep_impl_eq_snd _#5 Heqr); subst r.
  clear Heqth Heqr.
  invertc Hrs.
  intros nn r1 Hnn Hr1 <-.
  invertc Hr1.
  intros <-.
  fold (prev nn).
  invertc Hnn.
  intros r1 Hr1 <-.
  invertc Hr1.
  intros n r2 Hmn Hr2 <-.
  invertc Hr2.
  intros <-.
  fold (next n) in *.
  so (IH _ (reducer_cons (reduce_compat _ _ (mc_next _#3 Hmp)) reducer_nil)) as (u & Hsu & Htu).
  invertc Htu.
  intros qq r1 Hqq Hr <-.
  invertc Hr.
  intros <-.
  invertc Hqq.
  intros r1 Hr1 <-.
  invertc Hr1.
  intros q r2 Hpq Hr2 <-.
  invertc Hr2.
  intros <-.
  fold (next q) in *.
  invertc Hsu.
  intros H _.
  invertc H.
  intros H _.
  invertc H.
  intros Hnq _.
  exists q.
  split; auto.
  apply reduce_prev_beta; auto.
  }

  (* oper / bite_beta1 *)
  {
  intros m2 m3 Hmp <- Heqth Heqr.
  injectionT Heqth.
  intros <-.
  injectionT Heqr.
  intros <-.
  invertc Hrs.
  intros n1 r1 Hn1 Hr1 <-.
  invertc Hr1.
  intros n2 r2 Hn2 Hr2 <-.
  invertc Hr2.
  intros n3 r3 Hn3 Hr3 <-.
  invertc Hr3.
  intros <-.
  fold (bite n1 n2 n3) in *.
  so (IH _ (reducer_cons reduce_id (reducer_cons Hmp (reducer_cons reduce_id reducer_nil)))) as (u & Hru & Hsu).
  invertc Hsu.
  intros q1 r1 _ Hr1 <-.
  invertc Hr1.
  intros q2 r2 Hmq2 Hr2 <-.
  invertc Hr2.
  intros q3 r3 Hmq3 Hr3 <-.
  invertc Hr3.
  intros <-.
  invertc Hn1.
  intros r1 Hr1 <-.
  invertc Hr1.
  intros <-.
  fold (@btrue object) in *.
  invertc Hru.
  intros _ Hr2.
  invertc Hr2.
  intros Hnq2 _.
  exists q2.
  split; auto.
  apply reduce_bite_beta1; auto.
  }

  (* oper / bite_beta2 *)
  {
  intros m2 m3 Hmp <- Heqth Heqr.
  injectionT Heqth.
  intros <-.
  injectionT Heqr.
  intros <-.
  invertc Hrs.
  intros n1 r1 Hn1 Hr1 <-.
  invertc Hr1.
  intros n2 r2 Hn2 Hr2 <-.
  invertc Hr2.
  intros n3 r3 Hn3 Hr3 <-.
  invertc Hr3.
  intros <-.
  fold (bite n1 n2 n3) in *.
  so (IH _ (reducer_cons reduce_id (reducer_cons reduce_id (reducer_cons Hmp reducer_nil)))) as (u & Hru & Hsu).
  invertc Hsu.
  intros q1 r1 _ Hr1 <-.
  invertc Hr1.
  intros q2 r2 Hmq2 Hr2 <-.
  invertc Hr2.
  intros q3 r3 Hmq3 Hr3 <-.
  invertc Hr3.
  intros <-.
  invertc Hn1.
  intros r1 Hr1 <-.
  invertc Hr1.
  intros <-.
  fold (@bfalse object) in *.
  invertc Hru.
  intros _ Hr2.
  invertc Hr2.
  intros _ Hr3.
  invertc Hr3.
  intros Hnq3 _.
  exists q3.
  split; auto.
  apply reduce_bite_beta2; auto.
  }

  (* oper / ppi1_beta *)
  {
  intros m n Hmp <- Heqth Heqr.
  injectionT Heqth.
  intros <-.
  injectionT Heqr.
  intros <-.
  invertc Hrs.
  intros mn r1 Hmn Hr1 <-.
  invertc Hr1.
  intros <-.
  fold (ppi1 mn).
  invertc Hmn.
  intros r1 Hr1 <-.
  invertc Hr1.
  intros m' r2 Hm Hr2 <-.
  invertc Hr2.
  intros n' r3 Hn Hr3 <-.
  invertc Hr3.
  intros <-.
  fold (ppair m' n') in *.
  so (IH _ (reducer_cons (reduce_compat _ _ (mc_ppair _#5 Hmp reduce_id)) (reducer_id _ _))) as (u & Hru & Hsu).
  invertc Hsu.
  intros q r1 Hq Hr1 <-.
  invertc Hr1.
  intros <-.
  invertc Hq.
  intros r1 Hr1 <-.
  invertc Hr1.
  intros q1 r2 Hp_q1 Hr2 <-.
  invertc Hr2.
  intros q2 r3 Hn_q2 Hr3 <-.
  invertc Hr3.
  intros <-.
  fold (ppair q1 q2) in *.
  invertc Hru.
  intros H _.
  invertc H.
  intros H _.
  invertc H.
  intros Hm'_q1 H.
  invertc H.
  intros Hn'_q2 _.
  exists q1.
  split; auto.
  apply reduce_ppi1_beta; auto.
  }

  (* oper / ppi2_beta *)
  {
  intros m n Hmp <- Heqth Heqr.
  injectionT Heqth.
  intros <-.
  injectionT Heqr.
  intros <-.
  invertc Hrs.
  intros mn r1 Hmn Hr1 <-.
  invertc Hr1.
  intros <-.
  fold (ppi1 mn).
  invertc Hmn.
  intros r1 Hr1 <-.
  invertc Hr1.
  intros m' r2 Hm Hr2 <-.
  invertc Hr2.
  intros n' r3 Hn Hr3 <-.
  invertc Hr3.
  intros <-.
  fold (ppair m' n') in *.
  so (IH _ (reducer_cons (reduce_compat _ _ (mc_ppair _#5 reduce_id Hmp)) (reducer_id _ _))) as (u & Hru & Hsu).
  invertc Hsu.
  intros q r1 Hq Hr1 <-.
  invertc Hr1.
  intros <-.
  invertc Hq.
  intros r1 Hr1 <-.
  invertc Hr1.
  intros q1 r2 Hp_q1 Hr2 <-.
  invertc Hr2.
  intros q2 r3 Hn_q2 Hr3 <-.
  invertc Hr3.
  intros <-.
  fold (ppair q1 q2) in *.
  invertc Hru.
  intros H _.
  invertc H.
  intros H _.
  invertc H.
  intros Hm'_q1 H.
  invertc H.
  intros Hn'_q2 _.
  exists q2.
  split; auto.
  apply reduce_ppi2_beta; auto.
  }
}

(* app_beta *)
{
intros m m1 n n1 Hm1 IH1 Hn1 IH2 p Hmp.
invertc Hmp.
  (* app_beta / oper *)
  {
  intros s Hs <-.
  invertc Hs.
  intros a r1 Ha Hr1 <-.
  invertc Hr1.
  intros n2 r2 Hn2 Hr2 <-.
  invertc Hr2.
  intros <-.
  invertc Ha.
  intros r1 Hr1 <-.
  invertc Hr1.
  intros m2 r2 Hm2 Hr2 <-.
  invertc Hr2.
  intros <-.
  fold (lam m2).
  fold (app (lam m2) n2).
  so (IH1 _ Hm2) as (p & Hp1 & Hp2).
  so (IH2 _ Hn2) as (q & Hq1 & Hq2).
  exists (subst1 q p).
  split.
    {
    apply reduce_funct1; auto.
    }

    {
    apply reduce_app_beta; auto.
    }
  }

  (* app_beta / app_beta *)
  {
  intros m2 n2 Hm2 Hn2 <-.
  so (IH1 _ Hm2) as (p & Hp1 & Hp2).
  so (IH2 _ Hn2) as (q & Hq1 & Hq2).
  exists (subst1 q p).
  split; apply reduce_funct1; auto.
  }
}

(* prev_beta *)
{
intros m n _ IH t Hmt.
invertc Hmt.
  (* prev_beta / oper *)
  {
  intros r Hr <-.
  invertc Hr.
  intros t r1 Ht Hr1 <-.
  invertc Hr1.
  intros <-.
  invertc Ht.
  intros r1 Hr1 <-.
  invertc Hr1.
  intros p r2 Hmp Hr2 <-.
  invertc Hr2.
  intros <-.
  fold (next p).
  fold (prev (next p)).
  so (IH _ Hmp) as (q & Hmq & Hpq).
  exists q.
  split; auto.
  apply reduce_prev_beta; auto.
  }

  (* prev_beta / prev_beta *)
  {
  intros Hmt.
  so (IH _ Hmt) as (q & Hnq & Hpq).
  eauto.
  }
}

(* bite_beta1 *)
{
intros m m1 n Hm1 IH p Hmp.
invertc Hmp.
  (* bite_beta1 / oper *)
  {
  intros s Hs <-.
  invertc Hs.
  intros a r1 Ha Hr1 <-.
  invertc Hr1.
  intros b r2 Hb Hr2 <-.
  invertc Hr2.
  intros c r3 Hc Hr3 <-.
  invertc Hr3.
  intros <-.
  fold (bite a b c).
  invertc Ha.
  intros r Hr <-.
  invertc Hr.
  intros <-.
  fold (@btrue object).
  so (IH _ Hb) as (q & Hm1q & Hbq).
  exists q.
  split; auto.
  apply reduce_bite_beta1; auto.
  }

  (* bite_beta1 / bite_beta1 *)
  {
  intros Hmp.
  so (IH _ Hmp) as (q & Hm1q & Hpq).
  eauto.
  }
}

(* bite_beta2 *)
{
intros m m1 n Hm1 IH p Hmp.
invertc Hmp.
  (* bite_beta2 / oper *)
  {
  intros s Hs <-.
  invertc Hs.
  intros a r1 Ha Hr1 <-.
  invertc Hr1.
  intros b r2 Hb Hr2 <-.
  invertc Hr2.
  intros c r3 Hc Hr3 <-.
  invertc Hr3.
  intros <-.
  fold (bite a b c).
  invertc Ha.
  intros r Hr <-.
  invertc Hr.
  intros <-.
  fold (@btrue object).
  so (IH _ Hc) as (q & Hm1q & Hbq).
  exists q.
  split; auto.
  apply reduce_bite_beta2; auto.
  }

  (* bite_beta1 / bite_beta1 *)
  {
  intros Hmp.
  so (IH _ Hmp) as (q & Hm1q & Hpq).
  eauto.
  }
}

(* ppi1_beta *)
{
intros m m1 n Hm1 IH p Hmp.
invertc Hmp.
  {
  intros s Hs <-.
  invertc Hs.
  intros a r1 Ha Hr1 <-.
  invertc Hr1.
  intros <-.
  fold (ppi1 a).
  invertc Ha.
  intros s Hs <-.
  invertc Hs.
  intros b r1 Hb Hr1 <-.
  invertc Hr1.
  intros c r2 Hc Hr2 <-.
  invertc Hr2.
  intros <-.
  fold (ppair b c).
  so (IH _ Hb) as (q & Hm1q & Hbq).
  exists q.
  split; auto.
  apply reduce_ppi1_beta; auto.
  }

  {
  intros Hmp.
  so (IH _ Hmp) as (q & Hm1q & Hpq).
  eauto.
  }
}

(* ppi2_beta *)
{
intros m m1 n Hm1 IH p Hmp.
invertc Hmp.
  {
  intros s Hs <-.
  invertc Hs.
  intros a r1 Ha Hr1 <-.
  invertc Hr1.
  intros <-.
  fold (ppi1 a).
  invertc Ha.
  intros s Hs <-.
  invertc Hs.
  intros b r1 Hb Hr1 <-.
  invertc Hr1.
  intros c r2 Hc Hr2 <-.
  invertc Hr2.
  intros <-.
  fold (ppair b c).
  so (IH _ Hc) as (q & Hm1q & Hbq).
  exists q.
  split; auto.
  apply reduce_ppi2_beta; auto.
  }

  {
  intros Hmp.
  so (IH _ Hmp) as (q & Hm1q & Hpq).
  eauto.
  }
}

(* nil *)
{
intros t H.
invertc H.
intros <-.
exists rw_nil; split; apply reducer_nil.
}

(* cons *)
{
intros i a m m1 r r1 _ IH1 _ IH2 s Hs.
invertc Hs.
intros m2 r2 Hm2 Hr2 <-.
so (IH1 _ Hm2) as (p & Hp1 & Hp2).
so (IH2 _ Hr2) as (s & Hs1 & Hs2).
exists (rw_cons p s).
split; apply reducer_cons; auto.
}
Qed.


Lemma confluence :
  forall m n p,
    star reduce m n
    -> star reduce m p
    -> exists q,
         star reduce n q
         /\ star reduce p q.
Proof.
intros m n p Hmn Hmp.
revert p Hmp.
induct Hmn.

(* refl *)
{
intros m p Hmp.
exists p.
split; auto.
apply star_refl.
}

(* step *)
{
intros m q n Hmq Hqn IH p Hmp.
assert (exists r, reduce p r /\ star reduce q r) as (r & Hpr & Hqr).
  {
  clear n Hqn IH.
  revert q Hmq.
  induct Hmp.
    (* refl *)
    {
    intros m q Hmq.
    exists q.
    split; auto.
    apply star_refl.
    }

    (* step *)
    {
    intros m r p Hmr _ IH q Hmq.
    so (diamond _#3 Hmr Hmq) as (s & Hrs & Hqs).
    so (IH _ Hrs) as (t & Hpt & Hrt).
    exists t.
    split; auto.
    eapply star_step; eauto.
    }
  }
so (IH _ Hqr) as (s & Hns & Hps).
exists s.
split; auto.
eapply star_step; eauto.
}
Qed.


Lemma reduce_var_form :
  forall i m,
    reduce (var i) m
    -> m = var i.
Proof.
intros i m H.
invertc H.
auto.
Qed.


Lemma reduces_var_form :
  forall i m,
    star reduce (var i) m
    -> m = var i.
Proof.
intros i m H.
remember (var i) as n eqn:Heq.
revert Heq.
induct H; auto.
intros m1 m2 m3 H12 _ IH ->.
so (reduce_var_form _#2 H12); subst m2.
apply IH; auto.
Qed.


Lemma reduce_canon_form :
  forall a (th : @operator object a) r m,
    canon _ th
    -> reduce (oper a th r) m
    -> exists s, m = oper a th s /\ reducer r s.
Proof.
intros a th r m Hcanon Hreduce.
invert Hreduce.

(* oper *)
{
intros s Hrs <-.
exists s.
auto.
}

(* app_beta *)
{
intros _ _ _ _ _ _ <- Heq _ _.
injectionT Heq.
intros <-.
invert Hcanon.
}

(* prev_beta *)
{
intros _ _ <- Heq _.
injectionT Heq.
intros <-.
invert Hcanon.
}

(* bite_beta1 *)
{
intros _ _ _ <- Heq _.
injectionT Heq.
intros <-.
invert Hcanon.
}

(* bite_beta2 *)
{
intros _ _ _ <- Heq _.
injectionT Heq.
intros <-.
invert Hcanon.
}

(* ppi1_beta *)
{
intros _ _ _ <- Heq _.
injectionT Heq.
intros <-.
invert Hcanon.
}

(* ppi2_beta *)
{
intros _ _ _ <- Heq _.
injectionT Heq.
intros <-.
invert Hcanon.
}
Qed.


Lemma reduces_canon_form :
  forall a (th : @operator object a) r m,
    canon _ th
    -> star reduce (oper a th r) m
    -> exists s, m = oper a th s /\ star reducer r s.
Proof.
intros a th r m Hcanon Hreduces.
remember (oper a th r) as n eqn:Heq.
revert r Heq.
induct Hreduces.

(* refl *)
{
intros ? r ->.
exists r; auto using star_refl.
}

(* step *)
{
intros ? m n Hreduce _ IH r ->.
so (reduce_canon_form _#4 Hcanon Hreduce) as (s & -> & Hrs).
so (IH s (eq_refl _)) as (t & -> & Hst).
exists t.
split; auto.
eapply star_trans; eauto using star_one.
}
Qed.


Lemma reduces_lam_form :
  forall m n,
    star reduce (lam m) n
    -> exists m',
         n = lam m'
         /\ star reduce m m'.
Proof.
intros m n Hreduces.
so (reduces_canon_form _#4 (canon_lam _) Hreduces) as (r & -> & Hr).
so (star_mcr _#4 (star_mono _#3 (reducer_mcr _) _ _ Hr)) as H; clear Hr.
invertc H.
intros m' r1 Hm Hr1 <-.
invertc Hr1.
intros <-.
fold (lam m').
exists m'; auto.
Qed.


Lemma reduces_triv_form :
  forall (m : @term object),
    star reduce triv m
    -> m = triv.
Proof.
intros m Hred.
so (reduces_canon_form _#4 (canon_triv _) Hred) as (r & -> & Hr).
so (star_mcr _#4 (star_mono _#3 (reducer_mcr _) _ _ Hr)) as H; clear Hr.
invertc H.
intros <-.
reflexivity.
Qed.


Definition rigid (m : @term object) : Prop
  :=
  forall n,
    star reduce m n
    -> ((forall p, n <> lam p) /\ (forall p, n <> prev p)).


Lemma rigid_var :
  forall i, rigid (var i).
Proof.
intros i.
intros n Hreduce.
cut (n = var i).
  {
  intros ->.
  split; intros n Heq; discriminate Heq.
  }
remember (var i) as m eqn:Heq.
revert Heq.
induct Hreduce; auto.
intros m n p Hreduce _ IH ->.
invert Hreduce.
intros <-.
apply IH; auto.
Qed.


Lemma rigid_app :
  forall (m n : @term object),
    rigid m
    -> rigid (app m n).
Proof.
intros m n Hrigid.
intros p Hreduces.
remember (app m n) as mn eqn:Heq.
revert m n Hrigid Heq.
induct Hreduces.

(* refl *)
{
intros ? m n Hrigid ->.
split; intros ? Heq; discriminate Heq.
}

(* step *)
{
intros a b c Hab _ IH m1 n Hrigid ->.
invertc Hab.
2:{
  intros r _ _ _ _ <- _.
  exfalso.
  exact (Hrigid _ (star_refl _) andel _ (eq_refl _)).
  }
intros r Hreduce <-.
invertc Hreduce.
intros m2 r1 Hm12 Hr1 <-.
invertc Hr1.
intros n2 r2 Hn12 Hr2 <-.
invertc Hr2.
intros <-.
fold (app m2 n2) in IH.
apply (IH m2 n2); auto.
intros m3 Hm23.
apply Hrigid.
eapply star_step; eauto.
}
Qed.


Lemma reduce_rigid :
  forall (m n : @term object),
    reduce m n
    -> rigid m
    -> rigid n.
Proof.
intros m n Hreduce Hrigid.
intros p Hnp.
apply Hrigid; eauto using star_step.
Qed.


Lemma reduce_app_form :
  forall (m n p : @term object),
    rigid m
    -> reduce (app m n) p
    -> exists m' n', p = app m' n' /\ reduce m m' /\ reduce n n'.
Proof.
intros m n p Hrigid Hreduce.
invertc Hreduce.

(* oper *)
{
intros r Hreduce <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (m' & n' & ->).
fold (app m' n').
invertc Hreduce.
intros Hm Hreduce.
invertc Hreduce.
intros Hn _.
exists m', n'.
auto.
}

(* app_beta *)
{
intros m' _ _ _ _ <- _.
exfalso.
exact (Hrigid (lam m') (star_refl _) andel _ (eq_refl _)).
}
Qed.


Lemma reduces_app_form :
  forall (m n p : @term object),
    rigid m
    -> star reduce (app m n) p
    -> exists m' n', p = app m' n' /\ star reduce m m' /\ star reduce n n'.
Proof.
intros m n p Hrigid Hreduces.
remember (app m n) as mn eqn:Heq.
revert m n Hrigid Heq.
induct Hreduces.

(* refl *)
{
intros ? m n Hrigid ->.
exists m, n; auto using star_refl.
}

(* step *)
{
intros x b c Hreduce _ IH m n Hrigid ->.
so (reduce_app_form _#3 Hrigid Hreduce) as (m' & n' & -> & Hm & Hn).
so (IH _ _ (reduce_rigid _ _ Hm Hrigid) (eq_refl _)) as (m'' & n'' & -> & Hm' & Hn').
exists m'', n''.
do2 2 split; eauto using star_step.
}
Qed.


End object.


Arguments mcr {object}.
Arguments mc {object}.
Arguments mcr_nil {object}.
Arguments mcr_cons {object}.
Arguments mc_var {object}.
Arguments mc_oper {object}.
Arguments reduce {object}.
Arguments reducer {object a}.
Arguments reducer_nil {object}.
Arguments reducer_cons {object i a}.
Arguments rigid {object}.


Ltac invertc_mcr H :=
  revertnew
  (repeat (invertc H; []; intros ? ? ? H <-); invertc H; []; intros <-).


Ltac invertc_mc H :=
  let H' := fresh
  in
    invertc H; []; intros ? H'; invertc_mcr H'.
