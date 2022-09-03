
Require Import Coq.Lists.List.

Require Import Axioms.
Require Import Tactics.
Require Import Sigma.
Require Import Sequence.
Require Import Relation.
Require Import Ordinal.
Require Import Syntax.
Require Import SimpSub.
Require Import Dynamic.
Require Import Uniform.
Require Import Intensional.
Require Import Candidate.
Require Import Extend.
Require Import SemanticsKnot.
Require Import Promote.
Require Import MapTerm.
Require Import Uniform.
Require Import Model.
Require Import Truncate.
Require Import Standard.
Require Import ProperDownward.
Require Import Hygiene.
Require Import ProperClosed.
Require Import Ofe.
Require Import System.
Require Import Equality.
Require Export ContextHygiene.
Require Import SemanticsUniv.
Require Import SemanticsProperty.
Require Import SemanticsEqtype.
Require Import SemanticsSubtype.
Require Import SemanticsKuniv.
Require Import ProperFun.
Require Import ProperLevel.
Require Import Equivalence.


Inductive smaller : nat -> nat -> bool -> Prop :=
| smaller_le :
    forall i j,
      i <= j
      -> smaller i j false

| smaller_lt :
    forall i j,
      i < j
      -> smaller i j true
.


(* In the "later" cases, I really should have grouped all the only-if-positive
   premises together under a single guard so they could be reasoned about together,
   but I'm not going back and changing it now.
*)

Inductive seqhyp i : sterm -> sterm -> shyp -> shyp -> Prop :=
| seqhyp_tpl :
    forall a a' R,
      (i > 0 -> interp toppg true (pred i) a R)
      -> (i > 0 -> interp toppg false (pred i) a' R)
      -> hygiene clo a
      -> hygiene clo a'
      -> seqhyp i a a' hyp_tpl hyp_tpl

| seqhyp_tp :
    forall a a' R,
      interp toppg true i a R
      -> interp toppg false i a' R
      -> seqhyp i a a' hyp_tp hyp_tp

| seqhyp_tml :
    forall m m' a a' R,
      (i > 0 -> interp toppg true (pred i) a R)
      -> (i > 0 -> interp toppg false (pred i) a' R)
      -> (i > 0 -> rel (den R) (pred i) m m')
      -> hygiene clo m
      -> hygiene clo m'
      -> hygiene clo a
      -> hygiene clo a'
      -> seqhyp i m m' (hyp_tml a) (hyp_tml a')

| seqhyp_tm :
    forall m m' a a' R,
      interp toppg true i a R
      -> interp toppg false i a' R
      -> rel (den R) i m m'
      -> seqhyp i m m' (hyp_tm a) (hyp_tm a')

| seqhyp_emp :
    forall m m',
      hygiene clo m
      -> hygiene clo m'
      -> seqhyp i m m' hyp_emp hyp_emp
.


Inductive seqctx i : ssub -> ssub -> scontext -> Prop :=
| seqctx_nil :
    forall n,
      seqctx i (sh n) (sh n) nil

| seqctx_cons :
    forall m m' s s' h G,
      seqctx i s s' G
      -> seqhyp i m m' (substh s h) (substh s' h)
      -> seqctx i (dot m s) (dot m' s') (cons h G)
.


Inductive relhyp i z : shyp -> shyp -> Prop :=
| relhyp_tpl :
    relhyp i z hyp_tpl hyp_tpl

| relhyp_tp :
    relhyp i z hyp_tp hyp_tp

| relhyp_tml :
    forall a a' R,
      (i > 0 -> interp toppg z (pred i) a R)
      -> (i > 0 -> interp toppg z (pred i) a' R)
      -> hygiene clo a
      -> hygiene clo a'
      -> relhyp i z (hyp_tml a) (hyp_tml a')

| relhyp_tm :
    forall a a' R,
      interp toppg z i a R
      -> interp toppg z i a' R
      -> relhyp i z (hyp_tm a) (hyp_tm a')

| relhyp_emp :
    relhyp i z hyp_emp hyp_emp
.


Definition qpromote {object} (b : bool) (G : @context object) := if b then promote G else G.
Definition qpromote_hyp {object} (b : bool) (h : @hyp object) := if b then promote_hyp h else h.


Inductive pwctx : nat -> ssub -> ssub -> scontext -> Prop :=
| pwctx_nil :
    forall i n,
      pwctx i (sh n) (sh n) nil

| pwctx_cons :
    forall i m m' s s' h G,
      pwctx i s s' G
      -> seqhyp i m m' (substh s h) (substh s' h)
      -> (forall j b s'',
            smaller j i b
            -> seqctx j s s'' (qpromote b G)
            -> relhyp j false (substh s' (qpromote_hyp b h)) (substh s'' (qpromote_hyp b h)))
      -> (forall j b s'',
            smaller j i b
            -> seqctx j s'' s' (qpromote b G)
            -> relhyp j true (substh s (qpromote_hyp b h)) (substh s'' (qpromote_hyp b h)))
      -> pwctx i (dot m s) (dot m' s') (cons h G)
.


Inductive seq : scontext -> judgement -> Prop :=
| seq_i :
    forall G m n a,
      (forall i s s',
         pwctx i s s' G
         -> exists R,
              interp toppg true i (subst s a) R
              /\ interp toppg false i (subst s' a) R
              /\ rel (den R) i (subst s m) (subst s' m)
              /\ rel (den R) i (subst s n) (subst s' n)
              /\ rel (den R) i (subst s m) (subst s' n))
      -> seq G (deq m n a).


Lemma substh_promote_hyp :
  forall object (s : @sub object) h,
    substh s (promote_hyp h) = promote_hyp (substh s h).
Proof.
intros object s h.
induct h; simpsub; cbn; auto.
Qed.


Lemma promote_hyp_idem :
  forall object (h : @hyp object), promote_hyp (promote_hyp h) = promote_hyp h.
Proof.
intros object h.
cases h; auto.
Qed.


Lemma promote_idem :
  forall object (G : @context object), promote (promote G) = promote G.
Proof.
intros object G.
unfold promote.
rewrite -> List.map_map.
f_equal.
fextensionality 1.
intro; apply promote_hyp_idem.
Qed.  


Lemma length_promote :
  forall object (G : @context object), length (promote G) = length G.
Proof.
intros object G.
induct G; intros; cbn; f_equal; auto.
Qed.


Lemma ctxpred_promote :
  forall object (G : @context object),
    ctxpred (promote G) = ctxpred G.
Proof.
intros object G.
rewrite -> !ctxpred_length.
rewrite -> length_promote.
reflexivity.
Qed.


Lemma promote_append :
  forall object (G1 G2 : @context object),
    promote (G1 ++ G2) = promote G1 ++ promote G2.
Proof.
intros object G1 G2.
induct G1; intros; cbn; f_equal; auto.
Qed.


(* Smallerness *)

Lemma smaller_refl :
  forall i, smaller i i false.
Proof.
intros i.
apply smaller_le; auto.
Qed.


Lemma smaller_trans :
  forall i1 i2 i3 b1 b2,
    smaller i1 i2 b1
    -> smaller i2 i3 b2
    -> smaller i1 i3 (orb b1 b2).
Proof.
intros i1 i2 i3 b1 b2 H12.
cases H12.

(* le *)
{
intros i1 i2 Hi12 H23.
revert Hi12.
cases H23.
  {
  intros i2 i3 Hi23 Hi12.
  apply smaller_le; auto.
  omega.
  }

  {
  intros i2 i3 Hi23 Hi12.
  apply smaller_lt; auto.
  omega.
  }
}

(* lt *)
{
intros i1 i2 Hi12 H23.
revert Hi12.
cases H23.
  {
  intros i2 i3 Hi23 Hi12.
  apply smaller_lt; auto.
  omega.
  }

  {
  intros i2 i3 Hi23 Hi12.
  apply smaller_lt; auto.
  omega.
  }
}
Qed.


Lemma smaller_impl_le :
  forall i j b, smaller i j b -> i <= j.
Proof.
intros i j b H.
cases H; intros; omega.
Qed.


(* QPromote *)

Lemma substh_qpromote_hyp :
  forall object (s : @sub object) b h,
    substh s (qpromote_hyp b h) = qpromote_hyp b (substh s h).
Proof.
intros object s b h.
induct b; cbn; auto using substh_promote_hyp.
Qed.


Lemma qpromote_hyp_combine :
  forall object b b' (h : @hyp object),
    qpromote_hyp b (qpromote_hyp b' h) = qpromote_hyp (orb b b') h.
Proof.
intros object b b' h.
destruct b; destruct b'; auto.
cbn.
rewrite -> promote_hyp_idem; auto.
Qed.


Lemma qpromote_combine :
  forall object b b' (G : @context object),
    qpromote b (qpromote b' G) = qpromote (orb b b') G.
Proof.
intros object b b' G.
destruct b; destruct b'; auto.
cbn.
apply promote_idem.
Qed.


Lemma qpromote_hyp_tp :
  forall object b, qpromote_hyp b (@hyp_tp object) = hyp_tp.
Proof.
intros object b.
destruct b; auto.
Qed.


Lemma qpromote_hyp_tm :
  forall object b (a : @term object), qpromote_hyp b (hyp_tm a) = hyp_tm a.
Proof.
intros object b a.
destruct b; auto.
Qed.


Lemma qpromote_nil :
  forall object b, @qpromote object b nil = nil.
Proof.
intros object b.
destruct b; auto.
Qed.


Lemma qpromote_cons :
  forall object b h (G : @context object),
    qpromote b (cons h G) = cons (qpromote_hyp b h) (qpromote b G).
Proof.
intros object b h G.
destruct b; auto.
Qed.


Lemma qpromote_app :
  forall object (G1 G2 : @context object) b,
    qpromote b (G1 ++ G2) = qpromote b G1 ++ qpromote b G2.
Proof.
intros object G1 G2 b.
destruct b; auto.
cbn.
unfold promote.
rewrite -> List.map_app.
auto.
Qed.


Lemma hygieneh_qpromote :
  forall object b P (h : @hyp object),
    hygieneh P h <-> hygieneh P (qpromote_hyp b h).
Proof.
intros object b P h.
destruct b; try reflexivity.
apply hygieneh_promote.
Qed.


Lemma length_qpromote :
  forall object b (G : @context object),
    length (qpromote b G) = length G.
Proof.
intros object b G.
destruct b; auto.
cbn.
apply length_promote.
Qed.


Lemma ctxpred_qpromote :
  forall object b (G : @context object),
    ctxpred (qpromote b G) = ctxpred G.
Proof.
intros object b G.
rewrite -> !ctxpred_length.
rewrite -> length_qpromote.
reflexivity.
Qed.


Lemma qpromote_substctx :
  forall object (G : @context object) b s,
    qpromote b (substctx s G) = substctx s (qpromote b G).
Proof.
intros object G b s.
induct G.

(* nil *)
{
destruct b; cbn; auto.
}

(* cons *)
{
intros h G IH.
cbn.
rewrite -> !qpromote_cons.
cbn.
f_equal; auto.
rewrite -> substh_qpromote_hyp.
f_equal.
rewrite -> length_qpromote.
reflexivity.
}
Qed.


(* Hypothesis satisfaction *)

Lemma seqhyp_tm_leq :
  forall i j m m' a a' R,
    j <= i
    -> interp toppg true i a R
    -> interp toppg false i a' R
    -> rel (den R) j m m'
    -> seqhyp j m m' (hyp_tm a) (hyp_tm a').
Proof.
intros i j m m' a a' R Hj Hal Har Hm.
apply (seqhyp_tm _#5 (iutruncate (S j) R)).
  {
  eapply basic_downward; eauto.
  }

  {
  eapply basic_downward; eauto.
  }

  {
  split; auto.
  }
Qed.


Lemma seqhyp_smaller :
  forall i j b s s' h h',
    smaller j i b
    -> seqhyp i s s' h h'
    -> seqhyp j s s' (qpromote_hyp b h) (qpromote_hyp b h').
Proof.
intros i j b s s' h h' Hsmall Hh.
cases Hh.

(* tpl *)
{
intros a c R Ha Hc Hcla Hclc.
destruct b.
  {
  cbn.
  invert Hsmall.
  intro Hji.
  apply (seqhyp_tp _#3 (iutruncate (S j) R));
  apply (basic_downward _#3 (pred i)); try omega; [apply Ha | apply Hc]; omega.
  }

  {
  cbn.
  invert Hsmall.
  intro Hji.
  apply (seqhyp_tpl _#3 (iutruncate j R)); auto.
    {
    intro Hpos.
    replace j with (S (pred j)) at 2 by omega.
    apply (basic_downward _#3 (pred i)); try omega.
    apply Ha; omega.
    }

    {
    intro Hpos.
    replace j with (S (pred j)) at 2 by omega.
    apply (basic_downward _#3 (pred i)); try omega.
    apply Hc; omega.
    }
  }
}

(* tp *)
{
intros a c R Ha Hc.
so (smaller_impl_le _#3 Hsmall) as Hj.
rewrite -> qpromote_hyp_tp.
apply (seqhyp_tp _#3 (iutruncate (S j) R)); apply (basic_downward _#3 i); auto.
}

(* tml *)
{
intros m n a c R Ha Hc Hmn Hclm Hcln Hcla Hclc.
destruct b.
  {
  invert Hsmall.
  intros Hji.
  cbn.
  apply (seqhyp_tm _#5 (iutruncate (S j) R)).
    {
    apply (basic_downward _#3 (pred i)); [omega |].
    apply Ha; omega.
    }

    {
    apply (basic_downward _#3 (pred i)); [omega |].
    apply Hc; omega.
    }

    {
    rewrite -> den_iutruncate.
    split; [omega |].
    apply (urel_downward_leq _#3 (pred i)); [omega |].
    apply Hmn; omega.
    }
  }

  {
  invert Hsmall.
  intros Hji.
  cbn.
  apply (seqhyp_tml _#5 (iutruncate j R)); auto.
    {
    intros Hpos.
    replace j with (S (pred j)) at 2 by omega.
    apply (basic_downward _#3 (pred i)); [omega |].
    apply Ha; omega.
    }

    {
    intros Hpos.
    replace j with (S (pred j)) at 2 by omega.
    apply (basic_downward _#3 (pred i)); [omega |].
    apply Hc; omega.
    }

    {
    intros Hpos.
    rewrite -> den_iutruncate.
    split; [omega |].
    apply (urel_downward_leq _#3 (pred i)); [omega |].
    apply Hmn; omega.
    }
  }
}

(* tm *)
{
intros m n a c R Ha Hc Hmn.
rewrite -> !qpromote_hyp_tm.
so (smaller_impl_le _#3 Hsmall) as Hji.
apply (seqhyp_tm _#5 (iutruncate (S j) R)).
  {
  eapply basic_downward; eauto.
  }

  {
  eapply basic_downward; eauto.
  }

  {
  rewrite -> den_iutruncate.
  split; [omega |].
  eapply urel_downward_leq; eauto.
  }
}

(* emp *)
{
intros m n Hclm Hcln.
destruct b; cbn; apply seqhyp_emp; auto.
}
Qed.


Lemma seqhyp_downward :
  forall i j a a' h h',
    j <= i
    -> seqhyp i a a' h h'
    -> seqhyp j a a' h h'.
Proof.
intros i j a a' h h' Hj Hhh.
eapply (seqhyp_smaller _ _ false); eauto.
apply smaller_le; auto.
Qed.


Lemma seqhyp_promote :
  forall i m m' h h',
    seqhyp (S i) m m' h h'
    -> seqhyp i m m' (promote_hyp h) (promote_hyp h').
Proof.
intros i m m' h h' Hhh.
eapply (seqhyp_smaller _ _ true); eauto.
apply smaller_lt; omega.
Qed.


Lemma seqhyp_impl_hygieneh :
  forall i m m' h h',
    seqhyp i m m' h h'
    -> hygieneh clo h
       /\ hygieneh clo h'.
Proof.
intros i m m' h h' H.
induct H; auto using hygieneh_tpl, hygieneh_tp, hygieneh_emp.

(* tml *)
{
intros; split; apply hygieneh_tml; auto.
}

(* tm *)
{
intros m m' a a' R Ha Ha' _.
split; apply hygieneh_tm; eapply basic_closed; eauto.
}
Qed.


Lemma seqhyp_demote :
  forall i m p s s' h,
    seqhyp i m p (promote_hyp (substh s h)) (promote_hyp (substh s' h))
    -> seqhyp i m p (substh s h) (substh s' h).
Proof.
intros i m p s s' h.
cases h;
simpsub; cbn [promote_hyp];
auto.

(* tml *)
{
intros H.
invertc H.
intros R Hl Hr.
apply (seqhyp_tpl _#3 (iutruncate i R));
try (intros Hpos; replace i with (S (pred i)) at 2 by omega; apply (basic_downward _#3 i); auto; omega);
eapply basic_closed; eauto.
}

(* tml *)
{
intros a H.
simpsubin H.
cbn in H.
simpsub.
invertc H.
intros R Hal Har Hmp.
so (urel_closed _#5 Hmp) as (Hclm & Hclp).
apply (seqhyp_tml _#5 (iutruncate i R)); eauto using basic_closed.
  {
  intros Hpos.
  replace i with (S (pred i)) at 2 by omega.
  refine (basic_downward _#7 _ Hal).
  omega.
  }

  {
  intros Hpos.
  replace i with (S (pred i)) at 2 by omega.
  refine (basic_downward _#7 _ Har).
  omega.
  }

  {
  intros Hpos.
  split; [omega |].
  refine (urel_downward_leq _#6 _ Hmp).
  omega.
  }
}
Qed.


Lemma seqhyp_demote_maybe :
  forall i m p s s' h b,
    seqhyp i m p (qpromote_hyp b (substh s h)) (qpromote_hyp b (substh s' h))
    -> seqhyp i m p (substh s h) (substh s' h).
Proof.
intros i m p s s' h b H.
destruct b; auto.
apply seqhyp_demote; auto.
Qed.


Lemma seqhyp_impl_closed :
  forall i m m' h h',
    seqhyp i m m' h h'
    -> hygiene clo m /\ hygiene clo m'.
Proof.
intros i m m' h h' Hm.
induct Hm; auto.

(* tp *)
{
intros a a' R H H'.
split; eapply basic_closed; eauto.
}

(* tm *)
{
intros m m' a a' R _ _ Hm.
exact (urel_closed _#5 Hm).
}
Qed.


Lemma seqhyp_zigzag :
  forall i m n p q h1 h2 h3 h4,
    seqhyp i m p h1 h3
    -> seqhyp i n p h2 h3
    -> seqhyp i n q h2 h4
    -> seqhyp i m q h1 h4.
Proof.
intros i m n p q h1 h2 h3 h4 H13 H23 H24.
revert h2 h4 H23 H24.
cases H13.

(* tpl *)
{
intros m p K Hm Hp Hclm _ h2 h4 H23 H24.
invertc H23.
intros K' Hn Hp' _ _ <-.
invertc H24.
intros K'' Hn' Hq _ Hclq <-.
apply (seqhyp_tpl _#3 K); auto.
intro Hpos.
so (basic_fun _#7 (Hp Hpos) (Hp' Hpos)); subst K'.
so (basic_fun _#7 (Hn Hpos) (Hn' Hpos)); subst K''.
auto.
}

(* tp *)
{
intros k k' K Hm Hp h2 h4 H23 H24.
invertc H23.
intros K' Hn Hp' <-.
invertc H24.
intros K'' Hn' Hq <-.
so (basic_fun _#7 Hp Hp'); subst K'.
so (basic_fun _#7 Hn Hn'); subst K''.
apply (seqhyp_tp _#3 K); auto.
}

(* tml *)
{
intros m p a b R Ha Hb Hmp Hclm _ Hcla _ h2 h4 H23 H24.
invertc H23.
intros c R' Hc Hb' Hnp _ _ _ _ <-.
invertc H24.
intros d R'' Hc' Hd Hnq _ Hclq _ Hcld <-.
apply (seqhyp_tml _#5 R); auto.
  {
  intros Hpos.
  so (basic_fun _#7 (Hb Hpos) (Hb' Hpos)); subst R'.
  so (basic_fun _#7 (Hc Hpos) (Hc' Hpos)); subst R''.
  apply Hd; auto.
  }

  {
  intros Hpos.
  so (basic_fun _#7 (Hb Hpos) (Hb' Hpos)); subst R'.
  so (basic_fun _#7 (Hc Hpos) (Hc' Hpos)); subst R''.
  apply (urel_zigzag _ _ _ m p n q); auto.
  }
}

(* tm *)
{
intros m p a b R Ha Hb mp h2 h4 H23 H24.
invertc H23.
intros c R' Hc Hb' Hnp <-.
invertc H24.
intros d R'' Hc' Hd Hnq <-.
so (basic_fun _#7 Hb Hb'); subst R'.
so (basic_fun _#7 Hc Hc'); subst R''.
apply (seqhyp_tm _#5 R); auto.
eapply urel_zigzag; eauto.
}

(* emp *)
{
intros m p Hclm _ h2 h4 H23 H24.
invertc H23.
intros _ _ <-.
invertc H24.
intros _ Hclq <-.
apply seqhyp_emp; auto.
}
Qed.


(* Context satisfaction with minimal functionality *)

Lemma seqctx_smaller :
  forall i j b s s' G,
    smaller j i b
    -> seqctx i s s' G
    -> seqctx j s s' (qpromote b G).
Proof.
intros i j b s s' G Hsmaller Hs.
induct Hs.

(* nil *)
{
intros n.
rewrite -> qpromote_nil.
apply seqctx_nil.
}

(* cons *)
{
intros m m' s s' h G _ IH Hh.
rewrite -> qpromote_cons.
apply seqctx_cons; auto.
rewrite -> !substh_qpromote_hyp.
eapply seqhyp_smaller; eauto.
}
Qed.


Lemma seqctx_downward :
  forall i j s s' G,
    j <= i
    -> seqctx i s s' G
    -> seqctx j s s' G.
Proof.
intros i j s s' G Hj Hs.
eapply (seqctx_smaller _ _ false); eauto.
apply smaller_le; auto.
Qed.


Lemma seqctx_promote :
  forall i s s' G,
    seqctx (S i) s s' G
    -> seqctx i s s' (promote G).
Proof.
intros i s s' G Hs.
eapply (seqctx_smaller _ _ true); eauto.
apply smaller_lt; omega.
Qed.


Lemma seqctx_demote :
  forall i s s' G,
    seqctx i s s' (promote G)
    -> seqctx i s s' G.
Proof.
intros i s s' G.
revert s s'.
induct G.

(* nil *)
{
intros s s' H.
cbn in H.
invert H.
intros; subst.
apply seqctx_nil; auto.
}

(* cons *)
{
intros h G IH ss ss' H.
cbn in H.
fold (promote G) in H.
invertc H.
intros m p s s' Hs Hmp <- <-.
apply seqctx_cons; auto.
rewrite -> !substh_promote_hyp in Hmp.
eapply seqhyp_demote; eauto.
}
Qed.


Lemma seqctx_qdemote :
  forall i s s' b G,
    seqctx i s s' (qpromote b G)
    -> seqctx i s s' G.
Proof.
intros i s s' b G H.
destruct b; auto.
apply seqctx_demote; auto.
Qed.


Lemma seqctx_impl_closub :
  forall i s s' G,
    seqctx i s s' G
    -> closub (ctxpred G) s
       /\ closub (ctxpred G) s'.
Proof.
intros i s s' G Hs.
cut (forall j, ctxpred G j -> hygiene clo (project s j) /\ hygiene clo (project s' j)).
  {
  intro Hcond.
  split.
    {
    intros j Hj.
    exact (Hcond _ Hj andel).
    }

    {
    intros j Hj.
    exact (Hcond _ Hj ander).
    }
  }
induct Hs.

(* 0 *)
{
intros n j H.
cbn in H.
destruct H.
}

(* S *)
{
intros m m' s s' h G _ IH1 Hm j Hje.
cbn in Hje.
destruct j as [| j].
  {
  simpsub.
  eapply seqhyp_impl_closed; eauto.
  }

  {
  simpsub.
  eapply IH1; eauto.
  }
}
Qed.


Lemma seqctx_zigzag :
  forall i s t u v G,
    seqctx i s t G
    -> seqctx i u t G
    -> seqctx i u v G
    -> seqctx i s v G.
Proof.
intros i s t u v G Hst Hut Huv.
revert u v Hut Huv.
induct Hst.

(* nil *)
{
intros n u v Hut Huv.
invertc Hut.
intros <-.
invertc Huv.
intros <-.
apply seqctx_nil.
}

(* cons *)
{
intros m p s t h G _ IH Hmp uu vv Hut Huv.
invertc Hut.
intros n u Hut Hnp <-.
invertc Huv.
intros q v Huv Hnq <-.
apply seqctx_cons; eauto.
eapply seqhyp_zigzag; eauto.
}
Qed.


(* Related hypotheses *)

Lemma relhyp_refl :
  forall i m m' h h',
    seqhyp i m m' h h'
    -> relhyp i true h h /\ relhyp i false h' h'.
Proof.
intros i m m' h h' H.
cases H; intros; split; eauto using relhyp.
Qed.


Lemma relhyp_symm :
  forall i z h h',
    relhyp i z h h'
    -> relhyp i z h' h.
Proof.
intros i z h h' H.
cases H; eauto using relhyp.
Qed.


Lemma relhyp_trans :
  forall i z h1 h2 h3,
    relhyp i z h1 h2
    -> relhyp i z h2 h3
    -> relhyp i z h1 h3.
Proof.
intros i z h1 h2 h3 H12 H23.
revert H23.
cases H12; auto.

(* tml *)
{
intros a b R Ha Hb Hcla _ H23.
invertc H23.
intros c R' Hb' Hc _ Hclc <-.
apply (relhyp_tml _#4 R); auto.
intro Hpos.
so (basic_fun _#7 (Hb Hpos) (Hb' Hpos)); subst R'.
apply Hc; auto.
}

(* tm *)
{
intros a b R Ha Hb H23.
invertc H23.
intros c R' Hb' Hc <-.
so (basic_fun _#7 Hb Hb'); subst R'.
eapply relhyp_tm; eauto.
}
Qed.


Lemma relhyp_smaller :
  forall i j b z h h',
    smaller j i b
    -> relhyp i z h h' 
    -> relhyp j z (qpromote_hyp b h) (qpromote_hyp b h').
Proof.
intros i j b z h h' Hsmall Hh.
cases Hh;
try (destruct b; cbn; eauto using relhyp; done).

(* tml *)
{
intros a c R Ha Hc Hcla Hclc.
destruct b.
  {
  invert Hsmall.
  intros Hji.
  cbn.
  apply (relhyp_tm _#4 (iutruncate (S j) R)).
    {
    apply (basic_downward _#3 (pred i)); [omega |].
    apply Ha; omega.
    }

    {
    apply (basic_downward _#3 (pred i)); [omega |].
    apply Hc; omega.
    }
  }

  {
  invert Hsmall.
  intros Hji.
  cbn.
  apply (relhyp_tml _#4 (iutruncate j R)); auto.
    {
    intros Hpos.
    replace j with (S (pred j)) at 2 by omega.
    apply (basic_downward _#3 (pred i)); [omega |].
    apply Ha; omega.
    }

    {
    intros Hpos.
    replace j with (S (pred j)) at 2 by omega.
    apply (basic_downward _#3 (pred i)); [omega |].
    apply Hc; omega.
    }
  }
}

(* tm *)
{
intros a c R Ha Hc.
rewrite -> !qpromote_hyp_tm.
so (smaller_impl_le _#3 Hsmall) as Hji.
apply (relhyp_tm _#4 (iutruncate (S j) R)).
  {
  eapply basic_downward; eauto.
  }

  {
  eapply basic_downward; eauto.
  }
}
Qed.


Lemma seqhyp_relhyp :
  forall i m1 m2 h1 h1' h2 h2',
    relhyp i true h1 h1'
    -> relhyp i false h2 h2'
    -> seqhyp i m1 m2 h1 h2
    -> seqhyp i m1 m2 h1' h2'.
Proof.
intros i m1 m2 h1 h1' h2 h2' Hh1 Hh2 Hm.
revert Hh1 Hh2.
cases Hm;
try (intros; invertc Hh1; invertc Hh2; intros; subst; eauto using seqhyp; done).

(* tml *)
{
intros m m' a b R Hal Har Hm Hclm Hclm' _ _ Hh1 Hh2.
invertc Hh1.
intros c R' Hal' Hcl _ Hclc <-.
invertc Hh2.
intros d R'' Har' Hdr _ Hcld <-.
apply (seqhyp_tml _#5 R); auto.
  {
  intro Hpos.
  so (basic_fun _#7 (Hal Hpos) (Hal' Hpos)); subst R'.
  exact (Hcl Hpos).
  }

  {
  intro Hpos.
  so (basic_fun _#7 (Har Hpos) (Har' Hpos)); subst R''.
  exact (Hdr Hpos).
  }
}

(* tm *)
{
intros m m' a b R Hal Har Hm Hh1 Hh2.
invertc Hh1.
intros c R' Hal' Hcl <-.
invertc Hh2.
intros d R'' Har' Hdr <-.
so (basic_fun _#7 Hal Hal'); subst R'.
so (basic_fun _#7 Har Har'); subst R''.
eapply seqhyp_tm; eauto.
}
Qed.


Lemma seqhyp_relhyp_1 :
  forall i m1 m2 h1 h1' h2,
    relhyp i true h1 h1'
    -> seqhyp i m1 m2 h1 h2
    -> seqhyp i m1 m2 h1' h2.
Proof.
intros i m1 m2 h1 h1' h2 Hh2 Hm.
eapply seqhyp_relhyp; eauto.
exact (relhyp_refl _#5 Hm ander).
Qed.


Lemma seqhyp_relhyp_2 :
  forall i m1 m2 h1 h2 h2',
    relhyp i false h2 h2'
    -> seqhyp i m1 m2 h1 h2
    -> seqhyp i m1 m2 h1 h2'.
Proof.
intros i m1 m2 h1 h2 h2' Hh2 Hm.
eapply seqhyp_relhyp; eauto.
exact (relhyp_refl _#5 Hm andel).
Qed.


(* Pointwise functionality *)

Lemma pwctx_tail :
  forall i s s' G1 G2,
    pwctx i s s' (G2 ++ G1)
    -> pwctx i (compose (sh (length G2)) s) (compose (sh (length G2)) s') G1.
Proof.
intros i s s' G1 G2.
revert s s'.
induct G2.

(* nil *)
{
auto.
}

(* cons *)
{
intros h G IH ss ss' Hss.
cbn [length].
cbn in Hss.
invertc Hss.
intros m n s s' Hs _ _ _ <- <-.
simpsub.
apply IH; auto.
}
Qed.


Lemma pwctx_smaller :
  forall i j b s s' G,
    smaller j i b
    -> pwctx i s s' G
    -> pwctx j s s' (qpromote b G).
Proof.
intros i j b s s' G Hsmaller Hs.
revert Hsmaller.
induct Hs.

(* nil *)
{
destruct b; auto using pwctx_nil.
}

(* cons *)
{
intros i m m' s s' h G _ IH Hm Hleft Hright Hsmall.
rewrite -> qpromote_cons.
apply pwctx_cons; auto.
  {
  rewrite -> !substh_qpromote_hyp.
  eapply seqhyp_smaller; eauto.
  }

  {
  intros j' b' s'' Hsmall' Hs'.
  rewrite -> qpromote_hyp_combine.
  rewrite -> qpromote_combine in Hs'.
  apply Hleft; eauto using smaller_trans.
  }

  {
  intros j' b' s'' Hsmall' Hs'.
  rewrite -> qpromote_hyp_combine.
  rewrite -> qpromote_combine in Hs'.
  apply Hright; eauto using smaller_trans.
  }
}
Qed.


Lemma pwctx_downward :
  forall i j s s' G,
    j <= i
    -> pwctx i s s' G
    -> pwctx j s s' G.
Proof.
intros i j s s' G Hj Hs.
apply (pwctx_smaller i j false); auto.
apply smaller_le; auto.
Qed.


Lemma pwctx_promote :
  forall i s s' G,
    pwctx (S i) s s' G
    -> pwctx i s s' (promote G).
Proof.
intros i s s' G H.
apply (pwctx_smaller (S i) i true); auto.
apply smaller_lt; auto.
Qed.


Lemma pwctx_impl_seqctx :
  forall i s s' G,
    pwctx i s s' G
    -> seqctx i s s' G.
Proof.
intros i s s' G Hs.
induct Hs; auto using seqctx_nil.
(* cons *)
intros i m m' s s' h G _ IH Hh _ _.
apply seqctx_cons; auto.
Qed.


Lemma seqctx_pwctx_left :
  forall i s s' s'' G,
    pwctx i s s' G
    -> seqctx i s s'' G
    -> pwctx i s s'' G.
Proof.
intros i s s' s'' G Hs Hs'.
revert s'' Hs'.
induct Hs.

(* nil *)
{
intros i n s'' Hs'.
invertc Hs'.
intros <-.
apply pwctx_nil.
}

(* cons *)
{
intros i m m' s s' h G Hs IH Hh Hleft Hright ss Hss.
invertc Hss.
intros n s'' Hs' Hn <-.
apply pwctx_cons; auto.
  {
  intros j b t Hsmaller Ht.
  so (Hleft _#3 Hsmaller Ht).
  so (Hleft _#3 Hsmaller (seqctx_smaller _#6 Hsmaller Hs')).
  eauto using relhyp_symm, relhyp_trans.
  }

  {
  intros j b t Hsmaller Ht.
  apply Hright; auto.
  exact (seqctx_zigzag _#6 Ht (seqctx_smaller _#6 Hsmaller Hs') (seqctx_smaller _#6 Hsmaller (pwctx_impl_seqctx _#4 Hs))).
  }
}
Qed.


Lemma seqctx_pwctx_right :
  forall i s s' s'' G,
    pwctx i s s' G
    -> seqctx i s'' s' G
    -> pwctx i s'' s' G.
Proof.
intros i s s' s'' G Hs Hs'.
revert s'' Hs'.
induct Hs.

(* nil *)
{
intros i n s'' Hs'.
invertc Hs'.
intros <-.
apply pwctx_nil.
}

(* cons *)
{
intros i m m' s s' h G Hs IH Hh Hleft Hright ss Hss.
invertc Hss.
intros n s'' Hs' Hn <-.
apply pwctx_cons; auto.
  {
  intros j b t Hsmaller Ht.
  apply Hleft; auto.
  exact (seqctx_zigzag _#6 (seqctx_smaller _#6 Hsmaller (pwctx_impl_seqctx _#4 Hs)) (seqctx_smaller _#6 Hsmaller Hs') Ht).
  }

  {
  intros j b t Hsmaller Ht.
  so (Hright _#3 Hsmaller Ht).
  so (Hright _#3 Hsmaller (seqctx_smaller _#6 Hsmaller Hs')).
  eauto using relhyp_symm, relhyp_trans.
  }
}
Qed.


(* This is clever, if I do say so myself.  The lemma isn't true in full generality
   (we don't have pwctx i s s' (promote G) -> pwctx i s s' G), but this is all we need.
*)
Lemma seqctx_pwctx_demote_left :
  forall i j b s s' s'' G,
    smaller j i b
    -> pwctx i s s' G
    -> seqctx j s s'' (qpromote b G)
    -> pwctx j s s'' G.
Proof.
intros i j b s s' s'' G Hsmall Hs Hseq.
assert (seqctx j s s'' G) as Hseq'.
  {
  destruct b; auto.
  cbn in Hseq.
  apply seqctx_demote; auto.
  }
so (smaller_impl_le _#3 Hsmall) as Hle.
so (pwctx_downward _#5 Hle Hs) as Hsj.
eapply seqctx_pwctx_left; eauto.
Qed.


Lemma seqctx_pwctx_demote_right :
  forall i j b s s' s'' G,
    smaller j i b
    -> pwctx i s s' G
    -> seqctx j s'' s' (qpromote b G)
    -> pwctx j s'' s' G.
Proof.
intros i j b s s' s'' G Hsmall Hs Hseq.
assert (seqctx j s'' s' G) as Hseq'.
  {
  destruct b; auto.
  cbn in Hseq.
  apply seqctx_demote; auto.
  }
so (smaller_impl_le _#3 Hsmall) as Hle.
so (pwctx_downward _#5 Hle Hs) as Hsj.
eapply seqctx_pwctx_right; eauto.
Qed.


Lemma pwctx_impl_closub :
  forall i s s' G,
    pwctx i s s' G
    -> closub (ctxpred G) s
       /\ closub (ctxpred G) s'.
Proof.
intros i s s' G H.
exact (seqctx_impl_closub _#4 (pwctx_impl_seqctx _#4 H)).
Qed.


(* Pointwise functionality introduction/elimination *)

Lemma pwctx_cons_invert_simple :
  forall i s s' h G,
    pwctx i s s' (cons h G)
    -> exists m p t t',
         pwctx i t t' G
         /\ seqhyp i m p (substh t h) (substh t' h)
         /\ s = dot m t
         /\ s' = dot p t'.
Proof.
intros i s s' h G H.
invertc H.
intros m p t t' Ht Hmp _ _ <- <-.
exists m, p, t, t'.
do2 3 split; auto.
Qed.


Lemma pwctx_cons_tm :
  forall i m p s s' a G,
    pwctx i s s' G
    -> seqhyp i m p (hyp_tm (subst s a)) (hyp_tm (subst s' a))
    -> (forall j s'',
          j <= i
          -> pwctx j s s'' G
          -> relhyp j false (hyp_tm (subst s' a)) (hyp_tm (subst s'' a)))
    -> (forall j s'',
          j <= i
          -> pwctx j s'' s' G
          -> relhyp j true (hyp_tm (subst s a)) (hyp_tm (subst s'' a)))
    -> pwctx i (dot m s) (dot p s') (cons (hyp_tm a) G).
Proof.
intros i m p s s' a G Hs Hh Hleft Hright.
apply pwctx_cons; auto.
  {
  intros j b s'' Hsmall Hs'.
  rewrite -> qpromote_hyp_tm.
  simpsub.
  eapply Hleft; eauto using smaller_impl_le.
  eapply seqctx_pwctx_demote_left; eauto.
  }

  {
  intros j b s'' Hsmall Hs'.
  rewrite -> qpromote_hyp_tm.
  simpsub.
  eapply Hright; eauto using smaller_impl_le.
  eapply seqctx_pwctx_demote_right; eauto.
  }
Qed.


Lemma pwctx_cons_tm_seq :
  forall i m p s s' a G,
    pwctx i s s' G
    -> seqhyp i m p (hyp_tm (subst s a)) (hyp_tm (subst s' a))
    -> (forall i t t',
          pwctx i t t' G
          -> exists pg R,
               interp pg true i (subst t a) R
               /\ interp pg false i (subst t' a) R)
    -> pwctx i (dot m s) (dot p s') (cons (hyp_tm a) G).
Proof.
intros i m p s s' a G Hs Hh Hseq.
apply pwctx_cons_tm; auto.
  {
  intros j s'' Hj Hs'.
  so (Hseq _#3 Hs) as (pg & R & Hal & Har).
  so (Hseq _#3 Hs') as (pg' & R' & Hal' & Haa).
  so (interp_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst R'.
  apply (relhyp_tm _#4 (iutruncate (S j) R)); auto.
    {
    eapply basic_downward; eauto.
    eapply interp_increase; eauto using toppg_max.
    }

    {
    eapply interp_increase; eauto using toppg_max.
    }
  }

  {
  intros j s'' Hj Hs'.
  so (Hseq _#3 Hs) as (pg & R & Hal & Har).
  so (Hseq _#3 Hs') as (pg' & R' & Haa & Har').
  so (interp_fun _#7 (basic_downward _#7 Hj Har) Har'); subst R'.
  apply (relhyp_tm _#4 (iutruncate (S j) R)); auto.
    {
    eapply basic_downward; eauto.
    eapply interp_increase; eauto using toppg_max.
    }

    {
    eapply interp_increase; eauto using toppg_max.
    }
  }
Qed.


Lemma pwctx_cons_tp :
  forall i m p s s' G,
    pwctx i s s' G
    -> seqhyp i m p hyp_tp hyp_tp
    -> pwctx i (dot m s) (dot p s') (cons hyp_tp G).
Proof.
intros i m p s s' G Hs Hmp.
apply pwctx_cons; auto.
  {
  intros j b u Hsmall Hu.
  destruct b; cbn; eauto using relhyp.
  }

  {
  intros j b u Hsmall Hu.
  destruct b; cbn; eauto using relhyp.
  }
Qed.


(* Unrolling judgements *)

Lemma seq_deq :
  forall G m n a,
    seq G (deq m n a)
    <->
    (forall i s s',
       pwctx i s s' G
       -> exists R,
            interp toppg true i (subst s a) R
            /\ interp toppg false i (subst s' a) R
            /\ rel (den R) i (subst s m) (subst s' m)
            /\ rel (den R) i (subst s n) (subst s' n)
            /\ rel (den R) i (subst s m) (subst s' n)).
Proof.
intros G m n a.
split.
  {
  intros H.
  invertc H.
  auto.
  }

  {
  intros H.
  apply seq_i.
  auto.
  }
Qed.


Lemma seq_univ :
  forall G a b lv,
    seq G (deq a b (univ lv))
    <->
    (forall i s s',
       pwctx i s s' G
       -> exists pg R,
            pginterp (subst s lv) pg
            /\ pginterp (subst s' lv) pg
            /\ interp pg true i (subst s a) R
            /\ interp pg false i (subst s' a) R
            /\ interp pg true i (subst s b) R
            /\ interp pg false i (subst s' b) R).
Proof.
intros G a b lv.
split.

(* out *)
{
intros Hseqj.
invertc Hseqj.
intros Hseq.
intros i s s' Hs.
so (Hseq i s s' Hs) as (R & Huniv & Huniv' & Ha & Hb & Hab); clear Hseq.
simpsubin Huniv.
simpsubin Huniv'.
invert (basic_value_inv _#6 value_univ Huniv); clear Huniv.
intros pg Hlv Hstr Hcex <-.
remember (iuuniv the_system i pg) as R eqn:HeqR.
invert (basic_value_inv _#6 value_univ Huniv'); clear Huniv'.
subst R.
intros pg' Hlv' _ _  Heq.
so (iuuniv_inj _#5 Heq); subst pg'.
cbn in Ha, Hb, Hab.
destruct Ha as (_ & R & Hal & Har).
destruct Hb as (_ & R' & Hbl & Hbr).
destruct Hab as (_ & R'' & Hal' & Hbr').
rewrite -> sint_unroll in Hal, Har, Hbl, Hbr, Hal', Hbr'.
so (basic_fun _#7 Hal Hal'); subst R''.
so (basic_fun _#7 Hbr Hbr'); subst R'.
exists pg, R.
do2 5 split; auto.
}

(* in *)
{
intros Hseq.
apply seq_i.
intros i s s' Hs.
so (Hseq i s s' Hs) as (pg & R & Hlv & Hlv' & Hal & Har & Hbl & Hbr); clear Hseq.
exists (iuuniv the_system i pg).
do2 4 split.
  {
  simpsub.
  apply interp_eval_refl.
  apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
  }

  {
  simpsub.
  apply interp_eval_refl.
  apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
  }

  {
  split; auto.
  exists R.
  rewrite -> sint_unroll.
  auto.
  }

  {
  split; auto.
  exists R.
  rewrite -> sint_unroll.
  auto.
  }

  {
  split; auto.
  exists R.
  rewrite -> sint_unroll.
  auto.
  }
}
Qed.


Lemma seq_eqtype :
  forall G a b,
    seq G (deqtype a b)
    <->
    (forall i s s',
       pwctx i s s' G
       -> exists R,
            interp toppg true i (subst s a) R
            /\ interp toppg false i (subst s' a) R
            /\ interp toppg true i (subst s b) R
            /\ interp toppg false i (subst s' b) R).
Proof.
intros G a b.
split.

(* out *)
{
intros Hseqj.
invertc Hseqj.
intros Hseq.
intros i s s' Hs.
so (Hseq i s s' Hs) as (R & Hintl & Hintr & Hinh & _); clear Hseq.
simpsubin Hintl.
simpsubin Hintr.
invert (basic_value_inv _#6 value_eqtype Hintl); clear Hintl.
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_eqtype Hintr); clear Hintr.
intros A' B' Har Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iueqtype_inj _#6 Heq) as (<- & <-).
destruct Hinh as (HeqAB & _).
unfold eqtype_property in HeqAB.
so (basic_impl_iutruncate _#6 Hal) as HeqA.
so (basic_impl_iutruncate _#6 Hbl) as HeqB.
so (eqtrans HeqA (eqtrans HeqAB (eqsymm HeqB))).
subst B.
eauto.
}

(* in *)
{
intros Hseq.
apply seq_i.
intros i s s' Hs.
so (Hseq i s s' Hs) as (R & Hal & Har & Hbl & Hbr); clear Hseq.
exists (iueqtype stop i R R).
simpsub.
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_eqtype; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_eqtype; auto.
  }

  {
  apply property_action_triv; cbn; auto.
  exact (eq_refl _).
  }

  {
  apply property_action_triv; cbn; auto.
  exact (eq_refl _).
  }

  {
  apply property_action_triv; cbn; auto.
  exact (eq_refl _).
  }
}
Qed.


Lemma seq_eqkind :
  forall G k l lv,
    seq G (deq k l (kuniv lv))
    <->
    (forall i s s',
       pwctx i s s' G
       -> exists pg K R (h : lt_page pg toppg),
            pginterp (subst s lv) pg
            /\ pginterp (subst s' lv) pg
            /\ kinterp pg true i (subst s k) K
            /\ kinterp pg false i (subst s' k) K
            /\ kinterp pg true i (subst s l) K
            /\ kinterp pg false i (subst s' l) K
            /\ interp (succ_page pg h) true i (subst s k) R
            /\ interp (succ_page pg h) false i (subst s' k) R
            /\ interp (succ_page pg h) true i (subst s l) R
            /\ interp (succ_page pg h) false i (subst s' l) R).
Proof.
intros G k l lv.
split.

(* out *)
{
intros Hseqj.
invertc Hseqj.
intro Hseq.
intros i s s' Hs.
so (Hseq i s s' Hs) as (R & Hintl & Hintr & Hk & Hl & Hk_l); clear Hseq.
simpsubin Hintl.
simpsubin Hintr.
invert (basic_value_inv _#6 value_kuniv Hintl).
intros pg h Hlvl Hlt Heq1.
invert (basic_value_inv _#6 value_kuniv Hintr).
intros pg' h' Hlvr _ Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iukuniv_inj _#7 Heq); subst pg'; clear Heq.
so (proof_irrelevance _ h h'); subst h'.
cbn in Hk, Hl, Hk_l.
destruct Hk as (_ & K & R & Hkl & Hkr & Hklt & Hkrt).
destruct Hl as (_ & K' & R' & Hll & Hlr & Hllt & Hlrt).
destruct Hk_l as (_ & K'' & R'' & Hkl' & Hlr' & Hklt' & Hlrt').
rewrite -> sintk_unroll in Hkl, Hkr, Hll, Hlr, Hkl', Hlr'.
rewrite -> sint_unroll in Hklt, Hkrt, Hllt, Hlrt, Hklt', Hlrt'.
so (kbasic_fun _#7 Hkl Hkl'); subst K''.
so (kbasic_fun _#7 Hlr Hlr'); subst K'.
so (basic_fun _#7 Hklt Hklt'); subst R''.
so (basic_fun _#7 Hlrt Hlrt'); subst R'.
exists pg, K, R, h.
do2 9 split; auto.
}

(* in *)
{
intros Hseq.
apply seq_i.
intros i s s' Hs.
so (Hseq i s s' Hs) as (pg & K & R & Hlt & Hlvl & Hlvr & Hkl & Hkr & Hll & Hlr & Hklt & Hkrt & Hllt & Hlrt); clear Hseq.
so (pginterp_succ_lt_top _ _ Hlt Hlvl) as Hlt'.
so (kinterp_level_bound _#5 Hkl) as Hlev.
set (h := le_ord_succ _ _ (cin_top pg)).
exists (iukuniv the_system i pg Hlt).
simpsub.
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_kuniv; eauto using toppg_max, pginterp_cin_top.
  }

  {
  apply interp_eval_refl.
  apply interp_kuniv; eauto using toppg_max, pginterp_cin_top.
  }

  {
  cbn.
  split; auto.
  exists K, R.
  rewrite -> sintk_unroll.
  rewrite -> sint_unroll.
  auto.
  }

  {
  cbn.
  split; auto.
  exists K, R.
  rewrite -> sintk_unroll.
  rewrite -> sint_unroll.
  auto.
  }

  {
  cbn.
  split; auto.
  exists K, R.
  rewrite -> sintk_unroll.
  rewrite -> sint_unroll.
  auto.
  }
}
Qed.


Lemma seq_subtype :
  forall G a b,
    seq G (dsubtype a b)
    <->
    (forall i s s',
       pwctx i s s' G
       -> exists R R',
            interp toppg true i (subst s a) R
            /\ interp toppg false i (subst s' a) R
            /\ interp toppg true i (subst s b) R'
            /\ interp toppg false i (subst s' b) R'
            /\ subtype_property stop (den R) (den R') i).
Proof.
intros G a b.
split.

(* out *)
{
intros Hseqj.
invertc Hseqj.
intros Hseq.
intros i s s' Hs.
so (Hseq i s s' Hs) as (R & Hintl & Hintr & Hinh & _); clear Hseq.
simpsubin Hintl.
simpsubin Hintr.
invert (basic_value_inv _#6 value_subtype Hintl); clear Hintl.
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_subtype Hintr); clear Hintr.
intros A' B' Har Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iusubtype_inj _#6 Heq) as (<- & <-).
destruct Hinh as (HeqAB & _).
exists A, B.
do2 4 split; auto.
}

(* in *)
{
intros Hseq.
apply seq_i.
intros i s s' Hs.
so (Hseq i s s' Hs) as (A & B & Hal & Har & Hbl & Hbr & Hsub); clear Hseq.
exists (iusubtype stop i A B).
simpsub.
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_subtype; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_subtype; auto.
  }

  {
  apply property_action_triv; cbn; auto.
  }

  {
  apply property_action_triv; cbn; auto.
  }

  {
  apply property_action_triv; cbn; auto.
  }
}
Qed.


Lemma seq_exteqtype :
  forall G a b,
    (seq G (dsubtype a b) /\ seq G (dsubtype b a))
    <->
    (forall i s s',
       pwctx i s s' G
       -> exists R R',
            interp toppg true i (subst s a) R
            /\ interp toppg false i (subst s' a) R
            /\ interp toppg true i (subst s b) R'
            /\ interp toppg false i (subst s' b) R'
            /\ forall j,
                 j <= i
                 -> rel (den R) j = rel (den R') j).
Proof.
intros G a b.
split.

(* out *)
{
intros (Hab & Hba).
rewrite -> seq_subtype in Hab, Hba.
intros i s s' Hs.
so (Hab _#3 Hs) as (A & B & Hal & Har & Hbl & Hbr & H).
renameover H into Hab.
so (Hba _#3 Hs) as (B' & A' & Hbl' & _ & Hal' & _ & H).
renameover H into Hba.
so (basic_fun _#7 Hal Hal'); subst A'.
so (basic_fun _#7 Hbl Hbl'); subst B'.
exists A, B.
do2 4 split; auto.
intros j Hj.
fextensionality 2.
intros m p.
pextensionality.
  {
  intro Hmp.
  apply Hab; auto.
  }

  {
  intro Hmp.
  apply Hba; auto.
  }
}

(* in *)
{
intros Hseq.
split.
  {
  rewrite -> seq_subtype.
  intros i s s' Hs.
  so (Hseq _#3 Hs) as (A & B & Hal & Har & Hbl & Hbr & Heq).
  exists A, B.
  do2 4 split; auto.
  intros j m p Hj Hmp.
  rewrite <- Heq; auto.
  }

  {
  rewrite -> seq_subtype.
  intros i s s' Hs.
  so (Hseq _#3 Hs) as (A & B & Hal & Har & Hbl & Hbr & Heq).
  exists B, A.
  do2 4 split; auto.
  intros j m p Hj Hmp.
  rewrite -> Heq; auto.
  }
}
Qed.


Lemma map_deqtype :
  forall A B (f : A -> B) m1 m2,
    map_jud f (deqtype m1 m2) = deqtype (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_dsubtype :
  forall A B (f : A -> B) m1 m2,
    map_jud f (dsubtype m1 m2) = dsubtype (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Hint Rewrite map_deqtype map_dsubtype : map.
