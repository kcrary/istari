
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

Require Import SemanticsConstfn.
Require Import SemanticsSimple.
Require Import Defined.
Require Import PageCode.
Require Import PageType.
Require Import SoundSimple.
Require Import Equivalence.
Require Import Equivalences.
Require Import ProperEquiv.
Require Import Defined.
Require Import ProperFun.

Require Import SemanticsGuard.
Require Absentia.

Lemma subst_nonsense :
  forall object (s : @sub object), subst s nonsense = nonsense.
Proof.
prove_subst.
Qed.


Hint Rewrite subst_nonsense : subst.


Local Ltac prove_hygiene :=
  repeat (apply hygiene_auto; cbn; repeat2 split; auto);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1, subst_closub;
  try (apply hygiene_var; cbn; auto; done).


Lemma sound_constfn_formation :
  forall G,
    pseq G (deq constfn constfn (univ nzero)).
Proof.
refine (seq_pseq 0 0 _ _); cbn.
intros G.
rewrite -> seq_univ.
intros i s s' Hs.
exists zeropg, (iubase (constfn_urel stop i)).
simpsub.
do2 5 split; auto using pginterp_nzero;
apply interp_eval_refl; apply interp_constfn.
Qed.


Lemma absentia_closed :
  forall G m,
    (forall i s s',
       pwctx i s s' (hyp_tm nonsense :: G)
       -> exists R,
            interp toppg true i (subst s (sequal (subst (dot triv sh1) m) m)) R
            /\ interp toppg false i (subst s' (sequal (subst (dot triv sh1) m) m)) R
            /\ rel (den R) i (subst s triv) (subst s' triv)
            /\ rel (den R) i (subst s triv) (subst s' triv)
            /\ rel (den R) i (subst s triv) (subst s' triv))
    -> hygiene (permit (ctxpred G)) m
    -> forall i s s',
         pwctx i s s' G
         -> exists n n',
              equiv (subst (under 1 s) m) n 
              /\ equiv (subst (under 1 s') m) n'
              /\ hygiene clo n
              /\ hygiene clo n'.
Proof.
intros G m Hseq Hclm i s s' Hs.
assert (forall p,
          hygiene clo p
          -> pwctx i (dot p s) (dot p s') (hyp_tm nonsense :: G)) as Hssif.
  {
  intros p Hclp.
  apply pwctx_cons_tm_seq; auto.
    {
    simpsub.
    eapply seqhyp_tm.
      {
      apply interp_eval_refl.
      apply interp_nonsense.
      }

      {
      apply interp_eval_refl.
      apply interp_nonsense.
      }

      {
      cbn.
      exists (le_refl _).
      do2 2 split; auto.
      }
    }

    {
    intros j t t' Ht.
    exists toppg.
    eexists.
    simpsub.
    split; apply interp_eval_refl; apply interp_nonsense.
    }
  }
exploit (Absentia.subst_closed_equiv_impl_closed _ (subst (under 1 s) m)) as (n & Hequivn & Hn).
  {
  intros p q Hclp Hclq.
  simpsub.
  apply (equiv_trans _ _ (subst (dot triv s) m)).
    {
    so (Hssif p Hclp) as Hss.
    so (Hseq _ _ _ Hss) as (R & Hl & _).
    simpsubin Hl.
    invert (basic_value_inv _#6 value_sequal Hl).
    intros _ _ Hequiv _.
    apply equiv_symm; auto.
    }

    {
    so (Hssif q Hclq) as Hss.
    so (Hseq _ _ _ Hss) as (R & Hl & _).
    simpsubin Hl.
    invert (basic_value_inv _#6 value_sequal Hl).
    intros _ _ Hequiv _.
    auto.
    }
  }
exploit (Absentia.subst_closed_equiv_impl_closed _ (subst (under 1 s') m)) as (n' & Hequivn' & Hn').
  {
  intros p q Hclp Hclq.
  simpsub.
  apply (equiv_trans _ _ (subst (dot triv s') m)).
    {
    so (Hssif p Hclp) as Hss.
    so (Hseq _ _ _ Hss) as (R & _ & Hr & _).
    simpsubin Hr.
    invert (basic_value_inv _#6 value_sequal Hr).
    intros _ _ Hequiv _.
    apply equiv_symm; auto.
    }

    {
    so (Hssif q Hclq) as Hss.
    so (Hseq _ _ _ Hss) as (R & _ & Hr & _).
    simpsubin Hr.
    invert (basic_value_inv _#6 value_sequal Hr).
    intros _ _ Hequiv _.
    auto.
    }
  }
so (church_rosser _#3 Hequivn) as (r & Hredmr & Hrednr).
so (church_rosser _#3 Hequivn') as (t & Hredmt & Hrednt).
exists r, t.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (subst_closub_under_permit _#4 Hclm Hcls) as Hclsm.
so (subst_closub_under_permit _#4 Hclm Hcls') as Hclsm'.
so (reduces_hygiene _#4 Hredmr Hclsm) as Hclr1.
so (reduces_hygiene _#4 Hredmt Hclsm') as Hclt1.
so (reduces_hygiene _#4 Hrednr Hn) as Hclr2.
so (reduces_hygiene _#4 Hrednt Hn') as Hclt2.
do2 3 split; auto using reduces_equiv.
  {
  refine (hygiene_weaken _#4 _ (hygiene_conjoin _#4 Hclr1 Hclr2)).
  intros j (Hj & Hj').
  destruct j as [| j].
    {
    omega.
    }

    {
    unfold permit in Hj.
    destruct Hj.
    }
  }

  {
  refine (hygiene_weaken _#4 _ (hygiene_conjoin _#4 Hclt1 Hclt2)).
  intros j (Hj & Hj').
  destruct j as [| j].
    {
    omega.
    }

    {
    unfold permit in Hj.
    destruct Hj.
    }
  }
Qed.


Lemma sound_constfn_intro :
  forall G m n,
    pseq (cons (hyp_tm nonsense) G) (deq triv triv (sequal (subst (dot triv sh1) m) m))
    -> pseq (cons (hyp_tm nonsense) G) (deq triv triv (sequal (subst (dot triv sh1) n) n))
    -> pseq G (deq (lam m) (lam n) constfn).
Proof.
intros G m n.
revert G.
refine (seq_pseq 2 [hyp_emp] m [hyp_emp] n 2 [_] _ [_] _ _ _); cbn.
intros G Hclm Hcln Hseqm Hseqn.
rewrite -> seq_deq in Hseqm, Hseqn |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
exists (iubase (constfn_urel stop i)).
simpsub.
so (absentia_closed _ _ Hseqm Hclm _#3 Hs) as (ml & mr & Hequivml & Hequivmr & Hclml & Hclmr).
so (absentia_closed _ _ Hseqn Hcln _#3 Hs) as (nl & nr & Hequivnl & Hequivnr & Hclnl & Hclnr).
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_constfn.
  }

  {
  apply interp_eval_refl.
  apply interp_constfn.
  }

  {
  cbn.
  exists ml, mr.
  do2 6 split; auto.
    {
    prove_hygiene.
    eapply subst_closub_under_permit; eauto.
    }

    {
    prove_hygiene.
    eapply subst_closub_under_permit; eauto.
    }

    {
    apply equiv_lam; auto.
    }

    {
    apply equiv_lam; auto.
    }
  }

  {
  cbn.
  exists nl, nr.
  do2 6 split; auto.
    {
    prove_hygiene.
    eapply subst_closub_under_permit; eauto.
    }

    {
    prove_hygiene.
    eapply subst_closub_under_permit; eauto.
    }

    {
    apply equiv_lam; auto.
    }

    {
    apply equiv_lam; auto.
    }
  }

  {
  cbn.
  exists ml, nr.
  do2 6 split; auto.
    {
    prove_hygiene.
    eapply subst_closub_under_permit; eauto.
    }

    {
    prove_hygiene.
    eapply subst_closub_under_permit; eauto.
    }

    {
    apply equiv_lam; auto.
    }

    {
    apply equiv_lam; auto.
    }
  }
Qed.



Lemma sound_constfn_elim :
  forall G m p q,
    pseq G (deq m m constfn)
    -> pseq G (deq triv triv (sequal (app m p) (app m q))).
Proof.
intros G m p q.
revert G.
refine (seq_pseq 3 [] m [] p [] q 1 [] _ _ _); cbn.
intros G Hclm Hclp Hclq Hseqm.
rewrite -> seq_deq in Hseqm |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqm _#3 Hs) as (R & Hl & _ & Hm & _).
simpsubin Hl.
invert (basic_value_inv _#6 value_constfn Hl).
intros <-.
cbn in Hm.
decompose Hm.
intros n n' _ _ _ Hequiv Hequiv' Hcln Hcln'.
exists (iubase (unit_urel stop i)).
simpsub.
do2 2 split.
  {
  apply (basic_equiv _#4 (sequal (app (subst s m) (subst s p)) (app (subst s m) (subst s p)))).
    {
    prove_hygiene.
    }

  2:{
    apply interp_eval_refl.
    apply interp_sequal; try prove_hygiene.
    apply equiv_refl.
    }
  apply equiv_sequal; auto using equiv_refl.
  apply (equiv_trans _ _ n).
    {
    apply (equiv_trans _ _ (app (lam n) (subst s p))).
      {
      apply equiv_app; auto.
      apply equiv_refl.
      }
    apply steps_equiv.
    eapply star_step.
      {
      apply step_app2.
      }
    unfold subst1.
    rewrite -> subst_into_closed; auto using star_refl.
    }

    {
    apply equiv_symm.
    apply (equiv_trans _ _ (app (lam n) (subst s q))).
      {
      apply equiv_app; auto.
      apply equiv_refl.
      }
    apply steps_equiv.
    eapply star_step.
      {
      apply step_app2.
      }
    unfold subst1.
    rewrite -> subst_into_closed; auto using star_refl.
    }
  }

  {
  apply (basic_equiv _#4 (sequal (app (subst s' m) (subst s' p)) (app (subst s' m) (subst s' p)))).
    {
    prove_hygiene.
    }

  2:{
    apply interp_eval_refl.
    apply interp_sequal; try prove_hygiene.
    apply equiv_refl.
    }
  apply equiv_sequal; auto using equiv_refl.
  apply (equiv_trans _ _ n').
    {
    apply (equiv_trans _ _ (app (lam n') (subst s' p))).
      {
      apply equiv_app; auto.
      apply equiv_refl.
      }
    apply steps_equiv.
    eapply star_step.
      {
      apply step_app2.
      }
    unfold subst1.
    rewrite -> subst_into_closed; auto using star_refl.
    }

    {
    apply equiv_symm.
    apply (equiv_trans _ _ (app (lam n') (subst s' q))).
      {
      apply equiv_app; auto.
      apply equiv_refl.
      }
    apply steps_equiv.
    eapply star_step.
      {
      apply step_app2.
      }
    unfold subst1.
    rewrite -> subst_into_closed; auto using star_refl.
    }
  }
do2 2 split; do2 5 split; auto using star_refl; try prove_hygiene.
Qed.


Lemma sound_constfn_ext :
  forall G m n,
    pseq G (deq m m constfn)
    -> pseq G (deq n n constfn)
    -> pseq G (deq m n constfn).
Proof.
intros G m n.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqm Hseqn.
rewrite -> seq_deq in Hseqm, Hseqn |- *.
intros i s s' Hs.
so (Hseqm _#3 Hs) as (R & Hl & Hr & Hm & _).
so (Hseqn _#3 Hs) as (R' & Hl' & _ & Hn & _).
so (basic_fun _#7 Hl Hl').
subst R'.
exists R.
do2 4 split; auto.
simpsubin Hl.
invert (basic_value_inv _#6 value_constfn Hl).
intros <-.
cbn in Hm, Hn |- *.
decompose Hm.
intros l _ _ Hcl _ Hequiv _ Hhyg _.
decompose Hn.
intros _ l' _ _ Hcl' _ Hequiv' _ Hhyg'.
exists l, l'.
do2 6 split; auto.
Qed.

