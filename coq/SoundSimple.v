
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

Require Import Equivalence.
Require Import SemanticsSimple.
Require Import Equivalences.
Require Import SoundHyp.
Require Import SoundSubstitution.
Require Import ProperEquiv.
Require Import Defined.
Require Import PageCode.
Require Import PageType.
Require Import Subsumption.


Local Ltac prove_hygiene :=
  repeat (first [ apply hygiene_shift_permit
                | apply hygiene_auto; cbn; repeat2 split; auto
                ]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1;
  try (apply hygiene_var; cbn; auto; done).


Lemma lvinterp_nzero :
  lvinterp nzero (fin 0).
Proof.
exists 0.
split; auto.
exact natinterp_nzero.
Qed.


Definition zeropg : page := 
  mk_page (fin 0) (fin 0) (fin 0) (le_ord_zero _) (le_ord_zero _) (le_ord_refl _).


Lemma pginterp_nzero :
  pginterp nzero zeropg.
Proof.
exists (fin 0).
do2 3 split; auto.
exact lvinterp_nzero.
Qed.


Lemma sound_voidtp_formation :
  forall G,
    pseq G (deq voidtp voidtp (univ nzero)).
Proof.
cut
  (forall G, seq G (deq voidtp voidtp (univ nzero))).
  {
  intros Hsound G.
  exists 0; intros j Hj.
  simpsub.
  apply Hsound.
  }
intros G.
rewrite -> seq_univ.
intros i s s' Hs.
exists zeropg, (iubase (void_urel stop)).
simpsub.
do2 5 split; auto using pginterp_nzero;
apply interp_eval_refl; apply interp_void.
Qed.


Lemma sound_voidtp_elim_pre :
  forall G m n p q a,
    hygiene (ctxpred G) p
    -> hygiene (ctxpred G) q
    -> hygiene (ctxpred G) a
    -> seq G (deq m n voidtp)
    -> seq G (deq p q a).
Proof.
intros G m n p q a Hclp Hclq Hcla Hseq.
invertc Hseq; intro Hseq.
apply seq_i.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hvoid & _ & Hinh & _).
invert (basic_value_inv _#6 value_voidtp Hvoid).
intros <-.
destruct Hinh.
Qed.


Lemma sound_voidtp_elim :
  forall G m n p q a,
    pseq G (deq m n voidtp)
    -> pseq G (deq p q a).
Proof.
intros G m n p q a (i1 & Hseq).
so (shut_term _ G p) as (i2 & Hclp).
so (shut_term _ G q) as (i3 & Hclq).
so (shut_term _ G a) as (i4 & Hcla).
so (upper_bound_all 4 i1 i2 i3 i4) as (i & Hi1 & Hi2 & Hi3 & Hi4 & _).
exists i.
intros j Hj.
eapply sound_voidtp_elim_pre; eauto using le_trans.
Qed.


Lemma sound_unittp_kind_formation :
  forall G lv,
    pseq G (deq lv lv pagetp)
    -> pseq G (deq unittp unittp (kuniv lv)).
Proof.
intros G lv.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseqlv.
rewrite -> seq_eqkind.
invertc Hseqlv; intro Hseqlv.
intros i s s' Hs.
so (Hseqlv _#3 Hs) as (R & Hpagetp & _ & Hlv & _).
so (interp_pagetp_invert _#7 Hpagetp Hlv) as (pg & Hlvl & Hlvr).
exists pg, qone, (iubase (unit_urel stop i)), (pginterp_lt_top _ _ Hlvl).
simpsub.
do2 9 split; auto;
try (apply kinterp_eval_refl; apply interp_kunit);
apply interp_eval_refl; apply interp_unit.
Qed.


Lemma sound_unittp_formation :
  forall G,
    pseq G (deq unittp unittp (univ nzero)).
Proof.
refine (seq_pseq 0 0 _ _); cbn.
intros G.
rewrite -> seq_univ.
intros i s s' Hs.
exists zeropg, (iubase (unit_urel stop i)).
simpsub.
do2 5 split; auto using pginterp_nzero;
apply interp_eval_refl; apply interp_unit.
Qed.


Lemma sound_unittp_intro_pre :
  forall G,
    seq G (deq triv triv unittp).
Proof.
intros G.
apply seq_i.
intros i s s' Hs.
exists (iubase (unit_urel stop i)).
simpsub.
do2 2 split; try (apply interp_eval_refl; apply interp_unit).
assert (rel (unit_urel stop i) i triv triv) as H.
  {
  do2 5 split; auto using star_refl; prove_hygiene.
  }
auto.
Qed.


Lemma sound_unittp_intro :
  forall G,
    pseq G (deq triv triv unittp).
Proof.
refine (seq_pseq 0 0 _ _); cbn.
intros G.
apply sound_unittp_intro_pre.
Qed.


Lemma sound_unittp_eta :
  forall G p,
    pseq G (deq p p unittp)
    -> pseq G (deq p triv unittp).
Proof.
intros G p.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
invertc Hseq; intro Hseq.
apply seq_i.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hunitl & Hunitr & Hp & _).
simpsubin Hunitl.
simpsubin Hunitr.
invert (basic_value_inv _#6 value_unittp Hunitl).
intros <-.
exists (iubase (unit_urel stop i)).
do2 4 split; auto.
  {
  simpsub.
  apply unit_urel_triv; auto.
  }

  {
  simpsub.
  destruct Hp as (_ & _ & Hclsp & _ & Hsteps & _).
  do2 5 split; auto using star_refl; try prove_hygiene.
  }
Qed.


Lemma sound_unittp_eta_hyp :
  forall G1 G2 m n b,
    pseq (substctx (dot triv id) G2 ++ G1) (deq m n (subst (under (length G2) (dot triv id)) b))
    -> pseq (G2 ++ hyp_tm unittp :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) b).
Proof.
intros G1 G2 m n b Hseq.
eapply sound_property_eta_hyp; eauto.
intros s pg z i R H.
simpsubin H.
invert (basic_value_inv _#6 value_unittp H).
intros <-.
do 3 eexists.
reflexivity.
Qed.


Lemma sound_booltp_formation :
  forall G,
    pseq G (deq booltp booltp (univ nzero)).
Proof.
refine (seq_pseq 0 0 _ _).
cbn.
intros G.
rewrite -> seq_univ.
intros i s s' Hs.
exists zeropg, (iubase (bool_urel stop i)).
simpsub.
do2 5 split; auto using pginterp_nzero;
apply interp_eval_refl; apply interp_bool.
Qed.


Lemma sound_booltp_intro_btrue :
  forall G,
    pseq G (deq btrue btrue booltp).
Proof.
refine (seq_pseq 0 0 _ _).
intros G.
apply seq_i.
intros i s s' Hs.
exists (iubase (bool_urel stop i)).
simpsub.
do2 2 split;
try (apply interp_eval_refl; apply interp_bool).
assert (rel (bool_urel stop i) i btrue btrue) as H.
  {
  do2 3 split; auto; try prove_hygiene.
  left.
  split; apply star_refl.
  }
auto.
Qed.


Lemma sound_booltp_intro_bfalse :
  forall G,
    pseq G (deq bfalse bfalse booltp).
Proof.
refine (seq_pseq 0 0 _ _).
intros G.
apply seq_i.
intros i s s' Hs.
exists (iubase (bool_urel stop i)).
simpsub.
do2 2 split;
try (apply interp_eval_refl; apply interp_bool).
assert (rel (bool_urel stop i) i bfalse bfalse) as H.
  {
  do2 3 split; auto; try prove_hygiene.
  right.
  split; apply star_refl.
  }
auto.
Qed.


Lemma sound_booltp_elim_pre :
  forall G m n p q r s a,
    hygiene (ctxpred G) a
    -> hygiene (ctxpred G) m
    -> hygiene (ctxpred G) n
    -> hygiene (ctxpred G) p
    -> hygiene (ctxpred G) q
    -> hygiene (ctxpred G) r
    -> hygiene (ctxpred G) s
    -> seq G (deq m n booltp)
    -> seq G (deq p q (subst1 btrue a))
    -> seq G (deq r s (subst1 bfalse a))
    -> seq G (deq (bite m p r) (bite n q s) (subst1 m a)).
Proof.
intros G m n p q r t a Hcla Hclm Hcln Hclp Hclq Hclr Hclt Hseqmn Hseqpq Hseqrt.
invertc Hseqmn; intro Hseqmn.
invertc Hseqpq; intro Hseqpq.
invertc Hseqrt; intro Hseqrt.
apply seq_i.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmn _#3 Hs) as (R & Hbool & _ & Hm & Hn & Hmn).
simpsubin Hbool.
invert (basic_value_inv _#6 value_booltp Hbool).
intros <-.
destruct Hm as (_ & _ & _ & H).
destruct H as [(Hstepsml & Hstepsmr) | (Hstepsml & Hstepsmr)].
  {
  destruct Hn as (_ & _ & _ & H).
  destruct H as [(Hstepsnl & Hstepsnr) | (_ & Hstepsnr)].
  2:{
    exfalso.
    destruct Hmn as (_ & _ & _ & H).
    destruct H as [(_ & Hstepsnr') | (Hstepsml' & _)].
      {
      so (determinism_eval _#4 (conj Hstepsnr value_bfalse) (conj Hstepsnr' value_btrue)) as Heq.
      discriminate Heq.
      }

      {
      so (determinism_eval _#4 (conj Hstepsml value_btrue) (conj Hstepsml' value_bfalse)) as Heq.
      discriminate Heq.
      }
    }
  assert (forall (x y z : sterm),
            star step x btrue
            -> equiv y (bite x y z)) as Hequiv.
    {
    intros x y z Hsteps.
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_bite; [| apply equiv_refl ..].
      apply steps_equiv; eauto.
      }
    apply steps_equiv; apply star_one.
    apply step_bite2.
    }
  so (Hseqpq _#3 Hs) as (A & Hal & Har & Hp & Hq & Hpq).
  exists A.
  do2 4 split.
    {
    simpsub.
    eapply basic_equiv; eauto.
      {
      eapply hygiene_subst; eauto.
      intros j Hj.
      destruct j as [| j].
        {
        simpsub.
        eapply subst_closub; eauto.
        }
      simpsub.
      cbn in Hj.
      replace (project s j) with (subst s (var j)) by (simpsub; reflexivity).
      eapply subst_closub; eauto.
      apply hygiene_var.
      rewrite -> ctxpred_length in Hj |- *.
      omega.
      }

      {
      simpsub.
      apply equiv_funct; auto using equiv_refl.
      apply equivsub_dot; auto using equivsub_refl.
      apply equiv_symm.
      eapply steps_equiv; eauto.
      }
    }

    {
    simpsub.
    eapply basic_equiv; eauto.
      {
      eapply hygiene_subst; eauto.
      intros j Hj.
      destruct j as [| j].
        {
        simpsub.
        eapply subst_closub; eauto.
        }
      simpsub.
      cbn in Hj.
      replace (project s' j) with (subst s' (var j)) by (simpsub; reflexivity).
      eapply subst_closub; eauto.
      apply hygiene_var.
      rewrite -> ctxpred_length in Hj |- *.
      omega.
      }

      {
      simpsub.
      apply equiv_funct; auto using equiv_refl.
      apply equivsub_dot; auto using equivsub_refl.
      apply equiv_symm.
      eapply steps_equiv; eauto.
      }
    }
  
    {
    simpsub.
    refine (urel_equiv _#7 _ _ _ _ Hp); try (prove_hygiene; eapply subst_closub; eauto).
    }

    {
    simpsub.
    refine (urel_equiv _#7 _ _ _ _ Hq); try (prove_hygiene; eapply subst_closub; eauto).
    }

    {
    simpsub.
    refine (urel_equiv _#7 _ _ _ _ Hpq); try (prove_hygiene; eapply subst_closub; eauto).
    }
  }

  {
  destruct Hn as (_ & _ & _ & H).
  destruct H as [(_ & Hstepsnr) | (Hstepsnl & Hstepsnr)].
    {
    exfalso.
    destruct Hmn as (_ & _ & _ & H).
    destruct H as [(Hstepsml' & _) | (_ & Hstepsnr')].
      {
      so (determinism_eval _#4 (conj Hstepsml value_bfalse) (conj Hstepsml' value_btrue)) as Heq.
      discriminate Heq.
      }

      {
      so (determinism_eval _#4 (conj Hstepsnr value_btrue) (conj Hstepsnr' value_bfalse)) as Heq.
      discriminate Heq.
      }
    }
  assert (forall (x y z : sterm),
            star step x bfalse
            -> equiv z (bite x y z)) as Hequiv.
    {
    intros x y z Hsteps.
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_bite; [| apply equiv_refl ..].
      apply steps_equiv; eauto.
      }
    apply steps_equiv; apply star_one.
    apply step_bite3.
    }
  so (Hseqrt _#3 Hs) as (A & Hal & Har & Hp & Hq & Hpq).
  exists A.
  do2 4 split.
    {
    simpsub.
    eapply basic_equiv; eauto.
      {
      eapply hygiene_subst; eauto.
      intros j Hj.
      destruct j as [| j].
        {
        simpsub.
        eapply subst_closub; eauto.
        }
      simpsub.
      cbn in Hj.
      replace (project s j) with (subst s (var j)) by (simpsub; reflexivity).
      eapply subst_closub; eauto.
      apply hygiene_var.
      rewrite -> ctxpred_length in Hj |- *.
      omega.
      }

      {
      simpsub.
      apply equiv_funct; auto using equiv_refl.
      apply equivsub_dot; auto using equivsub_refl.
      apply equiv_symm.
      eapply steps_equiv; eauto.
      }
    }

    {
    simpsub.
    eapply basic_equiv; eauto.
      {
      eapply hygiene_subst; eauto.
      intros j Hj.
      destruct j as [| j].
        {
        simpsub.
        eapply subst_closub; eauto.
        }
      simpsub.
      cbn in Hj.
      replace (project s' j) with (subst s' (var j)) by (simpsub; reflexivity).
      eapply subst_closub; eauto.
      apply hygiene_var.
      rewrite -> ctxpred_length in Hj |- *.
      omega.
      }

      {
      simpsub.
      apply equiv_funct; auto using equiv_refl.
      apply equivsub_dot; auto using equivsub_refl.
      apply equiv_symm.
      eapply steps_equiv; eauto.
      }
    }
  
    {
    simpsub.
    refine (urel_equiv _#7 _ _ _ _ Hp); try (prove_hygiene; eapply subst_closub; eauto).
    }

    {
    simpsub.
    refine (urel_equiv _#7 _ _ _ _ Hq); try (prove_hygiene; eapply subst_closub; eauto).
    }

    {
    simpsub.
    refine (urel_equiv _#7 _ _ _ _ Hpq); try (prove_hygiene; eapply subst_closub; eauto).
    }
  }
Qed.


Lemma sound_booltp_elim :
  forall G m n p q r s a,
    pseq G (deq m n booltp)
    -> pseq G (deq p q (subst1 btrue a))
    -> pseq G (deq r s (subst1 bfalse a))
    -> pseq G (deq (bite m p r) (bite n q s) (subst1 m a)).
Proof.
intros G m n p q r t a (i1, Hmn) (i2, Hpq) (i3, Hrt).
so (shut_term _ G m) as (i4, Hclm).
so (shut_term _ G n) as (i5, Hcln).
so (shut_term _ G p) as (i6, Hclp).
so (shut_term _ G q) as (i7, Hclq).
so (shut_term _ G r) as (i8, Hclr).
so (shut_term _ G t) as (i9, Hclt).
so (shut_term _ G a) as (i10, Hcla).
so (upper_bound_all 10 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10) as (i & Hi1 & Hi2 & Hi3 & Hi4 & Hi5 & Hi6 & Hi7 & Hi8 & Hi9 & Hi10 & _).
exists i; intros j Hj.
eapply sound_booltp_elim_pre; eauto using le_trans.
Qed.


Lemma sound_booltp_elim_eqtype_pre :
  forall G m n p q r s,
    hygiene (ctxpred G) m
    -> hygiene (ctxpred G) n
    -> hygiene (ctxpred G) p
    -> hygiene (ctxpred G) q
    -> hygiene (ctxpred G) r
    -> hygiene (ctxpred G) s
    -> seq G (deq m n booltp)
    -> seq G (deqtype p q)
    -> seq G (deqtype r s)
    -> seq G (deqtype (bite m p r) (bite n q s)).
Proof.
intros G m n p q r t Hclm Hcln Hclp Hclq Hclr Hclt Hseqmn Hseqpq Hseqrt.
rewrite -> seq_eqtype in Hseqpq, Hseqrt |- *.
invertc Hseqmn; intro Hseqmn.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmn _#3 Hs) as (R & Hbool & _ & Hm & Hn & Hmn).
simpsubin Hbool.
invert (basic_value_inv _#6 value_booltp Hbool).
intros <-.
destruct Hm as (_ & _ & _ & H).
destruct H as [(Hstepsml & Hstepsmr) | (Hstepsml & Hstepsmr)].
  {
  destruct Hn as (_ & _ & _ & H).
  destruct H as [(Hstepsnl & Hstepsnr) | (_ & Hstepsnr)].
  2:{
    exfalso.
    destruct Hmn as (_ & _ & _ & H).
    destruct H as [(_ & Hstepsnr') | (Hstepsml' & _)].
      {
      so (determinism_eval _#4 (conj Hstepsnr value_bfalse) (conj Hstepsnr' value_btrue)) as Heq.
      discriminate Heq.
      }

      {
      so (determinism_eval _#4 (conj Hstepsml value_btrue) (conj Hstepsml' value_bfalse)) as Heq.
      discriminate Heq.
      }
    }
  assert (forall (x y z : sterm),
            star step x btrue
            -> equiv y (bite x y z)) as Hequiv.
    {
    intros x y z Hsteps.
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_bite; [| apply equiv_refl ..].
      apply steps_equiv; eauto.
      }
    apply steps_equiv; apply star_one.
    apply step_bite2.
    }
  so (Hseqpq _#3 Hs) as (P & Hpl & Hpr & Hql & Hqr).
  exists P.
  do2 3 split.
    {
    simpsub.
    eapply basic_equiv; eauto.
    prove_hygiene; eapply hygiene_subst; eauto.
    }

    {
    simpsub.
    eapply basic_equiv; eauto.
    prove_hygiene; eapply hygiene_subst; eauto.
    }

    {
    simpsub.
    eapply basic_equiv; eauto.
    prove_hygiene; eapply hygiene_subst; eauto.
    }

    {
    simpsub.
    eapply basic_equiv; eauto.
    prove_hygiene; eapply hygiene_subst; eauto.
    }
  }

  {
  destruct Hn as (_ & _ & _ & H).
  destruct H as [(_ & Hstepsnr) | (Hstepsnl & Hstepsnr)].
    {
    exfalso.
    destruct Hmn as (_ & _ & _ & H).
    destruct H as [(Hstepsml' & _) | (_ & Hstepsnr')].
      {
      so (determinism_eval _#4 (conj Hstepsml value_bfalse) (conj Hstepsml' value_btrue)) as Heq.
      discriminate Heq.
      }

      {
      so (determinism_eval _#4 (conj Hstepsnr value_btrue) (conj Hstepsnr' value_bfalse)) as Heq.
      discriminate Heq.
      }
    }
  assert (forall (x y z : sterm),
            star step x bfalse
            -> equiv z (bite x y z)) as Hequiv.
    {
    intros x y z Hsteps.
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply equiv_bite; [| apply equiv_refl ..].
      apply steps_equiv; eauto.
      }
    apply steps_equiv; apply star_one.
    apply step_bite3.
    }
  so (Hseqrt _#3 Hs) as (R & Hrl & Hrr & Htl & Htr).
  exists R.
  do2 3 split.
    {
    simpsub.
    eapply basic_equiv; eauto.
    prove_hygiene; eapply hygiene_subst; eauto.
    }

    {
    simpsub.
    eapply basic_equiv; eauto.
    prove_hygiene; eapply hygiene_subst; eauto.
    }

    {
    simpsub.
    eapply basic_equiv; eauto.
    prove_hygiene; eapply hygiene_subst; eauto.
    }

    {
    simpsub.
    eapply basic_equiv; eauto.
    prove_hygiene; eapply hygiene_subst; eauto.
    }
  }
Qed.


Lemma sound_booltp_elim_eqtype :
  forall G m n p q r s,
    pseq G (deq m n booltp)
    -> pseq G (deqtype p q)
    -> pseq G (deqtype r s)
    -> pseq G (deqtype (bite m p r) (bite n q s)).
Proof.
intros G m n p q r t (i1, Hmn) (i2, Hpq) (i3, Hrt).
so (shut_term _ G m) as (i4, Hclm).
so (shut_term _ G n) as (i5, Hcln).
so (shut_term _ G p) as (i6, Hclp).
so (shut_term _ G q) as (i7, Hclq).
so (shut_term _ G r) as (i8, Hclr).
so (shut_term _ G t) as (i9, Hclt).
so (upper_bound_all 9 i1 i2 i3 i4 i5 i6 i7 i8 i9) as (i & Hi1 & Hi2 & Hi3 & Hi4 & Hi5 & Hi6 & Hi7 & Hi8 & Hi9 & _).
exists i; intros j Hj.
eapply sound_booltp_elim_eqtype_pre; eauto using le_trans.
Qed.


Lemma equivsub_under_dot :
  forall object i (b : @term object) s,
    hygiene clo b
    -> star step (project s i) b
    -> equivsub (compose (under i (compose (dot b id) sh1)) s) s.
Proof.
intros object i b s Hclb Hsteps.
simpsub.
intro j.
rewrite -> project_compose.
so (lt_eq_lt_dec j i) as [[Hlt | Heq] | Hlt].
  {
  rewrite -> project_under_lt; auto.
  simpsub.
  apply equiv_refl.
  }

  {
  subst j.
  rewrite -> project_under_eq.
  simpsub.
  rewrite -> (subst_into_closed _ _ b); auto.
  apply equiv_symm.
  apply steps_equiv.
  exact Hsteps.
  }

  {
  rewrite -> project_under_geq; [| omega].
  replace (j - i) with (S (j - i - 1)) by omega.
  simpsub.
  replace (i + (1 + (j - i - 1))) with j by omega.
  apply equiv_refl.
  }
Qed.


Lemma sound_booltp_eta_hyp_pre :
  forall G1 G2 m n p q a,
    hygiene (ctxpred (substctx (dot btrue id) G2 ++ G1)) m
    -> hygiene (ctxpred (substctx (dot btrue id) G2 ++ G1)) n
    -> hygiene (ctxpred (substctx (dot bfalse id) G2 ++ G1)) p
    -> hygiene (ctxpred (substctx (dot bfalse id) G2 ++ G1)) q
    -> hygiene (ctxpred (G2 ++ hyp_tm booltp :: G1)) a
    -> seq (substctx (dot btrue id) G2 ++ G1) (deq m n (subst (under (length G2) (dot btrue id)) a))
    -> seq (substctx (dot bfalse id) G2 ++ G1) (deq p q (subst (under (length G2) (dot bfalse id)) a))
    -> seq (G2 ++ cons (hyp_tm booltp) G1) 
         (deq 
            (bite (var (length G2)) 
               (subst (under (length G2) sh1) m)
               (subst (under (length G2) sh1) p))
            (bite (var (length G2))
               (subst (under (length G2) sh1) n) 
               (subst (under (length G2) sh1) q))
            a).
Proof.
intros G1 G2 m n p q a Hclm Hcln Hclp Hclq Hcla Hseqmn Hseqpq.
apply seq_i.
invertc Hseqmn; intro Hseqmn.
invertc Hseqpq; intro Hseqpq.
intros i s s' Hs.
assert (index (length G2) (G2 ++ hyp_tm booltp :: G1)%list (hyp_tm booltp)) as Hindex.
  {
  replace (length G2) with (0 + length G2) by omega.
  apply index_app_right.
  apply index_0.
  }
so (seqctx_index _#6 (pwctx_impl_seqctx _#4 Hs) Hindex) as Hhyp.
simpsubin Hhyp.
set (x := project s (length G2)) in Hhyp.
set (y := project s' (length G2)) in Hhyp.
invertc Hhyp.
intros R Hbool _ Hxy.
invert (basic_value_inv _#6 value_booltp Hbool).
intros <-.
clear Hbool Hindex.
destruct Hxy as (_ & Hclx & Hcly & Hxy).
assert (exists b,
          hygiene clo b
          /\ star step x b
          /\ star step y b
          /\ (forall j, rel (bool_urel stop j) j b b)
          /\ forall s s',
               pwctx i s s' (substctx (dot b id) G2 ++ G1)
               -> exists A,
                    interp toppg true i (subst s (subst (under (length G2) (dot b id)) a)) A
                    /\ interp toppg false i (subst s' (subst (under (length G2) (dot b id)) a)) A
                    /\ rel (den A) i (bite x (subst s m) (subst s p)) (bite y (subst s' m) (subst s' p))
                    /\ rel (den A) i (bite x (subst s n) (subst s q)) (bite y (subst s' n) (subst s' q))
                    /\ rel (den A) i (bite x (subst s m) (subst s p)) (bite y (subst s' n) (subst s' q))) as H.
  {
  destruct Hxy as [(Hstepsx & Hstepsy) | (Hstepsx & Hstepsy)].
    {
    exists btrue.
    do2 4 split; auto; try prove_hygiene.
      {
      intro j.
      do2 3 split; auto; try prove_hygiene.
      left; auto using star_refl.
      }

      {
      intros t t' Ht.
      so (pwctx_impl_closub _#4 Ht) as (Hclt & Hclt').
      rewrite -> ctxpred_length in Hclt, Hclt', Hclm, Hcln, Hclp, Hclq.
      rewrite -> app_length in Hclt, Hclt', Hclm, Hcln, Hclp, Hclq.
      rewrite -> length_substctx in Hclt, Hclt', Hclm, Hcln, Hclp, Hclq.
      so (Hseqmn i t t' Ht) as (R & Hl & Hr & Hm & Hn & Hmn).
      exists R.
      assert (forall z z', equiv z (bite x z z')) as Hequivx.
        {
        intros z z'.
        apply equiv_symm.
        apply steps_equiv.
        eapply star_trans.
          {
          apply (star_map' _ _ (fun zz => bite zz _ _)); auto using step_bite1.
          exact Hstepsx.
          }
        apply star_one.
        apply step_bite2.
        }
      assert (forall z z', equiv z (bite y z z')) as Hequivy.
        {
        intros z z'.
        apply equiv_symm.
        apply steps_equiv.
        eapply star_trans.
          {
          apply (star_map' _ _ (fun zz => bite zz _ _)); auto using step_bite1.
          exact Hstepsy.
          }
        apply star_one.
        apply step_bite2.
        }
      do2 4 split; auto.
        {
        refine (urel_equiv _#7 _ _ _ _ Hm); try prove_hygiene; eauto using subst_closub.
        }

        {
        refine (urel_equiv _#7 _ _ _ _ Hn); try prove_hygiene; eauto using subst_closub.
        }

        {
        refine (urel_equiv _#7 _ _ _ _ Hmn); try prove_hygiene; eauto using subst_closub.
        }
      }
    }

    {
    exists bfalse.
    do2 4 split; auto; try prove_hygiene.
      {
      intro j.
      do2 3 split; auto; try prove_hygiene.
      right; auto using star_refl.
      }

      {
      intros t t' Ht.
      so (pwctx_impl_closub _#4 Ht) as (Hclt & Hclt').
      rewrite -> ctxpred_length in Hclt, Hclt', Hclm, Hcln, Hclp, Hclq.
      rewrite -> app_length in Hclt, Hclt', Hclm, Hcln, Hclp, Hclq.
      rewrite -> length_substctx in Hclt, Hclt', Hclm, Hcln, Hclp, Hclq.
      so (Hseqpq i t t' Ht) as (R & Hl & Hr & Hp & Hq & Hpq).
      exists R.
      assert (forall z z', equiv z' (bite x z z')) as Hequivx.
        {
        intros z z'.
        apply equiv_symm.
        apply steps_equiv.
        eapply star_trans.
          {
          apply (star_map' _ _ (fun zz => bite zz _ _)); auto using step_bite1.
          exact Hstepsx.
          }
        apply star_one.
        apply step_bite3.
        }
      assert (forall z z', equiv z' (bite y z z')) as Hequivy.
        {
        intros z z'.
        apply equiv_symm.
        apply steps_equiv.
        eapply star_trans.
          {
          apply (star_map' _ _ (fun zz => bite zz _ _)); auto using step_bite1.
          exact Hstepsy.
          }
        apply star_one.
        apply step_bite3.
        }
      do2 4 split; auto.
        {
        refine (urel_equiv _#7 _ _ _ _ Hp); try prove_hygiene; eauto using subst_closub.
        }

        {
        refine (urel_equiv _#7 _ _ _ _ Hq); try prove_hygiene; eauto using subst_closub.
        }

        {
        refine (urel_equiv _#7 _ _ _ _ Hpq); try prove_hygiene; eauto using subst_closub.
        }
      }
    }
  }
clear Hclm Hcln Hclp Hclq Hseqmn Hseqpq Hxy.
destruct H as (b & Hclb & Hpb & Hqb & Hrelb & Hseq).
exploit (subst_pwctx G1 G2 booltp b i s s' (iubase (bool_urel stop i))) as Ht; auto.
  {
  intros j u u' Hu.
  exists (iubase (bool_urel stop j)).
  simpsub.
  do2 2 split.
    {
    apply interp_eval_refl.
    apply interp_bool.
    }

    {
    apply interp_eval_refl.
    apply interp_bool.
    }

    {
    rewrite -> !(subst_into_closed _ _ b); auto.
    apply Hrelb.
    }
  }

  {
  apply interp_eval_refl.
  apply interp_bool.
  }

  {
  apply interp_eval_refl.
  apply interp_bool.
  }

  {
  rewrite -> !(subst_into_closed _ _ b); auto.
  apply Hrelb.
  }

  {
  rewrite -> !(subst_into_closed _ _ b); auto.
  apply (urel_equiv_1 _#3 b); auto.
    {
    apply equiv_symm.
    apply steps_equiv; auto.
    }

    {
    apply Hrelb.
    }
  }
set (t := compose (under (length G2) sh1) s) in Ht.
set (t' := compose (under (length G2) sh1) s') in Ht.
so (Hseq _ _ Ht) as (A & Hal & Har & Hm & Hn & Hmn).
clear Hseq.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
exists A.
simpsub.
do2 4 split; auto.
  {
  eapply basic_equiv; eauto.
    {
    eapply subst_closub; eauto.
    }
  simpsub. 
  unfold t.
  rewrite <- compose_assoc.
  rewrite <- compose_under.
  apply equiv_funct; auto using equiv_refl.
  apply equivsub_under_dot; auto.
 }

  {
  eapply basic_equiv; eauto.
    {
    eapply subst_closub; eauto.
    }
  simpsub.
  apply equiv_funct; auto using equiv_refl.
  unfold t'.
  rewrite <- compose_assoc.
  rewrite <- compose_under.
  apply equivsub_under_dot; auto.
  }
Qed.


Lemma sound_booltp_eta_hyp :
  forall G1 G2 m n p q a,
    pseq (substctx (dot btrue id) G2 ++ G1) (deq m n (subst (under (length G2) (dot btrue id)) a))
    -> pseq (substctx (dot bfalse id) G2 ++ G1) (deq p q (subst (under (length G2) (dot bfalse id)) a))
    -> pseq (G2 ++ cons (hyp_tm booltp) G1) 
         (deq 
            (bite (var (length G2)) 
               (subst (under (length G2) sh1) m)
               (subst (under (length G2) sh1) p))
            (bite (var (length G2))
               (subst (under (length G2) sh1) n) 
               (subst (under (length G2) sh1) q))
            a).
Proof.
intros G1 G2 m n p q a (i1, Hmn) (i2, Hpq).
so (shut_term _ (substctx (dot btrue id) G2 ++ G1) m) as (i3, Hclm).
so (shut_term _ (substctx (dot btrue id) G2 ++ G1) n) as (i4, Hcln).
so (shut_term _ (substctx (dot bfalse id) G2 ++ G1) p) as (i5, Hclp).
so (shut_term _ (substctx (dot bfalse id) G2 ++ G1) q) as (i6, Hclq).
so (shut_term _ (G2 ++ hyp_tm booltp :: G1) a) as (i7, Hcla).
so (upper_bound_all 7 i1 i2 i3 i4 i5 i6 i7) as (i & Hi1 & Hi2 & Hi3 & Hi4 & Hi5 & Hi6 & Hi7 & _).
exists i; intros j Hj.
autorewrite with canonlist.
apply sound_booltp_eta_hyp_pre; finish_pseq j.
Qed.
