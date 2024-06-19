
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

Require Import SemanticsSimple.
Require Import ProperLevel.
Require Import Equivalence.
Require Import Subsumption.
Require Import ProperEquiv.
Require Import Truncate.
Require Import ProperDownward.
Require Import Equivalences.



Local Ltac prove_hygiene :=
  repeat (apply hygiene_auto; cbn; repeat2 split; auto);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1, subst_closub;
  try (apply hygiene_var; cbn; auto; done).



Lemma sound_sequal_formation :
  forall G m n,
    pseq G (deqtype (sequal m m) (sequal n n)).
Proof.
intros G m n.
revert G.
refine (seq_pseq 2 [] m [] n 0 _ _); cbn.
intros G Hclm Hcln.
rewrite -> seq_eqtype.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (subst_closub _#4 Hcls Hclm) as Hclm'.
so (subst_closub _#4 Hcls' Hclm) as Hclm''.
so (subst_closub _#4 Hcls Hcln) as Hcln'.
so (subst_closub _#4 Hcls' Hcln) as Hcln''.
exists (iubase (unit_urel stop i)); auto using interp_eval_refl, interp_sequal.
simpsub.
do2 3 split; auto.
  {
  apply interp_eval_refl.
  apply interp_sequal; auto.
  apply equiv_refl.
  }

  {
  apply interp_eval_refl.
  apply interp_sequal; auto.
  apply equiv_refl.
  }
  {
  apply interp_eval_refl.
  apply interp_sequal; auto.
  apply equiv_refl.
  }

  {
  apply interp_eval_refl.
  apply interp_sequal; auto.
  apply equiv_refl.
  }
Qed.


Lemma sound_sequal_intro :
  forall G m,
    pseq G (deq triv triv (sequal m m)).
Proof.
intros G m.
revert G.
refine (seq_pseq 1 [] m 0 _ _); cbn.
intros G Hclm.
rewrite -> seq_deq.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (subst_closub _#4 Hcls Hclm) as Hclm'.
so (subst_closub _#4 Hcls' Hclm) as Hclm''.
exists (iubase (unit_urel stop i)); auto using interp_eval_refl, interp_sequal.
simpsub.
rewrite -> den_iubase.
assert (rel (unit_urel stop i) i triv triv) as Htriv.
  {
  do2 5 split; auto using star_refl.
    {
    apply hygiene_auto; cbn; auto.
    }

    {
    apply hygiene_auto; cbn; auto.
    }
  }
do2 4 split; auto.
  {
  apply interp_eval_refl.
  apply interp_sequal; auto.
  apply equiv_refl.
  }

  {
  apply interp_eval_refl.
  apply interp_sequal; auto.
  apply equiv_refl.
  }
Qed.


Lemma sound_sequal_eta :
  forall G m n p,
    pseq G (deq p p (sequal m n))
    -> pseq G (deq p triv (sequal m n)).
Proof.
intros G m n p.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hequall & Hequalr & Htrue & _).
simpsubin Hequall.
invert (basic_value_inv _#6 value_sequal Hequall).
intros _ _ _ Heq.
exists R.
do2 4 split; auto.
  {
  simpsub.
  subst R.
  do2 5 split; auto using star_refl.
    {
    apply hygiene_auto; cbn; auto.
    }

    {
    apply hygiene_auto; cbn; auto.
    }
  }

  {
  simpsub.
  subst R.
  destruct Htrue as (_ & _ & Hclsp & Hclsp' & Hsteps & _).
  do2 5 split; auto using star_refl.
    {
    apply hygiene_auto; cbn; auto.
    }
  }
Qed.


Lemma sound_sequal_eta_hyp :
  forall G1 G2 p q m n b,
    pseq (substctx (dot triv id) G2 ++ G1) (deq m n (subst (under (length G2) (dot triv id)) b))
    -> pseq (G2 ++ hyp_tm (sequal p q) :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) b).
Proof.
intros G1 G2 p q m n b Hseq.
eapply sound_property_eta_hyp; eauto.
intros s pg z i R H.
simpsubin H.
invert (basic_value_inv _#6 value_sequal H).
intros _ _ _ _ <-.
do 3 eexists; reflexivity.
Qed.


Lemma sound_sequal_equal :
  forall G a m n,
    pseq G (deq triv triv (sequal m n))
    -> pseq G (deq m m a)
    -> pseq G (deq m n a).
Proof.
intros G a m n.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqmn Hseqm.
rewrite -> seq_deq in Hseqmn, Hseqm |- *.
intros i s s' Hs.
so (Hseqm _#3 Hs) as (A & Hal & Har & Hm & _).
so (Hseqmn _#3 Hs) as (R & Hl & Hr & _).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_sequal Hl).
intros Hclsm Hclsn Hequiv _.
invert (basic_value_inv _#6 value_sequal Hr).
intros Hclsm' Hclsn' Hequiv' _.
exists A.
simpsub.
do2 4 split; auto.
  {
  eapply urel_equiv; eauto.
  }

  {
  apply (urel_equiv_2 _#4 (subst s' m)); auto.
  }
Qed.


Lemma sound_sequal_eqtype :
  forall G a b,
    pseq G (deq triv triv (sequal a b))
    -> pseq G (deqtype a a)
    -> pseq G (deqtype a b).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqab Hseqa.
rewrite -> seq_eqtype in Hseqa |- *.
rewrite -> seq_deq in Hseqab.
intros i s s' Hs.
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
so (Hseqab _#3 Hs) as (R & Hl & Hr & _).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_sequal Hl).
intros Hclsa Hclsb Hequiv _.
invert (basic_value_inv _#6 value_sequal Hr).
intros Hclsa' Hclsb' Hequiv' _.
exists A.
simpsub.
do2 3 split; auto.
  {
  eapply basic_equiv; eauto.
  }

  {
  eapply basic_equiv; eauto.
  }
Qed.


Lemma sound_syntactic_substitution :
  forall G1 G2 a m n n' b,
    pseq 
      (substctx (dot (var 0) (dot (subst (sh 2) m) (sh 2))) G2 ++ hyp_tm (sequal (var 0) (subst sh1 m)) :: hyp_tm a :: G1) 
      (deq n n' (subst (under (length G2) (dot (var 0) (dot (subst (sh 2) m) (sh 2)))) b))
    -> pseq 
         (G2 ++ hyp_tm (sequal (var 0) (subst sh1 m)) :: hyp_tm a :: G1)
         (deq n n' b).
Proof.
intros G1 G2 a m n n' b.
revert G1.
refine (seq_pseq_hyp 2 [] m (G2 ++ [hyp_tm (sequal (var 0) (subst sh1 m)); hyp_tm a]) b 1 _ [_; _] _ _ [_; _] _ _); cbn.
intros G1 Hclm Hclb Hseq _.
assert (subsume 
          (hyp_tm (sequal (var 0) (subst sh1 m)) :: hyp_tm a :: G1)
          (hyp_tm (sequal (var 0) (subst sh1 m)) :: hyp_tm a :: G1)
          id
          (dot (var 0) (dot (subst (sh 2) m) (sh 2)))) as Hsubsume.
  {
  clear b Hclb Hseq n n'.
  do2 2 split.
    {
    intro j.
    cbn.
    split.
      {
      intro H.
      destruct j as [|[ | j]].
        {
        simpsub.
        apply hygiene_var; auto.
        }

        {
        simpsub.
        apply hygiene_shift'; auto.
        }

        {
        simpsub.
        apply hygiene_var; auto.
        }
      }

      {
      intro H.
      destruct j as [|[| j]].
        {
        cbn.
        auto.
        }

        {
        cbn; auto.
        }

        {
        cbn.
        simpsubin H.
        invert H.
        cbn.
        auto.
        }
      }
    }

    {
    intro j.
    cbn.
    split.
      {
      intro H.
      simpsub.
      apply hygiene_var.
      auto.
      }

      {
      intro H.
      simpsubin H.
      cbn in H.
      invert H; auto.
      }
    }
    
    {
    intros i ss ss' Hss.
    invert Hss.
    intros n n' ss1 ss1' Hss1 Hn _ _ <- <-.
    invertc Hss1.
    intros p p' s s' Hs Hp Hleft Hright <- <-.
    simpsubin Hn.
    invertc Hn.
    intros R Hl Hr _.
    invert (basic_value_inv _#6 value_sequal Hl).
    intros _ _ Hequiv _.
    invert (basic_value_inv _#6 value_sequal Hr).
    intros _ _ Hequiv' _.
    clear R Hl Hr.
    do2 4 split; auto.
      {
      simpsub.
      apply equivsub_dot; auto using equiv_refl.
      apply equivsub_dot; auto using equivsub_refl.
      apply equiv_symm; auto.
      }

      {
      simpsub.
      apply equivsub_dot; auto using equiv_refl.
      apply equivsub_dot; auto using equivsub_refl.
      apply equiv_symm; auto.
      }

      {
      intros j b t Hj Htt.
      simpsubin Htt.
      rewrite -> !qpromote_cons in Htt |- *.
      rewrite -> !qpromote_hyp_tm in Htt |- *.
      invert Htt.
      intros n'' tt1 Htt1 Hn'' <-.
      invertc Htt1.
      intros p'' t Ht Hp'' <-.
      simpsub.
      simpsubin Hn''.
      invert Hn''.
      intros R _ HR _.
      invert (basic_value_inv _#6 value_sequal HR).
      intros Hclp'' Hcltm Hequivp''_tm _.
      clear R HR.
      simpsubin Hp''.
      apply seqctx_cons.
        {
        apply seqctx_cons; auto.
        simpsub.
        invert Hp''.
        intros R Hl Hr H.
        apply (seqhyp_tm _#5 R); auto.
        eapply urel_equiv_2; eauto.
        }

        {
        simpsub.
        eapply seqhyp_equivh_2; eauto.
          {
          apply equivh_tm.
          apply equiv_sequal; auto using equiv_refl.
          }

          {
          apply hygieneh_tm.
          apply hygiene_auto; cbn; auto.
          }
        }
      }

      {
      intros j b t Hj Htt.
      simpsubin Htt.
      rewrite -> !qpromote_cons in Htt |- *.
      rewrite -> !qpromote_hyp_tm in Htt |- *.
      invert Htt.
      intros n'' tt1 Htt1 Hn'' <-.
      invertc Htt1.
      intros p'' t Ht Hp'' <-.
      simpsub.
      simpsubin Hn''.
      invert Hn''.
      intros R HR _ _.
      invert (basic_value_inv _#6 value_sequal HR).
      intros Hclp'' Hcltm Hequivp''_tm _.
      clear R HR.
      simpsubin Hp''.
      apply seqctx_cons.
        {
        apply seqctx_cons; auto.
        simpsub.
        invert Hp''.
        intros R Hl Hr H.
        apply (seqhyp_tm _#5 R); auto.
        eapply urel_equiv_1; eauto.
        }

        {
        simpsub.
        eapply seqhyp_equivh_1; eauto.
          {
          apply equivh_tm.
          apply equiv_sequal; auto using equiv_refl.
          }

          {
          apply hygieneh_tm.
          apply hygiene_auto; cbn; auto.
          }
        }
      }
    }
  }
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (subsume_under _ _ G2 _ _ Hsubsume anderr _#3 Hs) as (Hs' & Heqs & Heqs' & _).
rewrite <- compose_assoc in Heqs, Heqs'.
rewrite <- compose_under in Heqs, Heqs'.
so (Hseq _#3 Hs') as (B & Hbl & Hbr & Hnl & Hnr & Hnlr).
exists B.
simpsubin Hbl.
simpsubin Hbr.
rewrite <- compose_assoc in Hbl, Hbr.
rewrite <- compose_under in Hbl, Hbr.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
rewrite <- app_assoc in Hclb.
cbn [List.app] in Hclb.
rewrite -> subst_compose in Hnl.
rewrite -> subst_compose in Hnl.
rewrite -> subst_compose in Hnr.
rewrite -> subst_compose in Hnr.
rewrite -> subst_compose in Hnlr.
rewrite -> subst_compose in Hnlr.
rewrite -> !(subst_eqsub _#4 (eqsub_under_id _ _)) in Hnl.
rewrite -> !(subst_eqsub _#4 (eqsub_under_id _ _)) in Hnr.
rewrite -> !(subst_eqsub _#4 (eqsub_under_id _ _)) in Hnlr.
simpsubin Hnl.
simpsubin Hnr.
simpsubin Hnlr.
do2 4 split; auto.
  {
  eapply basic_equiv; eauto.
    {
    eapply subst_closub; eauto.
    }

    {
    apply equiv_funct; auto using equiv_refl.
    }
  }

  {
  eapply basic_equiv; eauto.
    {
    eapply subst_closub; eauto.
    }

    {
    apply equiv_funct; auto using equiv_refl.
    }
  }
Qed.



Lemma sound_sequal_symm :
  forall G m n,
    pseq G (deq triv triv (sequal m n))
    -> pseq G (deq triv triv (sequal n m)).
Proof.
intros G m n.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hl & Hr & Hinh & _).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_sequal Hl).
intros Hclsm Hclsn Hequiv <-.
invert (basic_value_inv _#6 value_sequal Hr).
intros Hclsm' Hclsn' Hequiv'.
exists (iubase (unit_urel stop i)).
do2 4 split; auto.
  {
  apply interp_eval_refl.
  simpsub.
  apply interp_sequal; auto using equiv_symm.
  }

  {
  apply interp_eval_refl.
  simpsub.
  apply interp_sequal; auto using equiv_symm.
  }
Qed.


Lemma sound_sequal_trans :
  forall G m n p,
    pseq G (deq triv triv (sequal m n))
    -> pseq G (deq triv triv (sequal n p))
    -> pseq G (deq triv triv (sequal m p)).
Proof.
intros G m n p.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hmn Hnp.
rewrite -> seq_deq in Hmn, Hnp |- *.
intros i s s' Hs.
so (Hmn _#3 Hs) as (R & Hl1 & Hr1 & Hinh & _).
so (Hnp _#3 Hs) as (R' & Hl2 & Hr2 & _).
simpsubin Hl1.
simpsubin Hr1.
simpsubin Hl2.
simpsubin Hr2.
invert (basic_value_inv _#6 value_sequal Hl1).
intros Hclsm _ Hequivmn <-.
invert (basic_value_inv _#6 value_sequal Hr1).
intros Hclsm' _ Hequivmn'.
invert (basic_value_inv _#6 value_sequal Hl2).
intros _ Hclsp Hequivnp <-.
invert (basic_value_inv _#6 value_sequal Hr2).
intros _ Hclsp' Hequivnp'.
exists (iubase (unit_urel stop i)).
do2 4 split; auto.
  {
  apply interp_eval_refl.
  simpsub.
  apply interp_sequal; eauto using equiv_trans.
  }

  {
  apply interp_eval_refl.
  simpsub.
  apply interp_sequal; eauto using equiv_trans.
  }
Qed.


Lemma sound_sequal_compat :
  forall G m n p,
    pseq G (deq triv triv (sequal m n))
    -> pseq G (deq triv triv (sequal (subst1 m p) (subst1 n p))).
Proof.
intros G m n p.
revert G.
refine (seq_pseq 1 [hyp_emp] p 1 [] _ _ _); cbn.
intros G Hclp Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq _#3 Hs) as (R & Hl & Hr & _).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_sequal Hl).
intros Hclsm Hclsn Hequiv _.
invert (basic_value_inv _#6 value_sequal Hr).
intros Hclsm' Hclsn' Hequiv' _.
exists (iubase (unit_urel stop i)).
simpsub.
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_sequal.
    {
    eapply hygiene_subst; eauto.
    intros j Hj.
    destruct j as [| j].
      {
      simpsub.
      prove_hygiene.
      }
    cbn in Hj.
    simpsub.
    eapply project_closub; eauto.
    }

    {
    eapply hygiene_subst; eauto.
    intros j Hj.
    destruct j as [| j].
      {
      simpsub.
      prove_hygiene.
      }
    cbn in Hj.
    simpsub.
    eapply project_closub; eauto.
    }

    {
    cut (equiv (subst1 (subst s m) (subst (under 1 s) p)) (subst1 (subst s n) (subst (under 1 s) p))).
      {
      simpsub.
      auto.
      }
    apply equiv_funct1; auto using equiv_refl.
    }
  }

  {
  apply interp_eval_refl.
  apply interp_sequal.
    {
    eapply hygiene_subst; eauto.
    intros j Hj.
    destruct j as [| j].
      {
      simpsub.
      prove_hygiene.
      }
    cbn in Hj.
    simpsub.
    eapply project_closub; eauto.
    }

    {
    eapply hygiene_subst; eauto.
    intros j Hj.
    destruct j as [| j].
      {
      simpsub.
      prove_hygiene.
      }
    cbn in Hj.
    simpsub.
    eapply project_closub; eauto.
    }

    {
    cut (equiv (subst1 (subst s' m) (subst (under 1 s') p)) (subst1 (subst s' n) (subst (under 1 s') p))).
      {
      simpsub.
      auto.
      }
    apply equiv_funct1; auto using equiv_refl.
    }
  }

  {
  do2 5 split; auto using star_refl; prove_hygiene.
  }

  {
  do2 5 split; auto using star_refl; prove_hygiene.
  }

  {
  do2 5 split; auto using star_refl; prove_hygiene.
  }
Qed.


Definition flat a :=
  forall i j s A m p,
    interp toppg true i (subst s a) A
    -> rel (den A) j m p
    -> exists th,
         canon _ th
         /\ star step m (oper [] th rw_nil)
         /\ star step p (oper [] th rw_nil).
    

Theorem sound_flat_sequal :
  forall G a m n,
    flat a
    -> pseq G (deq m n a)
    -> pseq G (deq triv triv (sequal m n)).
Proof.
intros G a m n Hflat.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (Hseq i s s' Hs) as (A & Hal & _ & Hm & Hn & Hmn).
exists (iubase (unit_urel stop i)).
simpsub.
assert (rel (unit_urel stop i) i triv triv) as Htriv.
  {
  do2 5 split; auto using star_refl.
    {
    apply hygiene_auto; cbn; auto.
    }

    {
    apply hygiene_auto; cbn; auto.
    }
  }
assert (forall p q, rel (den A) i p q -> equiv p q) as Hequiv.
  {
  clear m n Hseq Hm Hn Hmn Htriv.
  intros p q Hpq.
  so (Hflat _#6 Hal Hpq) as (th & _ & Hp & Hq).
  apply (equiv_trans _ _ (oper [] th rw_nil)).
    {
    apply steps_equiv; auto.
    }

    {
    apply equiv_symm.
    apply steps_equiv; auto.
    }
  }
so (urel_closed _#5 Hm) as (Hclsm & Hclsm').
so (urel_closed _#5 Hn) as (Hclsn & Hclsn').
do2 4 split; auto.
  {
  apply interp_eval_refl.
  apply interp_sequal; auto.
  apply (equiv_trans _ _ (subst s' n)).
    {
    apply Hequiv; auto.
    }

    {
    apply equiv_symm.
    apply Hequiv; auto.
    }
  }

  {
  apply interp_eval_refl.
  apply interp_sequal; auto.
  apply (equiv_trans _ _ (subst s m)).
    {
    apply equiv_symm.
    apply Hequiv; auto.
    }

    {
    apply Hequiv; auto.
    }
  }
Qed.
