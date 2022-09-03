
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

Require Import Spaces.
Require Import Extend.
Require Import SemanticsPi.
Require Import ProperLevel.
Require Import Urelsp.
Require Import Ceiling.
Require Import Equivalence.
Require Import Equivalences.
Require Import Truncate.
Require Import ProperDownward.
Require Import ProperEquiv.
Require Import ProperLevel.
Require Import SoundUtil.
Require Import SemanticsWtype.
Require Import Defined.
Require Import PageType.
Require Import Model.
Require Import Standardization.
Require Import Subsumption.
Require Import ContextHygiene.
Require Import SemanticsSigma.
Require Import SemanticsSubtype.


Lemma wind_unroll :
  forall object (f m : term object),
    star step
      (app (wind f) m)
      (app (app (app f (ppi1 m)) (ppi2 m)) (lam (app (wind (subst sh1 f)) (app (ppi2 (subst sh1 m)) (var 0))))).
Proof.
intros object f m.
unfold wind at 1.
match goal with
| |- star step (app (app _ ?X) _) _ =>
    set (F := X)
end.
eapply star_trans.
  {
  apply (star_map' _ _ (fun z => app z _)); auto using step_app1.
  eapply star_trans.
    {
    apply theta_fix.
    }
  replace (app theta F) with (wind f) by reflexivity.
  unfold F at 1.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  replace (1 + 1) with 2 by omega.
  replace (1 + 0) with 1 by omega.
  apply star_refl.
  }
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma sound_wt_formation :
  forall G a a' b b',
    pseq G (deqtype a a')
    -> pseq (cons (hyp_tm a) G) (deqtype b b')
    -> pseq G (deqtype (wt a b) (wt a' b')).
Proof.
intros G a b c d.
revert G.
refine (seq_pseq 2 [hyp_emp] c [hyp_emp] d 2 [] _ [_] _ _ _); cbn.
intros G Hclc Hcld Hseqab Hseqcd.
rewrite -> seq_eqtype in Hseqab, Hseqcd |- *.
intros i s s' Hs.
so (seqctx_impl_closub _#4 (pwctx_impl_seqctx _#4 Hs)) as (Hcls & Hcls').
so (Hseqab _#3 Hs) as (A & Hal & Har & Hbl & Hbr).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional_multi toppg i (den A) (subst (under 1 s) c) (subst (under 1 s') c) (subst (under 1 s) d) (subst (under 1 s') d)) as (C & Hcl & Hcr & Hdl & Hdr); eauto using subst_closub_under_permit.
  {
  intros j m p Hmp.
  assert (pwctx j (dot m s) (dot p s') (cons (hyp_tm a) G)) as Hss.
    {
    assert (j <= i) as Hj.
      {
      rewrite -> HeqA in Hmp.
      destruct Hmp.
      omega.
      }
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
      }

      {
      intros j' t t' Ht.
      so (Hseqab _#3 Ht) as (R & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqcd _#3 Hss) as (R & Hcl & Hcr & Hdl & Hdr).
  exists R.
  simpsub.
  auto.
  }
exists (iuwt stop A C).
simpsub.
do2 3 split; auto;
apply interp_eval_refl;
apply interp_wt; auto.
Qed.


Lemma sound_wt_formation_univ :
  forall G lv a a' b b',
    pseq G (deq a a' (univ lv))
    -> pseq (cons (hyp_tm a) G) (deq b b' (univ (subst sh1 lv)))
    -> pseq G (deq (wt a b) (wt a' b') (univ lv)).
Proof.
intros G lv a b c d.
revert G.
refine (seq_pseq 2 [hyp_emp] c [hyp_emp] d 2 [] _ [_] _ _ _); cbn.
intros G Hclc Hcld Hseqab Hseqcd.
rewrite -> seq_univ in Hseqab, Hseqcd |- *.
intros i s s' Hs.
so (seqctx_impl_closub _#4 (pwctx_impl_seqctx _#4 Hs)) as (Hcls & Hcls').
so (Hseqab _#3 Hs) as (pg & A & Hlvl & Hlvr & Hal & Har & Hbl & Hbr).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional_multi pg i (den A) (subst (under 1 s) c) (subst (under 1 s') c) (subst (under 1 s) d) (subst (under 1 s') d)) as (C & Hcl & Hcr & Hdl & Hdr); eauto using subst_closub_under_permit.
  {
  intros j m p Hmp.
  assert (pwctx j (dot m s) (dot p s') (cons (hyp_tm a) G)) as Hss.
    {
    assert (j <= i) as Hj.
      {
      rewrite -> HeqA in Hmp.
      destruct Hmp.
      omega.
      }
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
      }

      {
      intros j' t t' Ht.
      so (Hseqab _#3 Ht) as (pg' & R & _ & _ & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqcd _#3 Hss) as (pg' & R & Hlvl' & _ & Hcl & Hcr & Hdl & Hdr).
  simpsubin Hlvl'.
  so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
  exists R.
  simpsub.
  auto.
  }
exists pg, (iuwt stop A C).
simpsub.
do2 5 split; auto;
apply interp_eval_refl;
apply interp_wt; auto.
Qed.


Lemma hygiene_wind :
  forall object P (f : @term object),
    hygiene P f
    -> hygiene P (wind f).
Proof.
intros object P f Hf.
unfold wind.
apply hygiene_auto; cbn.
do2 2 split; auto.
  {
  eapply hygiene_weaken; eauto using theta_closed, clo_min.
  }
repeat (first [ apply hygiene_shift_permit
              | apply hygiene_auto; cbn; repeat2 split; auto
              ]);
eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1;
try (apply hygiene_var; cbn; auto; done).
Qed.


Local Ltac prove_hygiene :=
  repeat (first [ apply hygiene_shift_permit
                | apply hygiene_wind
                | eapply subst_closub; eauto
                | apply hygiene_auto; cbn; repeat2 split; auto
                ]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1;
  try (apply hygiene_var; cbn; auto; done).


(* now redundant *)
Lemma sound_wt_intro :
  forall G m n p q a b,
    pseq G (deq m n a)
    -> pseq G (deq p q (arrow (subst1 m b) (wt a b)))
    -> pseq (cons (hyp_tm a) G) (deqtype b b)
    -> pseq G (deq (ppair m p) (ppair n q) (wt a b)).
Proof.
intros G m n p q a b.
revert G.
refine (seq_pseq 5 [hyp_emp] b [] m [] n [] p [] q 3 [] _ [] _ [_] _ _ _); cbn.
intros G Hclb Hclm Hcln Hclp Hclq Hseqmn Hseqpq Hseqb.
rewrite -> seq_eqtype in Hseqb.
rewrite -> seq_deq in Hseqmn, Hseqpq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmn _#3 Hs) as (A & Hal & Har & Hm & Hn & Hmn).
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as H; eauto using subst_closub_under_permit.
  {
  exact (f_equal den (basic_impl_iutruncate _#6 Hal)).
  }

  {
  intros j r t Hrt.
  so (basic_member_index _#9 Hal Hrt) as Hj.
  assert (pwctx j (dot r s) (dot t s') (cons (hyp_tm a) G)) as Hs'.
    {
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      apply (seqhyp_tm _#5 (iutruncate (S j) A)).
        {
        eapply basic_downward; eauto.
        }

        {
        eapply basic_downward; eauto.
        }
      split; auto.
      }

      {
      intros j' u u' Hu.
      so (Hseqmn _#3 Hu) as (R & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hs') as (B & Hbl & Hbr & _).
  simpsub.
  eauto.
  }
destruct H as (B & Hbl & Hbr).
so (Hseqpq _#3 Hs) as (R & Habl & Habr & Hp & Hq & Hpq); clear Hseqpq.
simpsubin Habl.
simpsubin Habr.
invert (basic_value_inv _#6 value_arrow Habl).
intros Bm C Hbml Hcl Heq1.
invert (basic_value_inv _#6 value_arrow Habr).
intros Bm' C' _ Hcr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iuarrow_inj _#7 Heq) as (<- & _).
clear Heq.
eassert _; [refine (basic_fun _#6 (iuwt stop A B) Hcl _) |].
  {
  apply interp_eval_refl.
  apply interp_wt; auto.
  }
subst C.
eassert _; [refine (basic_fun _#6 (iuwt stop A B) Hcr _) |].
  {
  apply interp_eval_refl.
  apply interp_wt; auto.
  }
subst C'.
eassert _; [refine (basic_fun _#6 (pi1 B (urelspinj (den A) _#3 Hm)) Hbml _) |].
  {
  invert Hbl.
  intros _ _ Hact.
  so (Hact _#3 (le_refl _) Hm) as H.
  simpsubin H.
  exact H.
  }
subst Bm.
clear Hseqmn Hseqb Hbml Habl Habr.
exists (iuwt stop A B).
simpsub.
do2 4 split; auto.
  {
  do2 2 split; try prove_hygiene.
  cbn in Hp.
  decompose Hp.
  intros l l' _ _ _ Hsteps Hsteps' Hact.
  apply (wt_action_ind_i _#6 (subst s m) (subst s' m) (subst s p) (subst s' p) l l' Hm); auto using star_refl.
  intros j r t Hj Hrt.
  so (urel_closed _#5 Hrt) as (Hclr & Hclt).
  so (Hact _#3 Hj Hrt) as H.
  destruct H as (_ & _ & H).
  eapply wt_action_ind_equiv; eauto; try prove_hygiene.
    {
    apply equiv_symm.
    eapply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun z => app z _)); auto using step_app1.
      exact Hsteps.
      }
    apply star_one; apply step_app2.
    }

    {
    apply equiv_symm.
    eapply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun z => app z _)); auto using step_app1.
      exact Hsteps'.
      }
    apply star_one; apply step_app2.
    }
  }

  {
  do2 2 split; try prove_hygiene.
  cbn in Hq.
  decompose Hq.
  intros l l' _ _ _ Hsteps Hsteps' Hact.
  apply (wt_action_ind_i _#6 (subst s n) (subst s' n) (subst s q) (subst s' q) l l' Hn); auto using star_refl.
  intros j r t Hj Hrt.
  so (urel_closed _#5 Hrt) as (Hclr & Hclt).
  exploit (Hact j r t) as H; auto.
    {
    force_exact Hrt.
    cbn.
    do 3 f_equal.
    apply urelspinj_equal.
    eapply urel_zigzag; eauto.
    }
  destruct H as (_ & _ & H).
  eapply wt_action_ind_equiv; eauto; try prove_hygiene.
    {
    apply equiv_symm.
    eapply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun z => app z _)); auto using step_app1.
      exact Hsteps.
      }
    apply star_one; apply step_app2.
    }

    {
    apply equiv_symm.
    eapply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun z => app z _)); auto using step_app1.
      exact Hsteps'.
      }
    apply star_one; apply step_app2.
    }
  }

  {
  do2 2 split; try prove_hygiene.
  cbn in Hpq.
  decompose Hpq.
  intros l l' _ _ _ Hsteps Hsteps' Hact.
  apply (wt_action_ind_i _#6 (subst s m) (subst s' n) (subst s p) (subst s' q) l l' Hmn); auto using star_refl.
  intros j r t Hj Hrt.
  so (urel_closed _#5 Hrt) as (Hclr & Hclt).
  exploit (Hact j r t) as H; auto.
    {
    force_exact Hrt.
    cbn.
    do 3 f_equal.
    apply urelspinj_equal.
    eapply urel_zigzag; eauto.
    }
  destruct H as (_ & _ & H).
  eapply wt_action_ind_equiv; eauto; try prove_hygiene.
    {
    apply equiv_symm.
    eapply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun z => app z _)); auto using step_app1.
      exact Hsteps.
      }
    apply star_one; apply step_app2.
    }

    {
    apply equiv_symm.
    eapply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun z => app z _)); auto using step_app1.
      exact Hsteps'.
      }
    apply star_one; apply step_app2.
    }
  }
Qed.


(* Usually it's nicer to keep the parameters unchanged through the induction,
   but in sound_wt_elim it's not.  So we define this version and show it's
   equivalent.
*)

Inductive wt_action_ind'
  : forall (A : siurel), (urelsp (den A) -n> siurel_ofe) -> nat -> sterm -> sterm -> Prop
  :=
| wt_action_ind_i' :
    forall A B i m m' n n' p p' l l' (Hn : rel (den A) i n n'),
      star step m (ppair n p)
      -> star step m' (ppair n' p')
      -> star step p (lam l)
      -> star step p' (lam l')
      -> (forall j q q' (Hj : j <= i),
            rel (den (pi1 (fntruncate (S j) (den A) B) (urelspinj (ceiling (S j) (den A)) j n n' (conj (Nat.lt_succ_diag_r j) (urel_downward_leq _#6 Hj Hn))))) j q q'
            -> wt_action_ind' 
                 (iutruncate (S j) A) (fntruncate (S j) (den A) B)
                 j (app p q) (app p' q'))
      -> wt_action_ind' A B i m m'
.


Lemma coerce_ind_obligation :
  forall (A : siurel) (B : urelsp (den A) -n> siurel_ofe) i m n p q j v w 
    (Hj : j <= i) (Hmn : rel (den A) i m n) (Hpq : rel (den A) i p q) (Hjs : j < S j),
      rel (den A) i p n
      -> rel (den (pi1 B (urelspinj (den A) i m n Hmn))) j v w
      -> rel (den (pi1 (fntruncate (S j) (den A) B) (urelspinj (ceiling (S j) (den A)) j p q (conj Hjs (urel_downward_leq _#6 Hj Hpq))))) j v w.
Proof.
intros A B i m n p q j v w Hj Hmn Hpq Hjs Hpn Hvw.
cbn.
split; [omega |].
rewrite -> embed_ceiling_urelspinj.
cut (dist (S j) (pi1 B (urelspinj (den A) i m n Hmn)) (pi1 B (urelspinj (den A) j p q (urel_downward_leq _#6 Hj Hpq)))).
  {
  intro Hdist.
  so (f_equal (fun z => z v w) (Hdist andel j (Nat.lt_succ_diag_r j))) as H.
  cbn in H.
  exact (transport H (fun z => z) Hvw).
  }
apply (pi2 B).
apply urelspinj_dist_diff; auto.
apply (urel_zigzag _#3 m n p q); eapply urel_downward_leq; eauto.
Qed.


Lemma ceiling_wt_action_ind' :
  forall n A B j m p,
    j < n
    -> wt_action_ind' A B j m p
       <->
       wt_action_ind' (iutruncate n A) (nearrow_compose2 (embed_ceiling_ne n (den A)) (iutruncate_ne n) B) j m p.
Proof.
assert (forall n A B j',
          S j' <= n
          -> eq_dep siurel (fun A' => urelsp (den A') -n> siurel_ofe)
               (iutruncate n (iutruncate (S j') A))
               (nearrow_compose2 (embed_ceiling_ne n (ceiling (S j') (fst A))) (iutruncate_ne n)
                  (nearrow_compose (nearrow_compose (iutruncate_ne (S j')) B)
                     (embed_ceiling_ne (S j') (den A)))) (iutruncate (S j') (iutruncate n A))
               (nearrow_compose
                  (nearrow_compose (iutruncate_ne (S j'))
                     (nearrow_compose2 (embed_ceiling_ne n (den A)) (iutruncate_ne n) B))
                  (embed_ceiling_ne (S j') (ceiling n (fst A))))) as Hcomm.
  {
  intros n A B j' Hj''.
  apply (eq_dep_trans _#3 (iutruncate (S j') A) _ _ (nearrow_compose2 (embed_ceiling_ne (S j') (fst A)) (iutruncate_ne (S j')) B)).
    {
    apply (eq_impl_eq_dep _#6 (iutruncate_combine_ge _#4 Hj'')).
    apply nearrow_extensionality.
    intros x.
    cbn.
    rewrite -> (pi1_transport_dep_lift _ _ (fun A' B' => @nonexpansive (urelsp (den A')) siurel_ofe B') _ _ (iutruncate_combine_ge _#3 A Hj'')).
    cbn.
    rewrite -> app_transport_dom.
    rewrite -> (iutruncate_combine_ge _ n (S j')); auto.
    f_equal.
    f_equal.
    rewrite -> (embed_ceiling_combine_ge _#5 Hj'').
    f_equal.
    rewrite <- (transport_compat _ _ den urelsp_car _#3 (eqsymm (iutruncate_combine_ge _#3 A Hj''))).
    rewrite -> transport_compose.
    rewrite -> transport_self.
    reflexivity.
    }

    {
    apply eq_dep_sym.
    apply (eq_impl_eq_dep _#6 (iutruncate_combine_le _#4 Hj'')).
    apply nearrow_extensionality.
    intros x.
    cbn.
    rewrite -> (pi1_transport_dep_lift _ _ (fun A' B' => @nonexpansive (urelsp (den A')) siurel_ofe B') _ _ (iutruncate_combine_le _#3 A Hj'')).
    cbn.
    rewrite -> app_transport_dom.
    rewrite -> (iutruncate_combine_le _ (S j') n); auto.
    f_equal.
    f_equal.
    rewrite -> (embed_ceiling_combine_le _#5 Hj'').
    f_equal.
    rewrite <- (transport_compat _ _ den urelsp_car _#3 (eqsymm (iutruncate_combine_le _#3 A Hj''))).
    rewrite -> transport_compose.
    rewrite -> transport_self.
    reflexivity.
    }
  }
intros n A B j m p Hjn.
split.
  {
  intros Hact.
  revert Hjn.
  induct Hact.
  intros A B j m p m1 p1 m2 p2 m3 p3 Hmp Hstepsm Hstepsp Hm3 Hp3 _ IH Hjn.
  eapply (wt_action_ind_i' (iutruncate n A) _#8 m3 p3 (conj Hjn Hmp)); eauto.
  intros j' q r Hj' Hqr.
  cbn in Hqr.
  destruct Hqr as (_ & _ & Hqr).
  rewrite -> embed_ceiling_urelspinj in Hqr.
  assert (j' < n) as Hjn' by omega.
  match type of Hqr with
  | rel (fst (pi1 _ (embed_ceiling _ _ (urelspinj _ _ _ _ ?X)))) _ _ _ => 
    replace X with (conj Hjn' (urel_downward_leq _#6 Hj' Hmp)) in Hqr by (apply proof_irrelevance)
  end.
  rewrite -> embed_ceiling_urelspinj in Hqr.
  exploit (IH j' q r Hj') as H; auto.
    {
    eapply (coerce_ind_obligation _#11 Hmp); auto.
    eapply rel_from_dist; eauto.
    apply (pi2 B).
    apply urelspinj_dist; auto.
    }
  unfold fntruncate in H |- *.
  cbn in H |- *.
  eassert _ as Heq.
  2:{
    exact (transport (f_equal_dep _#7 (fun A' B' => wt_action_ind' A' B' j' (app m2 q) (app p2 r)) Heq) (fun z => z) H).
    }
  clear H.
  apply Hcomm; auto.
  }

  {
  intros Hact.
  revert Hact.
  cut (forall A' B',
         eq_dep _ (fun z => urelsp (den z) -n> siurel_ofe) A' B' (iutruncate n A) (nearrow_compose2 (embed_ceiling_ne n (den A)) (iutruncate_ne n) B)
         -> wt_action_ind' A' B' j m p
         -> wt_action_ind' A B j m p).
    {
    intros Hind Hact.
    eapply Hind; eauto.
    apply eq_dep_refl.
    }
  intros A' B' Heq H.
  revert A B Hjn Heq.
  induct H.
  intros A' B' i m p m1 p1 m2 p2 m3 p3 Hmp Hstepsm Hstepsp Hm3 Hp3 _ IH A B Hin Heq.
  injectionT Heq.
  intros ->.
  injectionT Heq.
  intros ->.
  so Hmp as (_ & Hmp').
  eapply (wt_action_ind_i' _#11 Hmp'); eauto.
  intros j q r Hj Hqr.
  eapply (IH _#3 Hj); eauto; try omega.
    {
    cbn in Hqr |- *.
    destruct Hqr as (_ & Hqr).
    do2 2 split; try omega.
    rewrite -> embed_ceiling_urelspinj in Hqr.
    rewrite -> embed_ceiling_urelspinj.
    destruct Hmp as (H & Hmp).
    so (proof_irrelevance _ Hin H); subst H.
    assert (j < n) as Hjn by omega.
    rewrite <- (embed_ceiling_urelspinj _ n (den A) _#4 Hjn) in Hqr.
    force_exact Hqr.
    f_equal; f_equal; f_equal; f_equal; f_equal.
    apply proof_irrelevance.
    }

    {
    apply eq_dep_sym.
    apply Hcomm.
    omega.
    }
  }
Qed.


Lemma wt_action_ind_iff :
  forall A B i m n,
    wt_action_ind stop (den A) (fun x => den (pi1 B x)) i m n <-> wt_action_ind' A B i m n.
Proof.
intros A B i m n.
split.

{
intro Hmn.
induct Hmn.
intros i m n m1 n1 m2 n2 m3 n3 Hn Hstepsm Hstepsn Hstepsm2 Hstepsn2 _ IH.
eapply (wt_action_ind_i' _#11 Hn); eauto.
intros j q r Hj Hqr.
cbn in Hqr.
destruct Hqr as (_ & Hqr).
rewrite -> embed_ceiling_urelspinj in Hqr.
exploit (IH j q r) as H; auto.
  {
  eapply rel_from_dist; eauto.
  apply (pi2 B).
  apply urelspinj_dist_diff; auto.
  eapply urel_downward_leq; eauto.
  }
rewrite -> (ceiling_wt_action_ind' (S j)) in H; auto.
force_exact H; clear H.
f_equal.
apply nearrow_extensionality.
intro x.
cbn.
reflexivity.
}

{
intro Hmn.
induct Hmn.
intros A B i m n m1 n1 m2 n2 m3 n3 Hn Hstepsm Hstepsn Hstepsm2 Hstepsn2 _ IH.
eapply (wt_action_ind_i _#12 Hn); eauto.
intros j q r Hj Hqr.
exploit (IH j q r Hj) as H; auto.
  {
  eapply coerce_ind_obligation; eauto.
  }
rewrite -> (ceiling_wt_action_ind _ (S j) _ (nearrow_compose den_ne B)); auto.
}
Qed.


Lemma sound_wt_elim :
  forall G a b c m m' n n',
    pseq G (deq m m' (wt a b))
    -> pseq
         (cons 
            (hyp_tm (pi (subst sh1 b) (subst (dot (app (var 1) (var 0)) (sh 3)) c)))
            (cons (hyp_tm (arrow b (subst sh1 (wt a b)))) (cons (hyp_tm a) G)))
         (deq n n' (subst (dot (ppair (var 2) (var 1)) (sh 3)) c))
    -> pseq G (deq (app (wind (lam (lam (lam n)))) m) (app (wind (lam (lam (lam n')))) m') (subst1 m c)).
Proof.
intros G a b c m n p q.
revert G.
(* why necessary? *)
set (X := hyp_tm (arrow b (subst sh1 (wt a b)))).
refine (seq_pseq 5 [hyp_emp] c [] m [] n [hyp_emp; hyp_emp; hyp_emp] p [hyp_emp; hyp_emp; hyp_emp] q 2 [] _ [_; _; _] _ _ _); cbn.
subst X.
intros G Hclc Hclm Hcln Hclp Hclq Hseqmn Hseqpq.
rewrite -> seq_deq in Hseqmn, Hseqpq |- *.
assert (forall i s s',
          pwctx i s s' G
          -> exists A B,
               interp toppg true i (subst s a) A
               /\ interp toppg false i (subst s' a) A
               /\ functional the_system toppg true i (den A) (subst (under 1 s) b) B
               /\ functional the_system toppg false i (den A) (subst (under 1 s') b) B
               /\ rel (den (iuwt stop A B)) i (subst s m) (subst s' m)
               /\ rel (den (iuwt stop A B)) i (subst s n) (subst s' n)
               /\ rel (den (iuwt stop A B)) i (subst s m) (subst s' n)) as H.
  {
  intros i s s' Hs.
  so (Hseqmn _#3 Hs) as (R & Habl & Habr & Hm & Hn & Hmn); clear Hseqmn.
  simpsubin Habl.
  simpsubin Habr.
  invert (basic_value_inv _#6 value_wt Habl); clear Habl.
  intros A B Hal Hbl Heq1.
  invert (basic_value_inv _#6 value_wt Habr); clear Habr.
  intros A' B' Har Hbr Heq2.
  so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
  clear Heq2.
  subst R.
  so (iuwt_inj _#5 Heq) as H; clear Heq.
  injectionT H.
  intros <-.
  injectionT H.
  intros <-.
  exists A, B.
  do2 6 split; auto.
  }
clear Hseqmn.
assert (forall i s s',
          pwctx i s s' G
          -> exists A B,
               interp toppg true i (subst s a) A
               /\ interp toppg false i (subst s' a) A
               /\ functional the_system toppg true i (den A) (subst (under 1 s) b) B
               /\ functional the_system toppg false i (den A) (subst (under 1 s') b) B) as Hseqab.
  {
  intros i s s' Hs.
  so (H _#3 Hs) as (A & B & Hal & Har & Hbl & Hbr & _).
  exists A, B.
  auto.
  }
intros i s s' Hs.
so (H _#3 Hs) as (A & B & Hal & Har & Hbl & Hbr & Hm & Hn & Hmn); clear H.
destruct Hm as (_ & _ & Hactm).
destruct Hn as (_ & _ & Hactn).
destruct Hmn as (_ & _ & Hactmn).
set (lamp := lam (lam (lam p))).
set (lamq := lam (lam (lam q))).
cbn in Hactm, Hactn, Hactmn.
rewrite -> wt_action_ind_iff in Hactm, Hactn, Hactmn.
revert i s s' A B m n Hs Hal Har Hbl Hbr Hclm Hcln Hactm Hactn Hactmn.
cut (forall i s s' A B d e m n,
       pwctx i s s' G
       -> interp toppg true i (subst s a) A
       -> interp toppg false i (subst s' a) A
       -> functional the_system toppg true i (den A) (subst (under 1 s) b) B
       -> functional the_system toppg false i (den A) (subst (under 1 s') b) B
       -> hygiene clo m
       -> hygiene clo n
       -> wt_action_ind' A B i d e
       -> wt_action_ind' A B i m n
       -> wt_action_ind' A B i d n
       -> exists R,
            interp toppg true i (subst (dot m s) c) R
            /\ interp toppg false i (subst (dot n s') c) R
            /\ rel (den R) i (subst s (app (wind lamp) m)) (subst s' (app (wind lamp) n))
            /\ rel (den R) i (subst s (app (wind lamq) m)) (subst s' (app (wind lamq) n))
            /\ rel (den R) i (subst s (app (wind lamp) m)) (subst s' (app (wind lamq) n))).
  {
  intros Hind.
  intros i s s' A B m n Hs Hal Har Hbl Hbr Hclm Hcln Hactm Hactn Hactmn.
  so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
  assert (hygiene clo (subst s m)) as Hclsm.
    {
    eapply subst_closub; eauto.
    }
  assert (hygiene clo (subst s' m)) as Hclsm'.
    {
    eapply subst_closub; eauto.
    }
  assert (hygiene clo (subst s n)) as Hclsn.
    {
    eapply subst_closub; eauto.
    }
  assert (hygiene clo (subst s' n)) as Hclsn'.
    {
    eapply subst_closub; eauto.
    }
  clear Hclm Hcln.
  exploit (Hind i s s' A B (subst s m) (subst s' m) (subst s m) (subst s' m) Hs) as H; auto.
  destruct H as (C & Hcl & Hcr & Hm & _).
  exploit (Hind i s s' A B (subst s m) (subst s' m) (subst s n) (subst s' n) Hs) as H; auto.
  destruct H as (C' & _ & Hcr' & _ & Hn & _).
  exploit (Hind i s s' A B (subst s m) (subst s' m) (subst s m) (subst s' n) Hs) as H; auto.
  destruct H as (C'' & Hcl'' & Hcr'' & _ & _ & Hmn).
  clear Hind.
  so (basic_fun _#7 Hcl Hcl''); subst C''.
  so (basic_fun _#7 Hcr' Hcr''); subst C'.
  clear Hcr' Hcl'' Hcr''.
  exists C.
  simpsub.
  do2 4 split; auto.
    {
    rewrite -> !subst_app in Hm.
    rewrite -> (subst_into_closed _#3 Hclsm) in Hm.
    rewrite -> (subst_into_closed _#3 Hclsm') in Hm.
    simpsubin Hm.
    exact Hm.
    }

    {
    rewrite -> !subst_app in Hn.
    rewrite -> (subst_into_closed _#3 Hclsn) in Hn.
    rewrite -> (subst_into_closed _#3 Hclsn') in Hn.
    simpsubin Hn.
    exact Hn.
    }

    {
    rewrite -> !subst_app in Hmn.
    rewrite -> (subst_into_closed _#3 Hclsm) in Hmn.
    rewrite -> (subst_into_closed _#3 Hclsn') in Hmn.
    simpsubin Hmn.
    exact Hmn.
    }
  }
intros i s s' A B d e m n Hs Hal Har Hbl Hbr Hclm Hcln Hde Hmn Hdn.
revert s s' m n Hs Hal Har Hbl Hbr Hclm Hcln Hmn Hdn.
induct Hde.
intros A B i d e d1 e1 d2 e2 d3 e3 Hd1e1 Hstepsd Hstepse Hstepsd2 Hstepse2 _ IH s s' m n Hs Hal Har Hbl Hbr Hclm Hcln Hmn Hdn.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
invertc Hdn.
intros d1' n1 d2' n2 _ n3 Hd1n1 Hstepsd' Hstepsn _ Hstepsn2 Hactdn.
so (determinism_eval _#4 (conj Hstepsd value_ppair) (conj Hstepsd' value_ppair)) as Heq.
injectionc Heq.
intros <- <-.
invertc Hmn.
intros m1 n1' m2 n2' m3 _ Hm1n1 Hstepsm Hstepsn' Hstepsm2 _ Hactmn.
so (determinism_eval _#4 (conj Hstepsn value_ppair) (conj Hstepsn' value_ppair)) as Heq.
injectionc Heq.
intros <- <-.
clear Hstepsd' Hstepsn'.
assert (forall j (r t : sterm) u u',
          j <= i
          -> seqctx j u u' G
          -> seqctx j s u' G
          -> hygiene clo r
          -> hygiene clo t
          -> (forall j' v w,
                j' <= j
                -> rel (den (pi1 B (urelspinj (den A) i m1 n1 Hm1n1))) j' v w
                -> wt_action_ind' (iutruncate (S j') A) (fntruncate (S j') (den A) B) j' (app r v) (app t w))
          -> (forall j' v w,
                j' <= j
                -> rel (den (pi1 B (urelspinj (den A) i m1 n1 Hm1n1))) j' v w
                -> wt_action_ind' (iutruncate (S j') A) (fntruncate (S j') (den A) B) j' (app d2 v) (app t w))
          -> exists (C : urelsp (ceiling (S j) (den (pi1 B (urelspinj (den A) _#3 Hm1n1)))) -n> siurel_ofe),
               functional the_system toppg true j (ceiling (S j) (den (pi1 B (urelspinj (den A) _#3 Hm1n1))))
                 (subst (dot (app (subst sh1 r) (var 0)) (compose u sh1)) c) C
               /\ functional the_system toppg false j (ceiling (S j) (den (pi1 B (urelspinj (den A) _#3 Hm1n1))))
                    (subst (dot (app (subst sh1 t) (var 0)) (compose u' sh1)) c) C) as Hseqc.
  {
  intros j r t u u' Hj Hu_pre Hsu_pre Hclr Hclt Hrt Hd2t.
  so (seqctx_impl_closub _#4 Hu_pre) as (Hclu & Hclu').
  exploit (extract_functional toppg j (den (iutruncate (S j) (pi1 B (urelspinj _#4 Hm1n1))))
             (subst (dot (app (subst sh1 r) (var 0)) (compose u sh1)) c)
             (subst (dot (app (subst sh1 t) (var 0)) (compose u' sh1)) c)) as H.
    {
    cbn.
    rewrite -> ceiling_idem.
    reflexivity.
    }

    {
    eapply hygiene_subst; eauto.
    intros x Hx.
    destruct x as [| x]; simpsub; prove_hygiene.
    }

    {
    eapply hygiene_subst; eauto.
    intros x Hx.
    destruct x as [| x]; simpsub; prove_hygiene.
    }

    {
    intros j' v w Hvw.
    so (urel_closed _#5 Hvw) as (Hclv & Hclw).
    simpsub.
    destruct Hvw as (H & Hvw).
    assert (j' <= j) as Hj' by omega; clear H.
    assert (j' <= i) as Hj'_i by omega.
    assert (pwctx j s u' G) as Hsu.
      {
      apply (seqctx_pwctx_left _ _ s'); auto.
      eapply pwctx_downward; eauto.
      }
    assert (pwctx j u u' G) as Hu.
      {
      apply (seqctx_pwctx_right _ s); auto.
      }
    clear Hu_pre Hsu_pre.
    so (Hseqab _#3 Hsu) as (A' & B' & Hal' & Haur' & Hbl' & Hbur').
    so (Hseqab _#3 Hu) as (A'' & B'' & Haul & Haur & Hbul & Hbur).
    so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst A'.
    so (basic_fun _#7 Haur Haur'); subst A''.
    so (functional_fun _#8 (functional_downward _#8 Hj Hbl) Hbl'); subst B'.
    so (functional_fun _#8 Hbur Hbur'); subst B''.
    clear Hal' Hbl' Haur' Hbur'.
    assert (eq_dep _ (fun z => urelsp z -n> _) (den (iutruncate (S j') A)) (fntruncate (S j') (den A) B) (ceiling (S j') (den (iutruncate (S j) A))) (fntruncate (S j') (den (iutruncate (S j) A)) (fntruncate (S j) (den A) B))) as Heq.
      {
      cbn.
      apply eq_dep_sym.
      assert (S j' <= S j) as Hj's by omega.
      apply (eq_impl_eq_dep _#6 (ceiling_combine_le _#4 Hj's)).
      unfold fntruncate.
      apply nearrow_extensionality.
      intros x.
      cbn.
      rewrite -> (pi1_transport_dep_lift _ _ (fun A' B' => @nonexpansive (urelsp A') siurel_ofe B') _ _ (ceiling_combine_le _#3 (den A) Hj's)).
      cbn.
      rewrite -> app_transport_dom.
      rewrite -> iutruncate_combine_le; auto.
      f_equal.
      f_equal.
      rewrite -> (embed_ceiling_combine_le _#5 Hj's).
      rewrite -> transport_compose.
      rewrite -> transport_self.
      reflexivity.
      }
    exploit (IH j' v w (le_trans _#3 Hj' Hj)) as H; clear IH.
      {
      eapply coerce_ind_obligation; eauto.
      }
    exploit (H u u' (app r v) (app t w)) as H'; clear H; eauto using pwctx_downward; try prove_hygiene.
      {
      rewrite <- (iutruncate_combine_le _ (S j') (S j)); [| omega].
      apply (basic_downward _#3 j); auto.
      }

      {
      rewrite <- (iutruncate_combine_le _ (S j') (S j)); [| omega].
      apply (basic_downward _#3 j); auto.
      }

      {
      so (f_equal_dep _#7 (fun A' B' => functional the_system toppg true j' A' (subst (under 1 u) b) B') Heq) as Heq'.
      cbn beta in Heq'.
      rewrite -> Heq'.
      apply (functional_downward _#3 j); auto.
      }

      {
      so (f_equal_dep _#7 (fun A' B' => functional the_system toppg false j' A' (subst (under 1 u') b) B') Heq) as Heq'.
      cbn beta in Heq'.
      rewrite -> Heq'.
      apply (functional_downward _#3 j); auto.
      }
    destruct H' as (R & Hl & Hr & _).
    eauto.
    }
  exact H.
  }
assert (forall (r t : sterm),
          hygiene clo r
          -> hygiene clo t
          -> (forall j v w (Hj : j <= i),
                rel (den (pi1 B (urelspinj (den A) i m1 n1 Hm1n1))) j v w
                -> wt_action_ind' (iutruncate (S j) A) (fntruncate (S j) (den A) B) j (app r v) (app t w))
          -> (forall j v w (Hj : j <= i),
                rel (den (pi1 B (urelspinj (den A) i m1 n1 Hm1n1))) j v w
                -> wt_action_ind' (iutruncate (S j) A) (fntruncate (S j) (den A) B) j (app d2 v) (app t w))
          -> exists (C : urelsp (den (pi1 B (urelspinj (den A) _#3 Hm1n1))) -n> siurel_ofe),
               functional the_system toppg true i (den (pi1 B (urelspinj (den A) _#3 Hm1n1)))
                 (subst (dot (app (subst sh1 r) (var 0)) (compose s sh1)) c) C
               /\ functional the_system toppg false i (den (pi1 B (urelspinj (den A) _#3 Hm1n1)))
                    (subst (dot (app (subst sh1 t) (var 0)) (compose s' sh1)) c) C) as Hseqci.
  {
  intros r t Hclr Hclt Hrt Hd2t.
  so (Hseqc i r t s s' (le_refl _) (pwctx_impl_seqctx _#4 Hs) (pwctx_impl_seqctx _#4 Hs) Hclr Hclt Hrt Hd2t) as (C & Hl & Hr).  
  invert Hbl.
  intros _ _ H.
  so (f_equal den (basic_impl_iutruncate _#6 (H _#3 (le_refl _) Hm1n1))) as Heq; clear H.
  rewrite -> den_iutruncate in Heq.
  symmetry in Heq.
  exists (transport Heq (fun z => urelsp z -n> siurel_ofe) C).
  so (eq_impl_eq_dep _ (fun z => urelsp z -n> siurel_ofe) _ _ C _ Heq (eq_refl _)) as Heq'.
  split.
    {
    so (f_equal_dep _#7 (fun A' B' => functional the_system toppg true i A' (subst (dot (app (subst sh1 r) (var 0)) (compose s sh1)) c) B') Heq') as H.
    cbn beta in H.
    exact (transport H (fun z => z) Hl).
    }

    {
    so (f_equal_dep _#7 (fun A' B' => functional the_system toppg false i A' (subst (dot (app (subst sh1 t) (var 0)) (compose s' sh1)) c) B') Heq') as H.
    cbn beta in H.
    exact (transport H (fun z => z) Hr).
    }
  }
assert (forall pp qq,
          (pp = lamp \/ pp = lamq)
          -> (qq = lamp \/ qq = lamq)
          -> pwctx i
             (dot
                (lam (app (subst (compose s sh1) (wind pp)) (app (subst sh1 m2) (var 0)))) 
                (dot m2 (dot m1 s)))
             (dot
                (lam (app (subst (compose s' sh1) (wind qq)) (app (subst sh1 n2) (var 0)))) 
                (dot n2 (dot n1 s')))
             (cons 
                (hyp_tm (pi (subst sh1 b) (subst (dot (app (var 1) (var 0)) (sh 3)) c)))
                (cons (hyp_tm (arrow b (subst sh1 (wt a b))))
                   (cons (hyp_tm a) G)))) as Hs'.
  {
  intros pp qq Hpp Hqq.
  so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsm Hclm)) as H; cbn in H.
  destruct H as (_ & Hclm2 & _).
  so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsn Hcln)) as H; cbn in H.
  destruct H as (_ & Hcln2 & _).
  assert (hygiene (ctxpred G) pp) as Hclpp.
    {
    destruct Hpp; subst; prove_hygiene.
    }
  assert (hygiene (ctxpred G) qq) as Hclqq.
    {
    destruct Hqq; subst; prove_hygiene.
    }
  clear Hclp Hclq.
  apply pwctx_cons_tm.
    {
    apply pwctx_cons_tm_seq.
      {
      apply pwctx_cons_tm_seq.
        {
        eapply pwctx_downward; eauto.
        }
        
        {
        apply (seqhyp_tm _#5 (iutruncate (S i) A)).
          {
          eapply basic_downward; eauto.
          }

          {
          eapply basic_downward; eauto.
          }

          {
          split; auto.
          }
        }

        {
        intros k t t' Ht.
        so (Hseqab _#3 Ht) as (R & _ & Hl & Hr & _).
        eauto.
        }
      }

      {
      clear IH.
      simpsub.
      apply (seqhyp_tm _#5 (iuarrow stop i (pi1 B (urelspinj (den A) _#3 Hm1n1)) (iutruncate (S i) (iuwt stop A B)))).
        {
        apply interp_eval_refl.
        apply interp_arrow.
          {
          invert Hbl.
          intros _ _ Hact.
          so (Hact _#3 (le_refl _) Hm1n1) as H.
          simpsubin H.
          exact H.
          }

          {
          apply (basic_downward _#3 i); auto.
          apply interp_eval_refl.
          apply interp_wt; auto.
          }
        }

        {
        apply interp_eval_refl.
        apply interp_arrow.
          {
          invert Hbr.
          intros _ _ Hact.
          so (Hact _#3 (le_refl _) Hm1n1) as H.
          simpsubin H.
          exact H.
          }

          {
          apply (basic_downward _#3 i); auto.
          apply interp_eval_refl.
          apply interp_wt; auto.
          }
        }

        {
        cbn.
        eapply arrow_action_lam'; eauto.
        intros j r t Hj Hrt.
        so (urel_closed _#5 Hrt) as (Hclr & Hclt).
        do2 3 split; try prove_hygiene; try omega.
        exploit (Hactmn j r t Hj) as H.
          {
          eapply coerce_ind_obligation; eauto.
          }
        rewrite <- wt_action_ind_iff in H.
        cbn.
        change (wt_action_ind stop (den A) (pi1 (nearrow_compose den_ne B)) j (app m2 r) (app n2 t)).
        rewrite -> (ceiling_wt_action_ind _ (S j)); auto.
        }
      }
      
      {
      intros j tt tt' Htt.
      invertc Htt.
      intros r u t t' Ht Hru _ _ <- <-.
      so (Hseqab _#3 Ht) as (At & Bt & Hatl & Hatr & Hbtl & Hbtr).
      clear Hseqab.
      simpsubin Hru.
      invertc Hru.
      intros At' Hatl' _ Hru.
      so (basic_fun _#7 Hatl Hatl'); subst At'.
      exists toppg, (iuarrow stop j (pi1 Bt (urelspinj (den At) _#3 Hru)) (iuwt stop At Bt)).
      simpsub.
      split.
        {
        apply interp_eval_refl.
        apply interp_arrow.
          {
          invert Hbtl.
          intros _ _ H.
          so (H _#3 (le_refl _) Hru) as H'; clear H.
          simpsubin H'.
          exact H'.
          }

          {
          apply interp_eval_refl.
          apply interp_wt; auto.
          }
        }

        {
        apply interp_eval_refl.
        apply interp_arrow.
          {
          invert Hbtr.
          intros _ _ H.
          so (H _#3 (le_refl _) Hru) as H'; clear H.
          simpsubin H'.
          exact H'.
          }

          {
          apply interp_eval_refl.
          apply interp_wt; auto.
          }
        }
      }
    }

    {
    simpsub.
    exploit (Hseqci m2 n2) as H; auto.
      {
      intros j v w Hj Hvw.
      apply (Hactmn j v w Hj).
      eapply coerce_ind_obligation; eauto.
      }

      {
      intros j v w Hj Hvw.
      apply (Hactdn j v w Hj).
      eapply coerce_ind_obligation; eauto.
      }
    destruct H as (C & Hcl & Hcr).
    apply (seqhyp_tm _#5 (iupi stop i (pi1 B (urelspinj _#4 Hm1n1)) C)).
      {
      clear IH.
      apply interp_eval_refl.
      apply interp_pi; auto.
      invert Hbl.
      intros _ _ H.
      so (H _#3 (le_refl _) Hm1n1) as H'.
      simpsubin H'.
      exact H'.
      }

      {
      clear IH.
      apply interp_eval_refl.
      apply interp_pi; auto.
      invert Hbr.
      intros _ _ H.
      so (H _#3 (le_refl _) Hm1n1) as H'.
      simpsubin H'.
      exact H'.
      }
    do 2 eexists.
    do2 5 split; eauto using star_refl.
      {
      prove_hygiene.
      rewrite -> subst_compose.
      apply hygiene_shift_permit.
      eapply subst_closub; eauto.
      }

      {
      prove_hygiene.
      rewrite -> subst_compose.
      apply hygiene_shift_permit.
      eapply subst_closub; eauto.
      }
    intros j v w Hj Hvw.
    so (urel_closed _#5 Hvw) as (Hclv & Hclw).
    simpsub.
    exploit (IH j v w Hj) as H; clear IH.
      {
      eapply coerce_ind_obligation; eauto.
      }
    exploit (H s s' (app m2 v) (app n2 w)) as H'; clear H; eauto using pwctx_downward; try prove_hygiene.
      {
      apply (basic_downward _#3 i); auto.
      }

      {
      apply (basic_downward _#3 i); auto.
      }

      {
      apply (functional_downward _#3 i); auto.
      }

      {
      apply (functional_downward _#3 i); auto.
      }

      {
      apply (Hactmn j _ _ Hj).
      eapply coerce_ind_obligation; eauto.
      }

      {
      apply (Hactdn j _ _ Hj).
      eapply coerce_ind_obligation; eauto.
      }
    destruct H' as (R & Hl & _ & Hm & Hn & Hmn).
    invert Hcl.
    intros _ _ H.
    so (H j v w Hj Hvw) as Hl'; clear H.
    simpsubin Hl'.
    so (basic_fun _#7 Hl Hl'); subst R.
    clear Hl Hl'.
    simpsubin Hm.
    simpsubin Hn.
    simpsubin Hmn.
    rewrite -> (subst_into_closed _#3 Hclm2), -> (subst_into_closed _#3 Hcln2), -> (subst_into_closed _#3 Hclv), -> (subst_into_closed _#3 Hclw) in Hm, Hn, Hmn.
    destruct Hpp; destruct Hqq; subst; auto.
    exact (urel_zigzag _#7 Hn Hmn Hm).
    }

    {
    intros j uu Hj Huu.
    invertc Huu.
    intros r2 uu' Hur1 Hm2r2 _ _ <-.
    invert Hur1.
    intros r1 u Hu Hm1r1 _ _ <-.
    invertc Hm1r1.
    intros A' Hal' _ Hm1r1.
    so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst A'.
    clear Hal'.
    destruct Hm1r1 as (_ & Hm1r1).
    invertc Hm2r2.
    intros R Hwl _ Hm2r2.
    so (urel_closed _#5 Hm2r2) as (_ & Hclr2).
    simpsub.
    exploit (Hseqc j m2 n2 s s') as H; eauto using pwctx_impl_seqctx, pwctx_downward.
      {
      intros j' v w Hj' Hvw.
      assert (j' <= i) as Hj'_i by omega.
      apply (Hactmn _#3 (le_trans _#3 Hj' Hj)).
      eapply coerce_ind_obligation; eauto.
      }

      {
      intros j' v w Hj' Hvw.
      assert (j' <= i) as Hj'_i by omega.
      apply (Hactdn _#3 (le_trans _#3 Hj' Hj)).
      eapply coerce_ind_obligation; eauto.
      }
    destruct H as (C & Hcm & Hcn).
    simpsubin Hwl.
    assert (R = iutruncate (S j) (iuarrow stop i (pi1 B (urelspinj (den A) _#3 Hm1n1)) (iuwt stop A B))).
      {
      refine (basic_fun _#7 Hwl _).
      apply (basic_downward _#3 i); auto.
      apply interp_eval_refl.
      apply interp_arrow.
        {
        invert Hbl.
        intros _ _ H.
        so (H _#3 (le_refl _) Hm1n1) as H'; clear H.
        simpsubin H'.
        exact H'.
        }
      apply interp_eval_refl.
      apply interp_wt; auto.
      }
    subst R.
    clear Hwl.
    rewrite -> den_iutruncate in Hm2r2.
    destruct Hm2r2 as (_ & Hm2r2).
    rewrite -> den_iuarrow in Hm2r2.
    rewrite -> den_iuwt in Hm2r2.
    assert (forall j' v w,
              j' <= j
              -> rel (den (pi1 B (urelspinj (den A) i m1 n1 Hm1n1))) j' v w
              -> wt_action_ind stop (den (iutruncate (S j') A)) (pi1 (nearrow_compose den_ne (fntruncate (S j') (den A) B))) j' (app m2 v) (app r2 w)) as Hm2v_r2w.
      {
      intros j' v w Hj' Hvw.
      so (arrow_action_app _#9 (urel_downward_leq _#6 Hj' Hm2r2) Hvw) as H.
      destruct H as (_ & _ & Hact).
      cbn in Hact.
      change (wt_action_ind stop (den A) (pi1 (nearrow_compose den_ne B)) j' (app m2 v) (app r2 w)) in Hact.
      rewrite -> ceiling_wt_action_ind in Hact; auto.
      exact Hact.
      }
    exploit (Hseqc j m2 r2 s u) as H; auto using pwctx_impl_seqctx.
      {
      intros j' v w Hj' Hvw.
      rewrite <- wt_action_ind_iff.
      apply Hm2v_r2w; auto.
      }

      {
      intros j' v w Hj' Hvw.
      assert (j' <= i) as Hj'_i by omega.
      rewrite <- wt_action_ind_iff.
      apply (wt_action_ind_zigzag _#4 (app d2 v) (app n2 w) (app m2 v) (app r2 w)).
        {
        rewrite -> wt_action_ind_iff.
        apply (Hactdn _#3 Hj'_i).
        eapply coerce_ind_obligation; eauto.
        }

        {
        rewrite -> wt_action_ind_iff.
        apply (Hactmn _#3 Hj'_i).
        eapply coerce_ind_obligation; eauto.
        }

        {
        apply Hm2v_r2w; auto.
        }
      }
    destruct H as (C' & Hcm' & Hcr).
    so (functional_fun _#8 Hcm Hcm'); subst C'.
    clear Hcm Hcm'.
    apply (relhyp_tm _#4 (iupi stop j (iutruncate (S j) (pi1 B (urelspinj (den A) _#3 Hm1n1))) C)).
      {
      apply interp_eval_refl.
      apply interp_pi; auto.
      apply (basic_downward _#3 i); auto.
      invert Hbr.
      intros _ _ H.
      so (H i m1 n1 (le_refl _) Hm1n1) as H'; clear H.
      simpsubin H'.
      exact H'.
      }

      {
      so (Hseqab _#3 Hu) as (A' & B' & Hal' & Hau & Hbl' & Hbu).
      so (basic_fun _#7 (basic_downward _#7 Hj Hal) Hal'); subst A'.
      so (functional_fun _#8 (functional_downward _#8 Hj Hbl) Hbl'); subst B'.
      clear Hal' Hbl'.
      apply interp_eval_refl.
      apply interp_pi; auto.
      invert Hbu.
      intros B' _ _ H Heq.
      so (eq_dep_impl_eq_snd _#5 Heq); subst B'; clear Heq.
      so (H _#3 (le_refl _) (conj (Nat.lt_succ_diag_r j) Hm1r1)) as H'; clear H.
      simpsubin H'.
      force_exact H'; clear H'.
      cbn.
      f_equal.
      rewrite -> embed_ceiling_urelspinj.
      apply iutruncate_collapse.
      apply (pi2 B).
      apply urelspinj_dist_diff; auto.
      eapply urel_downward_leq; eauto.
      }
    }

    {
    intros j uu Hj Huu.
    invertc Huu.
    intros r2 uu' Hur1 Hr2n2 _ _ <-.
    invert Hur1.
    intros r1 u Hu Hr1n1 _ _ <-.
    invertc Hr1n1.
    intros A' _ Har' Hr1n1.
    so (basic_fun _#7 (basic_downward _#7 Hj Har) Har'); subst A'.
    clear Har'.
    destruct Hr1n1 as (_ & Hr1n1).
    invertc Hr2n2.
    intros R _ Hwr Hr2n2.
    so (urel_closed _#5 Hr2n2) as (Hclr2 & _).
    simpsub.
    exploit (Hseqc j m2 n2 s s') as H; eauto using pwctx_impl_seqctx, pwctx_downward.
      {
      intros j' v w Hj' Hvw.
      assert (j' <= i) as Hj'_i by omega.
      apply (Hactmn _#3 (le_trans _#3 Hj' Hj)).
      eapply coerce_ind_obligation; eauto.
      }

      {
      intros j' v w Hj' Hvw.
      assert (j' <= i) as Hj'_i by omega.
      apply (Hactdn _#3 (le_trans _#3 Hj' Hj)).
      eapply coerce_ind_obligation; eauto.
      }
    destruct H as (C & Hcm & Hcn).
    simpsubin Hwr.
    assert (R = iutruncate (S j) (iuarrow stop i (pi1 B (urelspinj (den A) _#3 Hm1n1)) (iuwt stop A B))).
      {
      refine (basic_fun _#7 Hwr _).
      apply (basic_downward _#3 i); auto.
      apply interp_eval_refl.
      apply interp_arrow.
        {
        invert Hbr.
        intros _ _ H.
        so (H _#3 (le_refl _) Hm1n1) as H'; clear H.
        simpsubin H'.
        exact H'.
        }
      apply interp_eval_refl.
      apply interp_wt; auto.
      }
    subst R.
    clear Hwr.
    rewrite -> den_iutruncate in Hr2n2.
    destruct Hr2n2 as (_ & Hr2n2).
    rewrite -> den_iuarrow in Hr2n2.
    rewrite -> den_iuwt in Hr2n2.
    assert (forall j' v w,
              j' <= j
              -> rel (den (pi1 B (urelspinj (den A) i m1 n1 Hm1n1))) j' v w
              -> wt_action_ind stop (den (iutruncate (S j') A)) (pi1 (nearrow_compose den_ne (fntruncate (S j') (den A) B))) j' (app r2 v) (app n2 w)) as Hr2v_n2w.
      {
      intros j' v w Hj' Hvw.
      so (arrow_action_app _#9 (urel_downward_leq _#6 Hj' Hr2n2) Hvw) as H.
      destruct H as (_ & _ & Hact).
      cbn in Hact.
      change (wt_action_ind stop (den A) (pi1 (nearrow_compose den_ne B)) j' (app r2 v) (app n2 w)) in Hact.
      rewrite -> ceiling_wt_action_ind in Hact; auto.
      exact Hact.
      }
    exploit (Hseqc j r2 n2 u s') as H; eauto using pwctx_impl_seqctx, pwctx_downward.
      {
      intros j' v w Hj' Hvw.
      rewrite <- wt_action_ind_iff.
      apply Hr2v_n2w; auto.
      }

      {
      intros j' v w Hj' Hvw.
      assert (j' <= i) as Hj'_i by omega.
      rewrite <- wt_action_ind_iff.
      rewrite -> wt_action_ind_iff.
      apply (Hactdn _#3 Hj'_i).
      eapply coerce_ind_obligation; eauto.
      }
    destruct H as (C' & Hl & Hcn').
    so (functional_fun _#8 Hcn Hcn'); subst C'.
    clear Hcn Hcn'.
    apply (relhyp_tm _#4 (iupi stop j (iutruncate (S j) (pi1 B (urelspinj (den A) _#3 Hm1n1))) C)).
      {
      apply interp_eval_refl.
      apply interp_pi; auto.
      apply (basic_downward _#3 i); auto.
      invert Hbl.
      intros _ _ H.
      so (H i m1 n1 (le_refl _) Hm1n1) as H'; clear H.
      simpsubin H'.
      exact H'.
      }

      {
      so (Hseqab _#3 Hu) as (A' & B' & Hau & Har' & Hbu & Hbr').
      so (basic_fun _#7 (basic_downward _#7 Hj Har) Har'); subst A'.
      so (functional_fun _#8 (functional_downward _#8 Hj Hbr) Hbr'); subst B'.
      clear Har' Hbr'.
      apply interp_eval_refl.
      apply interp_pi; auto.
      invert Hbu.
      intros B' _ _ H Heq.
      so (eq_dep_impl_eq_snd _#5 Heq); subst B'; clear Heq.
      so (H _#3 (le_refl _) (conj (Nat.lt_succ_diag_r j) Hr1n1)) as H'; clear H.
      simpsubin H'.
      force_exact H'; clear H'.
      cbn.
      f_equal.
      rewrite -> embed_ceiling_urelspinj.
      apply iutruncate_collapse.
      apply (pi2 B).
      apply urelspinj_dist_diff; auto.
      }
    }
  }
clear IH.
so (Hseqpq _#3 (Hs' _ _ (or_introl (eq_refl _)) (or_introl (eq_refl _)))) as (C & Hcl & Hcr & Hm & _).
so (Hseqpq _#3 (Hs' _ _ (or_intror (eq_refl _)) (or_intror (eq_refl _)))) as (C' & _ & Hcr' & _ & Hn & _).
so (Hseqpq _#3 (Hs' _ _ (or_introl (eq_refl _)) (or_intror (eq_refl _)))) as (C'' & Hcl'' & Hcr'' & _ & _ & Hmn).
clear Hs'.
so (basic_fun _#7 Hcl Hcl''); subst C''.
so (basic_fun _#7 Hcr' Hcr''); subst C'.
clear Hcr' Hcl'' Hcr''.
exists C.
simpsubin Hcl.
simpsubin Hcr.
do2 2 split.
  {
  refine (basic_equiv _#7 _ _ Hcl).
    {
    eapply hygiene_subst; eauto.
    intros x Hx.
    destruct x as [| x]; simpsub; prove_hygiene.
    }

    {
    simpsub.
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm.
    apply steps_equiv; auto.
    }
  }

  {
  refine (basic_equiv _#7 _ _ Hcr).
    {
    eapply hygiene_subst; eauto.
    intros x Hx.
    destruct x as [| x]; simpsub; prove_hygiene.
    }

    {
    simpsub.
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm.
    apply steps_equiv; auto.
    }
  }
assert (forall (x x1 x2 y : sterm) t,
          star step x (ppair x1 x2)
          -> equiv
               (subst (dot (lam (app (subst (compose t sh1) (wind (lam (lam (lam y))))) (app (subst sh1 x2) (var 0)))) (dot x2 (dot x1 t))) y) 
               (app (subst t (wind (lam (lam (lam y))))) x)) as Hcompute.
  {
  intros x x1 x2 y t Hx.
  apply equiv_symm.
  eapply equiv_trans.
    {
    apply steps_equiv.
    eapply star_trans.
      {
      rewrite -> subst_wind.
      apply wind_unroll.
      }
    eapply star_trans.
      {
      apply steps_app.
      eapply star_trans.
        {
        apply steps_app.
        simpsub.
        apply star_one; apply step_app2.
        }
      simpsub.
      apply star_one; apply step_app2.
      }
    simpsub.
    eapply star_trans.
      {
      apply star_one; apply step_app2.
      }
    simpsub.
    replace (1 + 1 + 0) with 2 by omega.
    replace (1 + 1 + (1 + 1)) with 4 by omega.
    replace (1 + 0) with 1 by omega.
    replace (1 + 1) with 2 by omega.
    simpsub.
    apply star_refl.
    }
  apply equiv_funct; auto using equiv_refl.
  apply equivsub_dot.
  2:{
    apply equivsub_dot.
      {
      apply steps_equiv.
      eapply star_trans.
        {
        apply steps_ppi2.
        exact Hx.
        }
      apply star_one; apply step_ppi22.
      }

      {
      apply equivsub_dot; auto using equivsub_refl.
      apply steps_equiv.
      eapply star_trans.
        {
        apply steps_ppi1.
        exact Hx.
        }
      apply star_one; apply step_ppi12.
      }
    }
  apply equiv_lam.
  apply equiv_app.
    {
    simpsub.
    apply equiv_refl.
    }
  apply equiv_app; auto using equiv_refl.
  rewrite <- subst_ppi2.
  apply equiv_subst.
  apply steps_equiv.
  eapply star_trans.
    {
    apply steps_ppi2.
    exact Hx.
    }
  apply star_one; apply step_ppi22.
  }
do2 2 split.
  {
  refine (urel_equiv _#7 _ _ _ _ Hm).
    {
    eapply subst_closub; eauto.
    prove_hygiene.
    }

    {
    eapply subst_closub; eauto.
    prove_hygiene.
    }

    {
    rewrite -> subst_app.
    rewrite -> (subst_into_closed _#3 Hclm).
    apply Hcompute; auto.
    }

    {
    rewrite -> subst_app.
    rewrite -> (subst_into_closed _#3 Hcln).
    apply Hcompute; auto.
    }
  }

  {
  refine (urel_equiv _#7 _ _ _ _ Hn).
    {
    eapply subst_closub; eauto.
    prove_hygiene.
    }

    {
    eapply subst_closub; eauto.
    prove_hygiene.
    }

    {
    rewrite -> subst_app.
    rewrite -> (subst_into_closed _#3 Hclm).
    apply Hcompute; auto.
    }

    {
    rewrite -> subst_app.
    rewrite -> (subst_into_closed _#3 Hcln).
    apply Hcompute; auto.
    }
  }

  {
  refine (urel_equiv _#7 _ _ _ _ Hmn).
    {
    eapply subst_closub; eauto.
    prove_hygiene.
    }

    {
    eapply subst_closub; eauto.
    prove_hygiene.
    }

    {
    rewrite -> subst_app.
    rewrite -> (subst_into_closed _#3 Hclm).
    apply Hcompute; auto.
    }

    {
    rewrite -> subst_app.
    rewrite -> (subst_into_closed _#3 Hcln).
    apply Hcompute; auto.
    }
  }
Qed.


(* now redundant *)
Lemma sound_wt_elim_pi1 :
  forall G a b m n,
    pseq G (deq m n (wt a b))
    -> pseq G (deq (ppi1 m) (ppi1 n) a).
Proof.
intros G a b m n.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Habl & Habr & Hm & Hn & Hmn).
simpsubin Habl.
simpsubin Habr.
invert (basic_value_inv _#6 value_wt Habl); clear Habl.
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_wt Habr); clear Habr.
intros A' B' Har Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
so (iuwt_inj _#5 Heq) as H; clear Heq.
injectionT H.
intros <-.
injectionT H.
intros <-.
subst R.
exists A.
simpsub.
rewrite -> den_iuwt in Hm, Hn, Hmn.
cbn in Hm, Hn, Hmn.
do2 4 split; auto.
  {
  destruct Hm as (Hclml & Hclmr & H).
  invertc H.
  intros m1l m1r m2l m2r ll lr Hm1 Hsteps Hsteps' _ _ _.
  eapply urel_equiv; eauto; try prove_hygiene; auto.
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi11.
      }
    apply star_one.
    apply step_ppi12.
    }

    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi11.
      }
    apply star_one.
    apply step_ppi12.
    }
  }

  {
  destruct Hn as (Hclml & Hclmr & H).
  invertc H.
  intros m1l m1r m2l m2r ll lr Hm1 Hsteps Hsteps' _ _ _.
  eapply urel_equiv; eauto; try prove_hygiene; auto.
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi11.
      }
    apply star_one.
    apply step_ppi12.
    }

    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi11.
      }
    apply star_one.
    apply step_ppi12.
    }
  }

  {
  destruct Hmn as (Hclml & Hclmr & H).
  invertc H.
  intros m1l m1r m2l m2r ll lr Hm1 Hsteps Hsteps' _ _ _.
  eapply urel_equiv; eauto; try prove_hygiene; auto.
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi11.
      }
    apply star_one.
    apply step_ppi12.
    }

    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi11.
      }
    apply star_one.
    apply step_ppi12.
    }
  }
Qed.


(* now redundant *)
Lemma sound_wt_elim_pi2 :
  forall G a b m n,
    pseq G (deq m n (wt a b))
    -> pseq G (deq (ppi2 m) (ppi2 n) (arrow (subst1 (ppi1 m) b) (wt a b))).
Proof.
intros G a b m n.
revert G.
refine (seq_pseq 3 [hyp_emp] b [] m [] n 1 [] _ _ _); cbn.
intros G Hclb Hclm Hcln Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseq _#3 Hs) as (R & Habl & Habr & Hm & Hn & Hmn).
simpsubin Habl.
simpsubin Habr.
invert (basic_value_inv _#6 value_wt Habl).
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_wt Habr).
intros A' B' Har Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
so (iuwt_inj _#5 Heq) as H; clear Heq.
injectionT H.
intros <-.
injectionT H.
intros <-.
subst R.
rewrite -> den_iuwt in Hm, Hn, Hmn.
cbn in Hm, Hn, Hmn.
destruct Hm as (Hclml & Hclmr & H).
invertc H.
intros m1l m1r m2l m2r m3l m3r Hm1 Hstepml Hstepmr Hstepm2l Hstepm2r Hindm.
destruct Hn as (Hclnl & Hclnr & H).
invertc H.
intros n1l n1r n2l n2r n3l n3r Hn1 Hstepnl Hstepnr Hstepn2l Hstepn2r Hindn.
destruct Hmn as (_ & _ & H).
invertc H.
intros m1l' n1r' m2l' n2r' m3l' n3r' Hmn1 Hstepml' Hstepnr' Hstepm2l' Hstepn2r' Hindmn.
so (determinism_eval _#4 (conj Hstepml value_ppair) (conj Hstepml' value_ppair)) as H.
injectionc H.
intros <- <-.
so (determinism_eval _#4 (conj Hstepnr value_ppair) (conj Hstepnr' value_ppair)) as H.
injectionc H.
intros <- <-.
so (determinism_eval _#4 (conj Hstepm2l value_lam) (conj Hstepm2l' value_lam)) as H.
injectionc H.
intros <-.
so (determinism_eval _#4 (conj Hstepn2r value_lam) (conj Hstepn2r' value_lam)) as H.
injectionc H.
intros <-.
clear Hstepml' Hstepnr' Hstepm2l' Hstepn2r'.
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepml Hclml)) as H; cbn in H.
destruct H as (Hclm1l & Hclm2l & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepmr Hclmr)) as H; cbn in H.
destruct H as (Hclm1r & Hclm2r & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepm2l Hclm2l)) as H; cbn in H.
destruct H as (Hclm3l & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepm2r Hclm2r)) as H; cbn in H.
destruct H as (Hclm3r & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepnl Hclnl)) as H; cbn in H.
destruct H as (Hcln1l & Hcln2l & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepnr Hclnr)) as H; cbn in H.
destruct H as (Hcln1r & Hcln2r & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepn2l Hcln2l)) as H; cbn in H.
destruct H as (Hcln3l & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepn2r Hcln2r)) as H; cbn in H.
destruct H as (Hcln3r & _).
exists (iuarrow stop i (pi1 B (urelspinj _#4 Hm1)) (iuwt stop A B)).
do2 4 split.
  {
  simpsub.
  apply interp_eval_refl.
  apply interp_arrow; auto.
  invert Hbl.
  intros _ _ Hact.
  so (Hact _ _ _ (le_refl _) Hm1) as H.
  simpsubin H.
  eapply basic_equiv; eauto.
    {
    eapply hygiene_subst; eauto.
    intros x Hx.
    destruct x as [| x].
      {
      simpsub.
      prove_hygiene.
      }

      {
      simpsub.
      eapply project_closub; eauto.
      }
    }

    {
    apply equiv_symm.
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply steps_equiv.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi11.
      }
    apply star_one.
    apply step_ppi12.
    }
  }

  {
  simpsub.
  apply interp_eval_refl.
  apply interp_arrow; auto.
  invert Hbr.
  intros _ _ Hact.
  so (Hact _ _ _ (le_refl _) Hm1) as H.
  simpsubin H.
  eapply basic_equiv; eauto.
    {
    eapply hygiene_subst; eauto.
    intros x Hx.
    destruct x as [| x].
      {
      simpsub.
      prove_hygiene.
      }

      {
      simpsub.
      eapply project_closub; eauto.
      }
    }

    {
    apply equiv_symm.
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply steps_equiv.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi11.
      }
    apply star_one.
    apply step_ppi12.
    }
  }

  {
  clear Hcln1l Hcln1r Hcln2l Hcln2r Hcln3l Hcln3r.
  rewrite -> den_iuarrow.
  exists m3l, m3r.
  do2 5 split; auto.
    {
    eapply hygiene_subst; eauto.
    prove_hygiene.
    }

    {
    eapply hygiene_subst; eauto.
    prove_hygiene.
    }

    {
    simpsub.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi21.
      }
    eapply star_step; eauto.
    apply step_ppi22.
    }

    {
    simpsub.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi21.
      }
    eapply star_step; eauto.
    apply step_ppi22.
    }
  intros j p q Hj Hpq.
  cbn.
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  assert (hygiene clo (subst1 p m3l)) as Hclm3l_p.
    {
    eapply hygiene_subst; eauto.
    intros x Hx.
    destruct x as [| x]; auto.
    destruct Hx.
    }
  assert (hygiene clo (subst1 q m3r)) as Hclm3r_q.
    {
    eapply hygiene_subst; eauto.
    intros x Hx.
    destruct x as [| x]; auto.
    destruct Hx.
    }
  do2 2 split; auto.
  so (Hindm j p q Hj Hpq) as H.
  eapply wt_action_ind_equiv; eauto.
    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun x => app x p)); eauto using step_app1.
      }
    apply star_one.
    apply step_app2.
    }

    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun x => app x q)); eauto using step_app1.
      }
    apply star_one.
    apply step_app2.
    }
  }

  {
  clear Hclm1l Hclm1r Hclm2l Hclm2r Hclm3l Hclm3r.
  rewrite -> den_iuarrow.
  exists n3l, n3r.
  do2 5 split; auto.
    {
    eapply hygiene_subst; eauto.
    prove_hygiene.
    }

    {
    eapply hygiene_subst; eauto.
    prove_hygiene.
    }

    {
    simpsub.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi21.
      }
    eapply star_step; eauto.
    apply step_ppi22.
    }

    {
    simpsub.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi21.
      }
    eapply star_step; eauto.
    apply step_ppi22.
    }
  intros j p q Hj Hpq.
  cbn.
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  assert (hygiene clo (subst1 p n3l)) as Hcln3l_p.
    {
    eapply hygiene_subst; eauto.
    intros x Hx.
    destruct x as [| x]; auto.
    destruct Hx.
    }
  assert (hygiene clo (subst1 q n3r)) as Hcln3r_q.
    {
    eapply hygiene_subst; eauto.
    intros x Hx.
    destruct x as [| x]; auto.
    destruct Hx.
    }
  do2 2 split; auto.
  assert (rel (den (pi1 B (urelspinj _#4 Hn1))) j p q) as Hpq'.
    {
    force_exact Hpq.
    f_equal.
    f_equal.
    f_equal.
    apply urelspinj_equal; auto.
    }
  so (Hindn j p q Hj Hpq') as H.
  eapply wt_action_ind_equiv; eauto.
    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun x => app x p)); eauto using step_app1.
      }
    apply star_one.
    apply step_app2.
    }

    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun x => app x q)); eauto using step_app1.
      }
    apply star_one.
    apply step_app2.
    }
  }

  {
  clear Hcln1l Hclm1r Hcln2l Hclm2r Hcln3l Hclm3r.
  rewrite -> den_iuarrow.
  exists m3l, n3r.
  do2 5 split; auto.
    {
    eapply hygiene_subst; eauto.
    prove_hygiene.
    }

    {
    eapply hygiene_subst; eauto.
    prove_hygiene.
    }

    {
    simpsub.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi21.
      }
    eapply star_step; eauto.
    apply step_ppi22.
    }

    {
    simpsub.
    eapply star_trans.
      {
      apply star_map'; eauto using step_ppi21.
      }
    eapply star_step; eauto.
    apply step_ppi22.
    }
  intros j p q Hj Hpq.
  cbn.
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  assert (hygiene clo (subst1 p m3l)) as Hclm3l_p.
    {
    eapply hygiene_subst; eauto.
    intros x Hx.
    destruct x as [| x]; auto.
    destruct Hx.
    }
  assert (hygiene clo (subst1 q n3r)) as Hcln3r_q.
    {
    eapply hygiene_subst; eauto.
    intros x Hx.
    destruct x as [| x]; auto.
    destruct Hx.
    }
  do2 2 split; auto.
  assert (rel (den (pi1 B (urelspinj _#4 Hmn1))) j p q) as Hpq'.
    {
    force_exact Hpq.
    f_equal.
    f_equal.
    f_equal.
    apply urelspinj_equal; auto.
    }
  so (Hindmn j p q Hj Hpq') as H.
  eapply wt_action_ind_equiv; eauto.
    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun x => app x p)); eauto using step_app1.
      }
    apply star_one.
    apply step_app2.
    }

    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun x => app x q)); eauto using step_app1.
      }
    apply star_one.
    apply step_app2.
    }
  }
Qed.


(* now redundant *)
Lemma sound_wt_eta :
  forall G a b m,
    pseq G (deq m m (wt a b))
    -> pseq G (deq m (ppair (ppi1 m) (ppi2 m)) (wt a b)).
Proof.
intros G a b m.
revert G.
refine (seq_pseq 1 [] m 1 [] _ _ _); cbn.
intros G Hclm Hseqm.
rewrite -> seq_deq in Hseqm |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqm _#3 Hs) as (R & Habl & Habr & Hm & _).
exists R.
do2 2 split; auto.
simpsub.
split; auto.
simpsubin Habl.
invert (basic_value_inv _#6 value_wt Habl).
intros A B Ha Hb <-.
cbn in Hm.
decompose Hm.
intros Hclsm Hclsm' Hact.
invertc Hact.
intros n n' p p' l l' Hn Hsteps Hsteps' Hstepsp Hstepsp' Hact.
so (urel_closed _#5 Hn) as (Hcln & Hcln').
assert (rel (den A) i (ppi1 (subst s m)) (ppi1 (subst s' m))) as Hn'.
  {
  refine (urel_equiv _#7 _ _ _ _ Hn); auto using equiv_refl; try prove_hygiene.
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      eapply star_map'; eauto using step_ppi11.
      }
    apply star_one.
    apply step_ppi12.
    }

    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      eapply star_map'; eauto using step_ppi11.
      }
    apply star_one.
    apply step_ppi12.
    }
  }
assert (rel (den A) i (ppi1 (subst s m)) n') as Hn''.
  {
  refine (urel_equiv _#7 _ _ _ _ Hn); auto using equiv_refl; try prove_hygiene.
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      eapply star_map'; eauto using step_ppi11.
      }
    apply star_one.
    apply step_ppi12.
    }
  }
assert (rel (den A) i n (ppi1 (subst s' m))) as Hn'''.
  {
  refine (urel_equiv _#7 _ _ _ _ Hn); auto using equiv_refl; try prove_hygiene.
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      eapply star_map'; eauto using step_ppi11.
      }
    apply star_one.
    apply step_ppi12.
    }
  }
split.
  {
  cbn.
  do2 2 split; try prove_hygiene.
  apply (wt_action_ind_i _#6 (ppi1 (subst s m)) (ppi1 (subst s' m)) (ppi2 (subst s m)) (ppi2 (subst s' m)) l l' Hn'); auto using star_refl.
    {
    eapply star_trans.
      {
      eapply star_map'; eauto using step_ppi21.
      }
    eapply star_step; eauto.
    apply step_ppi22.
    }

    {
    eapply star_trans.
      {
      eapply star_map'; eauto using step_ppi21.
      }
    eapply star_step; eauto.
    apply step_ppi22.
    }

    {
    intros j q q' Hj Hq.
    so (urel_closed _#5 Hq) as (Hclq & Hclq').
    exploit (Hact j q q') as Hact'; auto.
      {
      force_exact Hq.
      f_equal.
      f_equal.
      apply urelspinj_equal; auto.
      }
    eapply wt_action_ind_equiv; eauto; try prove_hygiene.
      {
      apply equiv_app; auto using equiv_refl.
      apply equiv_symm.
      apply steps_equiv.
      eapply star_trans.
        {
        eapply star_map'; eauto using step_ppi21.
        }
      eapply star_one.
      apply step_ppi22.
      }

      {
      apply equiv_app; auto using equiv_refl.
      apply equiv_symm.
      apply steps_equiv.
      eapply star_trans.
        {
        eapply star_map'; eauto using step_ppi21.
        }
      eapply star_one.
      apply step_ppi22.
      }
    }
  }

  {
  cbn.
  do2 2 split; try prove_hygiene.
  apply (wt_action_ind_i _#6 n (ppi1 (subst s' m)) p (ppi2 (subst s' m)) l l' Hn'''); auto using star_refl.
    {
    eapply star_trans.
      {
      eapply star_map'; eauto using step_ppi21.
      }
    eapply star_step; eauto.
    apply step_ppi22.
    }

    {
    intros j q q' Hj Hq.
    so (urel_closed _#5 Hq) as (Hclq & Hclq').
    exploit (Hact j q q') as Hact'; auto.
      {
      force_exact Hq.
      f_equal.
      f_equal.
      apply urelspinj_equal; auto.
      }
    refine (wt_action_ind_equiv _#8 _ _ _ _ Hact'); eauto using equiv_refl; try prove_hygiene.
      {
      so (steps_hygiene _#4 Hsteps Hclsm) as H.
      so (hygiene_invert_auto _#5 H) as H'; cbn in H'.
      destruct H' as (_ & ? & _); auto.
      }

      {
      apply equiv_app; auto using equiv_refl.
      apply equiv_symm.
      apply steps_equiv.
      eapply star_trans.
        {
        eapply star_map'; eauto using step_ppi21.
        }
      eapply star_one.
      apply step_ppi22.
      }
    }
  }
Qed.


Lemma arrow_urel_nonexpansive1 :
  forall w (A : wurel w) (B : urelsp A -n> wurel_ofe w) C,
    @nonexpansive (urelsp A) (wurel_ofe w) (fun x => arrow_urel w (urelsp_index A x) (pi1 B x) C).
Proof.
intros w A B C.
intros d x y Hdist.
intros j Hjd.
fextensionality 2.
intros m p.
pextensionality.
  {
  intro Hmp.
  cbn in Hmp.
  decompose Hmp.
  intros r t Hj Hclm Hclp Hstepsm Hstepsp Hact.
  exists r, t.
  do2 5 split; auto.
    {
    so (urelsp_eta _ _ x) as (k & x1 & x2 & Hx & ->).
    so (urelsp_eta _ _ y) as (k' & y1 & y2 & Hy & ->).
    rewrite -> urelsp_index_inj in Hj |- *.
    so (urelspinj_dist_index' _#11 Hdist) as [(<- & _) | (_ & Hle)]; auto.
    omega.
    }
  intros k n q Hk Hnq.
  eapply Hact; eauto.
  so (pi2 B _ _ _ Hdist k (le_lt_trans _#3 Hk Hjd)) as Heq.
  rewrite <- Heq in Hnq; auto.
  }

  {
  intro Hmp.
  cbn in Hmp.
  decompose Hmp.
  intros r t Hj Hclm Hclp Hstepsm Hstepsp Hact.
  exists r, t.
  do2 5 split; auto.
    {
    so (urelsp_eta _ _ x) as (k & x1 & x2 & Hx & ->).
    so (urelsp_eta _ _ y) as (k' & y1 & y2 & Hy & ->).
    rewrite -> urelsp_index_inj in Hj |- *.
    so (urelspinj_dist_index' _#11 Hdist) as [(<- & _) | (Hle & _)]; auto.
    omega.
    }
  intros k n q Hk Hnq.
  eapply Hact; eauto.
  so (pi2 B _ _ _ Hdist k (le_lt_trans _#3 Hk Hjd)) as Heq.
  rewrite -> Heq in Hnq; auto.
  }
Qed.


Lemma iuarrow_nonexpansive1 :
  forall w (A : wurel w) (B : urelsp A -n> wiurel_ofe w) C,
    @nonexpansive (urelsp A) (wiurel_ofe w) (fun x => iuarrow w (urelsp_index A x) (pi1 B x) C).
Proof.
intros w A B C.
intros j x y Hdist.
split.
  {
  cbn -[dist].
  so (arrow_urel_nonexpansive1 w A (nearrow_compose den_ne B) (den C)) as H.
  apply H; auto.
  }

  {
  cbn.
  apply meta_dist_pair.
    {
    apply meta_iurel_nonexpansive.
    apply (pi2 B); auto.
    }

    {
    apply meta_dist_fn; auto.
      {
      apply den_nonexpansive.
      apply (pi2 B); auto.
      }
    intros t u Htu.
    cbn.
    apply meta_iurel_nonexpansive.
    unfold semiconst.
    so (urelsp_eta _ _ t) as (k & p & q & Hpq & ->).
    so (urelsp_eta _ _ u) as (k' & p' & q' & Hpq' & ->).
    rewrite -> !urelsp_index_inj.
    so (urelspinj_dist_dep_index' _#12 Htu) as [(Heq & _) | (Hle & Hle')].
      {
      subst k'.
      apply dist_refl.
      }

      {
      eapply dist_trans.
        {
        eapply (dist_downward_leq _ _ (S k)); eauto.
        apply iutruncate_near.
        }
      apply dist_symm.
      eapply dist_trans.
        {
        eapply (dist_downward_leq _ _ (S k')); eauto.
        apply iutruncate_near.
        }
      apply dist_refl.
      }
    }
  }
Qed.


Definition iuarrow_ne1 w A B C : urelsp A -n> wiurel_ofe w :=
  expair
    (fun x => iuarrow w (urelsp_index A x) (pi1 B x) C)
    (iuarrow_nonexpansive1 w A B C).


Lemma entrunc_nonexpansive :
  forall w (A : wurel w) (B : urelsp A -n> wiurel_ofe w),
    @nonexpansive (urelsp A) (wiurel_ofe w) (fun x => iutruncate (S (urelsp_index A x)) (pi1 B x)).
Proof.
intros w A B.
intros i x y Hxy.
so (urelsp_eta _ _ x) as (j & m & p & Hmp & ->).
so (urelsp_eta _ _ y) as (j' & n & q & Hnq & ->).
rewrite -> !urelsp_index_inj.
so (urelspinj_dist_index' _#11 Hxy) as [(<- & _) | (Hle & Hle')].
  {
  apply iutruncate_nonexpansive.
  apply (pi2 B); auto.
  }

  {
  eapply dist_trans.
    {
    apply (dist_downward_leq _ _ (S j)); auto.
    apply iutruncate_near.
    }
  apply dist_symm.
  eapply dist_trans.
    {
    apply (dist_downward_leq _ _ (S j')); auto.
    apply iutruncate_near.
    }
  apply dist_symm.
  apply (pi2 B); auto.
  }
Qed.


Definition entrunc w (A : wurel w) (B : urelsp A -n> wiurel_ofe w) : urelsp A -n> wiurel_ofe w
  :=
  expair
    (fun x => iutruncate (S (urelsp_index A x)) (pi1 B x))
    (entrunc_nonexpansive w A B).


Lemma interp_wt_exploded :
  forall s i a b A B,
    interp toppg s i a A
    -> functional the_system toppg s i (den A) b B
    -> interp toppg s i (sigma a (arrow b (subst sh1 (wt a b))))
         (iusigma stop A (entrunc stop (den A) (iuarrow_ne1 stop (den A) B (iuwt stop A B)))).
Proof.
intros s i a b A B Ha Hb.
so (basic_closed _#6 Ha) as Hcla.
invert Hb.
intros Hclb Hceiling Hactb.
apply interp_eval_refl.
apply interp_sigma; auto.
apply functional_i; auto.
  {
  apply hygiene_auto; cbn -[subst].
  do2 2 split; auto.
  apply hygiene_shift_permit.
  prove_hygiene.
  }
intros j m p Hj Hmp.
cbn [pi1 entrunc iuarrow_ne1].
rewrite -> urelsp_index_inj.
rewrite -> iutruncate_iuarrow.
rewrite -> Nat.min_id.
simpsub.
apply interp_eval_refl.
apply interp_arrow.
  {
  apply (basic_downward _#3 j); auto.
  }

  {
  apply (basic_downward _#3 i); auto.
  apply interp_eval_refl.
  apply interp_wt; auto.
  erewrite <- (subst_eqsub _#4 (eqsub_expand_id _)).
  simpsub.
  auto.
  }
Qed.    


Lemma wt_exploded_eq_den :
  forall w (A : wiurel w) (B : urelsp (den A) -n> wiurel_ofe w),
    den (iuwt w A B)
    =
    den (iusigma w A (entrunc w (den A) (iuarrow_ne1 w (den A) B (iuwt w A B)))).
Proof.
intros w A B.
cbn.
apply urel_extensionality.
fextensionality 3.
intros i m p.
pextensionality.
  {
  intro H.
  destruct H as (Hclm & Hclp & H).
  invertc H.
  intros m1 p1 m2 p2 l l' Hmp1 Hstepsm Hstepsp Hstepsm2 Hstepsp2 Hact.
  so (steps_hygiene _#4 Hstepsm Hclm) as H.
  so (hygiene_invert_auto _#5 H) as H'; cbn in H'.
  destruct H' as (_ & Hclm2 & _); clear H.
  so (steps_hygiene _#4 Hstepsp Hclp) as H.
  so (hygiene_invert_auto _#5 H) as H'; cbn in H'.
  destruct H' as (_ & Hclp2 & _); clear H.
  so (steps_hygiene _#4 Hstepsm2 Hclm2) as H.
  so (hygiene_invert_auto _#5 H) as H'; cbn in H'.
  destruct H' as (Hcll & _); clear H.
  so (steps_hygiene _#4 Hstepsp2 Hclp2) as H.
  so (hygiene_invert_auto _#5 H) as H'; cbn in H'.
  destruct H' as (Hcll' & _); clear H.
  exists m1, p1, m2, p2, Hmp1.
  do2 4 split; auto.
  cbn.
  rewrite -> urelsp_index_inj.
  split; [omega |].
  exists l, l'.
  do2 5 split; auto.
  intros k r t Hk Hrt.
  so (urel_closed _#5 Hrt) as (Hclr & Hclt).
  do2 2 split; auto using hygiene_subst1.
  so (Hact k r t Hk Hrt) as H.
  eapply wt_action_ind_equiv; eauto using hygiene_subst1.
    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
      }
    apply star_one; apply step_app2.
    }

    {
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
      }
    apply star_one; apply step_app2.
    }
  }

  {
  intro H.
  cbn in H.
  decompose H.
  intros m1 p1 m2 p2 Hmp1 Hclm Hclp Hstepsm Hstepsp Hmp2.
  do2 2 split; auto.
  cbn in Hmp2.
  destruct Hmp2 as (_ & Hmp2).
  decompose Hmp2.
  intros l l' _ Hclm2 Hclp2 Hstepsm2 Hstepsp2 Hact.
  apply (wt_action_ind_i _#3 i m p m1 p1 m2 p2 l l' Hmp1); auto.
  intros j r t Hj Hrt.
  so (urel_closed _#5 Hrt) as (Hclr & Hclt).
  so (Hact j r t Hj Hrt) as H.
  destruct H as (_ & _ & H).
  eapply wt_action_ind_equiv; eauto; try prove_hygiene.
    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
      }
    apply star_one; apply step_app2.
    }

    {
    apply equiv_symm.
    apply steps_equiv.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun z => app z _)); eauto using step_app1.
      }
    apply star_one; apply step_app2.
    }
  }
Qed.


Lemma sound_wt_subtype_sigma :
  forall G a b,
    pseq G (deqtype a a)
    -> pseq (cons (hyp_tm a) G) (deqtype b b)
    -> pseq G (dsubtype (wt a b) (sigma a (arrow b (subst sh1 (wt a b))))).
Proof.
intros G a b.
revert G.
set (X := (sigma a (arrow b (subst sh1 (wt a b))))).
refine (seq_pseq 1 [hyp_emp] b 2 [] _ [_] _ _ _); cbn.
subst X.
intros G Hclb Hseqa Hseqb.
rewrite -> seq_eqtype in Hseqa, Hseqb.
rewrite -> seq_subtype.
intros i s s' Hs.
so (seqctx_impl_closub _#4 (pwctx_impl_seqctx _#4 Hs)) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr); eauto using subst_closub_under_permit.
  {
  intros j m p Hmp.
  assert (pwctx j (dot m s) (dot p s') (cons (hyp_tm a) G)) as Hss.
    {
    assert (j <= i) as Hj.
      {
      rewrite -> HeqA in Hmp.
      destruct Hmp.
      omega.
      }
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
      }

      {
      intros j' t t' Ht.
      so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hss) as (R & Hbl & Hbr & _).
  exists R.
  simpsub.
  auto.
  }
exists (iuwt stop A B).
exists (iusigma stop A (entrunc stop (den A) (iuarrow_ne1 stop (den A) B (iuwt stop A B)))).
simpsub.
do2 4 split; auto.
  {
  apply interp_eval_refl.
  apply interp_wt; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_wt; auto.
  }

  {
  exploit (interp_wt_exploded true i (subst s a) (subst (under 1 s) b) A B) as H; auto.
  simpsubin H.
  exact H.
  }

  {
  exploit (interp_wt_exploded false i (subst s' a) (subst (under 1 s') b) A B) as H; auto.
  simpsubin H.
  exact H.
  }

  {
  intros j m p Hj Hmp.
  rewrite <- wt_exploded_eq_den; auto.
  }
Qed.


Lemma sound_wt_sigma_subtype :
  forall G a b,
    pseq G (deqtype a a)
    -> pseq (cons (hyp_tm a) G) (deqtype b b)
    -> pseq G (dsubtype (sigma a (arrow b (subst sh1 (wt a b)))) (wt a b)).
Proof.
intros G a b.
revert G.
set (X := (sigma a (arrow b (subst sh1 (wt a b))))).
refine (seq_pseq 1 [hyp_emp] b 2 [] _ [_] _ _ _); cbn.
subst X.
intros G Hclb Hseqa Hseqb.
rewrite -> seq_eqtype in Hseqa, Hseqb.
rewrite -> seq_subtype.
intros i s s' Hs.
so (seqctx_impl_closub _#4 (pwctx_impl_seqctx _#4 Hs)) as (Hcls & Hcls').
so (Hseqa _#3 Hs) as (A & Hal & Har & _).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as (B & Hbl & Hbr); eauto using subst_closub_under_permit.
  {
  intros j m p Hmp.
  assert (pwctx j (dot m s) (dot p s') (cons (hyp_tm a) G)) as Hss.
    {
    assert (j <= i) as Hj.
      {
      rewrite -> HeqA in Hmp.
      destruct Hmp.
      omega.
      }
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
      }

      {
      intros j' t t' Ht.
      so (Hseqa _#3 Ht) as (R & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hss) as (R & Hbl & Hbr & _).
  exists R.
  simpsub.
  auto.
  }
exists (iusigma stop A (entrunc stop (den A) (iuarrow_ne1 stop (den A) B (iuwt stop A B)))).
exists (iuwt stop A B).
simpsub.
do2 4 split; auto.
  {
  exploit (interp_wt_exploded true i (subst s a) (subst (under 1 s) b) A B) as H; auto.
  simpsubin H.
  exact H.
  }

  {
  exploit (interp_wt_exploded false i (subst s' a) (subst (under 1 s') b) A B) as H; auto.
  simpsubin H.
  exact H.
  }

  {
  apply interp_eval_refl.
  apply interp_wt; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_wt; auto.
  }

  {
  intros j m p Hj Hmp.
  rewrite -> wt_exploded_eq_den; auto.
  }
Qed.


Lemma sound_wt_formation_inv1 :
  forall G a b,
    pseq G (deqtype (wt a b) (wt a b))
    -> pseq G (deqtype a a).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
so (Hseq _#3 Hs) as (R & Hl & Hr & _).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_wt Hl).
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_wt Hr).
intros A' B' Har Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq1 Heq2.
so (iuwt_inj _#5 Heq) as Heq'.
so (eq_dep_impl_eq_fst _#6 Heq'); subst A'.
exists A.
do2 3 split; auto.
Qed.


Lemma sound_wt_formation_inv2 :
  forall G a b,
    pseq G (deqtype (wt a b) (wt a b))
    -> pseq (cons (hyp_tm a) G) (deqtype b b).
Proof.
intros G a b.
revert G.
refine (seq_pseq_hyp 0 1 [] [] _ [] [_] _ _); cbn.
intros G Hseq _.
rewrite -> seq_eqtype in Hseq |- *.
intros i ss ss' Hss.
invert Hss.
intros m p s s' Hs Hh _ _ <- <-.
simpsubin Hh.
invertc Hh.
intros A Hal Har Hmp.
so (Hseq _#3 Hs) as (R & Hl & Hr & _).
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_wt Hl).
intros A' B Hal' Hbl Heq1.
so (basic_fun _#7 Hal Hal'); subst A'.
invert (basic_value_inv _#6 value_wt Hr).
intros A'' B' Har' Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq1 Heq2.
so (iuwt_inj _#5 Heq) as Heq'.
injectionT Heq'.
intros <-.
injectionT Heq'.
intros <-.
exists (pi1 B (urelspinj _#4 Hmp)).
invert Hbl.
intros _ _ Hactl.
so (Hactl _#3 (le_refl _) Hmp) as Hbxl.
simpsubin Hbxl.
invert Hbr.
intros _ _ Hactr.
so (Hactr _#3 (le_refl _) Hmp) as Hbxr.
simpsubin Hbxr.
do2 3 split; auto.
Qed.
