
Require Import Tactics.
Require Import Axioms.
Require Import Sigma.
Require Import Equality.
Require Import Ordinal.
Require Import Relation.
Require Import Ofe.
Require Import Syntax.
Require Import SimpSub.
Require Import Hygiene.
Require Import Uniform.
Require Import Urelsp.
Require Import Intensional.
Require Import Dynamic.
Require Import Equivalence.
Require Import Equivalences.
Require Import Candidate.
Require Import Model.
Require Import Ceiling.
Require Import Truncate.
Require Import Standard.
Require Import MapTerm.
Require Import Extend.
Require Import System.
Require Import Page.
Require Export PreSpacify.
Require Import Spaces.
Require Import SemanticsKnot.
Require Import ProperClosed.
Require Import ProperEquiv.
Require Import ProperFun.
Require Import ProperDownward.
Require Import ProperLevel.
Require Import Constructor.
Require Import Semantics.
Require Import SemanticsUniv.
Require Import SemanticsPi.
Require Import SemanticsFut.
Require Import SemanticsSimple.
Require Import SemanticsProperty.
Require Import SemanticsSigma.


Lemma interp_kext_kext :
  forall pg i K,
    level K <<= cin pg
    -> interp_kext pg i (kext stop K) (approx i K).
Proof.
intros pg i K Hlev.
so (le_ord_succ _ _ (le_ord_trans _#3 Hlev (cin_top pg))) as fit.
exists (expair K (space_inhabitant _)), fit.
do2 3 split; auto using kext_hygiene.
unfold kext.
unfold stop.
rewrite -> (lt_ord_dec_is _ _ fit).
apply star_refl.
Qed.


Lemma interp_uext_uext :
  forall pg i w (R : wurel w),
    w <<= cin pg
    -> interp_uext pg i (uext stop R) (ceiling (S i) (extend_urel w (cin pg) R)).
Proof.
intros pg i w R Hlev.
so (le_ord_succ _ _ (le_ord_trans _#3 Hlev (cin_top pg))) as fit.
exists w, (iubase R), fit.
do2 3 split; auto using uext_hygiene.
unfold uext.
unfold stop.
rewrite -> (lt_ord_dec_is _ _ fit).
apply star_refl.
Qed.


Local Ltac prove_hygiene :=
  repeat (first [ apply hygiene_shift_permit
                | apply hygiene_sumbool
                | apply hygiene_auto; cbn [row_rect nat_rect]; repeat2 split; auto
                ]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1, fromsp_hygiene, tosp_hygiene, kext_hygiene, uext_hygiene, pagelit_closed;
  try (apply hygiene_var; cbn; auto; done).


Lemma cty_formation :
  forall pg i j a b,
    rel (univ_urel the_system i pg) j a b
    -> rel (con_urel pg (qtype (cin pg))) j (cty a) (cty b).
Proof.
intros pg i j a b Hab.
destruct Hab as (Hj & R & Ha & Hb).
rewrite -> sint_unroll in Ha, Hb.
cbn.
so (interp_level_internal _#5 (cin_stop pg) Ha) as (R' & ->).
unfold con_action.
cbn [approx].
exists R'.
split.
  {
  apply cinterp_eval_refl.
  apply interp_cty; auto.
  }

  {
  apply cinterp_eval_refl.
  apply interp_cty; auto.
  }
Qed.


Lemma con_formation :
  forall pg i lv lv' j a b,
    j <= i
    -> pginterp lv pg
    -> pginterp lv' pg
    -> rel (con_urel pg (qtype (cin pg))) j a b
    -> rel (univ_urel the_system i pg) j (con lv a) (con lv' b).
Proof.
intros pg i lv lv' j a b Hj Hlv Hlv' Hab.
destruct Hab as (R & Ha & Hb).
cbn [approx] in R, Ha, Hb.
split; auto.
unfold spcar in R; cbn [space] in R.
exists (extend_iurel (cin_stop pg) R).
rewrite -> sint_unroll.
split.
  {
  apply interp_eval_refl.
  apply interp_con; auto using le_page_refl.
  }

  {
  apply interp_eval_refl.
  apply interp_con; auto using le_page_refl.
  }
Qed.


Definition spacification pg i K A :=
  K = approx i K
  /\
  (forall j u v,
     j <= i
     -> j <= u
     -> j <= v
     -> rel (arrow_urel stop i (den A) (con_urel pg K)) j
          (tosp stop pg (approx u K)) (tosp stop pg (approx v K)))
  /\
  (forall j u v,
     j <= i
     -> j <= u
     -> j <= v
     -> rel (arrow_urel stop i (con_urel pg K) (den A)) j
          (fromsp stop pg (approx u K)) (fromsp stop pg (approx v K)))
  /\
  (forall j m p,
     j <= i
     -> rel (den A) j m p
     -> rel (den A) j (app (fromsp stop pg K) (app (tosp stop pg K) m)) p)
  /\
  (forall j a b,
     j <= i
     -> rel (con_urel pg K) j a b
     -> rel (con_urel pg K) j (app (tosp stop pg K) (app (fromsp stop pg K) a)) b).


Lemma spacify_main :
  forall pg s i k K,
    kinterp pg s i k K
    -> exists A, interp toppg s i k A /\ spacification pg i K A.
Proof.
exploit
  (semantics_ind the_system
     (fun pg s i k K =>
        exists A,
          interpv toppg s i k A
          /\
          (forall j u v,
             j <= i
             -> j <= u
             -> j <= v
             -> rel (arrow_urel stop i (den A) (con_urel pg K)) j
                  (tosp stop pg (approx u K)) (tosp stop pg (approx v K)))
          /\
          (forall j u v,
             j <= i
             -> j <= u
             -> j <= v
             -> rel (arrow_urel stop i (con_urel pg K) (den A)) j
                  (fromsp stop pg (approx u K)) (fromsp stop pg (approx v K)))
          /\
          (forall j m p,
             j <= i
             -> rel (den A) j m p
             -> rel (den A) j (app (fromsp stop pg K) (app (tosp stop pg K) m)) p)
          /\
          (forall j a b,
             j <= i
             -> rel (con_urel pg K) j a b
             -> rel (con_urel pg K) j (app (tosp stop pg K) (app (fromsp stop pg K) a)) b))
     (fun _ _ _ _ _ => True)
     (fun _ _ _ _ _ => True)
     (fun pg s i k K =>
        exists A,
          interp toppg s i k A
          /\
          (forall j u v,
             j <= i
             -> j <= u
             -> j <= v
             -> rel (arrow_urel stop i (den A) (con_urel pg K)) j
                  (tosp stop pg (approx u K)) (tosp stop pg (approx v K)))
          /\
          (forall j u v,
             j <= i
             -> j <= u
             -> j <= v
             -> rel (arrow_urel stop i (con_urel pg K) (den A)) j
                  (fromsp stop pg (approx u K)) (fromsp stop pg (approx v K)))
          /\
          (forall j m p,
             j <= i
             -> rel (den A) j m p
             -> rel (den A) j (app (fromsp stop pg K) (app (tosp stop pg K) m)) p)
          /\
          (forall j a b,
             j <= i
             -> rel (con_urel pg K) j a b
             -> rel (con_urel pg K) j (app (tosp stop pg K) (app (fromsp stop pg K) a)) b))
     (fun _ _ _ _ _ => True)
     (fun _ _ _ _ _ => True)
     (fun _ _ _ _ _ _ => True)) as Hind; auto.

(* unit *)
{
intros ps s i.
eexists.
do2 4 split.
  {
  apply interp_unit.
  }

  {
  intros u v w Hu Hv Hw.
  cbn.
  apply arrow_action_lam; auto; try prove_hygiene.
  intros j m p Hj Hmp.
  simpsub.
  exists tt.
  split; apply cinterp_eval_refl; apply interp_cunit.
  }

  {
  intros u v w Hu Hv Hw.
  cbn.
  apply arrow_action_lam; auto; try prove_hygiene.
  intros j m p Hj Hmp.
  simpsub.
  apply property_action_triv; auto.
  omega.
  }

  {
  intros j m p Hj Hmp.
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  match goal with
  | |- rel _ _ ?X _ =>
     eassert (equiv _ X) as Hequiv
  end.
    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    apply equiv_refl.
    }
  refine (urel_equiv_1 _#6 _ Hequiv _).
    {
    prove_hygiene.
    }
  cbn in Hmp.
  destruct Hmp as (_ & _ & _ & _ & _ & Hp).
  cbn.
  do2 5 split; auto using star_refl.
  prove_hygiene.
  }

  {
  intros j a b Hj Hab.
  cbn [fromsp tosp].
  so (urel_closed _#5 Hab) as (Hcla & Hclb).
  match goal with
  | |- rel _ _ ?X _ =>
     eassert (equiv _ X) as Hequiv
  end.
    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    apply equiv_refl.
    }
  refine (urel_equiv_1 _#6 _ Hequiv _); clear Hequiv.
    {
    prove_hygiene.
    }
  destruct Hab as (R & Ha & Hb).
  cbn [approx] in R, Ha, Hb.
  exists R.
  split; auto.
  cbn in R.
  destruct R.
  apply cinterp_eval_refl.
  apply interp_cunit.
  }
}

(* type *)
{
intros pg s i lv Hintpg.
so (pginterp_str_top _ _ Hintpg) as Hstr.
so (pginterp_cex_top _ _ Hintpg) as Hcex.
so (pginterp_impl_pagelit _ _ Hintpg) as Hpg.
eexists.
do2 4 split.
  {
  apply interp_univ; eauto.
  }

  {
  intros u v w Hu Hv Hw.
  cbn [tosp approx].
  apply arrow_action_lam; try prove_hygiene.
  intros j m p Hj Hmp.
  simpsub.
  eapply (cty_formation _ i); auto.
  }

  {
  intros u v w Hu Hv Hw.
  cbn [fromsp approx].
  apply arrow_action_lam; try prove_hygiene.
  intros j m p Hj Hmp.
  simpsub.
  apply con_formation; simpsub; auto.
  omega.
  }

  {
  intros j m p Hj Hmp.
  cbn [fromsp tosp].
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  match goal with
  | |- rel _ _ ?X _ =>
     eassert (equiv _ X) as Hequiv
  end.
    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    apply equiv_con; [apply equiv_refl |].
    eapply equiv_trans.
      {
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    apply equiv_refl.
    }
  refine (urel_equiv_1 _#6 _ Hequiv _).
    {
    prove_hygiene.
    }
  cbn in Hmp.
  destruct Hmp as (_ & R & Hm & Hp).
  cbn.
  split; auto.
  exists R.
  split; auto.
  rewrite -> sint_unroll in Hm |- *.
  so (interp_level_internal _#5 (cin_stop pg) Hm) as (R' & ->).
  apply interp_eval_refl.
  apply interp_con; auto using le_page_refl.
  apply cinterp_eval_refl.
  apply interp_cty; auto.
  }

  {
  intros j a b Hj Hab.
  cbn [fromsp tosp].
  so (urel_closed _#5 Hab) as (Hcla & Hclb).
  match goal with
  | |- rel _ _ ?X _ =>
     eassert (equiv _ X) as Hequiv
  end.
    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    apply equiv_cty.
    eapply equiv_trans.
      {
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    apply equiv_refl.
    }
  refine (urel_equiv_1 _#6 _ Hequiv _); clear Hequiv.
    {
    prove_hygiene.
    }
  destruct Hab as (R & Ha & Hb).
  cbn [approx] in R, Ha, Hb.
  exists R.
  split; auto.
  apply cinterp_eval_refl.
  apply interp_cty.
  apply interp_eval_refl.
  apply interp_con; auto using le_page_refl.
  }
}

(* karrow *)
{
intros pg s i k l K L Hk IH1 Hl IH2.
destruct IH1 as (A & HintA & IH1a & IH1b & IH1c & IH1d).
destruct IH2 as (B & HintB & IH2a & IH2b & IH2c & IH2d).
so (kinterp_level_bound _#5 Hk) as HlevK.
so (kinterp_level_bound _#5 Hl) as HlevL.
eexists.
do2 4 split.
  {
  apply interp_karrow; eauto.
  }

  (* karrow tosp *)
  {
  clear IH1a IH1c IH1d IH2b IH2c IH2d.
  intros u v w Hu Hv Hw.
  cbn.
  apply arrow_action_lam; try prove_hygiene.
  intros j p q Hj Hpq.
  simpsub.
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  apply con_urel_raise.
  cbn [approx].
  apply clam_formation; auto using interp_kext_kext.
    {
    symmetry.
    apply approx_idem.
    }

    {
    relquest.
      {
      apply interp_kext_kext.
      eapply le_ord_trans; eauto using approx_level.
      }
    rewrite -> approx_combine_le; auto.
    omega.
    }

    {
    relquest.
      {
      apply interp_kext_kext.
      eapply le_ord_trans; eauto using approx_level.
      }
    rewrite -> approx_combine_le; auto.
    omega.
    }
  intros j' c d Hj' Hcd.
  simpsub.
  assert (j' <= u) as Hj'_u by omega.
  apply con_urel_raise.
  rewrite -> approx_combine_le; auto.
  apply con_urel_lower.
  refine (arrow_action_app _#9 (urel_downward_leq _#6 Hj'_u (IH2a u v w Hu Hv Hw)) _).
  refine (arrow_action_app _#9 (urel_downward_leq _#6 Hj' Hpq) _).
  refine (arrow_action_app _#9 (urel_downward_leq _#6 Hj'_u (IH1b u v w Hu Hv Hw)) _).
  apply con_urel_raise.
  so (con_urel_lower _#5 Hcd) as H.
  rewrite -> approx_combine_le in H; auto.
  }

  (* karrow fromsp *)
  {
  clear IH1b IH1c IH1d IH2a IH2c IH2d.
  intros u v w Hu Hv Hw.
  cbn.
  apply arrow_action_lam; try prove_hygiene.
  intros j m n Hj Hmn.
  simpsub.
  so (urel_closed _#5 Hmn) as (Hclm & Hcln).
  apply arrow_action_lam; try prove_hygiene.
    {
    omega.
    }
  intros j' p q Hj' Hpq.
  simpsub.
  assert (j' <= u) as Hj'_u by omega.
  refine (arrow_action_app _#9 (urel_downward_leq _#6 Hj'_u (IH2b u v w Hu Hv Hw)) _).
  apply (capp_formation _ K).
    {
    apply (urel_downward_leq _#3 j); auto.
    }
  exact (arrow_action_app _#9 (urel_downward_leq _#6 Hj'_u (IH1a u v w Hu Hv Hw)) Hpq).
  }

  (* karrow beta *)
  {
  clear IH1d IH2d.
  so (IH1a i i i (le_refl _) (le_refl _) (le_refl _)) as IH1ai.
  so (IH1b i i i (le_refl _) (le_refl _) (le_refl _)) as IH1bi.
  so (IH2a i i i (le_refl _) (le_refl _) (le_refl _)) as IH2ai.
  so (IH2b i i i (le_refl _) (le_refl _) (le_refl _)) as IH2bi.
  rewrite <- (kbasic_impl_approx _#6 Hk) in IH1ai, IH1bi.
  rewrite <- (kbasic_impl_approx _#6 Hl) in IH2ai, IH2bi.
  clear IH1a IH1b IH2a IH2b.
  intros j m p Hj Hmp.
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  cbn [fromsp tosp].
  rewrite -> den_iuarrow.
  match goal with
  | |- rel _ _ ?X _ =>
      eassert (equiv X _) as Hequiv
  end.
    {
    eapply equiv_trans.
      {
      apply steps_equiv.
      apply star_one.
      apply step_app2.
      }
    simpsub.
    eapply equiv_trans.
      {
      apply equiv_lam.
      apply equiv_app; [apply equiv_refl |].
      apply equiv_capp; [| apply equiv_refl].
      apply steps_equiv.
      apply star_one.
      apply step_app2.
      }
    simpsub.
    replace (1 + 1) with 2 by omega.
    apply equiv_refl.
    }
  refine (urel_equiv_1 _#6 _ (equiv_symm _#3 Hequiv) _).
    {
    prove_hygiene.
    }
  clear Hequiv.
  refine (arrow_action_lam1 _#8 _ Hmp _).
    {
    prove_hygiene.
    }
  intros j' n q Hj' Hnq.
  simpsub.
  so (le_trans _#3 Hj' Hj) as Hj'_i.
  so (IH1c j' n q Hj'_i Hnq) as Hetan_q.
  so (arrow_action_app _#9 (urel_downward_leq _#6 Hj' Hmp) Hetan_q) as Hmetan_pq.
  so (IH2c j' _ _ Hj'_i Hmetan_pq) as Hetametan_pq.
  exploit (capp_clam_beta_double pg (approx j' K) (approx j' L) j' (kext stop K)
             (app (tosp stop pg L) (app (subst sh1 m) (app (fromsp stop pg K) (var 0))))
             (app (tosp stop pg L) (app (subst sh1 p) (app (fromsp stop pg K) (var 0))))
             (app (tosp stop pg K) n)
             (app (tosp stop pg K) q)) as H.
    {
    symmetry.
    apply approx_idem.
    }

    {
    apply interp_kext_kext; auto.
    }

    {
    intros j'' c d Hj'' Hcd.
    simpsub.
    so (le_trans _#3 Hj'' Hj'_i) as Hj''_i.
    apply con_urel_raise.
    rewrite -> approx_combine_le; auto.
    apply con_urel_lower.
    refine (arrow_action_app _#9 (urel_downward_leq _#6 Hj''_i IH2ai) _).
    refine (arrow_action_app _#9 (urel_downward_leq _#6 (le_trans _#3 Hj'' Hj') Hmp) _).
    refine (arrow_action_app _#9 (urel_downward_leq _#6 Hj''_i IH1bi) _).
    so (con_urel_lower _#5 Hcd) as H.
    rewrite -> approx_combine_le in H; auto.
    apply con_urel_raise; auto.
    }

    {
    apply con_urel_lower.
    exact (arrow_action_app _#9 (urel_downward_leq _#6 Hj'_i IH1ai) Hnq).
    }
  simpsubin H.
  so (con_urel_raise _#5 (H andel)) as Hredex.
  so (con_urel_raise _#5 (H ander)) as Hcontractum.
  clear H.
  so (arrow_action_app _#9 (urel_downward_leq _#6 Hj'_i IH2bi) Hredex) as Hfromredex.
  so (arrow_action_app _#9 (urel_downward_leq _#6 Hj'_i IH2bi) Hcontractum) as Hfromcontractum.
  exact (urel_zigzag _#7 Hfromredex Hfromcontractum Hetametan_pq).
  }

  (* karrow eta *)
  {
  clear IH1a IH1b IH1c IH2a IH2b IH2c.
  intros j a b Hj Hab.
  so (urel_closed _#5 Hab) as (Hcla & Hclb).
  cbn [tosp fromsp].
  match goal with
  | |- rel _ _ ?X _ =>
     eassert (equiv _ X) as Hequiv
  end.
    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply steps_equiv.
      apply star_one.
      apply step_app2.
      }
    simpsub.
    apply equiv_clam; [apply equiv_refl |].
    apply equiv_app; [apply equiv_refl |].
    eapply equiv_trans.
      {
      apply equiv_app; [| apply equiv_refl].
      eapply equiv_trans.
        {
        apply steps_equiv.
        apply star_one.
        apply step_app2.
        }
      simpsub.
      replace (1 + 1) with 2 by omega.
      apply equiv_refl.
      }
    eapply equiv_trans.
      {
      apply steps_equiv.
      apply star_one.
      apply step_app2.
      }
    simpsub.
    apply equiv_refl.
    }
  refine (urel_equiv_1 _#6 _ Hequiv _).
    {
    prove_hygiene.
    }
  clear Hequiv.
  so (con_urel_lower _#5 Hab) as H.
  cbn in H.
  so (clam_capp_eta _#7 (eqsymm (approx_idem _ _)) (interp_kext_kext pg j K HlevK) H) as H12; clear H.
  exploit (clam_formation pg (approx j K) (approx j L) j (kext stop K) (kext stop K) (capp (subst sh1 a) (var 0)) (capp (subst sh1 b) (var 0))) as H13; auto using interp_kext_kext.
    {
    symmetry.
    apply approx_idem.
    }

    {
    intros j' c d Hj' Hcd.
    simpsub.
    apply con_urel_lower'; auto.
    apply (capp_formation _ K).
      {
      eapply urel_downward_leq; eauto.
      }
    
      {
      apply (con_urel_raise' _#6 Hj'); auto.
      }
    }
  exploit (clam_formation pg (approx j K) (approx j L) j (kext stop K) (kext stop K) (app (tosp stop pg L) (app (fromsp stop pg L) (capp (subst sh1 a) (app (tosp stop pg K) (app (fromsp stop pg K) (var 0)))))) (capp (subst sh1 b) (var 0))) as H43; auto using interp_kext_kext.
    {
    symmetry.
    apply approx_idem.
    }

    {
    intros j' c d Hj' Hcd.
    simpsub.
    apply con_urel_lower'; auto.
    apply IH2d; [omega |].
    apply (capp_formation _ K); eauto using urel_downward_leq.
    apply IH1d; [omega |].
    apply (con_urel_raise' _#3 j); auto.
    }
  so (urel_zigzag _#7 H43 H13 H12) as H.
  apply con_urel_raise.
  exact H.
  }
}

(* ktarrow *)
{
intros pg s i a k A K Ha _ Hk IH.
destruct IH as (B & HintB & IHa & IHb & IHc & IHd).
so (kinterp_level_bound _#5 Hk) as HlevK.
set (l := cin pg) in *.
set (fit := cin_stop pg) in *.
so (le_ord_succ _ _ (le_ord_trans _#3 HlevK (cin_top pg))) as kfit.
change (level K << stop) in kfit.
eexists.
do2 4 split.
  {
  apply interp_tarrow; eauto.
  exact (interp_increase _#6 (toppg_max pg) Ha).
  }

  (* ktarrow tosp *)
  {
  clear IHb IHc IHd.
  intros u v w Hu Hv Hw.
  cbn.
  apply arrow_action_lam; try prove_hygiene.
  intros j m p Hj Hmp.
  simpsub.
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  apply con_urel_raise.
  cbn [approx].
  rewrite <- den_iutruncate.
  assert (interp_uext pg j (uext stop (den A)) (den (iutruncate (S j) A))) as Huext.
    {
    so (interp_uext_uext pg j l (den A) (le_ord_refl _)) as H.
    rewrite -> extend_urel_id in H.
    rewrite -> den_iutruncate.
    exact H.
    }
  apply ctlam_formation; auto using interp_kext_kext; try prove_hygiene.
    {
    relquest.
      {
      apply interp_uext_uext.
      apply le_ord_refl.
      }
    rewrite -> den_iutruncate.
    rewrite -> extend_urel_id.
    rewrite -> ceiling_combine_le; auto.
    omega.
    }

    {
    relquest.
      {
      apply interp_uext_uext.
      apply le_ord_refl.
      }
    rewrite -> den_iutruncate.
    rewrite -> extend_urel_id.
    rewrite -> ceiling_combine_le; auto.
    omega.
    }

    {
    relquest.
      {
      apply interp_kext_kext.
      eapply le_ord_trans; eauto using approx_level.
      }
    rewrite -> approx_combine_le; auto.
    omega.
    }

    {
    relquest.
      {
      apply interp_kext_kext.
      eapply le_ord_trans; eauto using approx_level.
      }
    rewrite -> approx_combine_le; auto.
    omega.
    }
  intros j' n q Hnq.
  simpsub.
  rewrite -> den_iutruncate in Hnq.
  destruct Hnq as (H & Hnq).
  assert (j' <= j) as Hj' by omega; clear H.
  apply con_urel_lower'; auto.
  refine (arrow_action_app _#9 (urel_downward_leq _#6 (le_trans _#3 Hj' Hj) (IHa u v w Hu Hv Hw)) _).
  apply (arrow_action_app stop i (extend_urel _ _ (den A))); auto.
  exact (urel_downward_leq _#6 Hj' Hmp).
  }

  (* ktarrow fromsp *)
  {
  clear IHa IHc IHd.
  intros u v w Hu Hv Hw.
  cbn [fromsp approx].
  apply arrow_action_lam; try prove_hygiene.
  intros j m p Hj Hmp.
  simpsub.
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  rewrite -> den_iuarrow.
  apply arrow_action_lam; try prove_hygiene.
    {
    omega.
    }
  intros j' n q Hj' Hnq.
  simpsub.
  refine (arrow_action_app _#9 (urel_downward_leq _#6 (le_trans _#3 Hj' Hj) (IHb u v w Hu Hv Hw)) _).
  apply (ctapp_formation _ (den A)).
    {
    exact (urel_downward_leq _#6 Hj' Hmp).
    }

    {
    exact Hnq.
    }
  }

  (* ktarrow beta *)
  {
  so (IHa i i i (le_refl _) (le_refl _) (le_refl _)) as IHai.
  so (IHb i i i (le_refl _) (le_refl _) (le_refl _)) as IHbi.
  rewrite <- (kbasic_impl_approx _#6 Hk) in IHai, IHbi.
  clear IHa IHb IHd.
  intros j m p Hj Hmp.
  rewrite -> den_iuarrow in Hmp.
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  rewrite -> den_iuarrow.
  rewrite -> den_extend_iurel.
  cbn [fromsp tosp].
  match goal with
  | |- rel _ _ ?X _ =>
     eassert (equiv _ X) as Hequiv
  end.
    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    apply equiv_lam.
    apply equiv_app; [apply equiv_refl |].
    apply equiv_ctapp; [| apply equiv_refl].
    eapply equiv_trans.
      {
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    replace (1 + 1) with 2 by omega.
    apply equiv_refl.
    }
  refine (urel_equiv_1 _#6 _ Hequiv _); clear Hequiv.
    {
    prove_hygiene.
    }
  apply (arrow_action_lam1 _#6 m); auto.
    {
    prove_hygiene.
    }
  intros j' n q Hj' Hnq.
  simpsub.
  exploit (ctapp_ctlam_beta_double pg (ceiling (S j') (den A)) (approx j' K) j' (uext stop (den A)) 
             (app (tosp stop pg K) (app (subst sh1 m) (var 0)))
             (app (tosp stop pg K) (app (subst sh1 p) (var 0)))
             (kext stop K)
             n q); auto using interp_kext_kext; try prove_hygiene.
    {
    so (interp_uext_uext pg j' l (den A) (le_ord_refl _)) as H.
    rewrite -> extend_urel_id in H.
    exact H.
    }

    {
    intros j'' r t Hrt.
    simpsub.
    destruct Hrt as (H & Hrt).
    assert (j'' <= j') as Hj'' by omega; clear H.
    assert (j'' <= i) as Hj''_i by omega.
    apply con_urel_lower'; auto.
    refine (arrow_action_app _#9 (urel_downward_leq _#6 Hj''_i IHai) _).
    exact (arrow_action_app _#9 (urel_downward_leq _#6 (le_trans _#3 Hj'' Hj') Hmp) Hrt).
    }

    {
    split; auto.
    }
  simpsubin H.
  destruct H as (H1 & H2).
  so (con_urel_raise _#5 H1) as Hredex.
  so (con_urel_raise _#5 H2) as Hcontractum.
  clear H1 H2.
  assert (j' <= i) as Hj'_i by omega.
  so (arrow_action_app _#9 (urel_downward_leq _#6 Hj'_i IHbi) Hredex) as H.
  renameover H into Hredex.
  so (arrow_action_app _#9 (urel_downward_leq _#6 Hj'_i IHbi) Hcontractum) as H.
  renameover H into Hcontractum.
  so (arrow_action_app _#9 (urel_downward_leq _#6 Hj' Hmp) Hnq) as Hmn_pq.
  so (IHc _#3 Hj'_i Hmn_pq) as H.
  exact (urel_zigzag _#7 Hredex Hcontractum H).
  }

  (* ktarrow eta *)
  {
  clear IHa IHb IHc.
  intros j b c Hj Hbc.
  so (urel_closed _#5 Hbc) as (Hb & Hc).
  cbn [tosp fromsp].
  match goal with
  | |- rel _ _ ?X _ =>
     eassert (equiv _ X) as Hequiv
  end.
    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    apply equiv_ctlam; [apply equiv_refl | | apply equiv_refl].
    apply equiv_app; [apply equiv_refl |].
    eapply equiv_trans.
      {
      apply equiv_app; [| apply equiv_refl].
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    eapply equiv_trans.
      {
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    apply equiv_refl.
    }
  refine (urel_equiv_1 _#6 _ Hequiv _); clear Hequiv.
    {
    prove_hygiene.
    }
  so (interp_uext_uext pg j l (den A) (le_ord_refl _)) as Huext.
  rewrite -> extend_urel_id in Huext.
  so (con_urel_lower _#5 Hbc) as H.
  cbn [approx] in H.
  so (ctlam_ctapp_eta _#8 (interp_kext_kext pg j K HlevK) Huext H) as Heta; clear H.
  change (rel (con_urel pg (approx j (qtarrow (cin pg) (den A) K))) j (ctlam (uext stop (den A)) (ctapp (subst sh1 b) (var 0)) (kext stop K)) c) in Heta.
  so (con_urel_raise _#5 Heta) as H; renameover H into Heta.
  refine (urel_zigzag _#4 (ctlam (uext stop (den A)) (ctapp (subst sh1 c) (var 0)) (kext stop K)) _ _ _ _ Heta).
    {
    apply con_urel_raise.
    cbn [approx].
    apply ctlam_formation; auto using interp_kext_kext; try prove_hygiene.
    intros j' m p Hmp.
    simpsub.
    so Hmp as (H & _).
    assert (j' <= j) as Hj' by omega; clear H.
    apply con_urel_lower'; auto.
    apply IHd.
      {
      omega.
      }
    apply (ctapp_formation _ (den A)).
      {
      eapply urel_downward_leq; eauto.
      }

      {
      exact (Hmp ander).
      }
    }

    {
    apply con_urel_raise.
    cbn [approx].
    apply ctlam_formation; auto using interp_kext_kext; try prove_hygiene.
    intros j' m p Hmp.
    simpsub.
    so Hmp as (H & _).
    assert (j' <= j) as Hj' by omega; clear H.
    apply con_urel_lower'; auto.
    apply (ctapp_formation _ (den A)).
      {
      eapply urel_downward_leq; eauto.
      }

      {
      exact (Hmp ander).
      }
    }
  }
}

(* kprod *)
{
intros pg s i k l K L Hk IH1 Hl IH2.
destruct IH1 as (A & HintA & IH1a & IH1b & IH1c & IH1d).
destruct IH2 as (B & HintB & IH2a & IH2b & IH2c & IH2d).
so (kinterp_level_bound _#5 Hk) as HlevK.
so (kinterp_level_bound _#5 Hl) as HlevL.
eexists.
do2 4 split.
  {
  apply interp_prod; eauto.
  }





  (* kprod tosp *)
  {
  clear IH1b IH1c IH1d IH2b IH2c IH2d.
  intros u v w Hu Hv Hw.
  cbn.
  apply arrow_action_lam; try prove_hygiene.
  intros j p q Hj Hpq.
  simpsub.
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  apply cpair_formation.
    {
    eapply arrow_action_app.
      {
      apply IH1a; omega.
      }

      {
      eapply prod_action_ppi1.
      exact Hpq.
      }
    }

    {
    eapply arrow_action_app.
      {
      apply IH2a; omega.
      }

      {
      eapply prod_action_ppi2.
      exact Hpq.
      }
    }
  }

  (* kprod fromsp *)
  {
  clear IH1a IH1c IH1d IH2a IH2c IH2d.
  intros u v w Hu Hv Hw.
  cbn.
  apply arrow_action_lam; try prove_hygiene.
  intros j p q Hj Hpq.
  simpsub.
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  apply prod_action_ppair.
    {
    eapply arrow_action_app.
      {
      apply IH1b; omega.
      }
    eapply cpi1_formation; eauto.
    }

    {
    eapply arrow_action_app.
      {
      apply IH2b; omega.
      }
    eapply cpi2_formation; eauto.
    }
  }

  (* kprod beta *)
  {
  intros j m p Hj Hmp.
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  clear IH1d IH2d.
  so (IH1a i i i (le_refl _) (le_refl _) (le_refl _)) as IH1ai.
  so (IH1b i i i (le_refl _) (le_refl _) (le_refl _)) as IH1bi.
  so (IH2a i i i (le_refl _) (le_refl _) (le_refl _)) as IH2ai.
  so (IH2b i i i (le_refl _) (le_refl _) (le_refl _)) as IH2bi.
  rewrite <- (kbasic_impl_approx _#6 Hk) in IH1ai, IH1bi.
  rewrite <- (kbasic_impl_approx _#6 Hl) in IH2ai, IH2bi.
  cbn [fromsp tosp].
  match goal with
  | |- rel _ _ ?X _ =>
       eassert (equiv _ X) as Hequiv
  end.
    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    apply equiv_ppair.
      {
      apply equiv_app; [apply equiv_refl |].
      eapply equiv_trans.
        {
        apply equiv_cpi1.
        apply steps_equiv; apply star_one; apply step_app2.
        }
      simpsub.
      apply equiv_refl.
      }

      {
      apply equiv_app; [apply equiv_refl |].
      eapply equiv_trans.
        {
        apply equiv_cpi2.
        apply steps_equiv; apply star_one; apply step_app2.
        }
      simpsub.
      apply equiv_refl.
      }
    }
  refine (urel_equiv_1 _#6 _ Hequiv _); clear Hequiv; try prove_hygiene.
  so (prod_action_ppi1 _#6 Hmp) as Hmp1.
  so (prod_action_ppi2 _#6 Hmp) as Hmp2.
  refine (prod_action_ppair1 _#8 _ Hmp _ _); try prove_hygiene.
    {
    apply (urel_zigzag _#4 (app (fromsp stop pg K) (app (tosp stop pg K) (ppi1 p))) (app (fromsp stop pg K) (app (tosp stop pg K) (ppi1 m)))); auto.
      {
      eapply arrow_action_app.
        {
        exact (urel_downward_leq _#6 Hj IH1bi).
        }
      eapply cpi1_cpair_beta; eauto.
        {
        eapply arrow_action_app; eauto.
        exact (urel_downward_leq _#6 Hj IH1ai).
        }
      eapply arrow_action_app; eauto.
      exact (urel_downward_leq _#6 Hj IH2ai).
      }

      {
      eapply arrow_action_app.
        {
        exact (urel_downward_leq _#6 Hj IH1bi).
        }
      eapply arrow_action_app; eauto.
      exact (urel_downward_leq _#6 Hj IH1ai).
      }
    }

    {
    apply (urel_zigzag _#4 (app (fromsp stop pg L) (app (tosp stop pg L) (ppi2 p))) (app (fromsp stop pg L) (app (tosp stop pg L) (ppi2 m)))); auto.
      {
      eapply arrow_action_app.
        {
        exact (urel_downward_leq _#6 Hj IH2bi).
        }
      eapply cpi2_cpair_beta; eauto.
        {
        eapply arrow_action_app; eauto.
        exact (urel_downward_leq _#6 Hj IH1ai).
        }
      eapply arrow_action_app; eauto.
      exact (urel_downward_leq _#6 Hj IH2ai).
      }

      {
      eapply arrow_action_app.
        {
        exact (urel_downward_leq _#6 Hj IH2bi).
        }
      eapply arrow_action_app; eauto.
      exact (urel_downward_leq _#6 Hj IH2ai).
      }
    }
  }

  (* kprod eta *)
  {
  clear IH1a IH1b IH1c IH2a IH2b IH2c.
  intros j a b Hj Hab.
  so (urel_closed _#5 Hab) as (Hcla & Hclb).
  cbn [fromsp tosp].
  match goal with
  | |- rel _ _ ?X _ =>
       eassert (equiv _ X) as Hequiv
  end.
    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    apply equiv_cpair.
      {
      apply equiv_app; [apply equiv_refl |].
      eapply equiv_trans.
        {
        apply equiv_ppi1.
        apply steps_equiv; apply star_one; apply step_app2.
        }
      simpsub.
      apply steps_equiv; apply star_one; apply step_ppi12.
      }

      {
      apply equiv_app; [apply equiv_refl |].
      eapply equiv_trans.
        {
        apply equiv_ppi2.
        apply steps_equiv; apply star_one; apply step_app2.
        }
      simpsub.
      apply steps_equiv; apply star_one; apply step_ppi22.
      }
    }
  refine (urel_equiv_1 _#6 _ Hequiv _); clear Hequiv; try prove_hygiene.
  apply (urel_zigzag _#4 (cpair (cpi1 b) (cpi2 b)) (cpair (cpi1 a) (cpi2 a))).
    {
    apply cpair_formation.
      {
      exact (IH1d j _ _ Hj (cpi1_formation _#6 Hab)).
      }

      {
      exact (IH2d j _ _ Hj (cpi2_formation _#6 Hab)).
      }
    }

    {
    apply cpair_formation; eauto using cpi1_formation, cpi2_formation.
    }

    {
    apply cpair_cpi_eta; auto.
    }
  }
}

(* kfut zero *)
{
intros pg s k Hclk.
eexists.
do2 4 split.
  {
  apply interp_fut_zero; auto.
  }

  {
  intros u v w Hu Hv Hw.
  replace (approx v (qfut qone)) with (qfut qone).
  2:{
    destruct v; auto.
    }
  replace (approx w (qfut qone)) with (qfut qone).
  2:{
    destruct w; auto.
    }
  cbn [tosp approx].
  apply arrow_action_lam; try prove_hygiene.
  intros j m p Hj Hmp.
  simpsub.
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  assert (j = 0) by omega; subst j.
  apply cnext_formation_zero; prove_hygiene.
  }

  {
  intros u v w Hu Hv Hw.
  replace (approx v (qfut qone)) with (qfut qone).
  2:{
    destruct v; auto.
    }
  replace (approx w (qfut qone)) with (qfut qone).
  2:{
    destruct w; auto.
    }
  cbn [fromsp approx].
  apply arrow_action_lam; try prove_hygiene.
  intros j m p Hj Hmp.
  simpsub.
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  assert (j = 0) by omega; subst j.
  cbn.
  apply fut_action_next_zero; try prove_hygiene.
  }

  {
  cbn [fromsp tosp].
  intros j m p Hj Hmp.
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  assert (j = 0) by omega; subst j.
  match goal with
  | |- rel _ _ ?X _ =>
     eassert (equiv _ X) as Hequiv
  end.
    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    apply equiv_refl.
    }
  refine (urel_equiv_1 _#6 _ Hequiv _).
    {
    prove_hygiene.
    }
  cbn in Hmp.
  decompose Hmp.
  intros _ q _ _ _ _ Hsteps _.
  do 2 eexists.
  do2 5 split; auto.
    {
    prove_hygiene.
    }

    {
    apply star_refl.
    }

    {
    exact Hsteps.
    }

    {
    intro H; omega.
    }
  }

  {
  cbn [fromsp tosp].
  intros j m p Hj Hmp.
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  assert (j = 0) by omega; subst j.
  match goal with
  | |- rel _ _ ?X _ =>
     eassert (equiv _ X) as Hequiv
  end.
    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    apply equiv_refl.
    }
  refine (urel_equiv_1 _#6 _ Hequiv _).
    {
    prove_hygiene.
    }
  exists tt.
  split.
    {
    apply cinterp_eval_refl.
    apply interp_cnext_zero.
    prove_hygiene.
    }

    {
    destruct Hmp as (x & _ & Hp).
    cbn in x.
    destruct x.
    exact Hp.
    }
  }
}

(* kfut *)
{
intros pg s i k K Hk IH.
destruct IH as (A & HA & IHa & IHb & IHc & IHd).
eexists.
do2 4 split.
  {
  apply interp_fut; eauto.
  }

  {
  clear IHb IHc IHd.
  assert (forall u,
            exists m,
              hygiene (permit clo) m
              /\ tosp stop pg (approx u (qfut K)) = lam (cnext m)) as Hform.
    {
    intros u.
    destruct u as [| u].
      {
      cbn.
      eexists.
      split.
      2:{
        reflexivity.
        }
      prove_hygiene.
      }
  
      {
      cbn.
      eexists.
      split.
      2:{
        reflexivity.
        }
      prove_hygiene.
      }
    }
  intros u v w Hu Hv Hw.
  destruct u as [| u].
    {
    so (Hform v) as (a & Hcla & Heqa).
    so (Hform w) as (b & Hclb & Heqb).
    rewrite -> Heqa, -> Heqb; clear Heqa Heqb.
    apply arrow_action_lam; try prove_hygiene.
    intros j m p Hj Hmp.
    so (urel_closed _#5 Hmp) as (Hclm & Hclp).
    assert (j = 0) by omega; subst j.
    simpsub.
    apply cnext_formation_zero; auto using hygiene_subst1.
    }
  assert (u <= i) as H by omega; renameover H into Hu.
  destruct v as [| v].
    {
    omega.
    }
  assert (u <= v) as H by omega; renameover H into Hv.
  destruct w as [| w].
    {
    omega.
    }
  assert (u <= w) as H by omega; renameover H into Hw.
  cbn [tosp approx].
  apply arrow_action_lam; try prove_hygiene.
    {
    cbn; omega.
    }
  intros j m p Hj Hmp.
  simpsub.
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  destruct j as [| j].
    {
    apply cnext_formation_zero; prove_hygiene.
    }
  assert (j <= u) as H by omega; renameover H into Hj.
  apply cnext_formation.
  refine (arrow_action_app _#9 (urel_downward_leq _#6 Hj (IHa u v w Hu Hv Hw)) _).
  eapply fut_action_prev; eauto.
  exact Hmp.
  }

  {
  clear IHa IHc IHd.
  assert (forall u,
            exists m,
              hygiene (permit clo) m
              /\ fromsp stop pg (approx u (qfut K)) = lam (next m)) as Hform.
    {
    intros u.
    destruct u as [| u].
      {
      cbn.
      eexists.
      split.
      2:{
        reflexivity.
        }
      prove_hygiene.
      }
  
      {
      cbn.
      eexists.
      split.
      2:{
        reflexivity.
        }
      prove_hygiene.
      }
    }
  intros u v w Hu Hv Hw.
  destruct u as [| u].
    {
    so (Hform v) as (a & Hcla & Heqa).
    so (Hform w) as (b & Hclb & Heqb).
    rewrite -> Heqa, -> Heqb; clear Heqa Heqb.
    apply arrow_action_lam; try prove_hygiene.
    intros j m p Hj Hmp.
    so (urel_closed _#5 Hmp) as (Hclm & Hclp).
    assert (j = 0) by omega; subst j.
    simpsub.
    cbn.
    apply fut_action_next_zero; try prove_hygiene; auto using hygiene_subst1.
    }
  assert (u <= i) as H by omega; renameover H into Hu.
  destruct v as [| v].
    {
    omega.
    }
  assert (u <= v) as H by omega; renameover H into Hv.
  destruct w as [| w].
    {
    omega.
    }
  assert (u <= w) as H by omega; renameover H into Hw.
  cbn [fromsp approx].
  apply arrow_action_lam; try prove_hygiene.
    {
    cbn; omega.
    }
  intros j m p Hj Hmp.
  simpsub.
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  rewrite -> den_iufut.
  destruct j as [| j].
    {
    apply fut_action_next_zero; try prove_hygiene.
    }
  assert (j <= u) as H by omega; renameover H into Hj.
  apply fut_action_next.
    {
    cbn; omega.
    }
  refine (arrow_action_app _#9 (urel_downward_leq _#6 Hj (IHb u v w Hu Hv Hw)) _).
  apply cprev_formation; auto.
  }

  {
  so (IHa i i i (le_refl _) (le_refl _) (le_refl _)) as IHai.
  so (IHb i i i (le_refl _) (le_refl _) (le_refl _)) as IHbi.
  rewrite <- (kbasic_impl_approx _#6 Hk) in IHai, IHbi.
  clear IHa IHb IHd.
  intros j m p Hj Hmp.
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  cbn [fromsp tosp].
  rewrite -> den_iufut in Hmp |- *.
  match goal with
  | |- rel _ _ ?X _ =>
     eassert (equiv _ X) as Hequiv
  end.
    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    apply equiv_next.
    apply equiv_app; [apply equiv_refl |].
    apply equiv_cprev.
    eapply equiv_trans.
      {
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    apply equiv_refl.
    }
  refine (urel_equiv_1 _#6 _ Hequiv _).
    {
    prove_hygiene.
    }
  so Hmp as (_ & p' & _ & _ & _ & _ & Hp' & _).  
  destruct j as [| j].
    {
    so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hp' Hclp)) as H; cbn in H.
    destruct H as (Hclp' & _).
    refine (urel_equiv_2 _#6 Hclp (equiv_symm _#3 (steps_equiv _#3 Hp')) _).
    apply fut_action_next_zero; try prove_hygiene.
    }
  assert (j <= i) as H by omega; renameover H into Hj.
  so (fut_action_prev _#6 Hmp) as Hpm_pp.
  so (IHc _ _ _ Hj Hpm_pp) as Hftpm_pp.
  so (arrow_action_app _#9 (urel_downward_leq _#6 Hj IHai) Hpm_pp) as Htpm_tpp.
  so (cprev_cnext_beta _#5 Htpm_tpp) as Hpntpm_tpp.
  so (arrow_action_app _#9 (urel_downward_leq _#6 Hj IHbi) Htpm_tpp) as Hftpm_ftpp.
  so (arrow_action_app _#9 (urel_downward_leq _#6 Hj IHbi) Hpntpm_tpp) as Hfpntpm_ftpp.
  so (urel_zigzag _#7 Hfpntpm_ftpp Hftpm_ftpp Hftpm_pp) as Hfpntpm_pp.
  eassert _ as H; [refine (fut_action_next _ (S i) _#4 _ Hfpntpm_pp) |].
    {
    cbn; omega.
    }
  refine (urel_equiv_2 _ (fut_urel stop (S i) (den A)) _#4 Hclp _ H); clear H.
  apply (equiv_trans _ _ (next p')).
  2:{
    apply equiv_symm.
    apply steps_equiv; auto.
    }
  apply equiv_next.
  eapply equiv_trans.
    {
    apply equiv_prev.
    apply steps_equiv; eauto.
    }
  apply steps_equiv; apply star_one.
  apply step_prev2.
  }

  {
  clear IHa IHb IHc.
  intros j a b Hj Hab.
  so (urel_closed _#5 Hab) as (Hcla & Hclb).
  cbn [fromsp tosp].
  match goal with
  | |- rel _ _ ?X _ =>
     eassert (equiv _ X) as Hequiv
  end.
    {
    apply equiv_symm.
    eapply equiv_trans.
      {
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    apply equiv_cnext.
    apply equiv_app; [apply equiv_refl |].
    eapply equiv_trans.
      {
      apply equiv_prev.
      apply steps_equiv; apply star_one; apply step_app2.
      }
    simpsub.
    apply steps_equiv; apply star_one.
    apply step_prev2.
    }
  refine (urel_equiv_1 _#6 _ Hequiv _); try prove_hygiene; clear Hequiv.
  destruct j as [| j].
    {
    destruct Hab as (x & Ha & Hb).
    exists x.
    split; auto.
    apply cinterp_eval_refl.
    cbn in x.
    destruct x.
    cbn.
    apply interp_cnext_zero.
    prove_hygiene.
    }
  assert (j <= i) as H by omega; renameover H into Hj.
  so (cnext_formation _#5 (IHd _ _ _ Hj (cprev_formation _#5 Hab))) as Hntfpa_npb.
  so (cnext_cprev_eta _#5 Hab) as Hnpa_b.
  so (cnext_formation _#5 (cprev_formation _#5 Hab)) as Hnpa_npb.
  exact (urel_zigzag _#7 Hntfpa_npb Hnpa_npb Hnpa_b).
  }
}

(* krec *)
{
intros pg s i k K _ IH.
destruct IH as (A & HA & H).
exists A.
split.
  {
  apply interp_rec; auto.
  }
exact H.
}

(* kinterp *)
{
intros pg s i k l K Hcl Hstepsl HintK IH.
destruct IH as (A & HA & H).
exists A.
split.
  {
  eapply interp_eval; eauto.
  }
exact H.
}

(* wrapup *)
{
intros pg s i k K HK.
destruct Hind as (H & _).
so (H _#5 HK) as (A & HA & Hspace).
exists A.
do2 2 split; auto.
eapply kbasic_impl_approx; eauto.
}
Qed.


Lemma spacify :
  forall pg s i k K A,
    kinterp pg s i k K
    -> interp toppg s i k A
    -> spacification pg i K A.
Proof.
intros pg s i k K A HK HA.
so (spacify_main _#5 HK) as (A' & HA' & H).
so (basic_fun _#7 HA HA'); subst A'.
exact H.
Qed.


Lemma spacification_tosp :
  forall pg i K A,
    spacification pg i K A
    -> rel (arrow_urel stop i (den A) (con_urel pg K)) i
         (tosp stop pg K) (tosp stop pg K).
Proof.
intros pg i K A Hspace.
destruct Hspace as (HeqK & Htosp & _).
so (Htosp i i i (le_refl _) (le_refl _) (le_refl _)) as H.
rewrite <- HeqK in H.
exact H.
Qed.


Lemma spacification_fromsp :
  forall pg i K A,
    spacification pg i K A
    -> rel (arrow_urel stop i (con_urel pg K) (den A)) i
          (fromsp stop pg K) (fromsp stop pg K).
Proof.
intros pg i K A Hspace.
destruct Hspace as (HeqK & _ & Hfromsp & _).
so (Hfromsp i i i (le_refl _) (le_refl _) (le_refl _)) as H.
rewrite <- HeqK in H.
exact H.
Qed.
