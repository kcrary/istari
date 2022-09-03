
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Axioms.
Require Import Tactics.
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
Require Import System.
Require Import Semantics.
Require Import SemanticsKnot.
Require Import Judgement.
Require Import Hygiene.
Require Import ProperClosed.
Require Import ProperFun.
Require Import Shut.
Require Import Candidate.

Require Import SemanticsPositive.
Require Import Ceiling.
Require Import Extend.
Require Import Truncate.
Require Import ExtendTruncate.
Require Import ProperDownward.
Require Import ProperLevel.
Require Import SemanticsMu.
Require Import SemanticsSubtype.
Require Import SemanticsProperty.
Require Import MapTerm.
Require Import Equivalence.
Require Import ProperEquiv.
Require Import Urelsp.
Require Import SemanticsPi.
Require Import SoundUtil.
Require Import Defined.
Require Import PageType.
Require Import SemanticsUniv.
Require Import Lattice.
Require Import SoundPositive.


Lemma lfp_is_mu_urel :
  forall w (F : wurel w -> wurel w) (h : monotone F),
    lfp (wurel_ccp w) F h
    =
    mu_urel w F.
Proof.
intros w F h.
apply lat_le_antisymm.
  {
  apply lfp_least.
  apply mu_prefix; auto.
  }

  {
  apply mu_least.
  apply (lfp_prefix (wurel_ccp w)).
  }
Qed.


Lemma extend_urel_mono :
  forall u v,
    impl incl incl (extend_urel u v).
Proof.
intros u v.
intros X Y Hincl.
intros i m p Hmp.
cbn.
apply Hincl; auto.
Qed.


Lemma extend_urel_comono :
  forall u v X Y,
    u <<= v
    -> incl (extend_urel u v X) (extend_urel u v Y)
    -> incl X Y.
Proof.
intros u v X Y Huv Hincl.
intros i m p Hmp.
rewrite <- (extend_term_cancel _ _ Huv m) in Hmp |- *.
rewrite <- (extend_term_cancel _ _ Huv p) in Hmp |- *.
apply Hincl; auto.
Qed.    


Lemma positive_negative_impl_monotone_antitone :
  forall w (h : w << stop) (X Y : wurel w),
    incl X Y
    -> (forall n a pg s i A B,
          positive n a
          -> interp pg s i (subst (under n (dot (exttin w X h) id)) a) A
          -> interp pg s i (subst (under n (dot (exttin w Y h) id)) a) B
          -> incl (den A) (den B))
       /\
       (forall n a pg s i A B,
          negative n a
          -> interp pg s i (subst (under n (dot (exttin w X h) id)) a) A
          -> interp pg s i (subst (under n (dot (exttin w Y h) id)) a) B
          -> incl (den B) (den A)).
Proof.
intros w h X Y Hincl.
exploit (positive_negative_ind (obj stop)
           (fun n a =>
              forall s pg z i A B,
                interp pg z i (subst (compose (under n (dot (exttin w X h) id)) s) a) A
                -> interp pg z i (subst (compose (under n (dot (exttin w Y h) id)) s) a) B
                -> incl (den A) (den B))
           (fun n a =>
              forall s pg z i A B,
                interp pg z i (subst (compose (under n (dot (exttin w X h) id)) s) a) A
                -> interp pg z i (subst (compose (under n (dot (exttin w Y h) id)) s) a) B
                -> incl (den B) (den A))) as Hind.

(* var *)
{
intros n s pg z i A B HintA HintB.
simpsubin HintA.
rewrite -> project_under_eq in HintA.
simpsubin HintA.
rewrite -> subst_exttin in HintA.
simpsubin HintB.
rewrite -> project_under_eq in HintB.
simpsubin HintB.
rewrite -> subst_exttin in HintB.
invert (basic_value_inv _#6 value_extt HintA).
intros ? R h'' _ Heq1 Heq2.
injection (objin_inj _ _ _ Heq1).
intros Heq ->.
injectionT Heq.
intros ->.
so (proof_irrelevance _ h h''); subst h''.
subst A.
clear Heq1.
invert (basic_value_inv _#6 value_extt HintB).
intros ? R h'' _ Heq1 Heq2.
injection (objin_inj _ _ _ Heq1).
intros Heq ->.
injectionT Heq.
intros ->.
so (proof_irrelevance _ h h''); subst h''.
subst B.
clear Heq1.
rewrite -> !den_extend_iurel.
rewrite -> !den_iutruncate.
intros j m p Hmp.
destruct Hmp as (Hj & Hmp).
split; auto.
}

(* const *)
{
intros n a s pg z i A B HintA HintB.
simpsubin HintA.
rewrite <- compose_assoc in HintA.
rewrite <- compose_under in HintA.
simpsubin HintA.
simpsubin HintB.
rewrite <- compose_assoc in HintB.
rewrite <- compose_under in HintB.
simpsubin HintB.
so (interp_fun _#7 HintA HintB); subst B.
apply incl_refl.
}

(* prod *)
{
intros n a b _ IH1 _ IH2 s pg z i ABX ABY HintX HintY.
simpsubin HintX.
simpsubin HintY.
invert (basic_value_inv _#6 value_prod HintX).
intros AX BX HintAX HintBX <-.
invert (basic_value_inv _#6 value_prod HintY).
intros AY BY HintAY HintBY <-.
cbn.
so (IH1 _#6 HintAX HintAY) as HinclA.
so (IH2 _#6 HintBX HintBY) as HinclB.
intros j m p Hmp.
cbn in Hmp.
decompose Hmp.
intros m1 p1 m2 p2 Hclm Hclp Hstepsm Hstepsp Hmp1 Hmp2.
exists m1, p1, m2, p2.
do2 5 split; auto.
}

(* pi *)
{
intros n a b _ IH1 _ IH2 s pg z i ABX ABY HintX HintY.
simpsubin HintX.
simpsubin HintY.
invert (basic_value_inv _#6 value_pi HintX).
intros AX BX HintAX HintBX <-.
invert (basic_value_inv _#6 value_pi HintY).
intros AY BY HintAY HintBY <-.
intros j m p Hmp.
cbn in Hmp.
decompose Hmp.
intros ml pl Hj Hclm Hclp Hstepsm Hstepsp Hact.
exists ml, pl.
do2 5 split; auto.
intros k q r Hk Hqr.
assert (k <= i) as Hki by omega.
so (IH1 _#6 HintAX HintAY) as HinclA.
so (HinclA _ _ _ Hqr) as Hqr'.
so (Hact _#3 Hk Hqr') as Hrel.
invert HintBX.
intros _ _ HactX.
so (HactX _#3 Hki Hqr') as HintBXqr.
clear HactX.
invert HintBY.
intros _ _ HactY.
so (HactY _#3 Hki Hqr) as HintBYqr.
clear HactY.
simpsubin HintBXqr.
simpsubin HintBYqr.
set (qr := if z then q else r) in HintBXqr, HintBYqr.
replace (subst (dot qr (compose (under n (dot (exttin w X h) id)) s)) b)
   with (subst (compose (under (S n) (dot (exttin w X h) id)) (dot qr s)) b) in HintBXqr by (simpsub; auto).
replace (subst (dot qr (compose (under n (dot (exttin w Y h) id)) s)) b)
   with (subst (compose (under (S n) (dot (exttin w Y h) id)) (dot qr s)) b) in HintBYqr by (simpsub; auto).
so (IH2 _#6 HintBXqr HintBYqr) as HinclB.
apply HinclB; auto.
}

(* sigma *)
{
intros n a b _ IH1 _ IH2 s pg z i ABX ABY HintX HintY.
simpsubin HintX.
simpsubin HintY.
invert (basic_value_inv _#6 value_sigma HintX).
intros AX BX HintAX HintBX <-.
invert (basic_value_inv _#6 value_sigma HintY).
intros AY BY HintAY HintBY <-.
so (IH1 _#6 HintAX HintAY) as HinclA.
intros j m p Hmp.
cbn in Hmp.
decompose Hmp.
intros m1 p1 m2 p2 Hmp1 Hclm Hclp Hstepsm Hstepsp Hmp2.
so (HinclA _#3 Hmp1) as Hmp1'.
so (basic_member_index _#9 HintAX Hmp1) as Hj.
exists m1, p1, m2, p2, Hmp1'.
do2 4 split; auto.
invert HintBX.
intros _ _ HactX.
so (HactX _#3 Hj Hmp1) as HintBXmp.
clear HactX.
invert HintBY.
intros _ _ HactY.
so (HactY _#3 Hj Hmp1') as HintBYmp.
clear HactY.
simpsubin HintBXmp.
simpsubin HintBYmp.
set (mp := if z then m1 else p1) in HintBXmp, HintBYmp.
replace (subst (dot mp (compose (under n (dot (exttin w X h) id)) s)) b)
   with (subst (compose (under (S n) (dot (exttin w X h) id)) (dot mp s)) b) in HintBXmp by (simpsub; auto).
replace (subst (dot mp (compose (under n (dot (exttin w Y h) id)) s)) b)
   with (subst (compose (under (S n) (dot (exttin w Y h) id)) (dot mp s)) b) in HintBYmp by (simpsub; auto).
so (IH2 _#6 HintBXmp HintBYmp) as HinclB.
apply HinclB; auto.
}

(* mu *)
{
rename Hincl into HinclXY.
intros n a _ IH s pg z i A B HintA HintB.
simpsubin HintA.
simpsubin HintB.
invert (basic_value_inv _#6 value_mu HintA).
intros u F Hu HactX _ HmonoF HrobA <-.
replace (subst (dot (var 0) (compose (under n (dot (exttin w X h) id)) (compose s sh1))) a)
   with (subst (compose (under (S n) (dot (exttin w X h) id)) (under 1 s)) a) in HrobA by (simpsub; auto).
so (le_ord_succ _ _ (le_ord_trans _#3 Hu (cin_top pg))) as Hu_stop.
change (u << stop) in Hu_stop.
so (lt_ord_impl_le_ord _ _ Hu_stop) as Hu_stop'.
invert (basic_value_inv _#6 value_mu HintB).
intros v G Hv HactY _ HmonoG HrobB <-.
replace (subst (dot (var 0) (compose (under n (dot (exttin w Y h) id)) (compose s sh1))) a)
   with (subst (compose (under (S n) (dot (exttin w Y h) id)) (under 1 s)) a) in HrobB by (simpsub; auto).
so (le_ord_succ _ _ (le_ord_trans _#3 Hv (cin_top pg))) as Hv_stop.
change (v << stop) in Hv_stop.
so (lt_ord_impl_le_ord _ _ Hv_stop) as Hv_stop'.
rewrite -> !den_iubase.
(* If we knew v <<= u, this would be much simpler and we wouldn't need fixpoint iteration. *)
rewrite <- (lfp_is_mu_urel u (fun Z => den (F Z)) HmonoF).
apply (fixpoint_iteration (wurel_ccp u) (fun Z => den (F Z))
         (fun Z => incl (extend_urel u stop Z) (extend_urel v stop (mu_urel v (fun Z => den (G Z)))))).
  {
  intros Z IHZ.
  (* We have two endpoints.  We need a mediating term that uses the higher level (u or v). *)
  so (le_lt_ord_dec u v) as [Huv | Hvu_lt].
    {
    so (HactX Z Hu_stop) as HintXZ.
    simpsubin HintXZ.
    replace (subst (dot (extt (objin (objsome (expair (qtype u) (iubase Z)) Hu_stop))) (compose (under n (dot (exttin w X h) id)) s)) a)
       with (subst (compose (under (S n) (dot (exttin w X h) id)) (dot (exttin u Z Hu_stop) s)) a)
       in HintXZ by (simpsub; auto).
    so (HactY (extend_urel u v Z) Hv_stop) as HintYZ.
    simpsubin HintYZ.
    replace (subst (dot (extt (objin (objsome (expair (qtype v) (iubase (extend_urel u v Z))) Hv_stop))) (compose (under n (dot (exttin w Y h) id)) s)) a)
       with (subst (compose (under (S n) (dot (exttin w Y h) id)) (dot (exttin v (extend_urel u v Z) Hv_stop) s)) a)
       in HintYZ by (simpsub; auto).
    exploit (raise_robust the_system pg z i (subst (compose (under (S n) (dot (exttin w X h) id)) (under 1 s)) a) u v Z (extend_urel u v Z) Hu_stop Hv_stop (extend_iurel (lt_ord_impl_le_ord u stop Hu_stop) (F Z))) as HintXZ'; auto.
      {
      apply extend_urel_compose_up; auto.
      }
    
      {
      simpsub.
      simpsubin HintXZ.
      exact HintXZ.
      }
    replace (subst1 (exttin v (extend_urel u v Z) Hv_stop) (subst (compose (under (S n) (dot (exttin w X h) id)) (under 1 s)) a))
       with (subst (compose (under (S n) (dot (exttin w X h) id)) (dot (exttin v (extend_urel u v Z) Hv_stop) s)) a)
       in HintXZ' by (simpsub; auto).
    so (IH _#6 HintXZ' HintYZ) as Hincl.
    rewrite -> !den_extend_iurel in Hincl.
    eapply incl_trans; eauto.
    clear Hincl.
    rewrite -> mu_fix; auto.
    apply extend_urel_mono.
    apply HmonoG.
    rewrite -> (extend_urel_compose_up u v stop Huv) in IHZ.
    eapply extend_urel_comono; eauto.
    }

    {
    so (lt_ord_impl_le_ord _ _ Hvu_lt) as Hvu; clear Hvu_lt.
    so (HactY (mu_urel v (fun Z => den (G Z))) Hv_stop) as HintYB.
    simpsubin HintYB.
    replace (subst (dot (extt (objin (objsome (expair (qtype v) (iubase (mu_urel v (fun Z => den (G Z))))) Hv_stop))) (compose (under n (dot (exttin w Y h) id)) s)) a)
       with (subst (compose (under (S n) (dot (exttin w Y h) id)) (dot (exttin v (mu_urel v (fun Z => den (G Z))) Hv_stop) s)) a)
       in HintYB by (simpsub; auto).
    so (HactX (extend_urel v u (mu_urel v (fun Z => den (G Z)))) Hu_stop) as HintXB.
    simpsubin HintXB.
    replace (subst (dot (extt (objin (objsome (expair (qtype u) (iubase (extend_urel v u (mu_urel v (fun Z => den (G Z)))))) Hu_stop))) (compose (under n (dot (exttin w X h) id)) s)) a)
       with (subst (compose (under (S n) (dot (exttin w X h) id)) (dot (exttin u (extend_urel v u (mu_urel v (fun Z => den (G Z)))) Hu_stop) s)) a)
       in HintXB by (simpsub; auto).
    exploit (raise_robust the_system pg z i (subst (compose (under (S n) (dot (exttin w Y h) id)) (under 1 s)) a) v u (mu_urel v (fun Z => den (G Z))) (extend_urel v u (mu_urel v (fun Z => den (G Z)))) Hv_stop Hu_stop (extend_iurel (lt_ord_impl_le_ord v stop Hv_stop) (G (mu_urel v (fun Z => den (G Z)))))) as HintYB'; auto.
      {
      apply extend_urel_compose_up; auto.
      }
    
      {
      simpsub.
      simpsubin HintYB.
      exact HintYB.
      }
    replace (subst1 (exttin u (extend_urel v u (mu_urel v (fun Z => den (G Z)))) Hu_stop) (subst (compose (under (S n) (dot (exttin w Y h) id)) (under 1 s)) a))
       with (subst (compose (under (S n) (dot (exttin w Y h) id)) (dot (exttin u (extend_urel v u (mu_urel v (fun Z => den (G Z)))) Hu_stop) s)) a)
         in HintYB' by (simpsub; auto).
    so (IH _#6 HintXB HintYB') as Hincl.
    rewrite -> !den_extend_iurel in Hincl.
    rewrite -> mu_fix; auto.
    eapply incl_trans; eauto.
    clear Hincl.
    apply extend_urel_mono.
    apply HmonoF.
    rewrite -> (extend_urel_compose_up v u stop Hvu) in IHZ.
    eapply extend_urel_comono; eauto.
    }
  }

  {
  intros C Hchain IHC.
  intros j m p Hmp.
  cbn in Hmp.
  destruct Hmp as (R & HCR & Hmp).
  so (IHC _ HCR) as Hincl.
  apply Hincl; auto.
  }
}

(* bite *)
{
intros n m a b _ IH1 _ IH2 s pg z i ABX ABY HintX HintY.
simpsubin HintX.
simpsubin HintY.
rewrite <- compose_assoc in HintX, HintY.
rewrite <- compose_under in HintX, HintY.
simpsubin HintX.
simpsubin HintY.
invert HintX.
intros c HclX Hstepsc Hintc.
invert HintY.
intros d HclY Hstepsd Hintd.
so (eval_bite_invert _#5 (conj Hstepsc (basicv_value _#6 Hintc))) as [(Hstepsm & Hstepsa) | (Hstepsm & Hstepsb)].
  {
  so (eval_bite_invert _#5 (conj Hstepsd (basicv_value _#6 Hintd))) as [(_ & Hstepsa') | (Hstepsm' & _)].
  2:{
    so (determinism_eval _#4 (conj Hstepsm value_btrue) (conj Hstepsm' value_bfalse)) as H.
    discriminate H.
    }
  assert (interp pg z i (subst (compose (under n (dot (exttin w X h) id)) s) a) ABX) as HintX'.
    {
    eapply interp_eval; eauto.
    refine (steps_hygiene _#4 _ HclX).
    eapply star_trans.
      {
      eapply (star_map _#4 (fun z => bite z _ _)); eauto using step_bite1.
      }
    apply star_one.
    apply step_bite2.
    }
  assert (interp pg z i (subst (compose (under n (dot (exttin w Y h) id)) s) a) ABY) as HintY'.
    {
    eapply interp_eval; eauto.
      {
      refine (steps_hygiene _#4 _ HclY).
      eapply star_trans.
        {
        eapply (star_map _#4 (fun z => bite z _ _)); eauto using step_bite1.
        }
      apply star_one.
      apply step_bite2.
      }
    }
  eapply IH1; eauto.
  }

  {
  so (eval_bite_invert _#5 (conj Hstepsd (basicv_value _#6 Hintd))) as [(Hstepsm' & _) | (_ & Hstepsb')].
  1:{
    so (determinism_eval _#4 (conj Hstepsm value_bfalse) (conj Hstepsm' value_btrue)) as H.
    discriminate H.
    }
  assert (interp pg z i (subst (compose (under n (dot (exttin w X h) id)) s) b) ABX) as HintX'.
    {
    eapply interp_eval; eauto.
    refine (steps_hygiene _#4 _ HclX).
    eapply star_trans.
      {
      eapply (star_map _#4 (fun z => bite z _ _)); eauto using step_bite1.
      }
    apply star_one.
    apply step_bite3.
    }
  assert (interp pg z i (subst (compose (under n (dot (exttin w Y h) id)) s) b) ABY) as HintY'.
    {
    eapply interp_eval; eauto.
      {
      refine (steps_hygiene _#4 _ HclY).
      eapply star_trans.
        {
        eapply (star_map _#4 (fun z => bite z _ _)); eauto using step_bite1.
        }
      apply star_one.
      apply step_bite3.
      }
    }
  eapply IH2; eauto.
  }
}

(* weaken *)
{
intros n a _ IH s pg z i A B HintA HintB.
simpsubin HintA.
simpsubin HintB.
rewrite <- compose_assoc in HintA, HintB.
rewrite -> compose_sh_under_eq in HintA, HintB.
simpsubin HintA.
simpsubin HintB.
rewrite -> subst_exttin in HintA, HintB.
exploit (IH (compose (sh n) s) pg z i A B); auto.
}

(* equiv *)
{
intros n a b Hequiv _ IH s pg z i AX AY HintX HintY.
apply (IH s pg z i).
  {
  refine (basic_equiv _#7 _ _ HintX); eauto using equiv_subst, reduce_equiv.
  refine (reduce_hygiene _#4 _ (basic_closed _#6 HintX)).
  apply reduce_subst; auto.
  }

  {
  refine (basic_equiv _#7 _ _ HintY); eauto using equiv_subst, reduce_equiv.
  refine (reduce_hygiene _#4 _ (basic_closed _#6 HintY)).
  apply reduce_subst; auto.
  }
}

(* const *)
{
intros n a s pg z i A B HintA HintB.
simpsubin HintA.
rewrite <- compose_assoc in HintA.
rewrite <- compose_under in HintA.
simpsubin HintA.
simpsubin HintB.
rewrite <- compose_assoc in HintB.
rewrite <- compose_under in HintB.
simpsubin HintB.
so (interp_fun _#7 HintA HintB); subst B.
apply incl_refl.
}

(* prod *)
{
intros n a b _ IH1 _ IH2 s pg z i ABX ABY HintX HintY.
simpsubin HintX.
simpsubin HintY.
invert (basic_value_inv _#6 value_prod HintX).
intros AX BX HintAX HintBX <-.
invert (basic_value_inv _#6 value_prod HintY).
intros AY BY HintAY HintBY <-.
cbn.
so (IH1 _#6 HintAX HintAY) as HinclA.
so (IH2 _#6 HintBX HintBY) as HinclB.
intros j m p Hmp.
cbn in Hmp.
decompose Hmp.
intros m1 p1 m2 p2 Hclm Hclp Hstepsm Hstepsp Hmp1 Hmp2.
exists m1, p1, m2, p2.
do2 5 split; auto.
}

(* pi *)
{
intros n a b _ IH1 _ IH2 s pg z i ABX ABY HintX HintY.
simpsubin HintX.
simpsubin HintY.
invert (basic_value_inv _#6 value_pi HintX).
intros AX BX HintAX HintBX <-.
invert (basic_value_inv _#6 value_pi HintY).
intros AY BY HintAY HintBY <-.
intros j m p Hmp.
cbn in Hmp.
decompose Hmp.
intros ml pl Hj Hclm Hclp Hstepsm Hstepsp Hact.
exists ml, pl.
do2 5 split; auto.
intros k q r Hk Hqr.
assert (k <= i) as Hki by omega.
so (IH1 _#6 HintAX HintAY) as HinclA.
so (HinclA _ _ _ Hqr) as Hqr'.
so (Hact _#3 Hk Hqr') as Hrel.
invert HintBX.
intros _ _ HactX.
so (HactX _#3 Hki Hqr) as HintBXqr.
clear HactX.
invert HintBY.
intros _ _ HactY.
so (HactY _#3 Hki Hqr') as HintBYqr.
clear HactY.
simpsubin HintBXqr.
simpsubin HintBYqr.
set (qr := if z then q else r) in HintBXqr, HintBYqr.
replace (subst (dot qr (compose (under n (dot (exttin w X h) id)) s)) b)
   with (subst (compose (under (S n) (dot (exttin w X h) id)) (dot qr s)) b) in HintBXqr by (simpsub; auto).
replace (subst (dot qr (compose (under n (dot (exttin w Y h) id)) s)) b)
   with (subst (compose (under (S n) (dot (exttin w Y h) id)) (dot qr s)) b) in HintBYqr by (simpsub; auto).
so (IH2 _#6 HintBXqr HintBYqr) as HinclB.
apply HinclB; auto.
}

(* sigma *)
{
intros n a b _ IH1 _ IH2 s pg z i ABX ABY HintX HintY.
simpsubin HintX.
simpsubin HintY.
invert (basic_value_inv _#6 value_sigma HintX).
intros AX BX HintAX HintBX <-.
invert (basic_value_inv _#6 value_sigma HintY).
intros AY BY HintAY HintBY <-.
so (IH1 _#6 HintAX HintAY) as HinclA.
intros j m p Hmp.
cbn in Hmp.
decompose Hmp.
intros m1 p1 m2 p2 Hmp1 Hclm Hclp Hstepsm Hstepsp Hmp2.
so (HinclA _#3 Hmp1) as Hmp1'.
so (basic_member_index _#9 HintAY Hmp1) as Hj.
exists m1, p1, m2, p2, Hmp1'.
do2 4 split; auto.
invert HintBX.
intros _ _ HactX.
so (HactX _#3 Hj Hmp1') as HintBXmp.
clear HactX.
invert HintBY.
intros _ _ HactY.
so (HactY _#3 Hj Hmp1) as HintBYmp.
clear HactY.
simpsubin HintBXmp.
simpsubin HintBYmp.
set (mp := if z then m1 else p1) in HintBXmp, HintBYmp.
replace (subst (dot mp (compose (under n (dot (exttin w X h) id)) s)) b)
   with (subst (compose (under (S n) (dot (exttin w X h) id)) (dot mp s)) b) in HintBXmp by (simpsub; auto).
replace (subst (dot mp (compose (under n (dot (exttin w Y h) id)) s)) b)
   with (subst (compose (under (S n) (dot (exttin w Y h) id)) (dot mp s)) b) in HintBYmp by (simpsub; auto).
so (IH2 _#6 HintBXmp HintBYmp) as HinclB.
apply HinclB; auto.
}

(* mu *)
{
rename Hincl into HinclXY.
rename X into Z.
rename Y into X.
rename Z into Y.
intros n a _ IH s pg z i B A HintB HintA.
simpsubin HintA.
simpsubin HintB.
invert (basic_value_inv _#6 value_mu HintA).
intros u F Hu HactX _ HmonoF HrobA <-.
replace (subst (dot (var 0) (compose (under n (dot (exttin w X h) id)) (compose s sh1))) a)
   with (subst (compose (under (S n) (dot (exttin w X h) id)) (under 1 s)) a) in HrobA by (simpsub; auto).
so (le_ord_succ _ _ (le_ord_trans _#3 Hu (cin_top pg))) as Hu_stop.
change (u << stop) in Hu_stop.
so (lt_ord_impl_le_ord _ _ Hu_stop) as Hu_stop'.
invert (basic_value_inv _#6 value_mu HintB).
intros v G Hv HactY _ HmonoG HrobB <-.
replace (subst (dot (var 0) (compose (under n (dot (exttin w Y h) id)) (compose s sh1))) a)
   with (subst (compose (under (S n) (dot (exttin w Y h) id)) (under 1 s)) a) in HrobB by (simpsub; auto).
so (le_ord_succ _ _ (le_ord_trans _#3 Hv (cin_top pg))) as Hv_stop.
change (v << stop) in Hv_stop.
so (lt_ord_impl_le_ord _ _ Hv_stop) as Hv_stop'.
rewrite -> !den_iubase.
(* If we knew v <<= u, this would be much simpler and we wouldn't need fixpoint iteration. *)
rewrite <- (lfp_is_mu_urel u (fun Z => den (F Z)) HmonoF).
apply (fixpoint_iteration (wurel_ccp u) (fun Z => den (F Z))
         (fun Z => incl (extend_urel u stop Z) (extend_urel v stop (mu_urel v (fun Z => den (G Z)))))).
  {
  intros Z IHZ.
  (* We have two endpoints.  We need a mediating term that uses the higher level (u or v). *)
  so (le_lt_ord_dec u v) as [Huv | Hvu_lt].
    {
    so (HactX Z Hu_stop) as HintXZ.
    simpsubin HintXZ.
    replace (subst (dot (extt (objin (objsome (expair (qtype u) (iubase Z)) Hu_stop))) (compose (under n (dot (exttin w X h) id)) s)) a)
       with (subst (compose (under (S n) (dot (exttin w X h) id)) (dot (exttin u Z Hu_stop) s)) a)
       in HintXZ by (simpsub; auto).
    so (HactY (extend_urel u v Z) Hv_stop) as HintYZ.
    simpsubin HintYZ.
    replace (subst (dot (extt (objin (objsome (expair (qtype v) (iubase (extend_urel u v Z))) Hv_stop))) (compose (under n (dot (exttin w Y h) id)) s)) a)
       with (subst (compose (under (S n) (dot (exttin w Y h) id)) (dot (exttin v (extend_urel u v Z) Hv_stop) s)) a)
       in HintYZ by (simpsub; auto).
    exploit (raise_robust the_system pg z i (subst (compose (under (S n) (dot (exttin w X h) id)) (under 1 s)) a) u v Z (extend_urel u v Z) Hu_stop Hv_stop (extend_iurel (lt_ord_impl_le_ord u stop Hu_stop) (F Z))) as HintXZ'; auto.
      {
      apply extend_urel_compose_up; auto.
      }
    
      {
      simpsub.
      simpsubin HintXZ.
      exact HintXZ.
      }
    replace (subst1 (exttin v (extend_urel u v Z) Hv_stop) (subst (compose (under (S n) (dot (exttin w X h) id)) (under 1 s)) a))
       with (subst (compose (under (S n) (dot (exttin w X h) id)) (dot (exttin v (extend_urel u v Z) Hv_stop) s)) a)
       in HintXZ' by (simpsub; auto).
    so (IH _#6 HintYZ HintXZ') as Hincl.
    rewrite -> !den_extend_iurel in Hincl.
    eapply incl_trans; eauto.
    clear Hincl.
    rewrite -> mu_fix; auto.
    apply extend_urel_mono.
    apply HmonoG.
    rewrite -> (extend_urel_compose_up u v stop Huv) in IHZ.
    eapply extend_urel_comono; eauto.
    }

    {
    so (lt_ord_impl_le_ord _ _ Hvu_lt) as Hvu; clear Hvu_lt.
    so (HactY (mu_urel v (fun Z => den (G Z))) Hv_stop) as HintYB.
    simpsubin HintYB.
    replace (subst (dot (extt (objin (objsome (expair (qtype v) (iubase (mu_urel v (fun Z => den (G Z))))) Hv_stop))) (compose (under n (dot (exttin w Y h) id)) s)) a)
       with (subst (compose (under (S n) (dot (exttin w Y h) id)) (dot (exttin v (mu_urel v (fun Z => den (G Z))) Hv_stop) s)) a)
       in HintYB by (simpsub; auto).
    so (HactX (extend_urel v u (mu_urel v (fun Z => den (G Z)))) Hu_stop) as HintXB.
    simpsubin HintXB.
    replace (subst (dot (extt (objin (objsome (expair (qtype u) (iubase (extend_urel v u (mu_urel v (fun Z => den (G Z)))))) Hu_stop))) (compose (under n (dot (exttin w X h) id)) s)) a)
       with (subst (compose (under (S n) (dot (exttin w X h) id)) (dot (exttin u (extend_urel v u (mu_urel v (fun Z => den (G Z)))) Hu_stop) s)) a)
       in HintXB by (simpsub; auto).
    exploit (raise_robust the_system pg z i (subst (compose (under (S n) (dot (exttin w Y h) id)) (under 1 s)) a) v u (mu_urel v (fun Z => den (G Z))) (extend_urel v u (mu_urel v (fun Z => den (G Z)))) Hv_stop Hu_stop (extend_iurel (lt_ord_impl_le_ord v stop Hv_stop) (G (mu_urel v (fun Z => den (G Z)))))) as HintYB'; auto.
      {
      apply extend_urel_compose_up; auto.
      }
    
      {
      simpsub.
      simpsubin HintYB.
      exact HintYB.
      }
    replace (subst1 (exttin u (extend_urel v u (mu_urel v (fun Z => den (G Z)))) Hu_stop) (subst (compose (under (S n) (dot (exttin w Y h) id)) (under 1 s)) a))
       with (subst (compose (under (S n) (dot (exttin w Y h) id)) (dot (exttin u (extend_urel v u (mu_urel v (fun Z => den (G Z)))) Hu_stop) s)) a)
         in HintYB' by (simpsub; auto).
    so (IH _#6 HintYB' HintXB) as Hincl.
    rewrite -> !den_extend_iurel in Hincl.
    rewrite -> mu_fix; auto.
    eapply incl_trans; eauto.
    clear Hincl.
    apply extend_urel_mono.
    apply HmonoF.
    rewrite -> (extend_urel_compose_up v u stop Hvu) in IHZ.
    eapply extend_urel_comono; eauto.
    }
  }

  {
  intros C Hchain IHC.
  intros j m p Hmp.
  cbn in Hmp.
  destruct Hmp as (R & HCR & Hmp).
  so (IHC _ HCR) as Hincl.
  apply Hincl; auto.
  }
}

(* bite *)
{
intros n m a b _ IH1 _ IH2 s pg z i ABX ABY HintX HintY.
simpsubin HintX.
simpsubin HintY.
rewrite <- compose_assoc in HintX, HintY.
rewrite <- compose_under in HintX, HintY.
simpsubin HintX.
simpsubin HintY.
invert HintX.
intros c HclX Hstepsc Hintc.
invert HintY.
intros d HclY Hstepsd Hintd.
so (eval_bite_invert _#5 (conj Hstepsc (basicv_value _#6 Hintc))) as [(Hstepsm & Hstepsa) | (Hstepsm & Hstepsb)].
  {
  so (eval_bite_invert _#5 (conj Hstepsd (basicv_value _#6 Hintd))) as [(_ & Hstepsa') | (Hstepsm' & _)].
  2:{
    so (determinism_eval _#4 (conj Hstepsm value_btrue) (conj Hstepsm' value_bfalse)) as H.
    discriminate H.
    }
  assert (interp pg z i (subst (compose (under n (dot (exttin w X h) id)) s) a) ABX) as HintX'.
    {
    eapply interp_eval; eauto.
    refine (steps_hygiene _#4 _ HclX).
    eapply star_trans.
      {
      eapply (star_map _#4 (fun z => bite z _ _)); eauto using step_bite1.
      }
    apply star_one.
    apply step_bite2.
    }
  assert (interp pg z i (subst (compose (under n (dot (exttin w Y h) id)) s) a) ABY) as HintY'.
    {
    eapply interp_eval; eauto.
      {
      refine (steps_hygiene _#4 _ HclY).
      eapply star_trans.
        {
        eapply (star_map _#4 (fun z => bite z _ _)); eauto using step_bite1.
        }
      apply star_one.
      apply step_bite2.
      }
    }
  eapply IH1; eauto.
  }

  {
  so (eval_bite_invert _#5 (conj Hstepsd (basicv_value _#6 Hintd))) as [(Hstepsm' & _) | (_ & Hstepsb')].
  1:{
    so (determinism_eval _#4 (conj Hstepsm value_bfalse) (conj Hstepsm' value_btrue)) as H.
    discriminate H.
    }
  assert (interp pg z i (subst (compose (under n (dot (exttin w X h) id)) s) b) ABX) as HintX'.
    {
    eapply interp_eval; eauto.
    refine (steps_hygiene _#4 _ HclX).
    eapply star_trans.
      {
      eapply (star_map _#4 (fun z => bite z _ _)); eauto using step_bite1.
      }
    apply star_one.
    apply step_bite3.
    }
  assert (interp pg z i (subst (compose (under n (dot (exttin w Y h) id)) s) b) ABY) as HintY'.
    {
    eapply interp_eval; eauto.
      {
      refine (steps_hygiene _#4 _ HclY).
      eapply star_trans.
        {
        eapply (star_map _#4 (fun z => bite z _ _)); eauto using step_bite1.
        }
      apply star_one.
      apply step_bite3.
      }
    }
  eapply IH2; eauto.
  }
}

(* weaken *)
{
intros n a _ IH s pg z i A B HintA HintB.
simpsubin HintA.
simpsubin HintB.
rewrite <- compose_assoc in HintA, HintB.
rewrite -> compose_sh_under_eq in HintA, HintB.
simpsubin HintA.
simpsubin HintB.
rewrite -> subst_exttin in HintA, HintB.
exploit (IH (compose (sh n) s) pg z i A B); auto.
}

(* equiv *)
{
intros n a b Hequiv _ IH s pg z i AX AY HintX HintY.
apply (IH s pg z i).
  {
  refine (basic_equiv _#7 _ _ HintX); eauto using equiv_subst, reduce_equiv.
  refine (reduce_hygiene _#4 _ (basic_closed _#6 HintX)).
  apply reduce_subst; auto.
  }

  {
  refine (basic_equiv _#7 _ _ HintY); eauto using equiv_subst, reduce_equiv.
  refine (reduce_hygiene _#4 _ (basic_closed _#6 HintY)).
  apply reduce_subst; auto.
  }
}

(* epilogue *)
{
destruct Hind as (IHpos & IHneg).
split.
  {
  intros n a pg s i A B Hpos HintA HintB.
  exploit (IHpos _ _ Hpos id pg s i A B) as H; simpsub; auto.
  }

  {
  intros n a pg s i A B Hneg HintA HintB.
  exploit (IHneg _ _ Hneg id pg s i A B) as H; simpsub; auto.
  }
}
Qed.


Lemma positive_impl_monotone :
  forall n a w X Y pg s i A B (h : w << stop),
    positive n a
    -> incl X Y
    -> interp pg s i (subst (under n (dot (exttin w X h) id)) a) A
    -> interp pg s i (subst (under n (dot (exttin w Y h) id)) a) B
    -> incl (den A) (den B).
Proof.
intros n a w X Y pg s i A B h Hpos Hincl HintA HintB.
exact (positive_negative_impl_monotone_antitone w h X Y Hincl andel n a pg s i A B Hpos HintA HintB).
Qed.


Lemma extract_ind :
  forall pg i a b,
    (forall j (X Y : car (wurel_ofe (cin pg))) (h : cin pg << stop),
       j <= i
       -> dist (S j) X Y
       -> exists R,
            interp pg true j (subst1 (exttin (cin pg) X h) a) R
            /\ interp pg false j (subst1 (exttin (cin pg) Y h) b) R)
    -> exists (F : wurel_ofe (cin pg) -n> wiurel_ofe (cin pg)),
         forall (X : wurel (cin pg)) (h : cin pg << stop) (h' : cin pg <<= stop),
           interp pg true i (subst1 (exttin (cin pg) X h) a) (extend_iurel h' (pi1 F X))
           /\ interp pg false i (subst1 (exttin (cin pg) X h) b) (extend_iurel h' (pi1 F X)).
Proof.
intros pg i a b Hact.
set (w := cin pg).
so (le_ord_succ _ _ (cin_top pg)) as h.
change (cin pg << stop) in h.
so (lt_ord_impl_le_ord _ _ h) as h'.
exploit (choice (car (wurel_ofe w)) (car (wiurel_ofe w))
           (fun X R =>
              interp pg true i (subst1 (exttin w X h) a) (extend_iurel h' R)
              /\ interp pg false i (subst1 (exttin w X h) b) (extend_iurel h' R))) as H.
  {
  intros X.
  so (Hact i X X h (le_refl _) (dist_refl _ _ _)) as (R & Hl & Hr).
  so (interp_level_internal _#5 h' Hl) as (R' & ->).
  exists R'.
  split; auto.
  intros R''.
  intros (Hl' & _).
  so (interp_fun _#7 Hl Hl') as Heq.
  so (extend_iurel_inj _#5 Heq); subst R''.
  reflexivity.
  }
destruct H as (F & HF).
assert (nonexpansive F) as Hne.
  {
  intros j X Y Hdist.
  destruct j as [| j].
    {
    apply dist_zero.
    }
  so (le_lt_dec j i) as [Hji | Hlt].
    {
    apply (dist_trans _ _ _ (iutruncate (S j) (F X))).
      {
      apply dist_symm.
      apply iutruncate_near.
      }
    apply (dist_trans _ _ _ (iutruncate (S j) (F Y))).
    2:{
      apply iutruncate_near.
      }
    apply dist_refl'.
    so (HF X) as (Hli & _).
    so (HF Y) as (_ & Hri).
    so (Hact j X Y h Hji Hdist) as (R & Hlj & Hrj).
    so (basic_downward _#7 Hji Hli) as Hlj'.
    so (basic_downward _#7 Hji Hri) as Hrj'.
    so (interp_fun _#7 Hlj Hlj'); subst R.
    so (interp_fun _#7 Hrj Hrj') as Heq.
    rewrite -> !iutruncate_extend_iurel in Heq.
    exact (extend_iurel_inj _#5 Heq).
    }

    {
    assert (S i <= S j) as Hij by omega.
    apply dist_refl'.
    so (Hact i X Y h (le_refl _) (dist_downward_leq _#5 Hij Hdist)) as (R & Hl & Hr).
    so (HF X) as (Hl' & _).
    so (HF Y) as (_ & Hr').
    so (interp_fun _#7 Hl Hl'); subst R.
    so (interp_fun _#7 Hr Hr') as Heq.
    exact (extend_iurel_inj _#5 Heq).
    }
  }
exists (expair F Hne).
intros X h'' h'''.
so (proof_irrelevance _ h h''); subst h''.
so (proof_irrelevance _ h' h'''); subst h'''.
so (HF X) as (Hl & Hr).
split; auto.
Qed.


Lemma extract_ind_multi :
  forall pg i a a' b b',
    (forall j (X Y : car (wurel_ofe (cin pg))) (h : cin pg << stop),
       j <= i
       -> dist (S j) X Y
       -> exists R,
            interp pg true j (subst1 (exttin (cin pg) X h) a) R
            /\ interp pg false j (subst1 (exttin (cin pg) Y h) a') R
            /\ interp pg true j (subst1 (exttin (cin pg) X h) b) R
            /\ interp pg false j (subst1 (exttin (cin pg) Y h) b') R)
    -> exists (F : wurel_ofe (cin pg) -n> wiurel_ofe (cin pg)),
         forall (X : wurel (cin pg)) (h : cin pg << stop) (h' : cin pg <<= stop),
           interp pg true i (subst1 (exttin (cin pg) X h) a) (extend_iurel h' (pi1 F X))
           /\ interp pg false i (subst1 (exttin (cin pg) X h) a') (extend_iurel h' (pi1 F X))
           /\ interp pg true i (subst1 (exttin (cin pg) X h) b) (extend_iurel h' (pi1 F X))
           /\ interp pg false i (subst1 (exttin (cin pg) X h) b') (extend_iurel h' (pi1 F X)).
Proof.
intros pg i a b c d Hact.
exploit (extract_ind pg i a b) as (F1 & HF1).
  {
  intros j X Y h Hj HXY.
  so (Hact j X Y h Hj HXY) as (R & Ha & Hb & _).
  eauto.
  }
exploit (extract_ind pg i c d) as (F2 & HF2).
  {
  intros j X Y h Hj HXY.
  so (Hact j X Y h Hj HXY) as (R & _ & _ & Hc & Hd).
  eauto.
  }
exploit (extract_ind pg i a d) as (F & HF).
  {
  intros j X Y h Hj HXY.
  so (Hact j X Y h Hj HXY) as (R & Ha & _ & _ & Hd).
  eauto.
  }
exists F.
intros X h h'.
so (HF X h h') as (Ha & Hd).
do2 3 split; auto.
  {
  so (HF1 X h h') as (Ha' & Hb).
  so (interp_fun _#7 Ha Ha') as Heq.
  rewrite -> (extend_iurel_inj _#5 Heq).
  exact Hb.
  }

  {
  so (HF2 X h h') as (Hc & Hd').
  so (interp_fun _#7 Hd Hd') as Heq.
  rewrite -> (extend_iurel_inj _#5 Heq).
  exact Hc.
  }
Qed.


Lemma pwctx_cons_exttin :
  forall w i (X Y : car (wurel_ofe w)) h s s' G,
    w <<= top
    -> dist (S i) X Y
    -> pwctx i s s' G
    -> pwctx i (dot (exttin w X h) s) (dot (exttin w Y h) s') (hyp_tp :: G).
Proof.
intros w i X Y h s s' G Hw Hdist Hs.
apply pwctx_cons_tp; auto.
apply (seqhyp_tp _#3 (extend_iurel (lt_ord_impl_le_ord _ _ h) (iutruncate (S i) (iubase X)))).
  {
  apply interp_eval_refl.
  apply interp_extt; auto.
  }

  {
  replace (iutruncate (S i) (iubase X)) with (iutruncate (S i) (iubase Y)).
  2:{
    symmetry.
    rewrite -> !iutruncate_iubase.
    f_equal.
    apply ceiling_collapse; auto.
    }
  apply interp_eval_refl.
  apply interp_extt; auto.
  }
Qed.


Lemma pwctx_cons_exttin_univ :
  forall pg w i (X Y : car (wurel_ofe w)) h lv s s' G,
    w <<= cin pg
    -> pginterp (subst s lv) pg
    -> pginterp (subst s' lv) pg
    -> (forall j t t',
          j <= i
          -> pwctx j t t' G
          -> exists pg',
               pginterp (subst t lv) pg'
               /\ pginterp (subst t' lv) pg')
    -> dist (S i) X Y
    -> pwctx i s s' G
    -> pwctx i (dot (exttin w X h) s) (dot (exttin w Y h) s') (hyp_tm (univ lv) :: G).
Proof.
intros pg w i X Y h lv s s' G Hw Hlvl Hlvr Hlvfunc Hdist Hs.
so (pginterp_lt_top _ _ Hlvl) as Hltpg.
apply pwctx_cons_tm; auto.
  {
  apply (seqhyp_tm _#5 (iuuniv the_system i pg)).
    {
    simpsub.
    apply interp_eval_refl.
    destruct Hltpg.
    apply interp_univ; auto.
    }

    {
    simpsub.
    apply interp_eval_refl.
    destruct Hltpg.
    apply interp_univ; auto.
    }

    {
    split; auto.
    exists (extend_iurel (lt_ord_impl_le_ord _ _ h) (iutruncate (S i) (iubase X))).
    rewrite -> sint_unroll.
    split.
      {
      apply interp_eval_refl.
      apply interp_extt; auto.
      }

      {
      replace (iutruncate (S i) (iubase X)) with (iutruncate (S i) (iubase Y)).
      2:{
        symmetry.
        rewrite -> !iutruncate_iubase.
        f_equal.
        apply ceiling_collapse; auto.
        }
      apply interp_eval_refl.
      apply interp_extt; auto.
      }
    }
  }

  {
  intros j s'' Hj Hs'.
  simpsub.
  so (Hlvfunc _#3 Hj Hs') as (pg' & Hl & Hr).
  so (pginterp_fun _#3 Hlvl Hl); subst pg'.
  eapply relhyp_tm; eauto.
    {
    apply interp_eval_refl.
    destruct Hltpg.
    apply interp_univ; eauto.
    }

    {
    apply interp_eval_refl.
    destruct Hltpg.
    apply interp_univ; eauto.
    }
  }

  {
  intros j s'' Hj Hs'.
  simpsub.
  so (Hlvfunc _#3 Hj Hs') as (pg' & Hl & Hr).
  so (pginterp_fun _#3 Hlvr Hr); subst pg'.
  eapply relhyp_tm; eauto.
    {
    apply interp_eval_refl.
    destruct Hltpg.
    apply interp_univ; eauto.
    }

    {
    apply interp_eval_refl.
    destruct Hltpg.
    apply interp_univ; eauto.
    }
  }
Qed.


Lemma pwctx_cons_exttin_tm :
  forall pg w i (X Y : car (wurel_ofe w)) h s s' G lv,
    w <<= cin pg
    -> pginterp (subst s lv) pg
    -> seq G (deq lv lv pagetp)
    -> dist (S i) X Y
    -> pwctx i s s' G
    -> pwctx i (dot (exttin w X h) s) (dot (exttin w Y h) s') (hyp_tm (univ lv) :: G).
Proof.
intros pg w i X Y h s s' G lv Hw Hlvl Hseqlv Hdist Hs.
rewrite -> seq_deq in Hseqlv.
so (Hseqlv _#3 Hs) as (R & HR & _ & Hlv & _).
so (interp_pagetp_invert _#7 HR Hlv) as (pg' & Hlvl' & Hlvr).
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
so (pginterp_lt_top _ _ Hlvl) as (Hltstr, Hltcex).
apply pwctx_cons_tm_seq; auto.
  {
  apply (seqhyp_tm _#5 (iuuniv the_system i pg)).
    {
    simpsub.
    apply interp_eval_refl.
    apply interp_univ; eauto.
    }

    {
    simpsub.
    apply interp_eval_refl.
    apply interp_univ; eauto.
    }

    {
    cbn.
    split; auto.
    exists (extend_iurel (lt_ord_impl_le_ord _ _ h) (iutruncate (S i) (iubase X))).
    rewrite -> sint_unroll.
    split.
      {
      apply interp_eval_refl.
      apply interp_extt; auto.
      }
  
      {
      replace (iutruncate (S i) (iubase X)) with (iutruncate (S i) (iubase Y)).
      2:{
        symmetry.
        rewrite -> !iutruncate_iubase.
        f_equal.
        apply ceiling_collapse; auto.
        }
      apply interp_eval_refl.
      apply interp_extt; auto.
      }
    }
  }

  {
  clear pg Hw R HR Hlv Hlvl Hlvr Hlvl' Hltstr Hltcex.
  intros j t t' Ht.
  so (Hseqlv _#3 Ht) as (R & HR & _ & Hlv & _).
  so (interp_pagetp_invert _#7 HR Hlv) as (pg & Hlvl & Hlvr).
  exists toppg, (iuuniv the_system j pg).
  simpsub.
  so (pginterp_lt_top _ _ Hlvl) as (Hltstr, Hltcex).
  split; apply interp_eval_refl; apply interp_univ; auto.
  }
Qed.


Lemma monotone_from_ispositive :
  forall pg a G (F : wurel (cin pg) -> wiurel (cin pg)),
    (forall i s s',
       pwctx i s s' G
       -> positive 0 (subst (under 1 s) a) /\ positive 0 (subst (under 1 s') a))
    -> forall i s s',
         pwctx i s s' G
         -> (forall (X : wurel (cin pg)) (h : cin pg << stop) (h' : cin pg <<= stop),
               interp pg true i (subst (dot (exttin (cin pg) X h) s) a) (extend_iurel h' (F X)))
         -> monotone (fun X => den (F X)).
Proof.
intros pg a G F Hispos i s s' Hs Hact.
so (Hispos _#3 Hs) as (Hpos & _).
intros X Y Hincl.
so (le_ord_succ _ _ (cin_top pg)) as h.
change (cin pg << stop) in h.
so (cin_stop pg) as h'.
so (Hact X h h') as HX.
so (Hact Y h h') as HY.
exploit (positive_impl_monotone 0 (subst (under 1 s) a) (cin pg) X Y pg true i (extend_iurel h' (F X)) (extend_iurel h' (F Y)) h) as H; auto; try (simpsub; auto; done).
eapply extend_urel_comono; eauto.
Qed.


Lemma sound_mu_formation :
  forall G a b,
    pseq (hyp_tp :: G) (deqtype a b)
    -> pseq G (deq triv triv (ispositive a))
    -> pseq G (deq triv triv (ispositive b))
    -> pseq G (deqtype (mu a) (mu b)).
Proof.
intros G a b.
revert G.
refine (seq_pseq 2 [hyp_tp] a [hyp_tp] b 3 [_] _ [] _ [] _ _ _); cbn.
intros G Hcla Hclb Hab Hisroba Hisrobb.
rewrite -> seq_eqtype in Hab |- *.
rewrite -> seq_ispositive in Hisroba, Hisrobb; auto.
intros i s s' Hs.
simpsub.
exploit (extract_ind_multi toppg i (subst (under 1 s) a) (subst (under 1 s') a) (subst (under 1 s) b) (subst (under 1 s') b)) as H.
  {
  intros j X Y h Hj HXY.
  so (pwctx_cons_exttin top j X Y h s s' G (le_ord_refl _) HXY (pwctx_downward _#5 Hj Hs)) as Hss.
  so (Hab _ _ _ Hss) as (R & Hal & Har & Hbl & Hbr).
  exists R.
  simpsub.
  auto.
  }
destruct H as (F & HF).
assert (nonexpansive (fun X => den (pi1 F X))) as Hne.
  {
  apply compose_ne_ne; auto using den_nonexpansive.
  exact (pi2 F).
  }
assert (monotone (fun X => den (pi1 F X))) as HmonoF.
  {
  refine (monotone_from_ispositive _#4 Hisroba _#3 Hs _).
  intros X h h'.
  so (HF X h h') as (H & _).
  simpsubin H.
  exact H.
  }
exists (iubase (extend_urel top stop (mu_urel top (fun X => den (pi1 F X))))).
do2 3 split.
  {
  apply interp_eval_refl.
  apply interp_mu; auto using le_ord_refl.
    {
    intros X h.
    simpsub.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (H & _).
    simpsubin H.
    exact H.
    }

    {
    exact (positive_impl_robust _#3 (Hisroba _#3 Hs andel)).
    }
  }

  {
  apply interp_eval_refl.
  apply interp_mu; auto using le_ord_refl.
    {
    intros X h.
    simpsub.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (_ & H & _).
    simpsubin H.
    exact H.
    }

    {
    exact (positive_impl_robust _#3 (Hisroba _#3 Hs ander)).
    }
  }

  {
  apply interp_eval_refl.
  apply interp_mu; auto using le_ord_refl.
    {
    intros X h.
    simpsub.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (_ & _ & H & _).
    simpsubin H.
    exact H.
    }

    {
    exact (positive_impl_robust _#3 (Hisrobb _#3 Hs andel)).
    }
  }

  {
  apply interp_eval_refl.
  apply interp_mu; auto using le_ord_refl.
    {
    intros X h.
    simpsub.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (_ & _ & _ & H).
    simpsubin H.
    exact H.
    }

    {
    exact (positive_impl_robust _#3 (Hisrobb _#3 Hs ander)).
    }
  }
Qed.


Lemma sound_mu_formation_univ :
  forall G lv a b,
    pseq G (deq lv lv pagetp)
    -> pseq (hyp_tm (univ lv) :: G) (deq a b (univ (subst sh1 lv)))
    -> pseq G (deq triv triv (ispositive a))
    -> pseq G (deq triv triv (ispositive b))
    -> pseq G (deq (mu a) (mu b) (univ lv)).
Proof.
intros G lv a b.
revert G.
refine (seq_pseq 2 [hyp_tp] a [hyp_tp] b 4 [] _ [_] _ [] _ [] _ _ _); cbn.
intros G Hcla Hclb Hseqlv Hab Hisroba Hisrobb.
rewrite -> seq_deq in Hseqlv.
rewrite -> seq_univ in Hab |- *.
eassert _ as Hlv; [refine (seq_pagetp_invert G lv _) |].
  {
  intros i t t' Ht.
  so (Hseqlv _#3 Ht) as (R & Hl & _ & Hlv & _).
  eauto.
  }
rewrite -> seq_ispositive in Hisroba, Hisrobb; auto.
intros i s s' Hs.
simpsub.
so (Hlv _#3 Hs) as (pg & Hlvl & Hlvr).
set (w := cin pg).
exploit (extract_ind_multi pg i (subst (under 1 s) a) (subst (under 1 s') a) (subst (under 1 s) b) (subst (under 1 s') b)) as H.
  {
  intros j X Y h Hj HXY.
  exploit (pwctx_cons_exttin_univ pg w j X Y h lv s s' G) as Hss; auto.
    {
    apply le_ord_refl.
    }

    {
    intros k t t' Hk Ht.
    so (Hseqlv _#3 Ht) as (R & Hl & _ & Hlvlr & _).
    simpsubin Hl.
    fold (@pagetp (obj stop)) in Hl.
    exact (interp_pagetp_invert _#7 Hl Hlvlr).
    }

    {
    eapply pwctx_downward; eauto.
    }
  so (Hab _ _ _ Hss) as (pg' & R & Hlvl' & _ & Hal & Har & Hbl & Hbr).
  simpsubin Hlvl'.
  so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
  exists R.
  simpsub.
  auto.
  }
destruct H as (F & HF).
assert (nonexpansive (fun X => den (pi1 F X))) as Hne.
  {
  apply compose_ne_ne; auto using den_nonexpansive.
  exact (pi2 F).
  }
assert (monotone (fun X => den (pi1 F X))) as HmonoF.
  {
  refine (monotone_from_ispositive _#4 Hisroba _#3 Hs _).
  intros X h h'.
  so (HF X h h') as (H & _).
  simpsubin H.
  exact H.
  }
exists pg, (iubase (extend_urel w stop (mu_urel w (fun X => den (pi1 F X))))).
do2 5 split; auto.
  {
  apply interp_eval_refl.
  apply interp_mu; auto using le_ord_refl.
    {
    intros X h.
    simpsub.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (H & _).
    simpsubin H.
    exact H.
    }

    {
    exact (positive_impl_robust _#3 (Hisroba _#3 Hs andel)).
    }
  }

  {
  apply interp_eval_refl.
  apply interp_mu; auto using le_ord_refl.
    {
    intros X h.
    simpsub.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (_ & H & _).
    simpsubin H.
    exact H.
    }

    {
    exact (positive_impl_robust _#3 (Hisroba _#3 Hs ander)).
    }
  }

  {
  apply interp_eval_refl.
  apply interp_mu; auto using le_ord_refl.
    {
    intros X h.
    simpsub.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (_ & _ & H & _).
    simpsubin H.
    exact H.
    }

    {
    exact (positive_impl_robust _#3 (Hisrobb _#3 Hs andel)).
    }
  }

  {
  apply interp_eval_refl.
  apply interp_mu; auto using le_ord_refl.
    {
    intros X h.
    simpsub.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (_ & _ & _ & H).
    simpsubin H.
    exact H.
    }

    {
    exact (positive_impl_robust _#3 (Hisrobb _#3 Hs ander)).
    }
  }
Qed.


Lemma sound_mu_roll :
  forall G a,
    pseq (hyp_tp :: G) (deqtype a a)
    -> pseq G (deq triv triv (ispositive a))
    -> pseq G (dsubtype (subst1 (mu a) a) (mu a)).
Proof.
intros G a.
revert G.
refine (seq_pseq 1 [hyp_tp] a 2 [_] _ [] _ _ _); cbn.
intros G Hcla Hseqa Hisrob.
rewrite -> seq_eqtype in Hseqa.
rewrite -> seq_ispositive in Hisrob; auto.
rewrite -> seq_subtype.
intros i s s' Hs.
simpsub.
exploit (extract_ind toppg i (subst (under 1 s) a) (subst (under 1 s') a)) as H.
  {
  intros j X Y h Hj HXY.
  so (pwctx_cons_exttin top j X Y h s s' G (le_ord_refl _) HXY (pwctx_downward _#5 Hj Hs)) as Hss.
  so (Hseqa _ _ _ Hss) as (R & Hal & Har & _).
  exists R.
  simpsub.
  auto.
  }
destruct H as (F & HF).
assert (nonexpansive (fun X => den (pi1 F X))) as Hne.
  {
  apply compose_ne_ne; auto using den_nonexpansive.
  exact (pi2 F).
  }
assert (monotone (fun X => den (pi1 F X))) as HmonoF.
  {
  refine (monotone_from_ispositive _#4 Hisrob _#3 Hs _).
  intros X h h'.
  so (HF X h h') as (H & _).
  simpsubin H.
  exact H.
  }
set (Mu := (iubase (extend_urel top stop (mu_urel top (fun X => den (pi1 F X)))))).
assert (interp toppg true i (mu (subst (under 1 s) a)) Mu) as Hmul.
  {
  apply interp_eval_refl.
  apply interp_mu; auto using le_ord_refl.
    {
    intros X h.
    simpsub.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (H & _).
    simpsubin H.
    exact H.
    }

    {
    exact (positive_impl_robust _#3 (Hisrob _#3 Hs andel)).
    }
  }
assert (interp toppg false i (mu (subst (under 1 s') a)) Mu) as Hmur.
  {
  apply interp_eval_refl.
  apply interp_mu; auto using le_ord_refl.
    {
    intros X h.
    simpsub.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (_ & H).
    simpsubin H.
    exact H.
    }

    {
    exact (positive_impl_robust _#3 (Hisrob _#3 Hs ander)).
    }
  }
assert (pwctx i (dot (mu (subst (under 1 s) a)) s) (dot (mu (subst (under 1 s') a)) s') (hyp_tp :: G)) as Hss.
  {
  apply pwctx_cons_tp; auto.
  apply (seqhyp_tp _#3 Mu); auto.
  }
so (Hseqa _#3 Hss) as (AMu & Hamul & Hamur & _).
clear Hss.
assert (den AMu = den Mu) as Heq.
  {
  unfold Mu.
  rewrite -> mu_fix; auto.
  so (succ_increase top) as h.
  set (h' := lt_ord_impl_le_ord _ _ h).
  rewrite <- (extend_iubase _ _ h').
  assert (pwctx i (dot (mu (subst (under 1 s) a)) s) (dot (exttin top (mu_urel top (fun X => den (pi1 F X))) h) s') (hyp_tp :: G)) as Hss.
    {
    apply pwctx_cons_tp; auto.
    apply (seqhyp_tp _#3 Mu); auto.
    so (basic_impl_iutruncate _#6 Hmul) as Heq.
    rewrite -> Heq.
    unfold Mu.
    rewrite <- (extend_iubase _ _ h').
    rewrite -> iutruncate_extend_iurel.
    apply interp_eval_refl.
    apply interp_extt.
    apply le_ord_refl.
    }
  so (Hseqa _#3 Hss) as (R & Hamul' & Hamur' & _).
  simpsubin Hamul'.
  simpsubin Hamur'.
  so (HF (mu_urel top (fun X => den (pi1 F X))) h h') as (_ & Hamur'').
  simpsubin Hamur''.
  so (interp_fun _#7 Hamur' Hamur''); subst R.
  so (interp_fun _#7 Hamul Hamul'); subst AMu.
  rewrite -> !den_extend_iurel.
  rewrite -> den_iubase.
  reflexivity.
  }
exists AMu, Mu.  (* the only line that is different from sound_mu_unroll *)
do2 4 split; auto.
rewrite -> Heq.
intros j m p Hj Hmp.
unfold Mu in Hmp |- *.
exact Hmp.
Qed.


Lemma sound_mu_unroll :
  forall G a,
    pseq (hyp_tp :: G) (deqtype a a)
    -> pseq G (deq triv triv (ispositive a))
    -> pseq G (dsubtype (mu a) (subst1 (mu a) a)).
Proof.
intros G a.
revert G.
refine (seq_pseq 1 [hyp_tp] a 2 [_] _ [] _ _ _); cbn.
intros G Hcla Hseqa Hisrob.
rewrite -> seq_eqtype in Hseqa.
rewrite -> seq_ispositive in Hisrob; auto.
rewrite -> seq_subtype.
intros i s s' Hs.
simpsub.
exploit (extract_ind toppg i (subst (under 1 s) a) (subst (under 1 s') a)) as H.
  {
  intros j X Y h Hj HXY.
  so (pwctx_cons_exttin top j X Y h s s' G (le_ord_refl _) HXY (pwctx_downward _#5 Hj Hs)) as Hss.
  so (Hseqa _ _ _ Hss) as (R & Hal & Har & _).
  exists R.
  simpsub.
  auto.
  }
destruct H as (F & HF).
assert (nonexpansive (fun X => den (pi1 F X))) as Hne.
  {
  apply compose_ne_ne; auto using den_nonexpansive.
  exact (pi2 F).
  }
assert (monotone (fun X => den (pi1 F X))) as HmonoF.
  {
  refine (monotone_from_ispositive _#4 Hisrob _#3 Hs _).
  intros X h h'.
  so (HF X h h') as (H & _).
  simpsubin H.
  exact H.
  }
set (Mu := (iubase (extend_urel top stop (mu_urel top (fun X => den (pi1 F X)))))).
assert (interp toppg true i (mu (subst (under 1 s) a)) Mu) as Hmul.
  {
  apply interp_eval_refl.
  apply interp_mu; auto using le_ord_refl.
    {
    intros X h.
    simpsub.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (H & _).
    simpsubin H.
    exact H.
    }

    {
    exact (positive_impl_robust _#3 (Hisrob _#3 Hs andel)).
    }
  }
assert (interp toppg false i (mu (subst (under 1 s') a)) Mu) as Hmur.
  {
  apply interp_eval_refl.
  apply interp_mu; auto using le_ord_refl.
    {
    intros X h.
    simpsub.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (_ & H).
    simpsubin H.
    exact H.
    }

    {
    exact (positive_impl_robust _#3 (Hisrob _#3 Hs ander)).
    }
  }
assert (pwctx i (dot (mu (subst (under 1 s) a)) s) (dot (mu (subst (under 1 s') a)) s') (hyp_tp :: G)) as Hss.
  {
  apply pwctx_cons_tp; auto.
  apply (seqhyp_tp _#3 Mu); auto.
  }
so (Hseqa _#3 Hss) as (AMu & Hamul & Hamur & _).
clear Hss.
assert (den AMu = den Mu) as Heq.
  {
  unfold Mu.
  rewrite -> mu_fix; auto.
  so (succ_increase top) as h.
  set (h' := lt_ord_impl_le_ord _ _ h).
  rewrite <- (extend_iubase _ _ h').
  assert (pwctx i (dot (mu (subst (under 1 s) a)) s) (dot (exttin top (mu_urel top (fun X => den (pi1 F X))) h) s') (hyp_tp :: G)) as Hss.
    {
    apply pwctx_cons_tp; auto.
    apply (seqhyp_tp _#3 Mu); auto.
    so (basic_impl_iutruncate _#6 Hmul) as Heq.
    rewrite -> Heq.
    unfold Mu.
    rewrite <- (extend_iubase _ _ h').
    rewrite -> iutruncate_extend_iurel.
    apply interp_eval_refl.
    apply interp_extt.
    apply le_ord_refl.
    }
  so (Hseqa _#3 Hss) as (R & Hamul' & Hamur' & _).
  simpsubin Hamul'.
  simpsubin Hamur'.
  so (HF (mu_urel top (fun X => den (pi1 F X))) h h') as (_ & Hamur'').
  simpsubin Hamur''.
  so (interp_fun _#7 Hamur' Hamur''); subst R.
  so (interp_fun _#7 Hamul Hamul'); subst AMu.
  rewrite -> !den_extend_iurel.
  rewrite -> den_iubase.
  reflexivity.
  }
exists Mu, AMu.  (* the only line that is different from sound_mu_roll *)
do2 4 split; auto.
rewrite -> Heq.
intros j m p Hj Hmp.
unfold Mu in Hmp |- *.
exact Hmp.
Qed.


Lemma sound_mu_roll_univ :
  forall G lv a,
    pseq G (deq lv lv pagetp)
    -> pseq (hyp_tm (univ lv) :: G) (deq a a (univ (subst sh1 lv)))
    -> pseq G (deq triv triv (ispositive a))
    -> pseq G (dsubtype (subst1 (mu a) a) (mu a)).
Proof.
intros G lv a.
revert G.
refine (seq_pseq 1 [hyp_tp] a 3 [] _ [_] _ [] _ _ _); cbn.
intros G Hcla Hseqlv Hseqa Hisrob.
rewrite -> seq_deq in Hseqlv.
rewrite -> seq_univ in Hseqa.
rewrite -> seq_ispositive in Hisrob; auto.
rewrite -> seq_subtype.
exploit (seq_pagetp_invert G lv) as Hlevel.
  {
  intros i s s' Hs.
  so (Hseqlv _#3 Hs) as (R & H1 & _ & H2 & _).
  eauto.
  }
intros i s s' Hs.
simpsub.
so (Hlevel _#3 Hs) as (pg & Hlvl & Hlvr).
set (w := cin pg).
exploit (extract_ind pg i (subst (under 1 s) a) (subst (under 1 s') a)) as H.
  {
  intros j X Y h Hj HXY.
  exploit (pwctx_cons_exttin_univ pg w j X Y h lv s s' G) as Hss; auto.
    {
    apply le_ord_refl.
    }

    {
    intros k t t' Hk Ht.
    so (Hseqlv _#3 Ht) as (R & Hl & _ & Hlvlr & _).
    simpsubin Hl.
    fold (@pagetp (obj stop)) in Hl.
    exact (interp_pagetp_invert _#7 Hl Hlvlr).
    }

    {
    eapply pwctx_downward; eauto.
    }
  so (Hseqa _ _ _ Hss) as (pg' & R & Hlvl' & _ & Hal & Har & _).
  simpsubin Hlvl'.
  so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
  exists R.
  simpsub.
  auto.
  }
destruct H as (F & HF).
assert (nonexpansive (fun X => den (pi1 F X))) as Hne.
  {
  apply compose_ne_ne; auto using den_nonexpansive.
  exact (pi2 F).
  }
assert (monotone (fun X => den (pi1 F X))) as HmonoF.
  {
  refine (monotone_from_ispositive _#4 Hisrob _#3 Hs _).
  intros X h h'.
  so (HF X h h') as (H & _).
  simpsubin H.
  exact H.
  }
set (Mu := (iubase (extend_urel w stop (mu_urel w (fun X => den (pi1 F X)))))).
assert (interp pg true i (mu (subst (under 1 s) a)) Mu) as Hmul.
  {
  apply interp_eval_refl.
  apply interp_mu; auto using le_ord_refl.
    {
    intros X h.
    simpsub.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (H & _).
    simpsubin H.
    exact H.
    }

    {
    exact (positive_impl_robust _#3 (Hisrob _#3 Hs andel)).
    }
  }
assert (interp pg false i (mu (subst (under 1 s') a)) Mu) as Hmur.
  {
  apply interp_eval_refl.
  apply interp_mu; auto using le_ord_refl.
    {
    intros X h.
    simpsub.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (_ & H).
    simpsubin H.
    exact H.
    }

    {
    exact (positive_impl_robust _#3 (Hisrob _#3 Hs ander)).
    }
  }
assert (pwctx i (dot (mu (subst (under 1 s) a)) s) (dot (mu (subst (under 1 s') a)) s') (hyp_tm (univ lv) :: G)) as Hss.
  {
  apply pwctx_cons_tm_seq; auto.
    {
    simpsub.
    apply (seqhyp_tm _#5 (iuuniv the_system i pg)).
      {
      apply interp_eval_refl.
      apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
      }
  
      {
      simpsub.
      apply interp_eval_refl.
      apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
      }

      {
      cbn.
      split; auto.
      rewrite -> sint_unroll.
      exists Mu.
      auto.
      }
    }

    {
    intros j t t' Ht.
    so (Hlevel _#3 Ht) as (pgt & Hlvlt & Hlvrt).
    exists toppg, (iuuniv the_system j pgt).
    simpsub.
    split.
      {
      apply interp_eval_refl.
      apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
      }

      {
      apply interp_eval_refl.
      apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
      }
    }
  }
so (Hseqa _#3 Hss) as (pg' & AMu & Hlvl' & _ & Hamul & Hamur & _).
clear Hss.
simpsubin Hlvl'.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
clear Hlvl'.
assert (den AMu = den Mu) as Heq.
  {
  unfold Mu.
  rewrite -> mu_fix; auto.
  so (lt_ord_trans _#3 (pginterp_cin_top _ _ Hlvl) (succ_increase top)) as h.
  change (w << stop) in h.
  set (h' := lt_ord_impl_le_ord _ _ h).
  rewrite <- (extend_iubase _ _ h').
  assert (pwctx i (dot (mu (subst (under 1 s) a)) s) (dot (exttin w (mu_urel w (fun X => den (pi1 F X))) h) s') (hyp_tm (univ lv) :: G)) as Hss.
    {
    apply pwctx_cons_tm_seq; auto.
      {
      simpsub.
      apply (seqhyp_tm _#5 (iuuniv the_system i pg)).
        {
        apply interp_eval_refl.
        apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
        }
    
        {
        simpsub.
        apply interp_eval_refl.
        apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
        }

        {
        cbn.
        split; auto.
        rewrite -> sint_unroll.
        exists Mu.
        split; auto.
        so (basic_impl_iutruncate _#6 Hmul) as Heq.
        rewrite -> Heq.
        unfold Mu.
        rewrite <- (extend_iubase _ _ h').
        rewrite -> iutruncate_extend_iurel.
        apply interp_eval_refl.
        apply interp_extt.
        apply le_ord_refl.
        }
      }

      {
      intros j t t' Ht.
      so (Hlevel _#3 Ht) as (pgt & Hlvlt & Hlvrt).
      exists toppg, (iuuniv the_system j pgt).
      simpsub.
      split.
        {
        apply interp_eval_refl.
        apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
        }
  
        {
        apply interp_eval_refl.
        apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
        }
      }
    }
  so (Hseqa _#3 Hss) as (pg' & R & Hlvl' & _ & Hamul' & Hamur' & _).
  simpsubin Hlvl'.
  so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
  simpsubin Hamul'.
  simpsubin Hamur'.
  so (HF (mu_urel w (fun X => den (pi1 F X))) h h') as (_ & Hamur'').
  simpsubin Hamur''.
  so (interp_fun _#7 Hamur' Hamur''); subst R.
  so (interp_fun _#7 Hamul Hamul'); subst AMu.
  rewrite -> !den_extend_iurel.
  rewrite -> den_iubase.
  reflexivity.
  }
exists AMu, Mu.  (* the only line that is different from sound_mu_unroll_univ *)
do2 4 split.
  {
  apply (interp_increase pg); auto using toppg_max.
  }

  {
  apply (interp_increase pg); auto using toppg_max.
  }

  {
  apply (interp_increase pg); auto using toppg_max.
  }

  {
  apply (interp_increase pg); auto using toppg_max.
  }
rewrite -> Heq.
intros j m p Hj Hmp.
unfold Mu in Hmp |- *.
exact Hmp.
Qed.


Lemma sound_mu_unroll_univ :
  forall G lv a,
    pseq G (deq lv lv pagetp)
    -> pseq (hyp_tm (univ lv) :: G) (deq a a (univ (subst sh1 lv)))
    -> pseq G (deq triv triv (ispositive a))
    -> pseq G (dsubtype (mu a) (subst1 (mu a) a)).
Proof.
intros G lv a.
revert G.
refine (seq_pseq 1 [hyp_tp] a 3 [] _ [_] _ [] _ _ _); cbn.
intros G Hcla Hseqlv Hseqa Hisrob.
rewrite -> seq_deq in Hseqlv.
rewrite -> seq_univ in Hseqa.
rewrite -> seq_ispositive in Hisrob; auto.
rewrite -> seq_subtype.
exploit (seq_pagetp_invert G lv) as Hlevel.
  {
  intros i s s' Hs.
  so (Hseqlv _#3 Hs) as (R & H1 & _ & H2 & _).
  eauto.
  }
intros i s s' Hs.
simpsub.
so (Hlevel _#3 Hs) as (pg & Hlvl & Hlvr).
set (w := cin pg).
exploit (extract_ind pg i (subst (under 1 s) a) (subst (under 1 s') a)) as H.
  {
  intros j X Y h Hj HXY.
  exploit (pwctx_cons_exttin_univ pg w j X Y h lv s s' G) as Hss; auto.
    {
    apply le_ord_refl.
    }

    {
    intros k t t' Hk Ht.
    so (Hseqlv _#3 Ht) as (R & Hl & _ & Hlvlr & _).
    simpsubin Hl.
    fold (@pagetp (obj stop)) in Hl.
    exact (interp_pagetp_invert _#7 Hl Hlvlr).
    }

    {
    eapply pwctx_downward; eauto.
    }
  so (Hseqa _ _ _ Hss) as (pg' & R & Hlvl' & _ & Hal & Har & _).
  simpsubin Hlvl'.
  so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
  exists R.
  simpsub.
  auto.
  }
destruct H as (F & HF).
assert (nonexpansive (fun X => den (pi1 F X))) as Hne.
  {
  apply compose_ne_ne; auto using den_nonexpansive.
  exact (pi2 F).
  }
assert (monotone (fun X => den (pi1 F X))) as HmonoF.
  {
  refine (monotone_from_ispositive _#4 Hisrob _#3 Hs _).
  intros X h h'.
  so (HF X h h') as (H & _).
  simpsubin H.
  exact H.
  }
set (Mu := (iubase (extend_urel w stop (mu_urel w (fun X => den (pi1 F X)))))).
assert (interp pg true i (mu (subst (under 1 s) a)) Mu) as Hmul.
  {
  apply interp_eval_refl.
  apply interp_mu; auto using le_ord_refl.
    {
    intros X h.
    simpsub.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (H & _).
    simpsubin H.
    exact H.
    }

    {
    exact (positive_impl_robust _#3 (Hisrob _#3 Hs andel)).
    }
  }
assert (interp pg false i (mu (subst (under 1 s') a)) Mu) as Hmur.
  {
  apply interp_eval_refl.
  apply interp_mu; auto using le_ord_refl.
    {
    intros X h.
    simpsub.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (_ & H).
    simpsubin H.
    exact H.
    }

    {
    exact (positive_impl_robust _#3 (Hisrob _#3 Hs ander)).
    }
  }
assert (pwctx i (dot (mu (subst (under 1 s) a)) s) (dot (mu (subst (under 1 s') a)) s') (hyp_tm (univ lv) :: G)) as Hss.
  {
  apply pwctx_cons_tm_seq; auto.
    {
    simpsub.
    apply (seqhyp_tm _#5 (iuuniv the_system i pg)).
      {
      apply interp_eval_refl.
      apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
      }
  
      {
      simpsub.
      apply interp_eval_refl.
      apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
      }

      {
      cbn.
      split; auto.
      rewrite -> sint_unroll.
      exists Mu.
      auto.
      }
    }

    {
    intros j t t' Ht.
    so (Hlevel _#3 Ht) as (pgt & Hlvlt & Hlvrt).
    exists toppg, (iuuniv the_system j pgt).
    simpsub.
    split.
      {
      apply interp_eval_refl.
      apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
      }

      {
      apply interp_eval_refl.
      apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
      }
    }
  }
so (Hseqa _#3 Hss) as (pg' & AMu & Hlvl' & _ & Hamul & Hamur & _).
clear Hss.
simpsubin Hlvl'.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
clear Hlvl'.
assert (den AMu = den Mu) as Heq.
  {
  unfold Mu.
  rewrite -> mu_fix; auto.
  so (lt_ord_trans _#3 (pginterp_cin_top _ _ Hlvl) (succ_increase top)) as h.
  change (w << stop) in h.
  set (h' := lt_ord_impl_le_ord _ _ h).
  rewrite <- (extend_iubase _ _ h').
  assert (pwctx i (dot (mu (subst (under 1 s) a)) s) (dot (exttin w (mu_urel w (fun X => den (pi1 F X))) h) s') (hyp_tm (univ lv) :: G)) as Hss.
    {
    apply pwctx_cons_tm_seq; auto.
      {
      simpsub.
      apply (seqhyp_tm _#5 (iuuniv the_system i pg)).
        {
        apply interp_eval_refl.
        apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
        }
    
        {
        simpsub.
        apply interp_eval_refl.
        apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
        }

        {
        cbn.
        split; auto.
        rewrite -> sint_unroll.
        exists Mu.
        split; auto.
        so (basic_impl_iutruncate _#6 Hmul) as Heq.
        rewrite -> Heq.
        unfold Mu.
        rewrite <- (extend_iubase _ _ h').
        rewrite -> iutruncate_extend_iurel.
        apply interp_eval_refl.
        apply interp_extt.
        apply le_ord_refl.
        }
      }

      {
      intros j t t' Ht.
      so (Hlevel _#3 Ht) as (pgt & Hlvlt & Hlvrt).
      exists toppg, (iuuniv the_system j pgt).
      simpsub.
      split.
        {
        apply interp_eval_refl.
        apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
        }
  
        {
        apply interp_eval_refl.
        apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
        }
      }
    }
  so (Hseqa _#3 Hss) as (pg' & R & Hlvl' & _ & Hamul' & Hamur' & _).
  simpsubin Hlvl'.
  so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
  simpsubin Hamul'.
  simpsubin Hamur'.
  so (HF (mu_urel w (fun X => den (pi1 F X))) h h') as (_ & Hamur'').
  simpsubin Hamur''.
  so (interp_fun _#7 Hamur' Hamur''); subst R.
  so (interp_fun _#7 Hamul Hamul'); subst AMu.
  rewrite -> !den_extend_iurel.
  rewrite -> den_iubase.
  reflexivity.
  }
exists Mu, AMu.  (* the only line that is different from sound_mu_roll_univ *)
do2 4 split.
  {
  apply (interp_increase pg); auto using toppg_max.
  }

  {
  apply (interp_increase pg); auto using toppg_max.
  }

  {
  apply (interp_increase pg); auto using toppg_max.
  }

  {
  apply (interp_increase pg); auto using toppg_max.
  }
rewrite -> Heq.
intros j m p Hj Hmp.
unfold Mu in Hmp |- *.
exact Hmp.
Qed.


Definition down w := map_term (extend stop w).
Definition up w := map_term (extend w stop).


Definition contingent_action pg A (P : nat -> sterm -> sterm -> Prop)
  : nat -> relation (wterm (cin pg))
  :=
  fun i m p =>
    rel A i m p
    /\ exists R,
         forall j b c,
           j <= i
           -> P j b c
           -> interp pg true j (subst1 (up (cin pg) m) b) (iutruncate (S j) R)
              /\ interp pg false j (subst1 (up (cin pg) p) c) (iutruncate (S j) R)
              /\ rel (den R) j triv triv.


Lemma contingent_uniform :
  forall pg A P, uniform _ (contingent_action pg A P).
Proof.
intros pg A P.
do2 3 split.

(* closed *)
{
intros i m p Hmp.
destruct Hmp as (Hmp & _).
eapply urel_closed; eauto.
}

(* equiv *)
{
intros i m m' p p' Hclm' Hclp' Hequivm Hequivp Hmp.
destruct Hmp as (Hmp & R & HR).
split.
  {
  eapply urel_equiv; eauto.
  }
exists R.
intros j b c Hj Hbc.
so (HR j b c Hj Hbc) as (Hb & Hc & Hinh).
do2 2 split; auto.
  {
  eapply basic_equiv; eauto.
    {
    so (basic_closed _#6 Hb) as Hhyg.
    so (hygiene_clo_subst1_invert_permit _#3 Hhyg) as Hclb.
    apply hygiene_subst1; auto.
    apply map_hygiene; auto.
    }

    {
    apply equiv_funct1; auto using equiv_refl.
    apply map_equiv; auto.
    }
  }

  {
  eapply basic_equiv; eauto.
    {
    so (basic_closed _#6 Hc) as Hhyg.
    so (hygiene_clo_subst1_invert_permit _#3 Hhyg) as Hclb.
    apply hygiene_subst1; auto.
    apply map_hygiene; auto.
    }

    {
    apply equiv_funct1; auto using equiv_refl.
    apply map_equiv; auto.
    }
  }
}

(* zigzag *)
{
intros i m p n q Hmp Hnp Hnq.
destruct Hmp as (Hmp & R & HRmp).
destruct Hnp as (Hnp & R' & HRnp).
destruct Hnq as (Hnq & R'' & HRnq).
split.
  {
  eapply urel_zigzag; eauto.
  }
exists R.
intros j b c Hj Hbc.
so (HRmp _ _ _ Hj Hbc) as (Hm & Hp & Hinh).
so (HRnp _ _ _ Hj Hbc) as (Hn & Hp' & _).
so (interp_fun _#7 Hp Hp') as Heq.
so (HRnq _ _ _ Hj Hbc) as (Hn' & Hq & _).
so (interp_fun _#7 Hn Hn') as Heq'.
do2 2 split; auto.
  {
  rewrite -> Heq.
  rewrite -> Heq'.
  auto.
  }
}

(* downward *)
{
intros i m p Hmp.
destruct Hmp as (Hmp & R & HR).
split.
  {
  apply urel_downward; auto.
  }
exists R.
intros j b c Hj.
apply HR.
omega.
}
Qed.


Definition contingent pg A P := (mk_urel _ (contingent_uniform pg A P)).


Definition relctx i s s' t t' G :=
  pwctx i s s' G
  /\ seqctx i t t' G
  /\ seqctx i s t' G.


Lemma relctx_refl :
  forall i s s' G,
    pwctx i s s' G
    -> relctx i s s' s s' G.
Proof.
intros i s s' G H.
do2 2 split; auto using pwctx_impl_seqctx.
Qed.


Lemma relctx_downward :
  forall i j s s' t t' G,
    j <= i
    -> relctx i s s' t t' G
    -> relctx j s s' t t' G.
Proof.
intros i j s s' t t' G Hj (Hs & Ht & Hst).
do2 2 split; eauto using pwctx_downward, seqctx_downward.
Qed.


Lemma relctx_pwctx :
  forall i s s' t t' G,
    relctx i s s' t t' G
    -> pwctx i t t' G.
Proof.
intros i s s' t t' G Hst.
destruct Hst as (Hs & Ht & Hst).
so (seqctx_pwctx_left _#5 Hs Hst) as Hst'.
exact (seqctx_pwctx_right _#5 Hst' Ht).
Qed.


Lemma relctx_trans_right :
  forall i s s' t t' u' G,
    seqctx i t u' G
    -> relctx i s s' t t' G
    -> relctx i s s' t u' G.
Proof.
intros i s s' t t' u' G Htu (Hs & Ht & Hst).
do2 2 split; auto.
apply (seqctx_zigzag i s t' t u'); auto.
Qed.


Lemma relctx_trans_left :
  forall i s s' t t' u G,
    seqctx i u t' G
    -> relctx i s s' t t' G
    -> relctx i s s' u t' G.
Proof.
intros i s s' t t' u' G Htu (Hs & Ht & Hst).
do2 2 split; auto.
Qed.


Lemma relctx_swap1 :
  forall i s s' t t' G,
    relctx i s s' t t' G
    -> relctx i s s' s t' G.
Proof.
intros i s s' t t' G (Hs & Ht & Hst).
do2 2 split; auto.
Qed.


Lemma relctx_swap2 :
  forall i s s' t t' G,
    relctx i s s' t t' G
    -> relctx i s s' t s' G.
Proof.
intros i s s' t t' G (Hs & Ht & Hst).
do2 2 split; auto using pwctx_impl_seqctx.
eapply seqctx_zigzag; eauto using pwctx_impl_seqctx.
Qed.


Definition contingent_instance pg A b s s' G :=
  contingent pg A (fun j c d =>
                    exists t t',
                      relctx j s s' t t' G
                      /\ c = subst (under 1 t) b
                      /\ d = subst (under 1 t') b).


Lemma contingent_instance_elim :
  forall pg A b s s' G i m p,
    rel (contingent_instance pg A b s s' G) i m p
    -> rel A i m p
       /\ exists R,
            forall j t t',
              j <= i
              -> relctx j s s' t t' G
              -> interp pg true j (subst (dot (up (cin pg) m) t) b) (iutruncate (S j) R)
                 /\ interp pg false j (subst (dot (up (cin pg) p) t') b) (iutruncate (S j) R)
                 /\ rel (den R) j triv triv.
Proof.
intros pg A b s s' G i m p H.
destruct H as (Hmp & R & HR).
split; auto.
exists R.
intros j t t' Hj Ht.
exploit (HR j (subst (under 1 t) b) (subst (under 1 t') b)) as H; auto.
  {
  exists t, t'.
  auto.
  }
simpsubin H.
exact H.
Qed.

       
Lemma interp_updown :
  forall pg w z i s m a A,
    cex pg <<= w
    -> interp pg z i (subst (dot (up w (down w m)) s) a) A
    -> interp pg z i (subst (dot m s) a) A.
Proof.
intros pg w z i s m a A Hle Hint.
unfold up, down in Hint.
rewrite <- restrict_extend in Hint.
so (restrict_impl_restriction w m) as Hrestm.
so (restriction_refl w (subst (under 1 s) a)) as Hresta.
so (restriction_funct1 _#5 Hrestm Hresta) as Hrest.
simpsubin Hrest.
eapply interp_restriction; eauto.
eapply restriction_decrease; eauto.
Qed.


(* The sound_mu_ind_univ rule depends on the page's cex and cin being
   equal.  That turns out to be true for every page that the syntax
   supports, but we don't like to rely on that property.  If we ever
   were to relax it, we would have to add an extra premise to
   sound_mu_ind_univ to ensure it.
*)
Local Lemma pginterp_cin_cex :
  forall m pg,
    pginterp m pg
    -> cin pg = cex pg.
Proof.
intros m pg H.
destruct H as (w & _ & _ & Hin & Hex).
subst w.
auto.
Qed.


Lemma relctx_pginterp :
  forall G lv i s s' t t' pg,
    seq G (deq lv lv pagetp)
    -> relctx i s s' t t' G
    -> pginterp (subst s lv) pg
    -> pginterp (subst t lv) pg /\ pginterp (subst t' lv) pg.
Proof.
intros G lv i s s' t t' pg Hseq Hrel Hlv.
rewrite -> seq_deq in Hseq.
exploit (seq_pagetp_invert G lv) as Hlevel.
  {
  clear i s s' t t' Hrel Hlv.
  intros i s s' Hs.
  so (Hseq _#3 Hs) as (R & Hl & _ & Hinh & _).
  exists toppg, R.
  split; auto.
  }
so (Hlevel _#3 (relctx_pwctx _#6 (relctx_swap1 _#6 Hrel))) as (pg' & Hlv' & Hlvtr).
so (pginterp_fun _#3 Hlv Hlv'); subst pg'; clear Hlv'.
so (Hlevel _#3 (relctx_pwctx _#6 Hrel)) as (pg' & Hlvtl & Hlvtr').
so (pginterp_fun _#3 Hlvtr Hlvtr'); subst pg'.
auto.
Qed.


Lemma sound_mu_ind :
  forall G a b m,
    pseq (hyp_tp :: G) (deqtype a a)
    -> pseq G (deq triv triv (ispositive a))
    -> pseq
         (hyp_tm (pi (var 2) (subst (under 1 (sh 3)) b)) ::
          hyp_tm (subtype (var 1) (mu (subst (under 1 (sh 2)) a))) ::
          hyp_tm a ::
          hyp_tp :: 
          G)
         (deq triv triv (subst (dot (var 2) (sh 4)) b))
    -> pseq G (deq m m (mu a))
    -> pseq G (deq triv triv (subst1 m b)).
Proof.
intros G a b m.
revert G.
refine (seq_pseq 2 [hyp_tp] a [hyp_tp] b 4 [_] _ [] _ [_; _; _; _] _ [] _ _ _).
cbn.
(* why is this necessary? *)
replace (varx (obj stop) 0) with (@var (obj stop) 0) by reflexivity.
intros G Hcla Hclb Hseqa Hpos Hseqind Hseqm.
rewrite -> seq_eqtype in Hseqa.
rewrite -> seq_deq in Hseqind, Hseqm |- *.
rewrite -> seq_ispositive in Hpos; auto.
assert (forall i s s',
          pwctx i s s' G
          -> exists (F : wurel_ofe top -n> wiurel_ofe top) R,
               interp toppg true i (mu (subst (under 1 s) a)) R
               /\ interp toppg false i (mu (subst (under 1 s') a)) R
               /\ R = iubase (extend_urel top stop (mu_urel top (fun X => den (pi1 F X))))
               /\ monotone (fun X => den (pi1 F X))
               /\ (forall X (h : top << stop) (h' : top <<= stop),
                     interp toppg true i (subst (dot (exttin top X h) s) a) (extend_iurel h' (pi1 F X))
                     /\ interp toppg false i (subst (dot (exttin top X h) s') a) (extend_iurel h' (pi1 F X)))) as Hmu.
  {
  intros i s s' Hs.
  so (Hseqm _#3 Hs) as (A & Hmul & Hmur & Hm & _).
  simpsubin Hmul.
  simpsubin Hmur.
  exploit (extract_ind toppg i (subst (under 1 s) a) (subst (under 1 s') a)) as H.
    {
    intros j X Y h Hj HXY.
    so (pwctx_cons_exttin top j X Y h s s' G (le_ord_refl _) HXY (pwctx_downward _#5 Hj Hs)) as Hss.
    so (Hseqa _ _ _ Hss) as (R & Hal & Har & _).
    exists R.
    simpsub.
    auto.
    }
  destruct H as (F & HF).
  assert (nonexpansive (fun X => den (pi1 F X))) as Hne.
    {
    apply compose_ne_ne; auto using den_nonexpansive.
    exact (pi2 F).
    }
  assert (monotone (fun X => den (pi1 F X))) as HmonoF.
    {
    refine (monotone_from_ispositive _#4 Hpos _#3 Hs _).
    intros X h h'.
    so (HF X h h') as (H & _).
    simpsubin H.
    exact H.
    }
  so (positive_impl_robust _#3 (Hpos _#3 Hs andel)) as Hrobust.
  so (positive_impl_robust _#3 (Hpos _#3 Hs ander)) as Hrobust'.
  exists F.
  exists (iubase (extend_urel top stop (mu_urel top (fun X => den (pi1 F X))))).
  assert (interp toppg true i (mu (subst (under 1 s) a)) (iubase (extend_urel top stop (mu_urel top (fun X => den (pi1 F X)))))) as Hmul'.
    {
    apply interp_eval_refl.
    apply interp_mu; auto using le_ord_refl.
    intros X h.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (H & _).
    simpsubin H.
    simpsub.
    exact H.
    }
  so (interp_fun _#7 Hmul Hmul'); subst A.
  do2 4 split; auto.
  intros X h h'.
  so (HF X h h') as H.
  simpsubin H.
  exact H.
  }
intros i s s' Hs.
so (Hmu _ _ _ Hs) as (F & R & Hmul & Hmur & HeqMu & HmonoF & HF).
simpsubin Hmul.
simpsubin Hmur.
so (Hseqm _#3 Hs) as (R' & H & _ & Hm & _).
simpsubin H.
so (interp_fun _#7 H Hmul); subst R'; clear H.
subst R.
set (Mu := mu_urel top (fun X => den (pi1 F X))) in Hmul, Hmur, Hm.
rewrite -> den_iubase in Hm.
cbn -[mu_urel] in Hm.
set (C := contingent_instance toppg Mu b s s' G).
assert (incl C Mu) as Hincl.
  {
  clear m Hseqm Hseqind Hm Hmu.
  intros j m p Hmp.
  destruct Hmp; auto.
  }
cut (rel C i (down top (subst s m)) (down top (subst s' m))).
  {
  intro H.
  so (contingent_instance_elim _#9 H) as (Hn & R & HR); clear H.
  so (HR i s s' (le_refl _) (relctx_refl _#4 Hs)) as H.
  destruct H as (Hl & Hr & Hinh).
  simpsubin Hl.
  simpsubin Hr.
  exists (iutruncate (S i) R).
  simpsub.
  do2 4 split; auto; try (split; [omega | auto]; done).
    {
    eapply interp_updown; eauto using le_ord_refl.
    }

    {
    eapply interp_updown; eauto using le_ord_refl.
    }
  }
cut (incl Mu C); auto.
clear m Hm Hseqm.
apply mu_least.
intros j m p Hmp.
assert (j <= i) as Hj.
  {
  set (h := succ_increase top).
  set (h' := succ_nodecrease top).
  so (HF C h h') as (H & _).
  assert (rel (den (extend_iurel h' (pi1 F C))) j (up top m) (up top p)) as Hmp'.
    {
    cbn.
    unfold up.
    rewrite -> !extend_term_cancel; auto.
    }
  refine (basic_member_index _#9 H Hmp').
  }
so (succ_increase top) as h.
assert (forall k t t',
          k <= j
          -> relctx k s s' t t' G
          -> let h' := lt_ord_impl_le_ord _ _ h in
             let C' := extend_iurel h' (iutruncate (S k) (iubase C))
             in
               exists (B : urelsp (den C') -n> siurel_ofe),
                 functional the_system toppg true k (den C') (subst (under 1 t) b) B
                 /\ functional the_system toppg false k (den C') (subst (under 1 t') b) B) as Hfunc.
  {
  intros k t t' Hk Hst h' C'.
  assert (k <= i) as Hki by omega.
  so (pwctx_impl_closub _#4 (relctx_pwctx _#6 Hst)) as (Hclt & Hclt').
  apply extract_functional.
    {
    subst C'.
    rewrite -> !den_extend_iurel.
    rewrite -> !den_iutruncate.
    rewrite -> ceiling_extend_urel.
    rewrite -> ceiling_idem.
    reflexivity.
    }

    {
    eapply subst_closub_under_permit; eauto.
    }
    
    {
    eapply subst_closub_under_permit; eauto.
    }
    
    {
    intros l n q Hnq.
    unfold C' in Hnq.
    rewrite -> den_extend_iurel in Hnq.
    cbn -[C] in Hnq.
    destruct Hnq as (H & Hnq).
    assert (l <= k) as Hlk by omega.
    clear H.
    so (contingent_instance_elim _#9 Hnq) as (_ & R & HR).
    so (HR _#3 (le_refl _) (relctx_downward _#7 Hlk Hst)) as (Hn & Hq & _).
    clear HR.
    exists (iutruncate (S l) R).
    simpsub.
    change (map_term (extend (succ top) top) n) with (down top n) in Hn.
    change (map_term (extend (succ top) top) q) with (down top q) in Hq.
    split.
      {
      eapply (interp_updown _ top); eauto using le_ord_refl.
      }

      {
      eapply (interp_updown _ top); eauto using le_ord_refl.
      }
    }
  }
assert (forall k t t',
          k <= j
          -> relctx k s s' t t' G
          -> pwctx k (dot (exttin top C h) t) (dot (exttin top C h) t') (hyp_tp :: G)) as Htp.
  {
  intros k t t' Hk Ht.
  set (h' := lt_ord_impl_le_ord _ _ h).
  set (C' := extend_iurel h' (iutruncate (S k) (iubase C))).
  apply pwctx_cons_tp.
    {
    eapply relctx_pwctx; eauto.
    }
  apply (seqhyp_tp _#3 C').
    {
    apply interp_eval_refl.
    apply interp_extt.
    apply le_ord_refl.
    }

    {
    apply interp_eval_refl.
    apply interp_extt.
    apply le_ord_refl.
    }
  }
assert (forall k t t',
          k <= j
          -> relctx k s s' t t' G
          -> pwctx k
               (dot (lam triv) (dot triv (dot (up top m) (dot (exttin top C h) t))))
               (dot (lam triv) (dot triv (dot (up top p) (dot (exttin top C h) t'))))
               (hyp_tm (pi (var 2) (subst (under 1 (sh 3)) b)) ::
                hyp_tm (subtype (var 1) (mu (subst (dot (var 0) (sh 3)) a))) ::
                hyp_tm a :: hyp_tp :: G)) as Hss.
  {
  intros k t t' Hk Hst.
  assert (k <= i) as Hki by omega.
  set (h' := lt_ord_impl_le_ord _ _ h).
  set (C' := extend_iurel h' (iutruncate (S k) (iubase C))).
  apply pwctx_cons_tm.
    {
    apply pwctx_cons_tm_seq.
      {
      apply pwctx_cons_tm_seq.
        {
        apply Htp; auto.
        }

        {
        so (HF C h h') as (Hl & Hr).
        simpsubin Hl.
        simpsubin Hr.
        so (basic_downward _#7 Hj Hl) as H.
        renameover H into Hl.
        so (basic_downward _#7 Hj Hr) as H.
        renameover H into Hr.
        so (Hseqa _ _ _ (Htp _ _ _ Hk Hst)) as (R' & Hlt & Hrt & _).
        assert (R' = iutruncate (S k) (extend_iurel h' (pi1 F C))).
          {
          so (Hseqa _#3 (Htp _#3 Hk (relctx_swap1 _#6 Hst))) as (R'' & Hl' & _ & _ & Hrt').
          so (interp_fun _#7 (basic_downward _#7 Hk Hl) Hl'); subst R''.
          so (interp_fun _#7 Hrt Hrt') as H.
          rewrite -> iutruncate_combine_le in H; auto.
          omega.
          }
        subst R'.
        apply (seqhyp_tm _#5 (iutruncate (S k) (extend_iurel h' (pi1 F C)))); auto.
        cbn.
        split; [omega |].
        unfold up.
        rewrite -> !extend_term_cancel; auto.
        apply (urel_downward_leq _#3 j); auto.
        }

        {
        intros l u u' Hu.
        so (Hseqa _#3 Hu) as (R & Hl & Hr & _).
        exists toppg, R.
        auto.
        }
      }

      {
      simpsub.
      apply (seqhyp_tm _#5 (iusubtype stop k C' (iutruncate (S k) (iubase (extend_urel top stop Mu))))).
        {
        apply interp_eval_refl.
        apply interp_subtype.
          {
          apply interp_eval_refl.
          apply interp_extt.
          apply le_ord_refl.
          }

          {
          so (Hmu _#3 (relctx_pwctx _#6 (relctx_swap2 _#6 Hst))) as (_ & R & Hl & Hr & _).
          so (interp_fun _#7 (basic_downward _#7 Hki Hmur) Hr); subst R.
          exact Hl.
          }
        }

        {
        apply interp_eval_refl.
        apply interp_subtype.
          {
          apply interp_eval_refl.
          apply interp_extt.
          apply le_ord_refl.
          }

          {
          so (Hmu _#3 (relctx_pwctx _#6 (relctx_swap1 _#6 Hst))) as (_ & R & Hl & Hr & _).
          so (interp_fun _#7 (basic_downward _#7 Hki Hmul) Hl); subst R.
          exact Hr.
          }
        }

        {
        cbn.
        do2 5 split; auto using star_refl; try (apply hygiene_auto; cbn; auto; done).
        intros l n q Hl Hnq.
        destruct Hnq as (_, Hnq).
        split; [omega |].
        cbn -[Mu].
        destruct Hnq as (Hnq & _).
        exact Hnq.
        }
      }

      {
      clear i j m p Hmp s s' t t' Hs Hst Hmul Hmur HF C Hincl Hj Htp C' F Mu h h' HmonoF k Hk Hki Hfunc.
      intros i ss ss' Hss.
      so (pwctx_cons_invert_simple _#5 Hss) as (m & p & s1 & s1' & Hs1 & Hmp & -> & ->).
      so (pwctx_cons_invert_simple _#5 Hs1) as (c & d & s & s' & Hs & Hcd & -> & ->).
      simpsub.
      clear Hss Hs1.
      clear m p Hmp.
      invertc Hcd.
      intros R1 Hl1 Hr1.
      so (Hmu _#3 Hs) as (_ & R2 & Hl2 & Hr2 & _).
      exists toppg, (iusubtype stop i R1 R2).
      split.
        {
        apply interp_eval_refl.
        apply interp_subtype; auto.
        }

        {
        apply interp_eval_refl.
        apply interp_subtype; auto.
        }
      }
    }

    {
    simpsub.
    change (3 + 1) with 4.
    simpsub.
    clear m p Hmp.
    so (Hfunc _ _ _ Hk Hst) as H.
    destruct H as (B & Hbl & Hbr).
    fold h' in Hbl, Hbr.
    fold C' in Hbl, Hbr.
    apply (seqhyp_tm _#5 (iupi stop k C' B)).
      {
      apply interp_eval_refl.
      apply interp_pi; auto.
      apply interp_eval_refl.
      apply interp_extt.
      apply le_ord_refl.
      }

      {
      apply interp_eval_refl.
      apply interp_pi; auto.
      apply interp_eval_refl.
      apply interp_extt.
      apply le_ord_refl.
      }

      {
      exists triv, triv.
      do2 5 split; auto using star_refl.
        {
        apply hygiene_auto; cbn.
        split; auto.
        apply hygiene_auto; cbn; auto.
        }

        {
        apply hygiene_auto; cbn.
        split; auto.
        apply hygiene_auto; cbn; auto.
        }
      intros l n q Hlk Hnq.
      simpsub.
      so Hnq as H.
      unfold C' in H.
      rewrite -> den_extend_iurel in H.
      cbn -[C] in H.
      destruct H as (_ & H).
      so (contingent_instance_elim _#9 H) as (Hnq' & R & HR).
      clear H.
      so (HR _ _ _ (le_refl _) (relctx_downward _#7 Hlk Hst)) as (Hl & _ & Hinh).
      clear HR.
      invert Hbl.
      intros _ _ Hact.
      so (Hact _#3 Hlk Hnq) as Hl'.
      clear Hact.
      simpsubin Hl'.
      so (interp_fun _#7 (interp_updown _#8 (le_ord_refl _) Hl) Hl') as Heq.
      match goal with
      | |- rel (den ?Z) _ _ _ => replace Z with (iutruncate (S l) R)
      end.
      rewrite -> den_iutruncate.
      split; [omega |].
      auto.
      }
    }

    {
    intros l u Hlk Htuu.
    simpsub.
    change (3 + 1) with 4.
    simpsub.
    so (pwctx_cons_invert_simple _#5 Htuu) as (x & y & u1 & u1' & Hu1 & Hxy & Heq & ->).
    simpsub.
    simpsubin Hu1.
    injectionc Heq.
    intros <- _.
    clear x y Hxy Htuu.
    so (pwctx_cons_invert_simple _#5 Hu1) as (x & y & u2 & u2' & Hu2 & Hxy & Heq & ->).
    clear Hu1.
    simpsub.
    injectionc Heq.
    intros <- _.
    clear x y Hxy.
    so (pwctx_cons_invert_simple _#5 Hu2) as (x & y & u & u' & Htu & Hxy & Heq & ->).
    clear Hu2.
    injectionc Heq.
    intros <- <-.
    simpsub.
    simpsubin Hxy.
    invertc Hxy.
    intros R Hl Hr.
    invert (basic_value_inv _#6 value_extt Hl).
    intros w R' h'' _ Heq <-.
    injection (objin_inj _ _ _ Heq); clear Heq.
    intros Heq ->.
    injectionT Heq.
    intros ->.
    so (proof_irrelevance _ h h''); subst h''.
    assert (l <= j) as Hlj by omega.
    so (relctx_trans_right _#7 (pwctx_impl_seqctx _#4 Htu) (relctx_downward _#7 Hlk Hst)) as Hstu.
    clear C'.
    set (C' := extend_iurel h' (iutruncate (S l) (iubase C))).
    so (Hfunc _#3 Hlj Hstu) as (B & Hbtl & Hbur).
    so (Hfunc _#3 Hlj (relctx_downward _#7 Hlk Hst)) as (B' & Hbtl' & Hbtr).
    fold h' in Hbtl, Hbur, Hbtl', Hbtr.
    fold C' in Hbtl, Hbur, Hbtl', Hbtr.
    so (functional_fun _#8 Hbtl Hbtl'); subst B'.
    clear Hbtl Hbtl'.
    apply (relhyp_tm _#4 (iupi stop l C' B)).
      {
      apply interp_eval_refl.
      apply interp_pi; auto.
      apply interp_eval_refl.
      apply interp_extt.
      apply le_ord_refl.
      }

      {
      apply interp_eval_refl.
      apply interp_pi; auto.
      }
    }

    (* symmetric *)
    {
    intros l u Hlk Htuu.
    simpsub.
    change (3 + 1) with 4.
    simpsub.
    so (pwctx_cons_invert_simple _#5 Htuu) as (x & y & u1 & u1' & Hu1 & Hxy & -> & Heq).
    simpsub.
    simpsubin Hu1.
    injectionc Heq.
    intros <- _.
    clear x y Hxy Htuu.
    so (pwctx_cons_invert_simple _#5 Hu1) as (x & y & u2 & u2' & Hu2 & Hxy & -> & Heq).
    clear Hu1.
    simpsub.
    injectionc Heq.
    intros <- _.
    clear x y Hxy.
    so (pwctx_cons_invert_simple _#5 Hu2) as (x & y & u & u' & Hut & Hxy & -> & Heq).
    clear Hu2.
    injectionc Heq.
    intros <- <-.
    simpsub.
    simpsubin Hxy.
    invertc Hxy.
    intros R Hl Hr.
    invert (basic_value_inv _#6 value_extt Hr).
    intros w R' h'' _ Heq <-.
    injection (objin_inj _ _ _ Heq); clear Heq.
    intros Heq ->.
    injectionT Heq.
    intros ->.
    so (proof_irrelevance _ h h''); subst h''.
    assert (l <= j) as Hlj by omega.
    so (relctx_trans_left _#7 (pwctx_impl_seqctx _#4 Hut) (relctx_downward _#7 Hlk Hst)) as Hstu.
    clear C'.
    set (C' := extend_iurel h' (iutruncate (S l) (iubase C))).
    so (Hfunc _#3 Hlj Hstu) as (B & Hbul & Hbtr).
    so (Hfunc _#3 Hlj (relctx_downward _#7 Hlk Hst)) as (B' & Hbtl & Hbtr').
    fold h' in Hbul, Hbtr, Hbtl, Hbtr'.
    fold C' in Hbul, Hbtr, Hbtl, Hbtr'.
    so (functional_fun _#8 Hbtr Hbtr'); subst B'.
    clear Hbtr Hbtr'.
    apply (relhyp_tm _#4 (iupi stop l C' B)).
      {
      apply interp_eval_refl.
      apply interp_pi; auto.
      apply interp_eval_refl.
      apply interp_extt.
      apply le_ord_refl.
      }

      {
      apply interp_eval_refl.
      apply interp_pi; auto.
      }
    }
  }
so (Hseqind j _ _ (Hss j s s' (le_refl _) (relctx_refl _#4 (pwctx_downward _#5 Hj Hs)))) as (R & Hl & Hr & Hinh & _).
simpsubin Hl.
simpsubin Hr.
simpsubin Hinh.
split.
  {
  unfold Mu.
  rewrite -> mu_fix; auto.
  so (HmonoF C Mu Hincl) as Hincl'.
  cbn in Hincl'.
  apply Hincl'; auto.
  }
exists R.
intros k c d Hk Hcd.
destruct Hcd as (t & t' & Hst & -> & ->).
simpsub.
assert (k <= i) as Hki by omega.
so (Hseqind k _ _ (Hss k t t' Hk Hst)) as H.
simpsubin H.
destruct H as (R' & Hlt & Hrt & _).
so (Hseqind k _ _ (Hss k s t' Hk (relctx_swap1 _#6 Hst))) as H.
simpsubin H.
destruct H as (R'' & Hl' & Hrt' & _).
so (interp_fun _#7 Hl' (basic_downward _#7 Hk Hl)); subst R''.
so (interp_fun _#7 Hrt Hrt'); subst R'.
do2 2 split; auto.
apply (urel_downward_leq _#3 j); auto.
Qed.


Lemma sound_mu_ind_univ :
  forall G lv a b m,
    pseq G (deq lv lv pagetp)
    -> pseq (hyp_tm (univ lv) :: G) (deq a a (univ (subst sh1 lv)))
    -> pseq G (deq triv triv (ispositive a))
    -> pseq
         (hyp_tm (pi (var 2) (subst (under 1 (sh 3)) b)) ::
          hyp_tm (subtype (var 1) (mu (subst (under 1 (sh 2)) a))) ::
          hyp_tm a ::
          hyp_tm (univ lv) :: 
          G)
         (deq 
            (subst (dot (var 2) (sh 4)) b)
            (subst (dot (var 2) (sh 4)) b) 
            (univ (subst (sh 4) lv)))
    -> pseq
         (hyp_tm (pi (var 2) (subst (under 1 (sh 3)) b)) ::
          hyp_tm (subtype (var 1) (mu (subst (under 1 (sh 2)) a))) ::
          hyp_tm a ::
          hyp_tm (univ lv) :: 
          G)
         (deq triv triv (subst (dot (var 2) (sh 4)) b))
    -> pseq G (deq m m (mu a))
    -> pseq G (deq triv triv (subst1 m b)).
Proof.
intros G lv a b m.
revert G.
refine (seq_pseq 2 [hyp_tp] a [hyp_tp] b 6 [] _ [_] _ [] _ [_; _; _; _] _ [_; _; _; _] _ [] _ _ _).
cbn.
(* why is this necessary? *)
replace (varx (obj stop) 0) with (@var (obj stop) 0) by reflexivity.
intros G Hcla Hclb Hseqlv Hseqa Hpos Hseqb Hseqind Hseqm.
rewrite -> seq_univ in Hseqa, Hseqb.
rewrite -> seq_deq in Hseqind, Hseqm |- *.
rewrite -> seq_ispositive in Hpos; auto.
assert (forall i s s',
          pwctx i s s'
            (hyp_tm (pi (var 2) (subst (dot (var 0) (sh 4)) b))
             :: hyp_tm (subtype (var 1) (mu (subst (dot (var 0) (sh 3)) a)))
             :: hyp_tm a 
             :: hyp_tm (univ lv) 
             :: G)
          -> exists pg R,
               pginterp (subst s (subst (sh 4) lv)) pg
               /\ pginterp (subst s' (subst (sh 4) lv)) pg
               /\ interp pg true i (subst s (subst (dot (var 2) (sh 4)) b)) R
               /\ interp pg false i (subst s' (subst (dot (var 2) (sh 4)) b)) R
               /\ rel (den R) i triv triv) as Hseqind'.
  {
  intros i s s' Hs.
  so (Hseqb _#3 Hs) as (pg & R & Hlvl & Hlvr & Hbl & Hbr & _).
  so (Hseqind _#3 Hs) as (R' & Hbl' & _ & Hinh & _).
  so (interp_fun _#7 Hbl Hbl'); subst R'.
  exists pg, R.
  do2 4 split; auto.
  }
clear Hseqb Hseqind.
rename Hseqind' into Hseqind.
so Hseqlv as H.
rewrite -> seq_deq in H.
exploit (seq_pagetp_invert G lv) as Hlevel.
  {
  intros i s s' Hs.
  so (H _#3 Hs) as (R & H1 & _ & H2 & _).
  eauto.
  }
clear H.
assert (forall i s s',
          pwctx i s s' G
          -> exists pg (F : wurel_ofe (cin pg) -n> wiurel_ofe (cin pg)) R,
               pginterp (subst s lv) pg
               /\ interp toppg true i (mu (subst (under 1 s) a)) R
               /\ interp toppg false i (mu (subst (under 1 s') a)) R
               /\ R = iubase (extend_urel (cin pg) stop (mu_urel (cin pg) (fun X => den (pi1 F X))))
               /\ monotone (fun X => den (pi1 F X))
               /\ (forall X (h : cin pg << stop) (h' : cin pg <<= stop),
                     interp pg true i (subst (dot (exttin (cin pg) X h) s) a) (extend_iurel h' (pi1 F X))
                     /\ interp pg false i (subst (dot (exttin (cin pg) X h) s') a) (extend_iurel h' (pi1 F X)))) as Hmu.
  {
  intros i s s' Hs.
  so (Hlevel _#3 Hs) as (pg & Hlvl & Hlvr).
  so (Hseqm _#3 Hs) as (A & Hmul & Hmur & Hm & _).
  simpsubin Hmul.
  simpsubin Hmur.
  exploit (extract_ind pg i (subst (under 1 s) a) (subst (under 1 s') a)) as H.
    {
    intros j X Y h Hj HXY.
    so (pwctx_cons_exttin_tm pg (cin pg) j X Y h s s' G lv (le_ord_refl _) Hlvl Hseqlv HXY (pwctx_downward _#5 Hj Hs)) as Hss.
    so (Hseqa _ _ _ Hss) as (pg' & R & Hlvl' & _ & Hal & Har & _).
    simpsubin Hlvl'.
    so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
    exists R.
    simpsub.
    eauto.
    }
  destruct H as (F & HF).
  assert (nonexpansive (fun X => den (pi1 F X))) as Hne.
    {
    apply compose_ne_ne; auto using den_nonexpansive.
    exact (pi2 F).
    }
  assert (monotone (fun X => den (pi1 F X))) as HmonoF.
    {
    refine (monotone_from_ispositive _#4 Hpos _#3 Hs _).
    intros X h h'.
    so (HF X h h') as (H & _).
    simpsubin H.
    exact H.
    }
  so (positive_impl_robust _#3 (Hpos _#3 Hs andel)) as Hrobust.
  so (positive_impl_robust _#3 (Hpos _#3 Hs ander)) as Hrobust'.
  exists pg, F.
  exists (iubase (extend_urel (cin pg) stop (mu_urel (cin pg) (fun X => den (pi1 F X))))).
  assert (interp pg true i (mu (subst (under 1 s) a)) (iubase (extend_urel (cin pg) stop (mu_urel (cin pg) (fun X => den (pi1 F X)))))) as Hmul'.
    {
    apply interp_eval_refl.
    apply interp_mu; auto using le_ord_refl.
    intros X h.
    so (HF X h (lt_ord_impl_le_ord _ _ h)) as (H & _).
    simpsubin H.
    simpsub.
    exact H.
    }
  so (interp_fun _#7 Hmul Hmul'); subst A.
  do2 5 split; auto.
  intros X h h'.
  so (HF X h h') as H.
  simpsubin H.
  exact H.
  }
intros i s s' Hs.
so (Hmu _ _ _ Hs) as (pg & F & R & Hlvl & Hmul & Hmur & HeqMu & HmonoF & HF).
set (w := cin pg).
(* We need cex pg <<= w = cin pg because we're using terms of candidate
   level w (since they are in an inductive type belonging to pg), but 
   we need to cancel up and down inside a type expression (namely b),
   which we can only do if cex b <<= w.  (Consider the rules of restriction.)

   Perhaps this can be teased apart.  I haven't tried all that hard since, for
   the moment at least, we always have cex pg = cin pg.
*)
assert (cex pg <<= w) as Hexw.
  {
  unfold w.
  apply le_ord_refl'.
  symmetry.
  eapply pginterp_cin_cex; eauto.
  }
simpsubin Hmul.
simpsubin Hmur.
so (Hseqm _#3 Hs) as (R' & H & _ & Hm & _).
simpsubin H.
so (interp_fun _#7 H Hmul); subst R'; clear H.
subst R.
set (Mu := mu_urel w (fun X => den (pi1 F X))) in Hmul, Hmur, Hm.
rewrite -> den_iubase in Hm.
cbn -[mu_urel] in Hm.
set (C := contingent_instance pg Mu b s s' G).
assert (incl C Mu) as Hincl.
  {
  clear m Hseqm Hseqind Hm Hmu.
  intros j m p Hmp.
  destruct Hmp; auto.
  }
cut (rel C i (down w (subst s m)) (down w (subst s' m))).
  {
  intro H.
  so (contingent_instance_elim _#9 H) as (Hn & R & HR); clear H.
  so (HR i s s' (le_refl _) (relctx_refl _#4 Hs)) as H.
  destruct H as (Hl & Hr & Hinh).
  simpsubin Hl.
  simpsubin Hr.
  exists (iutruncate (S i) R).
  simpsub.
  do2 4 split; auto; try (split; [omega | auto]; done).
    {
    apply (interp_increase pg); auto using toppg_max.
    eapply interp_updown; eauto.
    }

    {
    apply (interp_increase pg); auto using toppg_max.
    eapply interp_updown; eauto.
    }
  }
cut (incl Mu C); auto.
clear m Hm Hseqm.
apply mu_least.
intros j m p Hmp.
assert (j <= i) as Hj.
  {
  set (h := le_ord_succ _ _ (cin_top pg)).
  set (h' := cin_stop pg).
  so (HF C h h') as (H & _).
  assert (rel (den (extend_iurel h' (pi1 F C))) j (up w m) (up w p)) as Hmp'.
    {
    cbn.
    unfold w, up.
    rewrite -> !extend_term_cancel; auto.
    }
  refine (basic_member_index _#9 H Hmp').
  }
so (le_ord_succ _ _ (cin_top pg)) as h.
change (w << stop) in h.
assert (forall k t t',
          k <= j
          -> relctx k s s' t t' G
          -> let h' := lt_ord_impl_le_ord _ _ h in
             let C' := extend_iurel h' (iutruncate (S k) (iubase C))
             in
               exists (B : urelsp (den C') -n> siurel_ofe),
                 functional the_system pg true k (den C') (subst (under 1 t) b) B
                 /\ functional the_system pg false k (den C') (subst (under 1 t') b) B) as Hfunc.
  {
  intros k t t' Hk Hst h' C'.
  assert (k <= i) as Hki by omega.
  so (pwctx_impl_closub _#4 (relctx_pwctx _#6 Hst)) as (Hclt & Hclt').
  apply extract_functional.
    {
    subst C'.
    rewrite -> !den_extend_iurel.
    rewrite -> !den_iutruncate.
    rewrite -> ceiling_extend_urel.
    rewrite -> ceiling_idem.
    reflexivity.
    }

    {
    eapply subst_closub_under_permit; eauto.
    }
    
    {
    eapply subst_closub_under_permit; eauto.
    }
    
    {
    intros l n q Hnq.
    unfold C' in Hnq.
    rewrite -> den_extend_iurel in Hnq.
    cbn -[C] in Hnq.
    destruct Hnq as (H & Hnq).
    assert (l <= k) as Hlk by omega.
    clear H.
    so (contingent_instance_elim _#9 Hnq) as (_ & R & HR).
    so (HR _#3 (le_refl _) (relctx_downward _#7 Hlk Hst)) as (Hn & Hq & _).
    clear HR.
    exists (iutruncate (S l) R).
    simpsub.
    change (map_term (extend stop w) n) with (down w n) in Hn.
    change (map_term (extend stop w) q) with (down w q) in Hq.
    split.
      {
      eapply interp_updown; eauto.
      }

      {
      eapply interp_updown; eauto.
      }
    }
  }
assert (forall k t t',
          k <= j
          -> relctx k s s' t t' G
          -> pwctx k (dot (exttin w C h) t) (dot (exttin w C h) t') (hyp_tm (univ lv) :: G)) as Htp.
  {
  intros k t t' Hk Ht.
  set (h' := lt_ord_impl_le_ord _ _ h).
  set (C' := extend_iurel h' (iutruncate (S k) (iubase C))).
  apply pwctx_cons_tm_seq.
    {
    eapply relctx_pwctx; eauto.
    }
    
    {
    apply (seqhyp_tm _#5 (iuuniv the_system k pg)).
      {
      simpsub.
      apply interp_eval_refl.
      apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
      exact (relctx_pginterp _#8 Hseqlv Ht Hlvl andel).
      }
  
      {
      simpsub.
      apply interp_eval_refl.
      apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
      exact (relctx_pginterp _#8 Hseqlv Ht Hlvl ander).
      }

      {
      cbn.
      split; auto.
      exists C'.
      rewrite -> sint_unroll.
      split.
        {
        apply interp_eval_refl.
        apply interp_extt.
        apply le_ord_refl.
        }

        {
        apply interp_eval_refl.
        apply interp_extt.
        apply le_ord_refl.
        }
      }
    }

    {
    clear a b Hcla Hclb Hseqa Hpos Hseqind Hmu i s s' Hs pg F Hlvl Hmur Hmul HmonoF HF w Hexw Mu C Hincl j m p Hmp Hj h Hfunc k t t' Hk Ht h' C'.
    intros i s s' Hs.
    so (Hlevel _#3 Hs) as (pg & Hlvl & Hlvr).
    exists toppg, (iuuniv the_system i pg).
    simpsub.
    split.
      {
      apply interp_eval_refl.
      apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
      }

      {
      apply interp_eval_refl.
      apply interp_univ; eauto using pginterp_str_top, pginterp_cex_top.
      }
    }
  }
assert (forall k t t',
          k <= j
          -> relctx k s s' t t' G
          -> pwctx k
               (dot (lam triv) (dot triv (dot (up w m) (dot (exttin w C h) t))))
               (dot (lam triv) (dot triv (dot (up w p) (dot (exttin w C h) t'))))
               (hyp_tm (pi (var 2) (subst (under 1 (sh 3)) b)) ::
                hyp_tm (subtype (var 1) (mu (subst (dot (var 0) (sh 3)) a))) ::
                hyp_tm a :: hyp_tm (univ lv) :: G)) as Hss.
  {
  intros k t t' Hk Hst.
  assert (k <= i) as Hki by omega.
  set (h' := lt_ord_impl_le_ord _ _ h).
  set (C' := extend_iurel h' (iutruncate (S k) (iubase C))).
  apply pwctx_cons_tm.
    {
    apply pwctx_cons_tm_seq.
      {
      apply pwctx_cons_tm_seq.
        {
        apply Htp; auto.
        }

        {
        so (HF C h h') as (Hl & Hr).
        simpsubin Hl.
        simpsubin Hr.
        so (basic_downward _#7 Hj Hl) as H.
        renameover H into Hl.
        so (basic_downward _#7 Hj Hr) as H.
        renameover H into Hr.
        so (Hseqa _ _ _ (Htp _ _ _ Hk Hst)) as (pg' & R' & Hlvtl & Hlvtr & Hlt & Hrt & _).
        assert (R' = iutruncate (S k) (extend_iurel h' (pi1 F C))).
          {
          so (Hseqa _#3 (Htp _#3 Hk (relctx_swap1 _#6 Hst))) as (pg'' & R'' & Hlvtl' & _ & Hl' & _ & _ & Hrt').
          so (interp_fun _#7 (basic_downward _#7 Hk Hl) Hl'); subst R''.
          so (interp_fun _#7 Hrt Hrt') as H.
          rewrite -> iutruncate_combine_le in H; auto.
          omega.
          }
        subst R'.
        apply (seqhyp_tm _#5 (iutruncate (S k) (extend_iurel h' (pi1 F C)))); eauto using interp_increase, toppg_max.
        cbn.
        split; [omega |].
        unfold up.
        rewrite -> !extend_term_cancel; auto.
        apply (urel_downward_leq _#3 j); auto.
        }

        {
        intros l u u' Hu.
        so (Hseqa _#3 Hu) as (pg' & R & _ & _ & Hl & Hr & _).
        exists pg', R.
        auto.
        }
      }

      {
      simpsub.
      apply (seqhyp_tm _#5 (iusubtype stop k C' (iutruncate (S k) (iubase (extend_urel w stop Mu))))).
        {
        apply interp_eval_refl.
        apply interp_subtype.
          {
          apply interp_eval_refl.
          apply interp_extt.
          apply cin_top.
          }

          {
          so (Hmu _#3 (relctx_pwctx _#6 (relctx_swap2 _#6 Hst))) as (_ & _ & R & _ & Hl & Hr & _).
          so (interp_fun _#7 (basic_downward _#7 Hki Hmur) Hr); subst R.
          exact Hl.
          }
        }

        {
        apply interp_eval_refl.
        apply interp_subtype.
          {
          apply interp_eval_refl.
          apply interp_extt.
          apply cin_top.
          }

          {
          so (Hmu _#3 (relctx_pwctx _#6 (relctx_swap1 _#6 Hst))) as (_ & _ & R & _ & Hl & Hr & _).
          so (interp_fun _#7 (basic_downward _#7 Hki Hmul) Hl); subst R.
          exact Hr.
          }
        }

        {
        cbn.
        do2 5 split; auto using star_refl; try (apply hygiene_auto; cbn; auto; done).
        intros l n q Hl Hnq.
        destruct Hnq as (_, Hnq).
        split; [omega |].
        cbn -[Mu].
        destruct Hnq as (Hnq & _).
        exact Hnq.
        }
      }

      {
      clear i j m p Hmp s s' t t' Hs Hst Hmul Hmur HF C Hincl Hj Htp C' F Mu h h' HmonoF k Hk Hki Hfunc Hlvl.
      intros i ss ss' Hss.
      so (pwctx_cons_invert_simple _#5 Hss) as (m & p & s1 & s1' & Hs1 & Hmp & -> & ->).
      so (pwctx_cons_invert_simple _#5 Hs1) as (c & d & s & s' & Hs & Hcd & -> & ->).
      simpsub.
      clear Hss Hs1.
      clear m p Hmp.
      simpsubin Hcd.
      invertc Hcd.
      intros Ru Huniv _ Hcd.
      invert (basic_value_inv _#6 value_univ Huniv).
      intros pg' _ _ _ <-.
      cbn in Hcd.
      destruct Hcd as (_ & R1 & Hl1 & Hr1).
      rewrite -> sint_unroll in Hl1, Hr1.
      so (Hmu _#3 Hs) as (_ & _ & R2 & _ & Hl2 & Hr2 & _).
      exists toppg, (iusubtype stop i R1 R2).
      split.
        {
        apply interp_eval_refl.
        apply interp_subtype; auto.
        apply (interp_increase pg'); auto using toppg_max.
        }

        {
        apply interp_eval_refl.
        apply interp_subtype; auto.
        apply (interp_increase pg'); auto using toppg_max.
        }
      }
    }

    {
    simpsub.
    change (3 + 1) with 4.
    simpsub.
    clear m p Hmp.
    so (Hfunc _ _ _ Hk Hst) as H.
    destruct H as (B & Hbl & Hbr).
    fold h' in Hbl, Hbr.
    fold C' in Hbl, Hbr.
    apply (seqhyp_tm _#5 (iupi stop k C' B)).
      {
      apply (interp_increase pg); auto using toppg_max.
      apply interp_eval_refl.
      apply interp_pi; auto.
      apply interp_eval_refl.
      apply interp_extt.
      apply le_ord_refl.
      }

      {
      apply (interp_increase pg); auto using toppg_max.
      apply interp_eval_refl.
      apply interp_pi; auto.
      apply interp_eval_refl.
      apply interp_extt.
      apply le_ord_refl.
      }

      {
      exists triv, triv.
      do2 5 split; auto using star_refl.
        {
        apply hygiene_auto; cbn.
        split; auto.
        apply hygiene_auto; cbn; auto.
        }

        {
        apply hygiene_auto; cbn.
        split; auto.
        apply hygiene_auto; cbn; auto.
        }
      intros l n q Hlk Hnq.
      simpsub.
      so Hnq as H.
      unfold C' in H.
      rewrite -> den_extend_iurel in H.
      cbn -[C] in H.
      destruct H as (_ & H).
      so (contingent_instance_elim _#9 H) as (Hnq' & R & HR).
      clear H.
      so (HR _ _ _ (le_refl _) (relctx_downward _#7 Hlk Hst)) as (Hl & _ & Hinh).
      clear HR.
      invert Hbl.
      intros _ _ Hact.
      so (Hact _#3 Hlk Hnq) as Hl'.
      clear Hact.
      simpsubin Hl'.
      so (interp_fun _#7 (interp_updown _#8 Hexw Hl) Hl') as Heq.
      match goal with
      | |- rel (den ?Z) _ _ _ => replace Z with (iutruncate (S l) R)
      end.
      rewrite -> den_iutruncate.
      split; [omega |].
      auto.
      }
    }

    {
    intros l u Hlk Htuu.
    simpsub.
    change (3 + 1) with 4.
    simpsub.
    so (pwctx_cons_invert_simple _#5 Htuu) as (x & y & u1 & u1' & Hu1 & Hxy & Heq & ->).
    simpsub.
    simpsubin Hu1.
    injectionc Heq.
    intros <- _.
    clear x y Hxy Htuu.
    so (pwctx_cons_invert_simple _#5 Hu1) as (x & y & u2 & u2' & Hu2 & Hxy & Heq & ->).
    clear Hu1.
    simpsub.
    injectionc Heq.
    intros <- _.
    clear x y Hxy.
    so (pwctx_cons_invert_simple _#5 Hu2) as (x & y & u & u' & Htu & Hxy & Heq & ->).
    clear Hu2.
    injectionc Heq.
    intros <- <-.
    simpsub.
    simpsubin Hxy.
    invertc Hxy.
    intros Ru Huniv _ Hlr.
    invert (basic_value_inv _#6 value_univ Huniv).
    intros pg' Hlvt _ _ <-.
    so (pginterp_fun _#3 Hlvt (relctx_pginterp _#8 Hseqlv Hst Hlvl andel)); subst pg'.
    cbn in Hlr.
    destruct Hlr as (_ & R & Hl & Hr).
    rewrite -> sint_unroll in Hl, Hr.
    invert (basic_value_inv _#6 value_extt Hl).
    intros w' R' h'' _ Heq <-.
    injection (objin_inj _ _ _ Heq); clear Heq.
    intros Heq ->.
    injectionT Heq.
    intros ->.
    so (proof_irrelevance _ h h''); subst h''.
    assert (l <= j) as Hlj by omega.
    so (relctx_trans_right _#7 (pwctx_impl_seqctx _#4 Htu) (relctx_downward _#7 Hlk Hst)) as Hstu.
    clear C'.
    set (C' := extend_iurel h' (iutruncate (S l) (iubase C))).
    so (Hfunc _#3 Hlj Hstu) as (B & Hbtl & Hbur).
    so (Hfunc _#3 Hlj (relctx_downward _#7 Hlk Hst)) as (B' & Hbtl' & Hbtr).
    fold h' in Hbtl, Hbur, Hbtl', Hbtr.
    fold C' in Hbtl, Hbur, Hbtl', Hbtr.
    so (functional_fun _#8 Hbtl Hbtl'); subst B'.
    clear Hbtl Hbtl'.
    apply (relhyp_tm _#4 (iupi stop l C' B)).
      {
      apply (interp_increase pg); auto using toppg_max.
      apply interp_eval_refl.
      apply interp_pi; auto.
      apply interp_eval_refl.
      apply interp_extt.
      apply le_ord_refl.
      }

      {
      apply (interp_increase pg); auto using toppg_max.
      apply interp_eval_refl.
      apply interp_pi; auto.
      }
    }

    (* symmetric *)
    {
    intros l u Hlk Htuu.
    simpsub.
    change (3 + 1) with 4.
    simpsub.
    so (pwctx_cons_invert_simple _#5 Htuu) as (x & y & u1 & u1' & Hu1 & Hxy & -> & Heq).
    simpsub.
    simpsubin Hu1.
    injectionc Heq.
    intros <- _.
    clear x y Hxy Htuu.
    so (pwctx_cons_invert_simple _#5 Hu1) as (x & y & u2 & u2' & Hu2 & Hxy & -> & Heq).
    clear Hu1.
    simpsub.
    injectionc Heq.
    intros <- _.
    clear x y Hxy.
    so (pwctx_cons_invert_simple _#5 Hu2) as (x & y & u & u' & Hut & Hxy & -> & Heq).
    clear Hu2.
    injectionc Heq.
    intros <- <-.
    simpsub.
    simpsubin Hxy.
    invertc Hxy.
    intros Ru Huniv _ Hlr.
    invert (basic_value_inv _#6 value_univ Huniv).
    intros pg' Hlvu _ _ <-.
    so (relctx_trans_left _#7 (pwctx_impl_seqctx _#4 Hut) (relctx_downward _#7 Hlk Hst)) as Hut'.
    so (pginterp_fun _#3 Hlvu (relctx_pginterp _#8 Hseqlv Hut' Hlvl andel)); subst pg'.
    cbn in Hlr.
    destruct Hlr as (_ & R & Hl & Hr).
    rewrite -> sint_unroll in Hl, Hr.
    invert (basic_value_inv _#6 value_extt Hr).
    intros w' R' h'' _ Heq <-.
    injection (objin_inj _ _ _ Heq); clear Heq.
    intros Heq ->.
    injectionT Heq.
    intros ->.
    so (proof_irrelevance _ h h''); subst h''.
    assert (l <= j) as Hlj by omega.
    so (relctx_trans_left _#7 (pwctx_impl_seqctx _#4 Hut) (relctx_downward _#7 Hlk Hst)) as Hstu.
    clear C'.
    set (C' := extend_iurel h' (iutruncate (S l) (iubase C))).
    so (Hfunc _#3 Hlj Hstu) as (B & Hbul & Hbtr).
    so (Hfunc _#3 Hlj (relctx_downward _#7 Hlk Hst)) as (B' & Hbtl & Hbtr').
    fold h' in Hbul, Hbtr, Hbtl, Hbtr'.
    fold C' in Hbul, Hbtr, Hbtl, Hbtr'.
    so (functional_fun _#8 Hbtr Hbtr'); subst B'.
    clear Hbtr Hbtr'.
    apply (relhyp_tm _#4 (iupi stop l C' B)).
      {
      apply (interp_increase pg); auto using toppg_max.
      apply interp_eval_refl.
      apply interp_pi; auto.
      apply interp_eval_refl.
      apply interp_extt.
      apply le_ord_refl.
      }

      {
      apply (interp_increase pg); auto using toppg_max.
      apply interp_eval_refl.
      apply interp_pi; auto.
      }
    }
  }
so (Hseqind j _ _ (Hss j s s' (le_refl _) (relctx_refl _#4 (pwctx_downward _#5 Hj Hs)))) as (pg' & R & Hlvl' & _ & Hl & Hr & Hinh).
simpsubin Hlvl'.
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'; clear Hlvl'.
simpsubin Hl.
simpsubin Hr.
simpsubin Hinh.
split.
  {
  unfold Mu.
  rewrite -> mu_fix; auto.
  so (HmonoF C Mu Hincl) as Hincl'.
  cbn in Hincl'.
  apply Hincl'; auto.
  }
exists R.
intros k c d Hk Hcd.
destruct Hcd as (t & t' & Hst & -> & ->).
simpsub.
assert (k <= i) as Hki by omega.
fold w.
so (Hseqind k _ _ (Hss k t t' Hk Hst)) as H.
simpsubin H.
destruct H as (pg' & R' & Hlvl' & _ & Hlt & Hrt & _).
simpsubin Hlvl'.
so (pginterp_fun _#3 Hlvl' (relctx_pginterp _#8 Hseqlv Hst Hlvl andel)); subst pg'; clear Hlvl'.
so (Hseqind k _ _ (Hss k s t' Hk (relctx_swap1 _#6 Hst))) as H.
simpsubin H.
destruct H as (pg' & R'' & Hlvl' & _ & Hl' & Hrt' & _).
so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'; clear Hlvl'.
so (interp_fun _#7 Hl' (basic_downward _#7 Hk Hl)); subst R''.
so (interp_fun _#7 Hrt Hrt'); subst R'.
do2 2 split; auto.
apply (urel_downward_leq _#3 j); auto.
Qed.
