
Require Import Coq.Lists.List.

Require Import Relation.
Require Import Tactics.
Require Import Sequence.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.
Require Import Promote.
Require Import Hygiene.
Require Import Rules.
Require Import DerivedRules.
Require Defs.
Require Import Obligations.
Require Import Morphism.
Require Import DefsEquiv.
Require Import Dynamic.
Require Import Equivalence.
Require Import Dots.

Require Import ValidationUtil.
Require Import ValidationAll.
Require Import ValidationSigma.
Require Import ValidationFuture.
Require Import ValidationRec.
Require Import ValidationLevel.
Require Import ValidationMu.
Require Import ValidationNat.
Require Import ValidationPi.
Require Import ValidationSimple.
Require Import ValidationSum.
Require Import ValidationUniv.


Theorem all_rules_valid :
  fold_right (fun P Q => P * Q)%type unit all_obligations.
Proof.
cbn.
repeat split.

exact forallForm_valid.
exact forallEq_valid.
exact forallFormUniv_valid.
exact forallEqUniv_valid.
exact forallSub_valid.
exact forallIntroOf_valid.
exact forallIntroEq_valid.
exact forallIntro_valid.
exact forallElimOf_valid.
exact forallElimEq_valid.
exact forallElim_valid.
exact forallEta_valid.
exact forallExt_valid.
exact forallOfExt_valid.
exact forallFormInv1_valid.
exact forallFormInv2_valid.
exact arrowForm_valid.
exact arrowEq_valid.
exact arrowFormUniv_valid.
exact arrowEqUniv_valid.
exact arrowSub_valid.
exact arrowForallSub_valid.
exact forallArrowSub_valid.
exact arrowIntroOf_valid.
exact arrowIntroEq_valid.
exact arrowIntro_valid.
exact arrowElimOf_valid.
exact arrowElimEq_valid.
exact arrowElim_valid.
exact arrowEta_valid.
exact arrowExt_valid.
exact arrowOfExt_valid.
exact arrowFormInv1_valid.
exact arrowFormInv2_valid.
exact tarrowKind_valid.
exact tarrowKindEq_valid.
exact tarrowForm_valid.
exact tarrowEq_valid.
exact tarrowFormUniv_valid.
exact tarrowEqUniv_valid.
exact tarrowArrowEq_valid.
exact tarrowArrowEqUniv_valid.
exact tarrowIntroOf_valid.
exact tarrowIntroEq_valid.
exact tarrowIntro_valid.
exact tarrowElimOf_valid.
exact tarrowElimEq_valid.
exact tarrowElim_valid.
exact tarrowEta_valid.
exact tarrowExt_valid.
exact karrowKind_valid.
exact karrowKindEq_valid.
exact karrowForm_valid.
exact karrowEq_valid.
exact karrowFormUniv_valid.
exact karrowEqUniv_valid.
exact karrowArrowEq_valid.
exact karrowArrowEqUniv_valid.
exact karrowIntroOf_valid.
exact karrowIntroEq_valid.
exact karrowIntro_valid.
exact karrowElimOf_valid.
exact karrowElimEq_valid.
exact karrowElim_valid.
exact karrowEta_valid.
exact karrowExt_valid.
exact intersectForm_valid.
exact intersectEq_valid.
exact intersectFormUniv_valid.
exact intersectEqUniv_valid.
exact intersectIntroOf_valid.
exact intersectIntroEq_valid.
exact intersectIntro_valid.
exact intersectElimOf_valid.
exact intersectElimEq_valid.
exact intersectElim_valid.
exact intersectFormInv1_valid.
exact intersectFormInv2_valid.
exact guardForm_valid.
exact guardEq_valid.
exact guardFormUniv_valid.
exact guardEqUniv_valid.
exact guardIntroOf_valid.
exact guardIntroEq_valid.
exact guardIntro_valid.
exact guardElimOf_valid.
exact guardElimEq_valid.
exact guardElim_valid.
exact guardSatEq_valid.
exact existsForm_valid.
exact existsEq_valid.
exact existsFormUniv_valid.
exact existsEqUniv_valid.
exact existsSub_valid.
exact existsIntroOf_valid.
exact existsIntroEq_valid.
exact existsIntro_valid.
exact existsElim1Of_valid.
exact existsElim1Eq_valid.
exact existsElim2Of_valid.
exact existsElim2Eq_valid.
exact existsEta_valid.
exact existsExt_valid.
exact existsLeft_valid.
exact existsFormInv1_valid.
exact existsFormInv2_valid.
exact existsFormInv2Eq_valid.
exact prodKind_valid.
exact prodKindEq_valid.
exact prodForm_valid.
exact prodEq_valid.
exact prodFormUniv_valid.
exact prodEqUniv_valid.
exact prodExistsEq_valid.
exact prodExistsEqUniv_valid.
exact prodSub_valid.
exact prodExistsSub_valid.
exact existsProdSub_valid.
exact prodIntroOf_valid.
exact prodIntroEq_valid.
exact prodIntro_valid.
exact prodElim1Of_valid.
exact prodElim1Eq_valid.
exact prodElim1_valid.
exact prodElim2Of_valid.
exact prodElim2Eq_valid.
exact prodElim2_valid.
exact prodEta_valid.
exact prodExt_valid.
exact prodLeft_valid.
exact prodFormInv1_valid.
exact prodFormInv2_valid.
exact futureKind_valid.
exact futureKindEq_valid.
exact futureForm_valid.
exact futureEq_valid.
exact futureFormUniv_valid.
exact futureEqUniv_valid.
exact futureSub_valid.
exact futureIntroOf_valid.
exact futureIntroEq_valid.
exact futureIntro_valid.
exact futureElimOf_valid.
exact futureElimOfLetnext_valid.
exact futureElimOfLetnextNondep_valid.
exact futureElimEq_valid.
exact futureElimIstype_valid.
exact futureElimIstypeLetnext_valid.
exact futureElimEqtype_valid.
exact futureEta_valid.
exact futureExt_valid.
exact futureLeft_valid.
exact recKind_valid.
exact recKindEq_valid.
exact recForm_valid.
exact recEq_valid.
exact recFormUniv_valid.
exact recEqUniv_valid.
exact recUnroll_valid.
exact recUnrollUniv_valid.
exact recBisimilar_valid.
exact voidForm_valid.
exact voidEq_valid.
exact voidFormUniv_valid.
exact voidEqUniv_valid.
exact voidElim_valid.
exact voidSub_valid.
exact abortType_valid.
exact unitKind_valid.
exact unitKindEq_valid.
exact unitForm_valid.
exact unitEq_valid.
exact unitFormUniv_valid.
exact unitEqUniv_valid.
exact unitIntroOf_valid.
exact unitIntro_valid.
exact unitExt_valid.
exact unitLeft_valid.
exact boolForm_valid.
exact boolEq_valid.
exact boolFormUniv_valid.
exact boolEqUniv_valid.
exact boolIntro1Of_valid.
exact boolIntro2Of_valid.
exact boolElimOf_valid.
exact boolElimEq_valid.
exact boolElim_valid.
exact boolElimIstype_valid.
exact boolElimEqtype_valid.
exact boolLeft_valid.
exact iteType_valid.
exact muForm_valid.
exact muEq_valid.
exact muFormUniv_valid.
exact muEqUniv_valid.
exact muUnroll_valid.
exact muUnrollUniv_valid.
exact muInd_valid.
exact muIndUniv_valid.
exact iforallForm_valid.
exact iforallEq_valid.
exact iforallFormUniv_valid.
exact iforallEqUniv_valid.
exact iforallIntroOf_valid.
exact iforallIntroEq_valid.
exact iforallIntro_valid.
exact iforallElimOf_valid.
exact iforallElimEq_valid.
exact iforallElim_valid.

Abort.
  


(* Hardcoded rules *)

Hint Rewrite def_inl def_inr def_sum def_sumcase : prepare.


Lemma sumLeft_valid :
  forall G1 G2 A B C M N, 
    tr (List.app (substctx (dot (app Defs.inl (var 0)) (sh 1)) G2) (cons (hyp_tm A) G1)) (Defs.dof M (subst (under (length G2) (dot (app Defs.inl (var 0)) (sh 1))) C)) 
    -> tr (List.app (substctx (dot (app Defs.inr (var 0)) (sh 1)) G2) (cons (hyp_tm B) G1)) (Defs.dof N (subst (under (length G2) (dot (app Defs.inr (var 0)) (sh 1))) C))
    -> tr 
         (List.app G2 (cons (hyp_tm (app (app Defs.sum A) B)) G1)) 
         (Defs.dof
            (app
               (app 
                  (app
                     Defs.sumcase 
                     (var (length G2)))
                  (lam (subst (dots 1 (length G2) (dot (var 0) (sh (S (S (length G2)))))) M)))
               (lam (subst (dots 1 (length G2) (dot (var 0) (sh (S (S (length G2)))))) N)))
            C).
Proof.
prepare.
intros G1 G2 a b c m n Hl Hr.
set (i := length G2).
assert (forall m,
          @equiv obj
            (app (lam (subst (dots 1 i (dot (var 0) (sh (S (S i))))) m)) (ppi2 (var i)))
            (subst (under i (dot (ppi2 (var 0)) sh1)) m)) as Hequiv.
  {
  clear_all.
  intro m.
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app2.
    }
  replace (ppi2 (var i)) with (@subst obj (sh i) (ppi2 (var 0))).
  2:{
    simpsub.
    rewrite -> Nat.add_0_r.
    auto.
    }
  replace (sh (S (S i))) with (@sh obj (S (1 + i))) by auto.
  rewrite -> subst1_dots_under.
  apply star_refl.
  }
rewrite -> !Hequiv; clear Hequiv.
replace (bite (ppi1 (var i))
           (subst (under i (dot (ppi2 (var 0)) sh1)) m)
           (subst (under i (dot (ppi2 (var 0)) sh1)) n))
   with (subst 
           (under i (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) sh1)))
           (bite (var (S i))
              (subst (under i (dot (var 0) (sh 2))) m)
              (subst (under i (dot (var 0) (sh 2))) n))).
2:{
  simpsub.
  rewrite -> !project_under_geq; [| omega].
  replace (S i - i) with 1 by omega.
  simpsub.
  rewrite -> Nat.add_0_r.
  rewrite <- compose_under.
  simpsub.
  reflexivity.
  }
apply tr_sigma_eta_hyp.
replace (substctx (dot (ppair (var 1) (var 0)) (sh 2)) G2 ++ hyp_tm (bite (var 0) (subst sh1 a) (subst sh1 b)) :: hyp_tm booltp :: G1)
   with ((substctx (dot (ppair (var 1) (var 0)) (sh 2)) G2 ++ hyp_tm (bite (var 0) (subst sh1 a) (subst sh1 b)) :: nil) ++ hyp_tm booltp :: G1).
2:{
  rewrite <- app_assoc.
  rewrite <- app_comm_cons.
  cbn.
  reflexivity.
  }
set (j := length (substctx (dot (ppair (var 1) (var 0)) (sh 2)) G2 ++ [hyp_tm (bite (var 0) (subst sh1 a) (subst sh1 b))])).
replace (under i (dot (var 0) (sh 2))) with (@under obj (S i) sh1).
2:{
  replace (S i) with (i + 1) by omega.
  rewrite <- under_sum.
  auto.
  }
replace (S i) with j.
2:{
  subst i j.
  rewrite -> app_length.
  rewrite -> length_substctx.
  cbn.
  omega.
  }
apply tr_booltp_eta_hyp.
  {
  rewrite -> app_length.
  rewrite -> length_substctx.
  cbn [length].
  replace (length G2 + 1) with (S (length G2)) by omega.
  rewrite -> substctx_app.
  cbn [length].
  simpsub.
  rewrite <- app_assoc.
  rewrite <- app_comm_cons.
  cbn [List.app].
  assert (equiv (bite btrue a b) a) as Hequiv.
    {
    apply steps_equiv.
    apply star_one.
    apply step_bite2.
    }
  rewrite -> Hequiv.
  force_exact Hl.
  f_equal.
  f_equal.
  rewrite <- under_succ.
  replace (S (length G2)) with (length G2 + 1) by omega.
  rewrite <- under_sum.
  rewrite <- compose_under.
  simpsub.
  reflexivity.
  }

  {
  rewrite -> app_length.
  rewrite -> length_substctx.
  cbn [length].
  replace (length G2 + 1) with (S (length G2)) by omega.
  rewrite -> substctx_app.
  cbn [length].
  simpsub.
  rewrite <- app_assoc.
  rewrite <- app_comm_cons.
  cbn [List.app].
  assert (equiv (bite bfalse a b) b) as Hequiv.
    {
    apply steps_equiv.
    apply star_one.
    apply step_bite3.
    }
  rewrite -> Hequiv.
  force_exact Hr.
  f_equal.
  f_equal.
  rewrite <- under_succ.
  replace (S (length G2)) with (length G2 + 1) by omega.
  rewrite <- under_sum.
  rewrite <- compose_under.
  simpsub.
  reflexivity.
  }
Qed.

