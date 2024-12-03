
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

Require Import ValidationAcc.
Require Import ValidationUtil.
Require Import ValidationAll.
Require Import ValidationCompat.
Require Import ValidationEqtp.
Require Import ValidationEqual.
Require Import ValidationExist.
Require Import ValidationSigma.
Require Import ValidationFuture.
Require Import ValidationGuard.
Require Import ValidationIstp.
Require Import ValidationRec.
Require Import ValidationLevel.
Require Import ValidationMisc.
Require Import ValidationMu.
Require Import ValidationNat.
Require Import ValidationOf.
Require Import ValidationPartial.
Require Import ValidationPi.
Require Import ValidationQuotient.
Require Import ValidationSet.
Require Import ValidationSequal.
Require Import ValidationSimple.
Require Import ValidationSquash.
Require Import ValidationSubtype.
Require Import ValidationSum.
Require Import ValidationUniv.


(* All the rules generated by the rule generator are correct. *)

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
exact forallExt'_valid.
exact forallOfExt_valid.
exact forallFormInv1_valid.
exact forallFormInv2_valid.
exact arrowForm_valid.
exact arrowEq_valid.
exact arrowFormUniv_valid.
exact arrowEqUniv_valid.
exact arrowForallEq_valid.
exact arrowForallEqUniv_valid.
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
exact arrowExt'_valid.
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
exact tarrowForallEq_valid.
exact tarrowForallEqUniv_valid.
exact tarrowIntroOf_valid.
exact tarrowIntroEq_valid.
exact tarrowIntro_valid.
exact tarrowElimOf_valid.
exact tarrowElimEq_valid.
exact tarrowElim_valid.
exact tarrowEta_valid.
exact tarrowExt_valid.
exact tarrowOfExt_valid.
exact karrowKind_valid.
exact karrowKindEq_valid.
exact karrowForm_valid.
exact karrowEq_valid.
exact karrowFormUniv_valid.
exact karrowEqUniv_valid.
exact karrowArrowEq_valid.
exact karrowArrowEqUniv_valid.
exact karrowForallEq_valid.
exact karrowForallEqUniv_valid.
exact karrowIntroOf_valid.
exact karrowIntroEq_valid.
exact karrowIntro_valid.
exact karrowElimOf_valid.
exact karrowElimEq_valid.
exact karrowElim_valid.
exact karrowEta_valid.
exact karrowExt_valid.
exact karrowOfExt_valid.
exact intersectForm_valid.
exact intersectEq_valid.
exact intersectFormUniv_valid.
exact intersectEqUniv_valid.
exact intersectSub_valid.
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
exact guardSub_valid.
exact guardSubIntro_valid.
exact coguardForm_valid.
exact coguardEq_valid.
exact coguardFormUniv_valid.
exact coguardEqUniv_valid.
exact coguardIntroEq_valid.
exact coguardIntroOf_valid.
exact coguardIntroOfSquash_valid.
exact coguardIntro_valid.
exact coguardElim1_valid.
exact coguardElim2Eq_valid.
exact coguardElim2Of_valid.
exact coguardElim2_valid.
exact coguardLeft_valid.
exact coguardSatEq_valid.
exact coguardSub_valid.
exact coguardSubElim_valid.
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
exact existsElim1_valid.
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
exact dprodForm_valid.
exact dprodEq_valid.
exact dprodFormUniv_valid.
exact dprodEqUniv_valid.
exact dprodExistsEq_valid.
exact dprodExistsEqUniv_valid.
exact prodDprodEq_valid.
exact prodDprodEqUniv_valid.
exact dprodSub_valid.
exact dprodExistsSub_valid.
exact existsDprodSub_valid.
exact dprodProdSub_valid.
exact prodDprodSub_valid.
exact dprodIntroOf_valid.
exact dprodIntroEq_valid.
exact dprodIntro_valid.
exact dprodElim1Of_valid.
exact dprodElim1Eq_valid.
exact dprodElim1_valid.
exact dprodElim2Of_valid.
exact dprodElim2Eq_valid.
exact dprodElim2_valid.
exact dprodEta_valid.
exact dprodExt_valid.
exact dprodLeft_valid.
exact dprodFormInv1_valid.
exact dprodFormInv2_valid.
exact unionForm_valid.
exact unionEq_valid.
exact unionFormUniv_valid.
exact unionEqUniv_valid.
exact unionSub_valid.
exact unionIntroOf_valid.
exact unionIntroEq_valid.
exact unionIntro_valid.
exact unionElimOf_valid.
exact unionElimEq_valid.
exact unionElim_valid.
exact unionElimOfDep_valid.
exact unionElimEqDep_valid.
exact unionElimDep_valid.
exact unionElimIstype_valid.
exact unionElimEqtype_valid.
exact sumForm_valid.
exact sumEq_valid.
exact sumFormUniv_valid.
exact sumEqUniv_valid.
exact sumSub_valid.
exact sumIntro1Of_valid.
exact sumIntro1Eq_valid.
exact sumIntro1_valid.
exact sumIntro2Of_valid.
exact sumIntro2Eq_valid.
exact sumIntro2_valid.
exact sumElimOf_valid.
exact sumElimOfNondep_valid.
exact sumElimEq_valid.
exact sumElim_valid.
exact sumElimNondep_valid.
exact sumElimIstype_valid.
exact sumElimEqtype_valid.
exact sumContradiction_valid.
exact sumInjection1_valid.
exact sumInjection2_valid.
exact sum_caseType_valid.
exact sumFormInv1_valid.
exact sumFormInv2_valid.
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
exact futureElim_valid.
exact futureElimIstype_valid.
exact futureElimIstypeLetnext_valid.
exact futureElimEqtype_valid.
exact futureEta_valid.
exact futureExt_valid.
exact futureLeft_valid.
exact futureInjection_valid.
exact recKind_valid.
exact recKindEq_valid.
exact recForm_valid.
exact recEq_valid.
exact recFormUniv_valid.
exact recEqUniv_valid.
exact recUnroll_valid.
exact recUnrollUniv_valid.
exact recBisimilar_valid.
exact muForm_valid.
exact muEq_valid.
exact muFormUniv_valid.
exact muEqUniv_valid.
exact muUnroll_valid.
exact muUnrollUniv_valid.
exact muInd_valid.
exact muIndUniv_valid.
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
exact boolElimOfNondep_valid.
exact boolElimEq_valid.
exact boolElim_valid.
exact boolElimIstype_valid.
exact boolElimEqtype_valid.
exact boolLeft_valid.
exact boolContradiction_valid.
exact iteType_valid.
exact natForm_valid.
exact natEq_valid.
exact natFormUniv_valid.
exact natEqUniv_valid.
exact natElimEq_valid.
exact natElimEqtype_valid.
exact natUnroll_valid.
exact natContradiction_valid.
exact natInjection_valid.
exact zeroType_valid.
exact succType_valid.
exact univKind_valid.
exact univKindEq_valid.
exact univForm_valid.
exact univEq_valid.
exact univFormUniv_valid.
exact univFormUnivSucc_valid.
exact univEqUniv_valid.
exact univCumulativeOf_valid.
exact univCumulativeEq_valid.
exact univCumulativeSuccOf_valid.
exact univSub_valid.
exact univForgetOf_valid.
exact univForgetEq_valid.
exact univIntroEqtype_valid.
exact univFormInv_valid.
exact kindForm_valid.
exact kindEq_valid.
exact kindFormUniv_valid.
exact kindEqUniv_valid.
exact kindForgetOf_valid.
exact kindForgetEq_valid.
exact kindUnivSub_valid.
exact levelForm_valid.
exact levelEq_valid.
exact levelFormUniv_valid.
exact levelEqUniv_valid.
exact lleqForm_valid.
exact lleqEq_valid.
exact lleqFormUniv_valid.
exact lleqEqUniv_valid.
exact lzeroLevel_valid.
exact lsuccLevel_valid.
exact lsuccEq_valid.
exact lmaxLevel_valid.
exact lmaxEq_valid.
exact lleqRefl_valid.
exact lleqTrans_valid.
exact lleqZero_valid.
exact lleqSucc_valid.
exact lleqIncrease_valid.
exact lleqMaxL_valid.
exact lleqMaxR1_valid.
exact lleqMaxR2_valid.
exact lleqResp_valid.
exact lsuccMaxDistTrans_valid.
exact lzeroType_valid.
exact lsuccType_valid.
exact lmaxType_valid.
exact eqForm_valid.
exact eqEq_valid.
exact eqFormUniv_valid.
exact eqEqUniv_valid.
exact eqIntro_valid.
exact eqElim_valid.
exact eqTrivialize_valid.
exact eqExt_valid.
exact eqLeft_valid.
exact eqRefl_valid.
exact eqSymm_valid.
exact eqTrans_valid.
exact eqFormInv1_valid.
exact eqFormInv2_valid.
exact eqFormInv3_valid.
exact ofForm_valid.
exact ofEq_valid.
exact ofFormUniv_valid.
exact ofEqUniv_valid.
exact ofIntro_valid.
exact ofElim_valid.
exact ofTrivialize_valid.
exact ofExt_valid.
exact ofLeft_valid.
exact ofEquand1_valid.
exact ofEquand2_valid.
exact eqtpForm_valid.
exact eqtpEq_valid.
exact eqtpFormUniv_valid.
exact eqtpEqUniv_valid.
exact eqtpIntro_valid.
exact eqtpElim_valid.
exact eqtpExt_valid.
exact eqtpLeft_valid.
exact eqtpFunct_valid.
exact eqtpFunctType_valid.
exact equivalenceOf_valid.
exact equivalenceEq_valid.
exact equivalence_valid.
exact equivalenceLeft_valid.
exact equivalenceLeftAlt_valid.
exact eqtpRefl_valid.
exact eqtpSymm_valid.
exact eqtpTrans_valid.
exact istpForm_valid.
exact istpEq_valid.
exact istpFormUniv_valid.
exact istpEqUniv_valid.
exact istpIntro_valid.
exact istpElim_valid.
exact istpExt_valid.
exact istpLeft_valid.
exact inhabitedForm_valid.
exact subtypeForm_valid.
exact subtypeEq_valid.
exact subtypeFormUniv_valid.
exact subtypeEqUniv_valid.
exact subtypeIntro_valid.
exact subtypeElim_valid.
exact subtypeExt_valid.
exact subtypeLeft_valid.
exact subtypeEstablish_valid.
exact subsumptionOf_valid.
exact subsumptionEq_valid.
exact subsumption_valid.
exact subsumptionAlt_valid.
exact subsumptionLeft_valid.
exact subsumptionLeftAlt_valid.
exact subsumptionLast_valid.
exact tighten_valid.
exact subtypeRefl_valid.
exact subtypeReflEqtype_valid.
exact subtypeTrans_valid.
exact subtypeIstp1_valid.
exact subtypeIstp2_valid.
exact eeqtpForm_valid.
exact eeqtpEq_valid.
exact eeqtpFormUniv_valid.
exact eeqtpEqUniv_valid.
exact setForm_valid.
exact setEq_valid.
exact setFormUniv_valid.
exact setEqUniv_valid.
exact setWeakenOf_valid.
exact setWeakenEq_valid.
exact setWeaken_valid.
exact setIntroOf_valid.
exact setIntroEq_valid.
exact setIntro_valid.
exact setIntroOfSquash_valid.
exact squashIntroOfSquash_valid.
exact setElim_valid.
exact setLeft_valid.
exact setSquash_valid.
exact setFormInv_valid.
exact setSubElim_valid.
exact isetForm_valid.
exact isetEq_valid.
exact isetFormUniv_valid.
exact isetEqUniv_valid.
exact isetWeakenOf_valid.
exact isetWeakenEq_valid.
exact isetWeaken_valid.
exact isetIntroOf_valid.
exact isetIntroEq_valid.
exact isetIntro_valid.
exact isetIntroOfSquash_valid.
exact isetElim_valid.
exact isetLeft_valid.
exact isetFormInv1_valid.
exact isetFormInv2_valid.
exact isetSubElim_valid.
exact squashForm_valid.
exact squashEq_valid.
exact squashFormUniv_valid.
exact squashEqUniv_valid.
exact squashIntroOf_valid.
exact squashIntro_valid.
exact squashElim_valid.
exact squashExt_valid.
exact squashLeft_valid.
exact squashSub_valid.
exact isquashForm_valid.
exact isquashEq_valid.
exact isquashFormUniv_valid.
exact isquashEqUniv_valid.
exact isquashIntroOf_valid.
exact isquashIntro_valid.
exact isquashIntroOfIsquash_valid.
exact isquashElim_valid.
exact isquashExt_valid.
exact isquashLeft_valid.
exact isquashSub_valid.
exact isquashFormInv_valid.
exact quotientForm_valid.
exact quotientEq_valid.
exact quotientFormUniv_valid.
exact quotientEqUniv_valid.
exact quotientIntroOf_valid.
exact quotientIntroEq_valid.
exact quotientElimOf_valid.
exact quotientElimEq_valid.
exact quotientElimIstype_valid.
exact quotientElimEqtype_valid.
exact quotientDescent_valid.
exact quotientLeft_valid.
exact quotientLeftRefl_valid.
exact quotientLeftIstype_valid.
exact quotientLeftEqtype_valid.
exact quotientLeftOf_valid.
exact quotientLeftEq_valid.
exact quotientLeftOfDep_valid.
exact quotientLeftEqDep_valid.
exact quotientFormInv_valid.
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
exact foralltpForm_valid.
exact foralltpEq_valid.
exact foralltpIntroOf_valid.
exact foralltpIntroEq_valid.
exact foralltpIntro_valid.
exact foralltpElimOf_valid.
exact foralltpElimEq_valid.
exact foralltpElim_valid.
exact iexistsForm_valid.
exact iexistsEq_valid.
exact iexistsFormUniv_valid.
exact iexistsEqUniv_valid.
exact iexistsIntroOf_valid.
exact iexistsIntroEq_valid.
exact iexistsIntro_valid.
exact iexistsElimOf_valid.
exact iexistsElimEq_valid.
exact iexistsElim_valid.
exact iexistsElimOfDep_valid.
exact iexistsElimEqDep_valid.
exact iexistsElimDep_valid.
exact iexistsElimIstype_valid.
exact iexistsElimEqtype_valid.
exact substitution_valid.
exact substitutionSimple_valid.
exact generalize_valid.
exact assert_valid.
exact assert'_valid.
exact inhabitant_valid.
exact letForm_valid.
exact lethForm_valid.
exact leteForm_valid.
exact accInd_valid.
exact sequalForm_valid.
exact sequalIntroOf_valid.
exact sequalIntro_valid.
exact sequalTrivialize_valid.
exact sequalExt_valid.
exact sequalLeft_valid.
exact sequalEq_valid.
exact sequalEqtp_valid.
exact sequivalence_valid.
exact sequivalenceLeft_valid.
exact substitutionSyntactic_valid.
exact sequalSymm_valid.
exact sequalTrans_valid.
exact sequalCompat_valid.
exact forallEtaSequal_valid.
exact arrowEtaSequal_valid.
exact existsEtaSequal_valid.
exact prodEtaSequal_valid.
exact futureEtaSequal_valid.
exact partialForm_valid.
exact partialEq_valid.
exact partialFormUniv_valid.
exact partialEqUniv_valid.
exact partialSub_valid.
exact partialStrict_valid.
exact partialStrictConverse_valid.
exact partialIdem_valid.
exact haltsForm_valid.
exact haltsEq_valid.
exact haltsFormUniv_valid.
exact haltsEqUniv_valid.
exact partialIntroBottomOf_valid.
exact bottomDiverges_valid.
exact partialExt_valid.
exact partialElimEq_valid.
exact partialElimOf_valid.
exact haltsTrivialize_valid.
exact haltsExt_valid.
exact haltsLeft_valid.
exact fixpointInductionEq_valid.
exact fixpointInductionOf_valid.
exact partialFormInv_valid.
exact seqBind_valid.
exact activeApp_valid.
exact activeAppSeq_valid.
exact appHaltsInv_valid.
exact activePi1_valid.
exact activePi1Seq_valid.
exact pi1HaltsInv_valid.
exact activePi2_valid.
exact activePi2Seq_valid.
exact pi2HaltsInv_valid.
exact prevHaltsInv_valid.
exact activeCase_valid.
exact activeCaseSeq_valid.
exact caseHaltsInv_valid.
exact seqHaltsSequal_valid.
exact seqHaltsInv_valid.
exact sequalUnderSeq_valid.
exact totalStrict_valid.
exact voidTotal'_valid.
exact voidStrict_valid.
exact unitTotal_valid.
exact unitTotal'_valid.
exact unitStrict_valid.
exact boolTotal_valid.
exact boolTotal'_valid.
exact boolStrict_valid.
exact forallTotal_valid.
exact forallTotal'_valid.
exact forallStrict_valid.
exact arrowTotal_valid.
exact arrowTotal'_valid.
exact arrowStrict_valid.
exact intersectStrict_valid.
exact existsTotal_valid.
exact existsTotal'_valid.
exact existsStrict_valid.
exact prodTotal_valid.
exact prodTotal'_valid.
exact prodStrict_valid.
exact dprodTotal_valid.
exact dprodTotal'_valid.
exact dprodStrict_valid.
exact sumTotal_valid.
exact sumTotal'_valid.
exact sumStrict_valid.
exact futureTotal_valid.
exact futureTotal'_valid.
exact futureStrict_valid.
exact setTotal'_valid.
exact setStrict_valid.
exact isetTotal'_valid.
exact isetStrict_valid.
exact quotientTotal'_valid.
exact natTotal_valid.
exact natTotal'_valid.
exact natStrict_valid.
exact typeHalts_valid.
exact univTotal'_valid.
exact univStrict_valid.
exact reduceSeqTotal_valid.
exact haltsTotal_valid.
exact uptypeForm_valid.
exact uptypeEq_valid.
exact uptypeFormUniv_valid.
exact uptypeEqUniv_valid.
exact uptypeTrivialize_valid.
exact uptypeExt_valid.
exact uptypeLeft_valid.
exact uptypeEeqtp_valid.
exact uptypeUnitary_valid.
exact voidUptype_valid.
exact unitUptype_valid.
exact boolUptype_valid.
exact forallUptype_valid.
exact arrowUptype_valid.
exact intersectUptype_valid.
exact existsUptype_valid.
exact prodUptype_valid.
exact dprodUptype_valid.
exact sumUptype_valid.
exact futureUptype_valid.
exact eqUptype_valid.
exact ofUptype_valid.
exact eqtpUptype_valid.
exact istpUptype_valid.
exact subtypeUptype_valid.
exact setUptype_valid.
exact isetUptype_valid.
exact muUptype_valid.
exact muUptypeUniv_valid.
exact recUptype_valid.
exact recUptypeUniv_valid.
exact natUptype_valid.
exact uptypeFormInv_valid.
exact admissForm_valid.
exact admissEq_valid.
exact admissFormUniv_valid.
exact admissEqUniv_valid.
exact admissTrivialize_valid.
exact admissExt_valid.
exact admissLeft_valid.
exact admissEeqtp_valid.
exact uptypeAdmiss_valid.
exact partialAdmiss_valid.
exact voidAdmiss_valid.
exact unitAdmiss_valid.
exact boolAdmiss_valid.
exact forallAdmiss_valid.
exact arrowAdmiss_valid.
exact intersectAdmiss_valid.
exact existsAdmissUptype_valid.
exact prodAdmiss_valid.
exact dprodAdmissUptype_valid.
exact sumAdmiss_valid.
exact futureAdmiss_valid.
exact eqAdmiss_valid.
exact ofAdmiss_valid.
exact eqtpAdmiss_valid.
exact istpAdmiss_valid.
exact subtypeAdmiss_valid.
exact recAdmiss_valid.
exact recAdmissUniv_valid.
exact natAdmiss_valid.
exact admissFormInv_valid.
exact partialType_valid.
exact haltsType_valid.
exact admissType_valid.
exact uptypeType_valid.
exact seqType_valid.
exact eeqtpRefl_valid.
exact eeqtpSymm_valid.
exact eeqtpTrans_valid.
exact weakenEqtpEeqtp_valid.
exact weakenSubtypeArrow_valid.
exact weakenEeqtpIff_valid.
exact compatGuardEqtp1_valid.
exact compatSetEqtp0_valid.
exact forallEeq_valid.
exact existsEeq_valid.
exact arrowEeq_valid.
exact prodEeq_valid.
exact dprodEeq_valid.
exact sumEeq_valid.
exact futureEeq_valid.
exact intersectEeq_valid.
exact unionEeq_valid.
exact compatGuardEeq1_valid.
exact compatSetEeq0_valid.
exact compatIsetEeq0_valid.
exact compatIsetIff1_valid.
exact compatForallSubtype0_valid.
exact compatForallSubtype1_valid.
exact compatExistsSubtype0_valid.
exact compatExistsSubtype1_valid.
exact compatIntersectSubtype0_valid.
exact compatIntersectSubtype1_valid.
exact compatUnionSubtype0_valid.
exact compatUnionSubtype1_valid.
exact compatGuardArrow0_valid.
exact compatGuardSubtype1_valid.
exact compatSetSubtype0_valid.
exact compatSetArrow1_valid.
exact compatIsetSubtype0_valid.
exact compatIsetArrow1_valid.
exact compatForallIff1_valid.
exact compatExistsIff1_valid.
exact compatArrowIff0_valid.
exact compatArrowIff1_valid.
exact compatProdIff0_valid.
exact compatProdIff1_valid.
exact compatDprodIff0_valid.
exact compatDprodIff1_valid.
exact compatSumIff0_valid.
exact compatSumIff1_valid.
exact compatFutureIff_valid.
exact compatForallArrow1_valid.
exact compatExistsArrow1_valid.
exact compatArrowArrow0_valid.
exact compatArrowArrow1_valid.
exact compatProdArrow0_valid.
exact compatProdArrow1_valid.
exact compatDprodArrow0_valid.
exact compatDprodArrow1_valid.
exact compatSumArrow0_valid.
exact compatSumArrow1_valid.
exact compatFutureArrow_valid.
exact compatForallEntails1_valid.
exact compatArrowEntails1_valid.
exact compatProdEntails0_valid.
exact compatProdEntails1_valid.
exact compatDprodEntails0_valid.
exact compatDprodEntails1_valid.
Qed.
  


(* Hardcoded rules *)

Lemma hypothesis_valid :
  forall G1 A G2,
    tr 
      (G2 ++ hyp_tm A :: G1)
      (Defs.dof (var (length G2)) (subst (sh (S (length G2))) A)).
Proof.
prepare.
intros G1 a G2.
apply tr_hyp_tm.
replace (length G2) with (0 + length G2) by auto.
apply index_app_right.
apply index_0.
Qed.


Lemma hypothesisOf_valid :
  forall G1 A G2,
    tr 
      (G2 ++ hyp_tm A :: G1)
      (Defs.dof Defs.triv (app (app Defs.of (subst (sh (S (length G2))) A)) (var (length G2)))).
Proof.
prepare.
intros G1 a G2.
apply tr_hyp_tm.
replace (length G2) with (0 + length G2) by auto.
apply index_app_right.
apply index_0.
Qed.


Lemma hypothesisEq_valid :
  forall G1 A G2,
    tr 
      (G2 ++ hyp_tm A :: G1)
      (Defs.dof Defs.triv (app (app (app Defs.eq (subst (sh (S (length G2))) A)) (var (length G2))) (var (length G2)))).
Proof.
prepare.
intros G1 a G2.
apply tr_hyp_tm.
replace (length G2) with (0 + length G2) by auto.
apply index_app_right.
apply index_0.
Qed.


Lemma hypothesisOfTp_valid :
  forall G1 G2,
    tr
      (G2 ++ hyp_tp :: G1)
      (Defs.dof Defs.triv (app Defs.istp (var (length G2)))).
Proof.
prepare.
intros G1 G2.
apply tr_hyp_tp.
replace (length G2) with (0 + length G2) by auto.
apply index_app_right.
apply index_0.
Qed.


Lemma hypothesisEqTp_valid :
  forall G1 G2,
    tr
      (G2 ++ hyp_tp :: G1)
      (Defs.dof Defs.triv (app (app Defs.eqtp (var (length G2))) (var (length G2)))).
Proof.
prepare.
intros G1 G2.
apply tr_hyp_tp.
replace (length G2) with (0 + length G2) by auto.
apply index_app_right.
apply index_0.
Qed.


Lemma weaken_valid :
  forall G1 G2 G3 A M,
    tr (G3 ++ G1) (Defs.dof M A)
    -> tr 
         (substctx (sh (length G2)) G3 ++ G2 ++ G1)
         (Defs.dof 
            (subst (under (length G3) (sh (length G2))) M)
            (subst (under (length G3) (sh (length G2))) A)).
Proof.
prepare.
intros G1 G2 G3 a m H.
apply weakening.
  {
  simpsub.
  rewrite <- compose_assoc.
  rewrite -> compose_sh_unlift.
  simpsub.
  auto.
  }

  {
  rewrite -> length_substctx.
  simpsub.
  rewrite <- !compose_under.
  rewrite <- !compose_assoc.
  rewrite -> compose_sh_unlift.
  simpsub.
  auto.
  }

  {
  rewrite -> length_substctx.
  simpsub.
  rewrite <- !compose_under.
  rewrite -> compose_sh_unlift.
  simpsub.
  auto.
  }
Qed.


Lemma compose_dots_dots :
  forall obj (i j k l m n : nat) (s s' : @sub obj),
    i >= l
    -> i - l + j <= n
    -> compose (dots i j s) (dots k l (dots m n s'))
       = dots (i - l + m) j (compose s (dots k l (dots m n s'))).
Proof.
intros obj i j k l m n s s' Hlo Hhi.
revert i s Hlo Hhi.
induct j.

(* 0 *)
{
intros i s Hlo Hhi.
cbn.
auto.
}

(* S *)
{
intros j IH i s Hlo Hhi.
cbn.
rewrite -> IH; try omega.
f_equal.
simpsub.
f_equal.
rewrite -> project_dots_ge; try omega.
rewrite -> project_dots_lt; try omega.
f_equal.
omega.
}
Qed.


Lemma exchange_valid :
  forall G1 G2 G3 G4 A M,
    let l := length G4 in
    let m := length G3 in
    let n := length G2 in
    let s := dots m n (dots 0 m (sh (m+n)))
    in
      tr
        (G4 ++ substctx (sh m) G2 ++ G3 ++ G1)
        (Defs.dof M A)
      -> tr
           (substctx s G4 ++ substctx (sh n) G3 ++ G2 ++ G1)
           (Defs.dof
              (subst (under l s) M)
              (subst (under l s) A)).
Proof.
prepare.
intros G1 G2 G3 G4 a p H.
set (l := length G4).
set (m := length G3).
set (n := length G2).
apply exchange.
  {
  simpsub.
  fold n.
  rewrite <- compose_assoc.
  rewrite -> compose_sh_unlift.
  auto.
  }
rewrite -> !length_substctx.
simpsub.
fold l.
fold m.
fold n.
rewrite <- compose_under.
rewrite -> compose_dots_dots; try omega.
replace (m - m + 0) with 0 by omega.
rewrite -> compose_dots_le; try omega.
cbn [Nat.add].
rewrite -> compose_sh_dots_ge; try omega.
replace (m + n - m) with n by omega.
rewrite -> compose_sh_dots_ge; try omega.
replace (n - n) with 0 by omega.
simpsub.
cbn [Nat.add].
rewrite -> Nat.add_comm.
rewrite <- compose_sh_sh.
rewrite <- (compose_dots_sh _ 0 m (sh m) n).
rewrite <- under_dots.
rewrite -> under_sum.
so (eqsub_trans _#4 (eqsub_under _ (l + n) _ _ (eqsub_dots_id obj m)) (eqsub_under_id _ _)) as Heq.
rewrite -> Heq.
clear Heq.
so (eqsub_trans _#4 (eqsub_under _ n _ _ (eqsub_dots_id obj m)) (eqsub_under_id _ _)) as Heq.
rewrite -> (substctx_eqsub _#4 Heq).
clear Heq.
rewrite -> compose_sh_unlift.
simpsub.
auto.
Qed.


Hint Rewrite def_inl def_inr def_sum def_sum_case : prepare.


(* The sumLeft rule is hardcoded because it involves a pattern not used in any other
   rule.  (To wit: the extract interacts with the far end of the context.)  There seems
   to be no robustness advantage to extending the rule generator with functionality
   that will only be used once.
*)

Lemma sumLeft_valid :
  forall G1 G2 A B C M N, 
    tr 
      (substctx (dot (app Defs.inl (var 0)) (sh 1)) G2 ++ hyp_tm A :: G1)
      (Defs.dof M (subst (under (length G2) (dot (app Defs.inl (var 0)) (sh 1))) C)) 
    -> tr 
         (substctx (dot (app Defs.inr (var 0)) (sh 1)) G2 ++ hyp_tm B :: G1)
         (Defs.dof N (subst (under (length G2) (dot (app Defs.inr (var 0)) (sh 1))) C))
    -> tr 
         (G2 ++ hyp_tm (app (app Defs.sum A) B) :: G1)
         (Defs.dof
            (app
               (app 
                  (app
                     Defs.sum_case 
                     (var (length G2)))
                  (lam (subst (dots 1 (length G2) (dot (var 0) (sh (S (S (length G2)))))) M)))
               (lam (subst (dots 1 (length G2) (dot (var 0) (sh (S (S (length G2)))))) N)))
            C).
Proof.
prepare.
intros G1 G2 a b c m n Hl Hr.
unfold Defined.sumcase.
unfold Defined.sumleft in Hl.
unfold Defined.sumright in Hr.
set (i := length G2).
assert (forall m,
          @equiv obj
            (subst1 (ppi2 (var i)) (subst (dots 1 i (dot (var 0) (sh (S (S i))))) m))
            (subst (under i (dot (ppi2 (var 0)) sh1)) m)) as Hequiv.
  {
  clear_all.
  intro m.
  apply steps_equiv.
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


(* The insert rule is hardcoded because it involves a pattern used only in the structural
   rules: it operates on the context, but does not operate on anything *in* the context.
*)
Lemma insert_valid :
  forall G1 G2 c m,
    tr (substctx sh1 G2 ++ hyp_tm Defs.unit :: G1) (Defs.dof m (subst (under (length G2) sh1) c))
    -> tr (G2 ++ G1) (Defs.dof (subst (under (length G2) (dot triv id)) m) c).
Proof.
unfold Defs.unit.
unfold Defs.dof.
intros G1 G2 c m H0.
so (exchange_valid G1 G2 (hyp_tm unittp :: nil) nil _ _ H0) as H.
cbn [length] in H.
simpsubin H.
cbn [List.app] in H.
eassert _ as H'; [refine (tr_generalize _ _ triv _ _ H) |].
  {
  apply tr_unittp_intro.
  }
renameover H' into H.
unfold Defs.dof in H.
simpsubin H.
cbn [dots] in H.
cbn [Nat.add] in H.
rewrite -> subst1_dots in H.
simpsubin H.
replace (@dot obj triv (sh (length G2))) with (@Subst.compose obj (dot triv id) (sh (length G2))) in H.
2:{
  simpsub.
  reflexivity.
  }
rewrite <- under_dots in H.
rewrite <- compose_under in H.
simpsubin H.
exact H.
Qed.


(* The forallLeft rule is hardcoded because it involves a pattern not used in any other rule
   (except arrowLeft): the conclusion has a hypothesis.
*)
Lemma forallLeft_valid :
  forall G a b m c n ext,
    tr G (Defs.dof ext (app (app Defs.of a) m))
    -> tr (hyp_tm (subst1 m b) :: G) (Defs.dof n (subst sh1 c))
    -> tr (hyp_tm (app (app Defs.pi a) (lam b)) :: G) (Defs.dof (subst (dot (app (var 0) (subst sh1 m)) sh1) n) (subst sh1 c)).
Proof.
prepare.
intros G a b m c n ext Hm Hc.
cut (tr (hyp_tm (pi a b) :: G) (substj (dot (app (var 0) (subst sh1 m)) id) (deq (subst (dot (var 0) (sh 2)) n) (subst (dot (var 0) (sh 2)) n) (subst (sh 2) c)))).
  {
  intro H.
  simpsubin H.
  exact H.
  }
apply (tr_generalize _ (subst (dot (subst sh1 m) sh1) b)).
  {
  eapply tr_pi_elim'.
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    eapply (weakening _ [_] nil).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    exact Hm.
    }

    {
    simpsub.
    reflexivity.
    }
  }
apply (weakening _ [_] [_]).
  {
  cbn [length unlift].
  simpsub.
  reflexivity.
  }

  {
  cbn [length unlift].
  simpsub.
  cbn [Nat.add].
  reflexivity.
  }
cbn [length unlift].
simpsub.
cbn [List.app].
rewrite -> subst_var0_sh1.
exact Hc.
Qed.


(* The arrowLeft rule is hardcoded because it involves a pattern not used in any other rule
   (except forallLeft): the conclusion has a hypothesis.
*)
Lemma arrowLeft_valid :
  forall G a b m c n,
    tr G (Defs.dof m a)
    -> tr (hyp_tm b :: G) (Defs.dof n (subst sh1 c))
    -> tr (hyp_tm (app (app Defs.arrow a) b) :: G) (Defs.dof (subst (dot (app (var 0) (subst sh1 m)) sh1) n) (subst sh1 c)).
Proof.
unfold Defs.dof.
intros G a b m c n Hm Hc.
rewrite -> def_arrow.
cut (tr (hyp_tm (pi a (subst sh1 b)) :: G) (substj (dot (app (var 0) (subst sh1 m)) id) (deq (subst (dot (var 0) (sh 2)) n) (subst (dot (var 0) (sh 2)) n) (subst (sh 2) c)))).
  {
  intro H.
  simpsubin H.
  exact H.
  }
apply (tr_generalize _ (subst sh1 b)).
  {
  eapply tr_pi_elim'.
    {
    eapply hypothesis; eauto using index_0.
    simpsub.
    reflexivity.
    }

    {
    eapply (weakening _ [_] nil).
      {
      simpsub.
      reflexivity.
      }

      {
      cbn [length unlift].
      simpsub.
      reflexivity.
      }
    cbn [length unlift].
    simpsub.
    cbn [List.app].
    exact Hm.
    }

    {
    simpsub.
    reflexivity.
    }
  }
apply (weakening _ [_] [_]).
  {
  cbn [length unlift].
  simpsub.
  reflexivity.
  }

  {
  cbn [length unlift].
  simpsub.
  cbn [Nat.add].
  reflexivity.
  }
cbn [length unlift].
simpsub.
cbn [List.app].
rewrite -> subst_var0_sh1.
exact Hc.
Qed.


(* The haltsValue rule is hardcoded because the rule generator does
   not know about values.  There seems to be no robustness advantage
   to extending the rule generator with functionality that will only
   be used once.

   The rule as hardcoded relies on the correctness of the valuability
   implementation to accept only when M is equivalent to some value.
*)
Lemma haltsValue_valid :
  forall G M N,
    equiv M N
    -> value N
    -> tr G (Defs.dof triv (app Defs.halts M)).
Proof.
intros G m n Hequiv Hvalue.
unfold Defs.dof.
rewrite -> def_halts.
rewrite -> Hequiv.
apply tr_halts_value; auto.
Qed.



(* The remaining rules without validations above are:

   1. the reduction rules

      The reduction rules follow immediately from tr_compute and
      tr_compute_hyp.

   2. sequivalencePath and sequivalenceLeftPath

      These rules follow from tr_sequal_compat and the proofs of sequivalence and sequivalenceLeft.

   3. checkPositive and checkNegative

      The correctness of checkPositive and checkNegative follow
      immediately from tr_positive_algorithm, and
      tr_negative_algorithm, assuming the checker is implemented
      correctly with respect to the formal algorithm.

   4. the rules pertaining to let hypotheses

      The let-hypothesis rules pertain to a definition mechanism in
      the proof assistant that does not exist in the type theory.  But
      the rules are simple and it is easy to see they are correct.

   5. the rules pertaining to native data types (integers and symbols)

      The native data type rules cannot be proven correct because the
      native data types do not exist in the type theory.  These rules
      fall into several categories:

      (a) the formation of the type (b) the membership of literals in
      the type (c) the flatness of the type (d) in the case of
      integers, an isomorphism

      The correctness of each of these rules is apparent by
      inspection.

      A flat type is one in which the elements are precisely a set of
      values without any internal structure (in addition to
      expressions that are beta-equivalent to such a value).  There
      are several consequences of flatness:

      (i) totality (by sound_total_flat) (ii) strictness (follows from
      totality by tr_total_strict) (iii) upward closure (by
      sound_flat_upward) (iv) admissibility (follows from upward
      closure by tr_uptype_admiss) (v) equality implies syntactic
      equality (by sound_flat_sequal)

      For integers, several rules establish an isomorphism between
      native integers and defined integers (as quotiented pairs of
      natural numbers).  The correctness of the isomorphism code is
      apparent by inspection.
*)
