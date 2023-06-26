
Require Import Coq.Lists.List.
Import ListNotations.
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
Require Import Equivalence.
Require Import Dots.

Require Import ValidationUtil.


Lemma tr_sigma_sub :
  forall G a a' b b',
    tr G (dsubtype a a')
    -> tr (hyp_tm a :: G) (dsubtype b b')
    -> tr (hyp_tm a' :: G) (deqtype b' b')
    -> tr G (dsubtype (sigma a b) (sigma a' b')).
Proof.
intros G a a' b b' Ha Hb Hb'.
apply tr_subtype_intro.
  {
  apply tr_sigma_formation.
    {
    eapply tr_subtype_istype1; eauto.
    }

    {
    eapply tr_subtype_istype1; eauto.
    }
  }

  {
  apply tr_sigma_formation; auto.
  eapply tr_subtype_istype2; eauto.
  }
simpsub.
cbn [Nat.add].
eapply tr_sigma_ext.
  {
  apply (tr_subtype_elim _ (subst sh1 a)).
    {
    eapply (weakening _ [_] []).
      {
      cbn [unlift length].
      simpsub.
      auto.
      }

      {
      cbn [unlift length].
      simpsub.
      auto.
      }
    cbn [unlift length].
    simpsub.
    cbn [List.app].
    exact Ha.
    }
  eapply tr_sigma_elim1.
  eapply hypothesis; eauto using index_0.
  simpsub.
  cbn [Nat.add].
  eauto.
  }

  {
  simpsub.
  apply (tr_subtype_elim _ (subst (dot (ppi1 (var 0)) sh1) b)).
    {
    match goal with
    | |- tr _ ?X =>
       replace X with
       (substj (dot (ppi1 (var 0)) id)
          (deq triv triv (subtype
                            (subst (dot (var 0) (sh 2)) b)
                            (subst (dot (var 0) (sh 2)) b'))))
    end.
    2:{
      simpsub.
      auto.
      }
    apply (tr_generalize _ (subst sh1 a)).
      {
      eapply tr_sigma_elim1.
      eapply hypothesis; eauto using index_0.
      simpsub.
      eauto.
      }

      {
      eapply (weakening _ [_] [_]).
        {
        cbn [unlift length].
        simpsub.
        auto.
        }
    
        {
        cbn [unlift length].
        simpsub.
        auto.
        }
      cbn [unlift length].
      simpsub.
      cbn [List.app].
      rewrite -> !subst_var0_sh1.
      exact Hb.
      }
    }

    {
    eapply tr_sigma_elim2'.
      {
      eapply hypothesis; eauto using index_0.
      simpsub.
      cbn [Nat.add].
      eauto.
      }
    simpsub.
    auto.
    }
  }

  {
  eapply (weakening _ [_] [_]).
    {
    cbn [unlift length].
    simpsub.
    auto.
    }

    {
    cbn [unlift length].
    simpsub.
    auto.
    }
  cbn [unlift length].
  simpsub.
  cbn [List.app].
  rewrite -> subst_var0_sh1.
  exact Hb'.
  }

  {
  eapply hypothesis; eauto using index_0.
  simpsub.
  eauto.
  }

  {
  eapply hypothesis; eauto using index_0.
  simpsub.
  eauto.
  }
Qed.


Lemma tr_prod_sub :
  forall G a a' b b',
    tr G (dsubtype a a')
    -> tr G (dsubtype b b')
    -> tr G (dsubtype (prod a b) (prod a' b')).
Proof.
intros G a a' b b' Ha Hb.
unfold dsubtype.
apply (tr_eqtype_convert _ _ _ (subtype (sigma a (subst sh1 b)) (sigma a' (subst sh1 b')))).
  {
  apply tr_eqtype_symmetry.
  apply tr_subtype_formation.
    {
    apply tr_prod_sigma_equal; eauto using tr_subtype_istype1, tr_subtype_istype2.
    }

    {
    apply tr_prod_sigma_equal; eauto using tr_subtype_istype1, tr_subtype_istype2.
    }
  }
apply tr_sigma_sub; auto.
  {
  apply (weakening _ [_] []).
    {
    simpsub.
    auto.
    }

    {
    cbn [length Dots.unlift].
    simpsub.
    auto.
    }
  cbn [length Dots.unlift].
  simpsub.
  cbn [List.app].
  auto.
  }

  {
  apply (weakening _ [_] []).
    {
    simpsub.
    auto.
    }

    {
    cbn [length Dots.unlift].
    simpsub.
    auto.
    }
  cbn [length Dots.unlift].
  simpsub.
  cbn [List.app].
  eapply tr_subtype_istype2; eauto.
  }
Qed.


Lemma tr_prod_sigma_sub :
  forall G a a' b b',
    tr G (dsubtype a a')
    -> tr (hyp_tm a :: G) (dsubtype (subst sh1 b) b')
    -> tr G (deqtype b b)
    -> tr (hyp_tm a' :: G) (deqtype b' b')
    -> tr G (dsubtype (prod a b) (sigma a' b')).
Proof.
intros G a a' b b' Ha Hb Hbl Hbr.
unfold dsubtype.
apply (tr_eqtype_convert _ _ _ (subtype (sigma a (subst sh1 b)) (sigma a' b'))).
  {
  apply tr_eqtype_symmetry.
  apply tr_subtype_formation.
    {
    apply tr_prod_sigma_equal; eauto using tr_subtype_istype1, tr_subtype_istype2.
    }

    {
    apply tr_sigma_formation; eauto using tr_subtype_istype1, tr_subtype_istype2.
    }
  }
apply tr_sigma_sub; auto.
Qed.



Lemma tr_sigma_prod_sub :
  forall G a a' b b',
    tr G (dsubtype a a')
    -> tr (hyp_tm a :: G) (dsubtype b (subst sh1 b'))
    -> tr G (deqtype b' b')
    -> tr G (dsubtype (sigma a b) (prod a' b')).
Proof.
intros G a a' b b' Ha Hb Hbr.
unfold dsubtype.
apply (tr_eqtype_convert _ _ _ (subtype (sigma a b) (sigma a' (subst sh1 b')))).
  {
  apply tr_eqtype_symmetry.
  apply tr_subtype_formation.
    {
    apply tr_sigma_formation; eauto using tr_subtype_istype1, tr_subtype_istype2.
    }

    {
    apply tr_prod_sigma_equal; eauto using tr_subtype_istype1, tr_subtype_istype2.
    }
  }
apply tr_sigma_sub; auto.
apply (weakening _ [_] []).
  {
  simpsub.
  auto.
  }

  {
  cbn [length Dots.unlift].
  simpsub.
  auto.
  }
cbn [length Dots.unlift].
simpsub.
cbn [List.app].
auto.
Qed.



Hint Rewrite def_sigma def_prod : prepare.



Lemma existsForm_valid : existsForm_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b triv0 triv1 H1 H2.
  valid_rewrite.
  constructor; eauto using deqtype_intro.
Qed.

Lemma existsEq_valid : existsEq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a a' b b' triv0 triv1 H1 H2.
  valid_rewrite.
  constructor; eauto using deqtype_intro.
  Qed.

Lemma existsFormUniv_valid : existsFormUniv_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b i triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  apply tr_sigma_formation_univ; eauto using deq_intro.
  Qed.

Lemma existsEqUniv_valid : existsEqUniv_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a a' b b' i triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  apply tr_sigma_formation_univ; eauto using deq_intro.
Qed.


Lemma existsSub_valid : existsSub_obligation.
Proof.
prepare.
intros G a a' b b' ext2 ext1 ext0 H0 H1 H2.
apply tr_sigma_sub; auto.
Qed.


Lemma existsIntroOf_valid : existsIntroOf_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m n triv0 triv1 triv2 H0 H1 H2.
  valid_rewrite.
  constructor.
  apply tr_sigma_intro; try eauto using deq_intro; eauto using deqtype_intro.
  Qed.

Lemma existsIntroEq_valid : existsIntroEq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m m' n n' triv0 triv1 triv2 H0 H1 H2.
  valid_rewrite.
  constructor.
  apply tr_sigma_intro; try eauto using deq_intro; eauto using deqtype_intro.
  Qed.


Lemma existsIntro_valid : existsIntro_obligation.
Proof.
prepare.
intros G a b m ext1 ext0 n Hb Hm Hn.
apply tr_sigma_intro; auto.
Qed.


Lemma existsElim1Of_valid : existsElim1Of_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m triv0 H.
  valid_rewrite.
  constructor.
  eapply tr_sigma_elim1; eauto using deq_intro.
  Qed.

Lemma existsElim1Eq_valid : existsElim1Eq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m n triv0 H.
  valid_rewrite.
  constructor.
  eapply tr_sigma_elim1; eauto using deq_intro.
  Qed.


Lemma existsElim1_valid : existsElim1_obligation.
Proof.
prepare.
intros G a b m Hm.
eapply tr_sigma_elim1; eauto.
Qed.


Lemma existsElim2Of_valid : existsElim2Of_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m triv0 H.
  valid_rewrite.
  constructor.
  eapply tr_sigma_elim2; eauto using deq_intro.
  Qed.

Lemma existsElim2Eq_valid : existsElim2Eq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m n triv0 H.
  valid_rewrite.
  constructor.
  eapply tr_sigma_elim2; eauto using deq_intro.
  Qed.

Lemma existsEta_valid : existsEta_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m triv0 Hexists.
  valid_rewrite.
  constructor.
  apply tr_sigma_eta. eauto using deq_intro.
Qed.


Lemma existsExt_valid : existsExt_obligation.
Proof.
prepare.
intros G a b m n ext3 ext2 ext1 ext0 Hm Hn H1 H2.
eapply tr_sigma_ext; eauto.
eapply tr_sigma_formation_invert2; eauto.
eapply tr_inhabitation_formation; eauto.
Qed.


Lemma existsLeft_valid : existsLeft_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G1 G2 a b c m H.
  valid_rewrite.
  match goal with |- tr ?G ?J =>
                  assert (equivctx G
    (G2 ++
     hyp_tm (sigma a b) :: G1)
                         ) as Hctx end.

  { apply Forall2_app;
      [apply equivctx_refl | constructor; try apply equivctx_refl].
    apply equivh_refl. }
  apply tr_sigma_eta_hyp; auto.
  Qed.

Lemma existsFormInv1_valid : existsFormInv1_obligation.
Proof.
prepare.
intros G a b ext0 H.
eapply tr_sigma_formation_invert1; eauto.
Qed.


Lemma existsFormInv2_valid : existsFormInv2_obligation.
Proof.
prepare.
intros G a b m ext0 ext1 Hsig Hm.
simpsub.
cut (tr (hyp_tm a :: G) (deqtype b b)).
  {
  intro Hb.
  so (tr_generalize _#4 Hm Hb) as H.
  simpsubin H.
  exact H.
  }
eapply tr_sigma_formation_invert2; eauto.
Qed.


Lemma existsFormInv2Eq_valid : existsFormInv2Eq_obligation.
Proof.
prepare.
intros G a b m n ext1 ext0 Hsig Hm.
simpsub.
so (tr_sigma_formation_invert2 _#5 Hsig) as Hb.
unfold deqtype in Hb.
so (tr_generalize_eq_type _#7 Hm Hb) as Hbmn.
simpsubin Hbmn.
eapply tr_eqtype_formation_invert1; eauto.
Qed.


(*product helper lemmas *)
Lemma tr_prod_invert1 {G m m' a b} :
      tr G (deq m m' (prod a b) )
      -> tr G (deqtype a a).
  intros H.
  apply tr_prod_elim1 in H.
  eauto using tr_inhabitation_formation.
Qed.

Lemma tr_prod_invert2 {G m m' a b} :
      tr G (deq m m' (prod a b) )
      -> tr G (deqtype b b).
  intros H.
  apply tr_prod_elim2 in H.
  eauto using tr_inhabitation_formation.
Qed.

Lemma tr_prod_intro G A B M M' N N' :
    tr G (deq M M' A) -> tr G (deq N N' B) ->
    tr G (deq (ppair M N) (ppair M' N') (prod A B)).
  intros H0 H1.
  pose proof (tr_inhabitation_formation _#4 H0) as Ha.
  pose proof (tr_inhabitation_formation _#4 H1) as Hb.
  eapply tr_eqtype_convert.
  apply tr_eqtype_symmetry. apply tr_prod_sigma_equal; try assumption.
  eapply tr_sigma_intro; try assumption. simpsub. assumption.
  match goal with |- tr ?G' ?J => change J with (substj (under 0 sh1)
                                                    (deqtype B B));
                                  change G' with (nil ++ G') end.
  change nil with (@substctx Rules.obj sh1 nil).
  apply tr_weakening. assumption.
  Qed.

Lemma prodKind_valid : prodKind_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a i k l triv0 H0 H1.
  valid_rewrite. 
  constructor.
  apply tr_prod_kind_formation; eauto using deq_intro.
  Qed.

Lemma prodKindEq_valid : prodKindEq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G i k k' l l' triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  apply tr_prod_kind_formation; eauto using deq_intro; eauto using deq.
Qed.

Lemma prodForm_valid : prodForm_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor; eauto using deqtype_intro.
  Qed.

Lemma prodEq_valid : prodEq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a a' b b' triv0 triv1 H1 H2.
  valid_rewrite.
  constructor; eauto using deqtype_intro.
  Qed.

Lemma prodFormUniv_valid : prodFormUniv_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b i triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  eapply tr_prod_formation_univ; eauto using deq_intro.
  Qed.


Lemma prodEqUniv_valid : prodEqUniv_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a a' b b' i triv0 triv1 H1 H2.
  valid_rewrite. 
  constructor.
  eapply tr_prod_formation_univ; eauto using deq_intro.
  Qed.

Lemma prodExistsEq_valid: prodExistsEq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a a' b b' triv1 triv0 H0 H1.
  valid_rewrite. 
  constructor; eauto using deqtype_intro, tr_eqtype_formation_left.
  Qed.

Lemma prodExistsEqUniv_valid : prodExistsEqUniv_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a a' b b' i triv0 triv1 H1 H2.
  valid_rewrite. 
  do 2 constructor; eauto using deq_intro, tr_eq_reflexivity.
Qed.


Lemma prodSub_valid : prodSub_obligation.
Proof.
prepare.
intros G a a' b b' ext1 ext0 Ha Hb.
apply tr_prod_sub; auto.
Qed.


Lemma prodExistsSub_valid : prodExistsSub_obligation.
Proof.
prepare.
intros G a a' b b' ext3 ext2 ext1 ext0 Ha Hb Hbl Hbr.
apply tr_prod_sigma_sub; auto.
Qed.


Lemma existsProdSub_valid : existsProdSub_obligation.
Proof.
prepare.
intros G a a' b b' ext2 ext1 ext0 Ha Hb Hbr.
apply tr_sigma_prod_sub; auto.
Qed.


Lemma prodIntroOf_valid : prodIntroOf_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m n triv0 triv1 H0 H1.
  valid_rewrite.
  constructor.
  apply deq_intro in H0. apply deq_intro in H1.
  auto using tr_prod_intro.
Qed.

Lemma prodIntroEq_valid : prodIntroEq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m m' n n' triv0 triv1 H0 H1.
  valid_rewrite.
  constructor.
  apply deq_intro in H0. apply deq_intro in H1.
  auto using tr_prod_intro.
Qed.

Lemma prodIntro_valid : prodIntro_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m n H0 H1.
  valid_rewrite.
  auto using tr_prod_intro.
Qed.

Lemma prodElim1Of_valid : prodElim1Of_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m triv0 H.
  valid_rewrite.
  constructor.
  eapply tr_prod_elim1; eauto using deq_intro.
Qed.

Lemma prodElim1Eq_valid : prodElim1Eq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m n triv0 H.
  valid_rewrite.
  constructor.
  eapply tr_prod_elim1; eauto using deq_intro.
Qed.

Lemma prodElim1_valid : prodElim1_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m H.
  valid_rewrite.
  eapply tr_prod_elim1; eauto.
Qed.

Lemma prodElim2Of_valid : prodElim2Of_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m triv0 H.
  valid_rewrite.
  constructor.
  eapply tr_prod_elim2; eauto using deq_intro.
Qed.

Lemma prodElim2Eq_valid : prodElim2Eq_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m n triv0 H.
  valid_rewrite.
  constructor.
  eapply tr_prod_elim2; eauto using deq_intro.
Qed.

Lemma prodElim2_valid : prodElim2_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m H.
  valid_rewrite.
  eapply tr_prod_elim2; eauto. 
Qed.


Lemma prodEta_valid : prodEta_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G a b m triv0 Hm.
  valid_rewrite.
  constructor.
  apply deq_intro in Hm.
  pose proof (tr_prod_invert1 Hm) as Ha.
  pose proof (tr_prod_invert2 Hm) as Hb.
  eapply tr_eqtype_convert.
  apply tr_eqtype_symmetry. apply tr_prod_sigma_equal; try assumption.
  apply tr_sigma_eta.
  eapply tr_eqtype_convert; try apply tr_prod_sigma_equal;
    try assumption.
Qed.


Lemma prodExt_valid : prodExt_obligation.
Proof.
prepare.
intros G a b m n ext3 ext2 ext1 ext0 Hm Hn H1 H2.
so (tr_prod_formation_invert1 _#5 (tr_inhabitation_formation _#4 Hm)) as Ha.
assert (tr G (deqtype b b)) as Hb.
  {
  so (tr_prod_formation_invert2 _#5 (tr_inhabitation_formation _#4 Hm)) as H.
  replace (deqtype b b) with (substj (dot (ppi1 m) id) (deqtype (subst sh1 b) (subst sh1 b))).
  2:{
    simpsub.
    auto.
    }
  eapply tr_generalize; eauto.
  eapply tr_prod_elim1; eauto.
  }
apply (tr_eqtype_convert _ _ _ (sigma a (subst sh1 b))).
  {
  apply tr_eqtype_symmetry.
  apply tr_prod_sigma_equal; auto.
  }
apply (tr_sigma_ext _#5 a a (subst sh1 b) (subst sh1 b)).
  {
  simpsub.
  auto.
  }

  {
  simpsub.
  auto.
  }

  {
  apply (weakening _ [_] []).
    {
    simpsub.
    auto.
    }

    {
    cbn [length Dots.unlift].
    simpsub.
    auto.
    }
  cbn [length Dots.unlift].
  simpsub.
  cbn [List.app].
  auto.
  }

  {
  apply (tr_eqtype_convert _ _ _ (prod a b)); auto.
  apply tr_prod_sigma_equal; auto.
  }

  {
  apply (tr_eqtype_convert _ _ _ (prod a b)); auto.
  apply tr_prod_sigma_equal; auto.
  }
Qed.


Notation "[ x ]" := (cons x nil). (*... no idea why Coq.Lists notation doesn't work*)

Definition rcons {T} (L: list T) a := L ++ [a].

Lemma rcons_s1_cons_s2 {A} (L1 L2 : list A) a : L1 ++ (a::L2) = (rcons L1 a) ++ L2.
  unfold rcons. rewrite <- app_assoc.
  simpl. auto.
Qed.

Lemma substctx_app: forall G1 G2 s,
    @substctx Rules.obj s (G1 ++ G2) = (substctx (under (length G2) s) G1) ++ (substctx s G2).
  intros.
  induction G1; simpsub.
  - repeat rewrite app_nil_l. auto.
  - simpl. simpsub.
    rewrite <- app_length.
    rewrite <- IHG1. auto.
    Qed.

Lemma substctx_rcons: forall G1 g s,
    @substctx Rules.obj s (rcons G1 g) = rcons (substctx (under 1 s) G1) (substh s g).
  intros. unfold rcons. rewrite substctx_app. auto. Qed.

Lemma sigma_to_prod G1 G2 a b m1 m2 t :
  tr (G2 ++ (hyp_tm (sigma a (subst sh1 b)))::G1) (deq m1 m2 t) ->
  tr (G2 ++ (hyp_tm (prod a b))::G1) (deq m1 m2 t).
  intros Hsigma.
  (*getting ready to add another hyp of type (prod a b) *)
  replace m1 with
      (subst (under (length G2) (dot (var 0) id))
             (subst (under (length G2) sh1) m1)).
  2 : { simpsub. rewrite <- compose_under. simpsub. auto. }
  replace m2 with
      (subst (under (length G2) (dot (var 0) id))
             (subst (under (length G2) sh1) m2)).
  2 : { simpsub. rewrite <- compose_under. simpsub. auto. }
  (*adding the hyp*)
  apply (tr_contraction _ _ (hyp_tm (prod a b)) _#3).
  constructor.
  (*getting ready to exchange the two (prod a b) hyps*)
  replace (subst (under (length G2) sh1) m1) with
      (subst (under (length G2) (dot (var 1) (dot (var 0) (sh 2))))
             (subst (under (length G2 + 1) sh1) m1 )).
  2 : { simpsub. rewrite <- under_sum. simpsub. rewrite <- compose_under.
        simpsub.
        apply subst_eqsub. apply eqsub_symm. apply eqsub_under.
        apply eqsub_expand_sh.
  }
  replace (subst (under (length G2) sh1) m2) with
      (subst (under (length G2) (dot (var 1) (dot (var 0) (sh 2))))
             (subst (under (length G2 + 1) sh1) m2 )).
  2 : { simpsub. rewrite <- under_sum. simpsub. rewrite <- compose_under.
        simpsub.
        apply subst_eqsub. apply eqsub_symm. apply eqsub_under.
        apply eqsub_expand_sh.
  }
  rewrite <- (length_substctx _ sh1 G2).
  (*exchanging the hyps*)
  apply tr_exchange.
  (*getting ready to convert the most recent hyp from prod to sigma*)
  simpsub.
  assert (tr (hyp_tm (prod a b) :: G1) (deqtype (subst sh1 a) (subst sh1 a))) as Ha.
  (*a is a type*)
    apply (tr_inhabitation_formation _ (ppi1 (var 0)) (ppi1 (var 0))).
    eapply (tr_prod_elim1 _ _ (subst sh1 b)).
    rewrite <- subst_prod. apply tr_hyp_tm. constructor.
  assert (tr (hyp_tm (prod a b) :: G1) (deqtype (subst sh1 b) (subst sh1 b))) as Hb.
  (*b is a type*)
    apply (tr_inhabitation_formation _ (ppi2 (var 0)) (ppi2 (var 0))).
    eapply (tr_prod_elim2 _ (subst sh1 a)).
    rewrite <- subst_prod. apply tr_hyp_tm. constructor.
  (*converting*)
  eapply (tr_eqtype_convert_hyp _ _ (prod (subst sh1 a) (subst sh1 b))).
  apply tr_prod_sigma_equal; assumption.
  (*getting ready to weaken the (prod a b) hyp away*)
  simpsub. rewrite <- compose_under. simpsub.
  replace (under (length (substctx sh1 G2)) (dot (var 0) (sh 2)))
      with
        (@under Rules.obj (length (substctx sh1 G2) + 1) sh1).
  2: { rewrite <- under_sum. simpsub. auto. }
  match goal with |- tr ?G ?J => replace G with
      ((substctx sh1 (rcons G2 (hyp_tm (sigma a (subst sh1 b)))))
         ++ hyp_tm (prod a b) :: G1) end.
  2: { simpsub. simpl. rewrite (rcons_s1_cons_s2 _
                                              (hyp_tm (prod a b) :: G1)).
       f_equal.
       rewrite substctx_rcons.
       simpsub. auto. }
  replace (length (substctx sh1 G2) + 1) with (length (rcons G2 (hyp_tm (sigma a (subst sh1 b))))).
  rewrite <- substj_deq.
  (*(prod a b) hyp is gone!*)
  apply tr_weakening.
  rewrite <- rcons_s1_cons_s2.
  apply Hsigma.
  unfold rcons. rewrite app_length. simpl.
  auto using length_substctx.
Qed.


Lemma prodLeft_valid : prodLeft_obligation.
  unfoldtop. autounfold with valid_hint.
  intros G1 G2 a b c m H.
  valid_rewrite.
  (*change the context to have a normal product as a hyp*)
  match goal with |- tr ?G ?J =>
                  assert (equivctx G
    (G2 ++
     hyp_tm (prod a b) :: G1)
                         ) as Hctx end.

  { apply Forall2_app;
      [apply equivctx_refl | constructor; try apply equivctx_refl].
    apply equivh_refl. }
  apply sigma_to_prod. apply tr_sigma_eta_hyp. assumption.
Qed.


Lemma prodFormInv1_valid : prodFormInv1_obligation.
Proof.
prepare.
intros G a b ext0 H.
eapply tr_prod_formation_invert1; eauto.
Qed.


Lemma prodFormInv2_valid : prodFormInv2_obligation.
Proof.
prepare.
intros G a b ext0 m Hprod Hm.
so (tr_prod_formation_invert2 _#5 Hprod) as Hb.
cut (tr (hyp_tm a :: G) (deqtype (subst sh1 b) (subst sh1 b))).
  {
  intro Hb'.
  so (tr_generalize _#4 Hm Hb') as H.
  simpsubin H.
  exact H.
  }
eapply tr_prod_formation_invert2; eauto.
Qed.
