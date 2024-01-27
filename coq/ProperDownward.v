
Require Import Axioms.
Require Import Tactics.
Require Import Sigma.
Require Import Relation.
Require Import Equality.
Require Import Syntax.
Require Import SimpSub.
Require Import Dynamic.
Require Import Ofe.
Require Import Spaces.
Require Import Uniform.
Require Import Urelsp.
Require Import Intensional.
Require Import Ordinal.
Require Import Candidate.
Require Import Model.
Require Import Ceiling.
Require Import Truncate.
Require Import Standard.
Require Import System.
Require Import Semantics.
Require Import ProperClosed.
Require Import ProperFun.
Require Import MapTerm.
Require Import Hygiene.
Require Import Extend.
Require Import ExtendTruncate.
Require Import SemanticsPi.
Require Import SemanticsEqual.
Require Import SemanticsAll.
Require Import SemanticsExist.
Require Import SemanticsMu.
Require Import SemanticsGuard.
Require Import SemanticsKind.
Require Import SemanticsUniv.
Require Import SemanticsFut.
Require Import SemanticsQuotient.
Require Import SemanticsSet.
Require Import SemanticsWtype.
Require Import SemanticsSigma.
Require Import SemanticsSimple.
Require Import SemanticsSubtype.
Require Import SemanticsEqtype.
Require Import ExtSpace.
Require Import PreSpacify.
Require Import Lattice.


Lemma interp_kext_downward :
  forall pg i j k K,
    j <= i
    -> interp_kext pg i k K
    -> interp_kext pg j k (approx j K).
Proof.
intros pg i j k K Hji Hint.
destruct Hint as (Q & h & Hcl & Hsteps & Hlev & <-).
rewrite -> approx_combine_le; auto.
exists Q, h.
auto.
Qed.


Lemma interp_uext_downward :
  forall pg i j a R,
    j <= i
    -> interp_uext pg i a R
    -> interp_uext pg j a (ceiling (S j) R).
Proof.
intros pg i j a R Hji Hint.
destruct Hint as (w & A & h & Hcl & Hsteps & Hlev & <-).
rewrite -> ceiling_combine_le; [| omega].
exists w, A, h.
auto.
Qed.


Lemma cbasic_std_ind :
  forall system pg s i a Q,
    cbasic system pg s i a Q
    -> (forall j, j <= i -> cbasic system pg s j a (projc j (stdc (S j) Q)))
    -> Q = stdc (S i) Q.
Proof.
intros system pg s i a Q Hint IH.
so (IH i (le_refl _)) as Hint'.
so (cbasic_fun _#7 Hint Hint') as Heq.
so Heq as Heq'.
rewrite <- stdc_idem in Heq'.
rewrite -> projc_stdc in Heq'; [| apply le_refl].
rewrite <- Heq in Heq'.
exact Heq'.
Qed.


Definition fntruncate i (A : surel) (B : urelsp A -n> siurel_ofe) 
  : urelsp (ceiling i A) -n> siurel_ofe
  :=
  nearrow_compose
    (nearrow_compose (iutruncate_ne i) B)
    (embed_ceiling_ne i A).


Lemma semantics_downward :
  forall system,
    (forall pg s i j a K,
       j <= i
       -> kbasic system pg s i a K
       -> kbasic system pg s j a (approx j K))
    /\
    (forall pg s i j a Q,
       j <= i
       -> cbasic system pg s i a Q
       -> cbasic system pg s j a (projc j (stdc (S j) Q)))
    /\
    (forall pg s i j a R,
       j <= i
       -> basic system pg s i a R
       -> basic system pg s j a (iutruncate (S j) R))
    /\
    (forall pg s i j A b B,
       j <= i
       -> functional system pg s i A b B
       -> functional system pg s j (ceiling (S j) A) b (fntruncate (S j) A B)).
Proof.
intro system.
exploit
  (semantics_ind system
     (fun pg s i a K => forall j, j <= i -> kbasicv system pg s j a (approx j K))
     (fun pg s i a Q => forall j, j <= i -> cbasicv system pg s j a (projc j (stdc (S j) Q)))
     (fun pg s i a R => forall j, j <= i -> basicv system pg s j a (iutruncate (S j) R))
     (fun pg s i a K => forall j, j <= i -> kbasic system pg s j a (approx j K))
     (fun pg s i a Q => forall j, j <= i -> cbasic system pg s j a (projc j (stdc (S j) Q)))
     (fun pg s i a R => forall j, j <= i -> basic system pg s j a (iutruncate (S j) R))
     (fun pg s i A b B =>
        forall j, 
          j <= i 
          -> functional system pg s j (ceiling (S j) A) b (fntruncate (S j) A B))) as Hind;
try (intros; 
     cbn; 
     eauto using kbasicv, cbasicv; 
     first [apply interp_cty];
     eauto;
     done).

(* ktarrow *)
{
intros pg s i a k A K _ IH1 _ IH2 j Hj.
cbn.
rewrite <- den_iutruncate.
apply interp_ktarrow; eauto.
rewrite <- iutruncate_extend_iurel; auto.
}

(* kfut_zero *)
{
intros pg s k Hcl j Hj.
assert (j = 0) by omega; subst j.
apply interp_kfut_zero; auto.
}

(* kfut *)
{
intros pg s i k K _ IH j Hj.
cbn.
destruct j as [| j].
  {
  apply interp_kfut_zero; auto.
  exact (kbasic_closed _#6 (IH 0 (Nat.le_0_l i))).
  }
apply interp_kfut; auto.
apply IH.
omega.
}

(* ext *)
{
intros pg s i Q h Hcin j Hj.
rewrite <- projc_stdc; [| omega].
rewrite -> projc_combine_le; auto.
rewrite -> stdc_combine_le; [| omega].
apply interp_ext; auto.
}

(* clam *)
{
intros pg s i k a K L A h HeqL Hk _ IH2 j Hj.
rewrite -> stdc_combine_le; [| omega].
rewrite -> projc_stdc; auto.
unfold projc.
cbn.
eapply (interp_clam _#9 (le_ord_trans _#3 (approx_level j K) h)); eauto using approx_idem, interp_kext_downward.
intros j' Hj' x.
so (IH2 j' (le_trans _#3 Hj' Hj) (transport (approx_combine_le j' j K Hj') spcar x) j' (le_refl _)) as Hint.
force_exact Hint; clear Hint.
f_equal.
  {
  f_equal.
  f_equal.
  f_equal.
  symmetry.
  apply objsome_compat.
  apply (expair_compat_transport _#6 (approx_combine_le j' j K Hj')).
  cut (forall l l' x (h : l = l'),
         transport h spcar (std (S j') l x)
         = std (S j') l' (transport h spcar x)).
    {
    intro Hcond.
    apply Hcond.
    }
  intros l l' y Heq.
  subst l'.
  reflexivity.
  }

  {
  cbn.
  fold (proj j L).
  fold (embed j K).
  change (projc j' (stdc (S j') (projc j' (stdc (S j') (expair L (pi1 A (std (S j') K (embed j' K (transport (approx_combine_le _#3 Hj') spcar x))))))))
          =
          projc j' (stdc (S j') (projc j (expair L (pi1 A (embed j K (std (S j') (approx j K) (embed j' (approx j K) x)))))))).
  setoid_rewrite <- projc_stdc at 1 2; [| omega ..].
  rewrite -> projc_idem.
  rewrite -> projc_combine_le; auto.
  f_equal.
  rewrite -> stdc_idem.
  f_equal.
  f_equal.
  f_equal.
  rewrite <- embed_std; auto.
  rewrite -> !embed_std; [| omega ..].
  f_equal.
  rewrite -> (embed_combine_le _#4 Hj').
  reflexivity.
  }
}

(* capp *)
{
intros pg s i a b K L A B _ IH1 Hintb IH2 j Hj.
so (IH1 _ Hj) as H1.
so (IH2 _ Hj) as H2.
unfold projc, stdc in H1, H2 |- *.
cbn in H1, H2 |- *.
relquest.
  {
  apply interp_capp; eauto.
  }
f_equal.
cbn.
rewrite -> std_arrow_is.
cbn.
fold (proj j L).
fold (std (S j) L).
fold (std (S j) K).
fold (embed j K).
f_equal.
apply std_collapse.
apply (pi2 A).
so (cbasic_std_ind _ pg s i b (expair K B) Hintb IH2) as Heq.
unfold stdc in Heq.
cbn in Heq.
injectionc Heq.
intros H.
injectionT H.
intros HeqB.
rewrite -> HeqB at 2.
eapply dist_trans.
2:{
  apply std_dist; omega.
  }
apply std_nonexpansive.
eapply dist_trans.
  {
  apply embed_proj.
  }

  {
  rewrite -> HeqB at 2.
  apply std_dist.
  omega.
  }
}

(* ctlam *)
{
intros pg s i a b k K A f B Hcl Ha Hk _ IH Hf j Hj.
unfold projc, stdc.
cbn.
set (l := cin pg).
so (interp_kext_downward _#5 Hj Hk) as Hk'.
so (interp_uext_downward _#5 Hj Ha) as Ha'.
assert (forall j' m n,
          rel (extend_urel l stop (ceiling (S j) A)) j' m n
          -> j' <= j) as Hcimpl.
  {
  intros j' m n H.
  destruct H.
  omega.
  }
set (f' :=
       (fun j' m n (Hmn : rel (extend_urel l stop (ceiling (S j) A)) j' m n) =>
          (transport
             (eqsymm (approx_combine_le _#3 (Hcimpl _ _ _ Hmn)))
             spcar
             (std (S j') (approx j' K) 
                (f j' m n (Hmn ander)))))).
set (B' := (proj j (qtarrow l A K) (std (S j) (qtarrow l A K) B))).
cbn in B'.
exploit (interp_ctlam system pg s j a b k 
           (approx j K) (ceiling (S j) A) f' B') as H; auto.
  {
  clear Hf B'.
  intros j' m n Hmn.
  subst f'.
  cbn.
  destruct Hmn as (Hj'a & Hmn).
  assert (j' <= j) as Hj' by omega.
  so (IH j' m n Hmn j' (le_refl _)) as H.
  unfold projc, stdc in H.
  cbn in H.
  force_exact H; clear H.
  f_equal.
  apply (expair_compat_transport _#6 (eqtrans (approx_idem _ _) (eqsymm (approx_combine_le _#3 Hj')))).
  rewrite <- transport_compose.
  symmetry.
  apply (transport_symm _ spcar _ _ (approx_combine_le _#3 Hj')).
  rewrite -> proj_near.
  rewrite -> transport_compose.
  match goal with
  | |- transport ?X _ _ = _ => rewrite -> (proof_irrelevance _ X (eq_refl _))
  end.
  reflexivity.
  }

  {
  clear IH.
  intros j' m n Hmn.
  destruct Hmn as (Hj'a & Hmn).
  subst f' B'.
  cbn.
  rewrite -> std_tarrow_is.
  cbn.
  unfold std_tarrow_action.
  rewrite -> urelsp_index_embed_ceiling.
  rewrite -> urelsp_index_inj.
  rewrite -> Nat.min_r; auto.
  fold (std (S j') K).
  fold (proj j K).
  rewrite -> embed_ceiling_urelspinj.
  rewrite -> Hf.
  rewrite <- proj_embed_up.
  rewrite -> embed_std; auto.
  }
}

(* ctapp *)
{
intros pg s i b m l A K B n p Hnp Hm _ IH j Hj.
so (IH j Hj) as Hint.
unfold projc, stdc in Hint.
cbn in Hint.
assert (rel (ceiling (S j) A) j n p) as Hnp'.
  {
  split; auto.
  eapply urel_downward_leq; eauto.
  }
so (interp_ctapp _#12 Hnp' Hm Hint) as H.
cbn in H.
unfold projc, stdc.
cbn.
force_exact H; clear H.
f_equal.
f_equal.
destruct Hnp' as (Hja, Hnp').
rewrite -> embed_ceiling_urelspinj.
rewrite -> std_tarrow_is.
cbn.
unfold std_tarrow_action.
rewrite -> urelsp_index_inj.
rewrite -> Nat.min_id.
fold (proj j K).
fold (std (S j) K).
f_equal.
apply std_collapse.
apply (pi2 B).
apply urelspinj_dist; auto.
}

(* cpair *)
{
intros pg s i a b K L x y _ IH1 _ IH2 j Hj.
unfold projc, stdc.
cbn.
apply interp_cpair; [apply IH1 | apply IH2]; auto.
}

(* cpi1 *)
{
intros pg s i a K L x _ IH j Hj.
unfold projc, stdc.
cbn.
so (IH _ Hj) as H.
unfold projc, stdc in H.
cbn in H.
exact (interp_cpi1 _#8 H).
}

(* cpi2 *)
{
intros pg s i a K L x _ IH j Hj.
unfold projc, stdc.
cbn.
so (IH _ Hj) as H.
unfold projc, stdc in H.
cbn in H.
exact (interp_cpi2 _#8 H).
}

(* cnext zero *)
{
intros pg s a Hcl j Hj.
assert (j = 0) by omega; subst j.
unfold projc, stdc.
cbn.
apply interp_cnext_zero; auto.
}

(* cnext *)
{
intros pg s i a K x Hinta IH j Hj.
unfold projc, stdc.
destruct j as [| j].
  {
  cbn.
  apply interp_cnext_zero.
  exact (cbasic_closed _#6 Hinta).
  }
cbn.
apply interp_cnext.
rewrite -> std_fut_is.
cbn.
apply IH.
omega.
}

(* cprev *)
{
intros pg s i A k x Hinta IH j Hj.
unfold projc, stdc.
cbn.
apply interp_cprev.
apply IH.
omega.
}

(* cty *)
{
intros pg s i a R _ IH j Hj.
unfold projc, stdc; cbn.
apply interp_cty; auto.
rewrite -> std_type_is.
rewrite <- iutruncate_extend_iurel.
apply IH; auto.
}

(* ccon *)
{
intros pg s i lv a gpg R Hlv Hle _ IH j Hj.
rewrite -> iutruncate_extend_iurel.
apply interp_con; auto.
apply IH; auto.
}

(* karrow *)
{
intros pg s i a b A B Ha IH1 Hb IH2 j Hj.
rewrite -> iutruncate_iuarrow.
rewrite -> min_r; auto.
apply interp_karrow; auto.
}

(* tarrow *)
{
intros pg s i a b A B Ha IH1 Hb IH2 j Hj.
rewrite -> iutruncate_iuarrow.
rewrite -> min_r; auto.
apply interp_tarrow; auto.
}

(* pi *)
{
intros pg s i a b A B Ha IH1 Hb IH2 j Hj.
rewrite -> iutruncate_iupi.
rewrite -> min_r; auto.
apply interp_pi; auto.
apply IH2; auto.
}

(* intersect *)
{
intros pg s i a b A B Ha IH1 Hb IH2 j Hj.
rewrite -> iutruncate_iuintersect.
rewrite -> min_r; auto.
apply interp_intersect; auto.
apply IH2; auto.
}

(* union *)
{
intros pg s i a b A B Ha IH1 Hb IH2 j Hj.
rewrite -> iutruncate_iuunion.
apply interp_union; auto.
apply IH2; auto.
}

(* prod *)
{
intros pg s i a b A B Ha IH1 Hb IH2 j Hj.
rewrite -> iutruncate_iuprod.
apply interp_prod; auto.
}

(* sigma *)
{
intros pg s i a b A B Ha IH1 Hb IH2 j Hj.
rewrite -> iutruncate_iusigma.
apply interp_sigma; auto.
apply IH2; auto.
}

(* set *)
{
intros pg s i a b A B Ha IH1 Hb IH2 j Hj.
rewrite -> iutruncate_iuset.
apply interp_set; auto.
apply IH2; auto.
}

(* iset *)
{
intros pg s i a b A B Ha IH1 Hb IH2 j Hj.
rewrite -> iutruncate_iuiset.
apply interp_iset; auto.
apply IH2; auto.
}

(* quotient *)
{
intros pg s i a b A B hs ht Ha IH1 Hb IH2 j Hj.
rewrite -> iutruncate_iuquotient.
apply interp_quotient; auto.
force_exact (IH2 _ Hj).
apply functional_rewrite.
apply (eq_impl_eq_dep _#6 (ceiling_prod _#4)).
apply nearrow_extensionality.
intros C.
cbn.
rewrite -> (pi1_transport_dep_lift _ _ (fun A B => @nonexpansive (urelsp A) (wiurel_ofe stop) B) _ _ (ceiling_prod j stop (den A) (den A))).
rewrite -> app_transport_dom.
auto.
}

(* guard *)
{
intros pg s i a b A B Ha IH1 Hb IH2 j Hj.
rewrite -> (iutruncate_iuguard _#5 Hj).
apply interp_guard; auto.
so (IH2 _ Hj) as Hfunc.
unfold fntruncate in Hfunc.
unfold embed_ceiling_squash_ne.
rewrite <- nearrow_compose_assoc.
apply transport_functional.
exact Hfunc.
}

(* fut zero *)
{
intros pg s a H j Hj.
assert (j = 0) by omega; subst j.
rewrite -> iutruncate_iufut0; [| omega].
apply interp_fut_zero; auto.
}

(* fut *)
{
intros pg s i a A Ha IH j Hj.
destruct j as [| j].
  {
  rewrite -> iutruncate_iufut_one.
  apply interp_fut_zero.
  eapply basic_closed; eauto.
  }
rewrite -> iutruncate_iufut; [| omega].
rewrite -> Nat.min_r; [| omega].
cbn.
apply interp_fut.
apply IH.
omega.
}

(* void *)
{
intros pg s i j Hj.
rewrite -> iutruncate_iubase.
rewrite -> ceiling_void.
apply interp_void.
}

(* unit *)
{
intros pg s i j Hj.
rewrite -> iutruncate_iubase.
rewrite -> ceiling_unit.
rewrite -> Nat.min_r; auto.
apply interp_unit.
}

(* bool *)
{
intros pg s i j Hj.
rewrite -> iutruncate_iubase.
rewrite -> ceiling_bool.
rewrite -> Nat.min_r; auto.
apply interp_bool.
}

(* wt *)
{
intros pg s i a b A B Ha IH1 Hb IH2 j Hj.
rewrite -> iutruncate_iuwt.
apply interp_wt; auto.
apply IH2; auto.
}

(* equal *)
{
intros pg s i a m n p q A Hmp Hnq _ IH j H2.
so (srel_ceiling_intro _#7 (Nat.le_min_r (S i) (S j)) (srel_downward_leq _#7 (Nat.le_min_l i j) Hmp)) as Hmp'.
so (srel_ceiling_intro _#7 (Nat.le_min_r (S i) (S j)) (srel_downward_leq _#7 (Nat.le_min_l i j) Hnq)) as Hnq'.
fold min in Hmp', Hnq'.
rewrite -> (iutruncate_iuequal _#11 Hmp' Hnq').
setoid_rewrite <- (Nat.min_r i j) at 1; auto.
apply interp_equal.
rewrite -> Nat.min_r; auto.
}

(* eqtype *)
{
intros pg s i a b R R' _ IH1 _ IH2 j Hj.
unfold iutruncate, iueqtype, eqtype_urel.
cbn [fst snd].
rewrite -> ceiling_property.
rewrite -> min_r; [| omega].
rewrite -> meta_truncate_pair; [| omega].
rewrite -> !meta_truncate_iurel; try omega.
replace (property_urel (eqtype_property stop R R') stop j (eqtype_property_downward _#3)) with (property_urel (eqtype_property stop (iutruncate (S j) R) (iutruncate (S j) R')) stop j (eqtype_property_downward _#3)).
  {
  apply interp_eqtype; auto.
  }
apply property_urel_extensionality; auto.
intros j' Hj'.
unfold eqtype_property.
rewrite -> !iutruncate_combine_le; try omega.
reflexivity.
}

(* sequal *)
{
intros s i m n Hclm Hcln Hequiv j Hj.
rewrite -> iutruncate_iubase.
rewrite -> ceiling_unit.
rewrite -> Nat.min_r; auto.
apply interp_sequal; auto.
}

(* subtype *)
{
intros pg s i a b R R' _ IH1 _ IH2 j Hj.
unfold iutruncate, iusubtype, subtype_urel.
cbn [fst snd].
rewrite -> ceiling_property.
rewrite -> min_r; [| omega].
rewrite -> meta_truncate_pair; [| omega].
rewrite -> !meta_truncate_iurel; try omega.
replace (property_urel (subtype_property stop (den R) (den R')) stop j (subtype_property_downward _#3)) with (property_urel (subtype_property stop (den (iutruncate (S j) R)) (den (iutruncate (S j) R'))) stop j (subtype_property_downward _#3)).
  {
  apply interp_subtype; auto.
  }
apply property_urel_extensionality; auto.
intros j' Hj'.
unfold subtype_property.
split.
  {
  intros Hact k m p Hk Hmp.
  assert (k < S j) as Hkj by omega.
  so (Hact _#3 Hk (conj Hkj Hmp)) as H.
  destruct H; auto.
  }

  {
  intros Hact k m p Hk Hmp.
  destruct Hmp as (Hks & Hmp).
  split; auto.
  }
}

(* all *)
{
intros pg s i lv k a gpg K A h Hlv _ IH1 Hle _ IH2 j Hj.
so (le_ord_trans _#3 (approx_level j _) h) as h'.
rewrite -> iutruncate_iuall.
replace (nearrow_compose2 (embed_ne j K) (iutruncate_ne (S j)) (std (S i) (qarrow K (qtype stop)) A))
  with (std (S j) (qarrow (approx j K) (qtype stop)) (nearrow_compose A (embed_ne j K))).
2:{
  rewrite -> !std_arrow_is; cbn.
  apply nearrow_extensionality.
  intro x.
  cbn.
  change (std (S j) (qtype stop) (pi1 A (embed j K (std (S j) (approx j K) x)))
          =
          iutruncate (S j) (std (S i) (qtype stop) (pi1 A (std (S i) K (embed j K x))))).
  rewrite -> !std_type_is.
  rewrite -> iutruncate_combine_le; [| omega].
  apply iutruncate_collapse.
  apply (pi2 A).
  rewrite -> embed_std; auto.
  apply std_dist; omega.
  }
apply (interp_all _#7 gpg _ _ h'); auto.
intros j' Hj' x.
so (IH2 j' (le_trans _#3 Hj' Hj) (transport (approx_combine_le j' j K Hj') spcar x) j' (le_refl _)) as Hint.
force_exact Hint; clear Hint.
f_equal.
  {
  f_equal.
  f_equal.
    {
    f_equal.
    rewrite -> approx_combine_le; auto.
    }
  f_equal.
  f_equal.
  symmetry.
  apply objsome_compat.
  apply (expair_compat_transport _#6 (approx_combine_le j' j K Hj')).
  cut (forall l l' x (h : l = l'),
         transport h spcar (std (S j') l x)
         = std (S j') l' (transport h spcar x)).
    {
    intro Hcond.
    apply Hcond.
    }
  intros l l' y Heq.
  subst l'.
  reflexivity.
  }

  {
  cbn.
  fold (embed j K).
  rewrite -> iutruncate_idem.
  f_equal.
  f_equal.
  rewrite -> embed_std; [| omega].
  f_equal.
  symmetry.
  apply embed_combine_le.
  }
}

(* alltp *)
{
intros pg s i a A _ IH j Hj.
rewrite -> iutruncate_iualltp.
apply interp_alltp.
intros k Hk X.
cbn.
apply IH; auto.
omega.
}

(* exist *)
{
intros pg s i lv k a gpg K A h Hlv _ IH1 Hle _ IH2 j Hj.
so (le_ord_trans _#3 (approx_level j _) h) as h'.
rewrite -> iutruncate_iuexist.
replace (nearrow_compose2 (embed_ne j K) (iutruncate_ne (S j)) (std (S i) (qarrow K (qtype stop)) A))
  with (std (S j) (qarrow (approx j K) (qtype stop)) (nearrow_compose A (embed_ne j K))).
2:{
  rewrite -> !std_arrow_is; cbn.
  apply nearrow_extensionality.
  intro x.
  cbn.
  change (std (S j) (qtype stop) (pi1 A (embed j K (std (S j) (approx j K) x)))
          =
          iutruncate (S j) (std (S i) (qtype stop) (pi1 A (std (S i) K (embed j K x))))).
  rewrite -> !std_type_is.
  rewrite -> iutruncate_combine_le; [| omega].
  apply iutruncate_collapse.
  apply (pi2 A).
  rewrite -> embed_std; auto.
  apply std_dist; omega.
  }
apply (interp_exist _#7 gpg _ _ h'); auto.
intros j' Hj' x.
so (IH2 j' (le_trans _#3 Hj' Hj) (transport (approx_combine_le j' j K Hj') spcar x) j' (le_refl _)) as Hint.
force_exact Hint; clear Hint.
f_equal.
  {
  f_equal.
  f_equal.
    {
    f_equal.
    rewrite -> approx_combine_le; auto.
    }
  f_equal.
  f_equal.
  symmetry.
  apply objsome_compat.
  apply (expair_compat_transport _#6 (approx_combine_le j' j K Hj')).
  cut (forall l l' x (h : l = l'),
         transport h spcar (std (S j') l x)
         = std (S j') l' (transport h spcar x)).
    {
    intro Hcond.
    apply Hcond.
    }
  intros l l' y Heq.
  subst l'.
  reflexivity.
  }

  {
  cbn.
  fold (embed j K).
  rewrite -> iutruncate_idem.
  f_equal.
  f_equal.
  rewrite -> embed_std; [| omega].
  f_equal.
  symmetry.
  apply embed_combine_le.
  }
}

(* extt *)
{
intros pg s i w R h Hw j Hj.
rewrite -> iutruncate_extend_iurel.
rewrite -> iutruncate_combine_le; try omega.
apply interp_extt; auto.
}

(* mu *)
{
intros pg w s i a F Hw _ IH Hne Hmono Hlocal j Hj.
rewrite -> iutruncate_iubase.
assert (monotone (fun X => ceiling (S j) (den (F X)))) as Hmono'.
  {
  eapply impl_compose; eauto.
  apply monotone_ceiling.
  }
assert (@nonexpansive (wurel_ofe w) (wurel_ofe w) (fun X => ceiling (S j) (den (F X)))) as Hne'.
  {
  apply compose_ne_ne; auto.
  apply ceiling_nonexpansive.
  }
rewrite -> ceiling_extend_urel.
rewrite -> ceiling_mu; auto.
change (basicv system pg s j (mu a) (iubase (extend_urel w stop (mu_urel w (fun X => den (iutruncate (S j) (F X))))))).
apply interp_mu; auto.
intros X h.
rewrite <- iutruncate_extend_iurel.
apply IH; auto.
}

(* ispositive *)
{
intros pg s i a Hcl j Hj.
rewrite -> iutruncate_iubase.
unfold SemanticsPositive.ispositive_urel.
rewrite -> ceiling_property.
rewrite -> Nat.min_r; auto.
apply interp_ispositive; auto.
}

(* isnegative *)
{
intros pg s i a Hcl j Hj.
rewrite -> iutruncate_iubase.
unfold SemanticsPositive.isnegative_urel.
rewrite -> ceiling_property.
rewrite -> Nat.min_r; auto.
apply interp_isnegative; auto.
}

(* rec *)
{
intros pg s i a A _ IH j Hj.
apply interp_rec.
apply IH; auto.
}

(* univ *)
{
intros pg s i m gpg Hm Hstr Hcex j Hj.
rewrite -> iutruncate_iuuniv.
rewrite -> Nat.min_r; auto.
apply interp_univ; auto.
}

(* kind *)
{
intros pg s i m gpg h Hm Hlt j Hj.
rewrite -> iutruncate_iukind.
rewrite -> Nat.min_r; auto.
apply interp_kind; auto.
}

(* kbasic *)
{
intros pg s i k k' K Hcl Hsteps _ IH j Hj.
eapply kinterp_eval; eauto.
}

(* cbasic *)
{
intros pg s i c c' Q Hcl Hsteps _ IH j Hj.
eapply cinterp_eval; eauto.
}

(* basic *)
{
intros pg s i a a' R Hcl Hsteps _ IH j Hj.
eapply interp_eval; eauto.
}

(* functional *)
{
intros pg s i A b B Hclb Hcoarse Hb IH j Hj.
eapply functional_i; eauto.
  {
  symmetry.
  apply ceiling_idem.
  }
intros j' m p Hj' Hmp.
destruct Hmp as (Hj'' & Hmp).
cbn.
rewrite -> embed_ceiling_urelspinj.
so (Hb j' m p (le_trans _#3 Hj' Hj) Hmp) as HB.
force_exact HB.
f_equal.
so (IH j' m p (le_trans _#3 Hj' Hj) Hmp j' (le_refl j')) as HB'.
so (basic_fun _#7 HB HB') as Heq.
rewrite -> Heq.
setoid_rewrite -> Heq at 2.
rewrite -> iutruncate_combine.
rewrite -> Nat.min_r; auto.
}

(* wrapup *)
{
do 6 (destruct Hind as (?, Hind)).
do2 3 split; intros; eauto.
}
Qed.


Lemma kbasic_downward :
  forall system pg s i j a K,
    j <= i
    -> kbasic system pg s i a K
    -> kbasic system pg s j a (approx j K).
Proof.
intro system.
exact (semantics_downward system andel).
Qed.


Lemma cbasic_downward :
  forall system pg s i j a Q,
    j <= i
    -> cbasic system pg s i a Q
    -> cbasic system pg s j a (projc j (stdc (S j) Q)).
Proof.
intro system.
exact (semantics_downward system anderl).
Qed.


Lemma basic_downward :
  forall system pg s i j a R,
    j <= i
    -> basic system pg s i a R
    -> basic system pg s j a (iutruncate (S j) R).
Proof.
intro system.
exact (semantics_downward system anderrl).
Qed.


Lemma functional_downward :
  forall system pg s i j A b B,
    j <= i
    -> functional system pg s i A b B
    -> functional system pg s j (ceiling (S j) A) b (fntruncate (S j) A B).
Proof.
intro system.
exact (semantics_downward system anderrr).
Qed.


Lemma kbasic_impl_approx :
  forall system pg s i k K,
    kbasic system pg s i k K
    -> K = approx i K.
Proof.
intros system pg s i k K Hint.
so (kbasic_downward _#7 (le_refl i) Hint) as Hint'.
exact (kbasic_fun _#7 Hint Hint').
Qed.


Lemma cbasic_impl_proj :
  forall system pg s i a Q,
    cbasic system pg s i a Q
    -> Q = projc i Q.
Proof.
intros system pg s i a Q Hint.
so (cbasic_downward _#7 (le_refl _) Hint) as Hint'.
so (cbasic_fun _#7 Hint Hint') as Heq.
so Heq as H.
rewrite <- projc_idem in H.
rewrite <- Heq in H.
exact H.
Qed.


Lemma cbasic_impl_std :
  forall system pg s i a Q,
    cbasic system pg s i a Q
    -> Q = stdc (S i) Q.
Proof.
intros system pg s i a Q Hint.
so (cbasic_downward _ pg s i i a Q (le_refl _) Hint) as Hint'.
so (cbasic_fun _#7 Hint Hint') as Heq.
so Heq as H.
rewrite -> projc_stdc in H; [| omega].
rewrite <- stdc_idem in H.
rewrite <- projc_stdc in H; [| omega].
rewrite <- Heq in H.
exact H.
Qed.


Lemma cbasic_impl_form :
  forall system pg s i a Q,
    cbasic system pg s i a Q
    -> Q = projc i (stdc (S i) Q).
Proof.
intros system pg s i a Q Hint.
so (cbasic_downward _#7 (le_refl _) Hint) as Hint'.
exact (cbasic_fun _#7 Hint Hint').
Qed.


Lemma basic_impl_iutruncate :
  forall system pg s i a R,
    basic system pg s i a R
    -> R = iutruncate (S i) R.
Proof.
intros system pg s i a R Hint.
so (basic_downward _#7 (le_refl _) Hint) as H.
exact (basic_fun _#7 Hint H).
Qed.


Lemma interp_kext_impl_approx :
  forall pg i k K,
    interp_kext pg i k K
    -> K = approx i K.
Proof.
intros pg i k K H.
decompose H.
intros Q h _ _ _ <-.
symmetry.
apply approx_idem.
Qed.


Lemma interp_uext_impl_ceiling :
  forall pg i a A,
    interp_uext pg i a A
    -> A = ceiling (S i) A.
Proof.
intros pg i a A H.
decompose H.
intros w R h _ _ _ <-.
symmetry.
apply ceiling_idem.
Qed.


Lemma basic_member_index :
  forall system pg s i a A j m n,
    basic system pg s i a A
    -> rel (den A) j m n
    -> j <= i.
Proof.
intros system pg s i a A j m n Hint Hrel.
so (basic_impl_iutruncate _#6 Hint) as Heq.
rewrite -> Heq in Hrel.
destruct Hrel as (H & _).
omega.
Qed.
