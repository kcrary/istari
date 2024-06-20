
Require Import Tactics.
Require Import Sigma.
Require Import Relation.
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
Require Import Equivalence.
Require Import Equivalences.
Require Import System.
Require Import Semantics.
Require Import Hygiene.
Require Import Extend.
Require Import MapTerm.
Require Import SemanticsEqual.
Require Import SemanticsMu.
Require Import SemanticsProperty.
Require Import SemanticsPositive.
Require Import SemanticsPartial.
Require Import Approximation.


Section semantics.


Variable system : System.


Lemma interp_kext_equiv :
  forall pg i m m' K,
    hygiene clo m'
    -> equiv m m'
    -> interp_kext pg i m K
    -> interp_kext pg i m' K.
Proof.
intros pg i m m' K Hcl Hequiv H.
destruct H as (Q & h & _ & Hsteps & Hle & Heq).
exists Q, h.
do2 3 split; auto.
so (equiv_eval _#4 Hequiv (conj Hsteps value_ext)) as (n & (Hsteps' & _) & Hmc).
invertc_mc Hmc.
intros <-.
exact Hsteps'.
Qed.


Lemma interp_uext_equiv :
  forall pg i m m' R,
    hygiene clo m'
    -> equiv m m'
    -> interp_uext pg i m R
    -> interp_uext pg i m' R.
Proof.
intros pg i m m' R Hcl Hequiv H.
destruct H as (w & R' & h & _ & Hsteps & Hle & Heq).
exists w, R', h.
do2 3 split; auto.
so (equiv_eval _#4 Hequiv (conj Hsteps value_ext)) as (n & (Hsteps' & _) & Hmc).
invertc_mc Hmc.
intros <-.
exact Hsteps'.
Qed.


Lemma semantics_equiv :
  (forall pg s i a a' X,
     hygiene clo a'
     -> equiv a a'
     -> kbasic system pg s i a X
     -> kbasic system pg s i a' X)
  /\
  (forall pg s i a a' X,
     hygiene clo a'
     -> equiv a a'
     -> cbasic system pg s i a X
     -> cbasic system pg s i a' X)
  /\
  (forall pg s i a a' X,
     hygiene clo a'
     -> equiv a a'
     -> basic system pg s i a X
     -> basic system pg s i a' X).
Proof.
exploit
  (semantics_ind system
     (fun pg s i a X => forall a', hygiene clo a' -> mc equiv a a' -> kbasicv system pg s i a' X)
     (fun pg s i a X => forall a', hygiene clo a' -> mc equiv a a' -> cbasicv system pg s i a' X)
     (fun pg s i a X => forall a', hygiene clo a' -> mc equiv a a' -> basicv system pg s i a' X)
     (fun pg s i a X => forall a', hygiene clo a' -> equiv a a' -> kbasic system pg s i a' X)
     (fun pg s i a X => forall a', hygiene clo a' -> equiv a a' -> cbasic system pg s i a' X)
     (fun pg s i a X => forall a', hygiene clo a' -> equiv a a' -> basic system pg s i a' X)
     (fun pg s i A a X => forall a', hygiene (permit clo) a' -> equiv a a' -> functional system pg s i A a' X)) as Hind;
try (intros;
     match goal with
     | Hequiv : mc equiv _ _ |- _ =>
       invertc_mc Hequiv
     end;
     intros; subst;
     match goal with
     | Hclo : hygiene clo _ |- _ =>
         so (hygiene_invert_auto _#5 Hclo) as HH; cbn in HH; destruct_all HH
     end;
     (* No way this should be necessary. *)
     first [apply interp_kunit
           |apply interp_kuniv
           |apply interp_kprod
           |apply interp_kfut_zero
           |apply interp_kfut
           |apply interp_ext
           |apply interp_cpair
           |apply interp_cpi1
           |apply interp_cpi2
           |apply interp_cunit
           |apply interp_capp
           |eapply interp_cty
           |apply interp_cnext_zero
           |apply interp_cnext
           |apply interp_cprev
           |apply interp_con
           |apply interp_pi
           |apply interp_intersect
           |apply interp_union
           |apply interp_sigma
           |apply interp_set
           |apply interp_iset
           |apply interp_fut_zero
           |apply interp_fut
           |apply interp_karrow
           |apply interp_tarrow
           |apply interp_prod
           |apply interp_void
           |apply interp_unit
           |apply interp_bool
           |apply interp_extt
           |apply interp_wt
           |apply interp_univ
           |apply interp_kind
           ];
     eauto using equiv_funct1, pginterp_equiv with equiv_compat;
     apply hygiene_auto; cbn;
     done).

(* karrow *)
{
intros pg s i k1 k2 K1 K2 _ IH1 _ IH2 aa Hhyg Hequiv.
invertc_mc Hequiv.
intros k1' Heqk1 k2' Heqk2 <-.
so (hygiene_invert_auto _#5 Hhyg) as H; cbn in H.
destruct H as (Hcl1 & Hcl2 & _).
fold (pi k1' k2').
apply interp_kkarrow; eauto.
}

(* ktarrow *)
{
intros pg s i a k A K _ IH1 _ IH2 aa Hhyg Hequiv.
invertc_mc Hequiv.
intros a' Ha k' Hk <-.
fold (tarrow a' k') in Hhyg |- *.
so (hygiene_invert_auto _#5 Hhyg) as H; cbn in H.
destruct H as (Hcla & Hclk & _).
apply interp_ktarrow; auto using map_hygiene, map_equiv.
}

(* krec *)
{
intros pg s i k K _ IH a' Hhyg Hequiv.
invertc_mc Hequiv.
intros k' Hk <-.
fold (rec k').
so (hygiene_invert_auto _#5 Hhyg) as H; cbn in H.
destruct H as (Hhyg' & _).
apply interp_krec; eauto.
apply IH; eauto using equiv_funct1 with equiv_compat.
apply hygiene_subst1; auto.
}

(* clam *)
{
intros pg s i k a K L A levK HeqL Hintk _ IH aa Hclaa Hequiv.
invertc_mc Hequiv.
intros k' Hk a' Ha <-.
fold (clam k' a').
so (hygiene_invert_auto _#5 Hclaa) as H; cbn in H.
destruct H as (Hclk' & Hcla' & _).
eapply interp_clam; eauto using map_equiv, map_hygiene.
  {
  eapply interp_kext_equiv; eauto.
  }
intros j Hj x.
apply IH; auto.
  {
  apply hygiene_subst1; auto.
  apply hygiene_auto; cbn; auto.
  }
apply equiv_subst; auto using map_equiv.
}

(* ctlam *)
{
intros pg s i a b k K A f B Hclb Hinta Hintk _ IH Hf aa Hcl Hequiv.
invertc_mc Hequiv.
intros a' Hequiva b' Hequivb k' Hequivk <-.
fold (ctlam a' b' k') in Hcl |- *.
so (hygiene_invert_auto _#5 Hcl) as H; cbn in H.
destruct H as (Hcla' & Hclb' & Hclk' & _).
eapply interp_ctlam; eauto using map_equiv, map_hygiene, interp_kext_equiv, interp_uext_equiv.
intros j m n Hmn.
apply IH; auto.
  {
  apply hygiene_subst1; auto using map_hygiene.
  so (urel_closed _#5 Hmn) as (Hclm, Hcln).
  destruct s; auto.
  }

  {
  apply equiv_subst; auto.
  }
}

(* ctapp *)
{
intros pg s i b m l A K B n p Hnp Hm _ IH aa Hcl Hequiv.
invertc_mc Hequiv.
intros b' Hequivb m' Hequivm <-.
fold (ctapp b' m') in Hcl |- *.
so (hygiene_invert_auto _#5 Hcl) as H; cbn in H.
destruct H as (Hclb' & Hclm' & _).
set (ex := extend stop l) in Hm.
assert (exists n' p',
          map_term ex m' = (if s then n' else p')
          /\ equiv n n'
          /\ equiv p p'
          /\ hygiene clo n'
          /\ hygiene clo p') as (n' & p' & Hm' & Hequivn & Hequivp & Hcln' & Hclp').
  {
  so (urel_closed _#5 Hnp) as (Hcln & Hclp).
  destruct s; [exists (map_term ex m'), p | exists n, (map_term ex m')]; do2 4 split; auto using equiv_refl, map_hygiene; try (rewrite <- Hm; apply map_equiv; auto).
  }
assert (rel A i n' p') as Hnp'.
  {
  eapply urel_equiv; eauto.
  }
replace (urelspinj A i n p Hnp) with (urelspinj A i n' p' Hnp').
2:{
  apply urelspinj_equal.
  so (urel_closed _#5 Hnp) as (_ & Hclp).
  eapply urel_equiv_2; eauto using equiv_symm.
  }
apply interp_ctapp; auto.
}

(* quotient *)
{
intros pg s i a b A B hs ht _ IH1 _ IH2 aa Hcl Hequiv.
invertc_mc Hequiv.
intros a' Hequiva b' Hequivb <-.
fold (quotient a' b') in *.
so (hygiene_invert_auto _#5 Hcl) as H; cbn in H.
destruct H as (Hcla' & Hclb' & _).
apply interp_quotient; auto.
apply IH2.
  {
  eapply hygiene_subst; eauto.
  intros j Hj.
  destruct j as [|[|j]]; simpsub.
    {
    apply hygiene_auto; cbn; split; auto.
    apply hygiene_var; auto.
    }

    {
    apply hygiene_auto; cbn; split; auto.
    apply hygiene_var; auto.
    }

    {
    apply hygiene_var; auto.
    }
  }

  {
  apply equiv_subst; auto.
  }
}

(* guard *)
{
intros pg s i a b A B _ IH1 _ IH2 aa Hcl Hequiv.
invertc_mc Hequiv.
intros a' Hequiva b' Hequivb <-.
fold (guard a' b') in *.
so (hygiene_invert_auto _#5 Hcl) as H; cbn in H.
destruct H as (Hcla' & Hclb' & _).
apply interp_guard; auto.
apply IH2.
  {
  apply hygiene_shift_permit; auto.
  }
apply equiv_subst; auto.
}

(* coguard *)
{
intros pg s i a b A B _ IH1 _ IH2 aa Hcl Hequiv.
invertc_mc Hequiv.
intros a' Hequiva b' Hequivb <-.
fold (guard a' b') in *.
so (hygiene_invert_auto _#5 Hcl) as H; cbn in H.
destruct H as (Hcla' & Hclb' & _).
apply interp_coguard; auto.
apply IH2.
  {
  apply hygiene_shift_permit; auto.
  }
apply equiv_subst; auto.
}

(* equal *)
{
intros pg s i a m n p q A Hmp Hnq _ IH c Hclc Hequiv.
invertc_mc Hequiv.
intros a' Ha m' Hm n' Hn <-.
fold (equal a' m' n') in Hclc |- *.
so (hygiene_invert_auto _#5 Hclc) as H; cbn in H.
destruct H as (Hcla' & Hclm' & Hcln' & _).
so (srel_closed _#6 Hmp) as (_ & Hclp).
so (srel_closed _#6 Hnq) as (_ & Hclq).
assert (srel s (den A) i m' p) as Hmp'.
  {
  refine (srel_equiv _#8 _#4 Hmp); auto using equiv_refl.
  }
assert (srel s (den A) i n' q) as Hnq'.
  {
  refine (srel_equiv _#8 _#4 Hnq); auto using equiv_refl, map_equiv.
  }
match goal with
| |- basicv _ _ _ _ _ ?X =>
    replace X with
    (iuequal stop s i A m' n' p q Hmp' Hnq')
end.
2:{
  apply iuequal_equal; auto.
  }
apply interp_equal; auto.
}

(* eqtype *)
{
intros pg s i a b R R' _ IH1 _ IH2 aa Hclaa Hequiv.
invertc_mc Hequiv.
intros a' Ha b' Hb <-.
fold (eqtype a' b').
so (hygiene_invert_auto _#5 Hclaa) as H; cbn in H.
destruct H as (Hcla' & Hclb' & _).
apply interp_eqtype; auto.
}

(* sequal *)
{
intros s i m n _ _ Hequivmn aa Hclaa Hequiv.
invertc_mc Hequiv.
intros m' Hequivm n' Hequivn <-.
fold (sequal m' n').
so (hygiene_invert_auto _#5 Hclaa) as H; cbn in H.
destruct H as (Hclm' & Hcln' & _).
apply interp_sequal; auto.
eauto using equiv_trans, equiv_symm.
}

(* subtype *)
{
intros pg s i a b R R' _ IH1 _ IH2 aa Hclaa Hequiv.
invertc_mc Hequiv.
intros a' Ha b' Hb <-.
fold (eqtype a' b').
so (hygiene_invert_auto _#5 Hclaa) as H; cbn in H.
destruct H as (Hcla' & Hclb' & _).
apply interp_subtype; auto.
}

(* all *)
{
intros pg s i lv k a gpg K A h Hlv _ IH1 Hle _ IH2 aa Hclaa Hequiv.
invertc_mc Hequiv.
intros lv' Hlv' k' Hk a' Ha <-.
fold (all lv' k' a') in *.
so (hygiene_invert_auto _#5 Hclaa) as H; cbn in H.
destruct H as (Hcllv' & Hclk' & Hcla' & _).
eapply interp_all; eauto using pginterp_equiv.
intros j Hj x.
apply IH2; auto.
  {
  apply hygiene_subst1; auto.
  apply hygiene_auto; cbn.
  do2 2 split; auto.
    {
    apply PreSpacify.fromsp_hygiene.
    }

    {
    apply hygiene_auto; cbn; auto.
    }
  }
apply equiv_subst; auto.
}

(* alltp *)
{
intros pg s i a A _ IH aa Hclaa Hequiv.
invertc_mc Hequiv.
intros a' Ha <-.
so (hygiene_invert_auto _#5 Hclaa) as H; cbn in H.
destruct H as (Hcla' & _).
eapply interp_alltp; eauto using pginterp_equiv.
intros j Hj x.
apply IH; auto.
  {
  apply hygiene_subst1; auto.
  apply hygiene_auto; cbn; auto.
  }
apply equiv_subst; auto.
}

(* exist *)
{
intros pg s i lv k a gpg K A h Hlv _ IH1 Hle _ IH2 aa Hclaa Hequiv.
invertc_mc Hequiv.
intros lv' Hlv' k' Hk a' Ha <-.
fold (exist lv' k' a') in *.
so (hygiene_invert_auto _#5 Hclaa) as H; cbn in H.
destruct H as (Hcllv' & Hclk' & Hcla' & _).
eapply interp_exist; eauto using pginterp_equiv.
intros j Hj x.
apply IH2; auto.
  {
  apply hygiene_subst1; auto.
  apply hygiene_auto; cbn.
  do2 2 split; auto.
    {
    apply PreSpacify.fromsp_hygiene.
    }

    {
    apply hygiene_auto; cbn; auto.
    }
  }
apply equiv_subst; auto.
}

(* mu *)
{
intros pg w s i a F Hw _ IH Hne Hmono Hrobust aa Hclaa Hequiv.
invertc_mc Hequiv.
intros a' Ha <-.
fold (mu a').
so (hygiene_invert_auto _#5 Hclaa) as H; cbn in H.
destruct H as (Hcla' & _).
apply interp_mu; eauto using equiv_robust.
intros X h.
eapply IH; eauto.
  {
  apply hygiene_subst1; auto.
  apply hygiene_auto; cbn.
  trivial.
  }
apply equiv_subst; auto.
}

(* ispositive *)
{
intros pg s i a _ aa Hclaa Hequiv.
invertc_mc Hequiv.
intros a' Ha <-.
fold (ispositive a').
replace (ispositive_urel stop i a) with (ispositive_urel stop i a').
2:{
  apply property_urel_extensionality; auto.
  intros _ _.
  split; eauto using equiv_positive, equiv_symm.
  }
apply interp_ispositive.
so (hygiene_invert_auto _#5 Hclaa) as H; cbn in H.
destruct H; auto.
}

(* isnegative *)
{
intros pg s i a _ aa Hclaa Hequiv.
invertc_mc Hequiv.
intros a' Ha <-.
fold (isnegative a').
replace (isnegative_urel stop i a) with (isnegative_urel stop i a').
2:{
  apply property_urel_extensionality; auto.
  intros _ _.
  split; eauto using equiv_negative, equiv_symm.
  }
apply interp_isnegative.
so (hygiene_invert_auto _#5 Hclaa) as H; cbn in H.
destruct H; auto.
}

(* rec *)
{
intros pg s i a A _ IH a' Hhyg Hequiv.
invertc_mc Hequiv.
intros k' Hk <-.
fold (rec k').
so (hygiene_invert_auto _#5 Hhyg) as H; cbn in H.
destruct H as (Hhyg' & _).
apply interp_rec; eauto.
apply IH; eauto using equiv_funct1 with equiv_compat.
apply hygiene_subst1; auto.
}

(* partial *)
{
intros pg s i a A _ IH aa Hclaa Hequiv.
invertc_mc Hequiv.
intros a' Ha.
fold (partial a').
intros <-.
so (hygiene_invert_auto _#5 Hclaa) as H; cbn in H.
destruct H as (Hcla' & _).
apply interp_partial; auto.
}

(* halts *)
{
intros pg s i m _ aa Hclaa Hequiv.
invertc_mc Hequiv.
intros m' Hm.
fold (halts m').
intros <-.
so (hygiene_invert_auto _#5 Hclaa) as H; cbn in H.
destruct H as (Hclm' & _).
replace (halts_urel stop i m) with (halts_urel stop i m').
2:{
  apply property_urel_extensionality; auto.
  intros j Hj.
  split; eauto using equiv_converges, equiv_symm.
  }
apply interp_halts; auto.
}

(* admiss *)
{
intros pg s i a A _ IH aa Hclaa Hequiv.
invertc_mc Hequiv.
intros a' Ha.
fold (admiss a').
intros <-.
so (hygiene_invert_auto _#5 Hclaa) as (Hcla' & _).
apply interp_admiss; auto.
}

(* uptype *)
{
intros pg s i a A _ IH aa Hclaa Hequiv.
invertc_mc Hequiv.
intros a' Ha.
fold (uptype a').
intros <-.
so (hygiene_invert_auto _#5 Hclaa) as (Hcla' & _).
apply interp_uptype; auto.
}

(* kbasic *)
{
intros pg s i k w K _ Hsteps Hl IH k' Hcl Hequiv.
so (kbasicv_value _#6 Hl) as Hvalue.
so (equiv_eval _#4 Hequiv (conj Hsteps Hvalue)) as (l' & (Hsteps' & _) & Hl').
eapply kinterp_eval; eauto using steps_hygiene.
}

(* cbasic *)
{
intros pg s i k w K _ Hsteps Hl IH k' Hcl Hequiv.
so (cbasicv_value _#6 Hl) as Hvalue.
so (equiv_eval _#4 Hequiv (conj Hsteps Hvalue)) as (l' & (Hsteps' & _) & Hl').
eapply cinterp_eval; eauto using steps_hygiene.
}

(* basic *)
{
intros pg s i k l K _ Hsteps Hl IH k' Hcl Hequiv.
so (basicv_value _#6 Hl) as Hvalue.
so (equiv_eval _#4 Hequiv (conj Hsteps Hvalue)) as (l' & (Hsteps' & _) & Hl').
eapply interp_eval; eauto using steps_hygiene.
}

(* functional *)
{
intros pg s i A b B Hclb Hcoarse Hb IH b' Hcl Hequiv.
eapply functional_i; eauto.
intros j m p Hj Hmp.
apply IH; auto.
  {
  apply hygiene_subst1; auto.
  so (urel_closed _#5 Hmp) as (Hclm & Hclp).
  destruct s; auto.
  }
apply equiv_subst; auto.
}

(* wrapup *)
{
do 6 (destruct Hind as (? & Hind)).
do2 2 split; intros; eauto.
}
Qed.


Lemma kbasic_equiv :
  forall pg s i a a' Q,
    hygiene clo a'
    -> equiv a a'
    -> kbasic system pg s i a Q
    -> kbasic system pg s i a' Q.
Proof.
exact (semantics_equiv andel).
Qed.


Lemma cbasic_equiv :
  forall pg s i a a' Q,
    hygiene clo a'
    -> equiv a a'
    -> cbasic system pg s i a Q
    -> cbasic system pg s i a' Q.
Proof.
exact (semantics_equiv anderl).
Qed.


Lemma basic_equiv :
  forall pg s i a a' R,
    hygiene clo a'
    -> equiv a a'
    -> basic system pg s i a R
    -> basic system pg s i a' R.
Proof.
exact (semantics_equiv anderr).
Qed.


End semantics.
