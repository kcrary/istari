
Require Import Axioms.
Require Import Tactics.
Require Import Sigma.
Require Import Equality.
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
Require Import Model.
Require Import Truncate.
Require Import Standard.
Require Import System.
Require Import Semantics.
Require Import Extend.
Require Import SemanticsEqual.
Require Import Ceiling.
Require Import MapTerm.
Require Import Hygiene.
Require Import ExtendTruncate.
Require Import Equivalence.
Require Import SemanticsMu.
Require Import SemanticsPositive.

(* These two are needed for raise_robust.  The later could be dispensed with,
   with some work, by basing robust on step instead of reduce.
*)
Require Import ProperClosed.
Require Import ProperEquiv.


Section semantics.


Variable system : System.


Lemma interp_kext_fun :
  forall pg i m K K',
    interp_kext pg i m K
    -> interp_kext pg i m K'
    -> K = K'.
Proof.
intros pg i m K K' Hint Hint'.
destruct Hint as (Q & h & _ & Hsteps & _ & Heq).
destruct Hint' as (Q' & h' & _ & Hsteps' & _ & Heq').
so (determinism_eval _#4 (conj Hsteps value_ext) (conj Hsteps' value_ext)) as H.
injectionc H.
intro H.
injection (objin_inj _ _ _ H); clear H.
intros <-.
exact (eqtrans (eqsymm Heq) Heq').
Qed.


Lemma interp_uext_fun :
  forall pg i m R R',
    interp_uext pg i m R
    -> interp_uext pg i m R'
    -> R = R'.
Proof.
intros pg i m R R' Hint Hint'.
destruct Hint as (w & A & h & _ & Hsteps & _ & Heq).
destruct Hint' as (w' & A' & h' & _ & Hsteps' & _ & Heq').
so (determinism_eval _#4 (conj Hsteps value_ext) (conj Hsteps' value_ext)) as H.
injectionc H.
intro H.
injection (objin_inj _ _ _ H); clear H.
intros H <-.
injectionT H.
intros <-.
exact (eqtrans (eqsymm Heq) Heq').
Qed.


Lemma eval_bite_invert :
  forall object (m n p q : term object),
    eval (bite m n p) q
    -> (star step m btrue /\ star step n q)
       \/ (star step m bfalse /\ star step p q).
Proof.
intros object m n p q Heval.
destruct Heval as (Hsteps & Hval).
remember (bite m n p) as r eqn:Heq.
revert m Heq Hval.
induct Hsteps.

(* refl *)
{
intros q m -> Hval.
invert Hval.
intro H.
invert H.
}

(* step *)
{
intros x s q Hstep Hsteps IH m -> Hval.
invert Hstep.
  {
  intros m' Hstepm <-.
  so (IH m' (eq_refl _) Hval) as [(Hstepsm & Hstepsq) | (Hstepsm & Hstepsq)].
    {
    left.
    split; auto.
    eapply star_step; eauto.
    }

    {
    right.
    split; auto.
    eapply star_step; eauto.
    }
  }

  {
  intros <- <-.
  left.
  split; auto using star_refl.
  }

  {
  intros <- <-.
  right.
  split; auto using star_refl.
  }
}
Qed.


Definition exttin w X h := 
  @extt (obj stop) (objin (objsome (expair (qtype w) (iubase X)) h)).


Lemma subst_exttin :
  forall s w X h, subst s (exttin w X h) = exttin w X h.
Proof.
intros s w X h.
unfold exttin.
simpsub.
reflexivity.
Qed.


Hint Rewrite subst_exttin : subst.


Lemma subst_under_extt_hygiene :
  forall object a k (x y : object) s,
    hygiene clo (subst (compose (under k (dot (extt x) id)) s) a)
    -> hygiene clo (subst (compose (under k (dot (extt y) id)) s) a).
Proof.
intros object a k x y s Hcla.
so (hygiene_subst_invert _#4 Hcla) as H.
eapply hygiene_subst; eauto; clear H.
intros i Hi.
cbn in Hi.
rewrite -> project_compose in Hi |- *.
so (Nat.lt_trichotomy i k) as [Hik | [H | Hki]].
  {
  rewrite -> project_under_lt in Hi |- *; auto.
  }

  {
  subst i.
  rewrite -> project_under_eq.
  simpsub.
  apply hygiene_auto; cbn; auto.
  }

  {
  rewrite -> project_under_geq in Hi |- *; try omega.
  replace (i - k) with (S (i - k - 1)) in Hi |- * by omega.
  simpsub.
  simpsubin Hi.
  auto.
  }
Qed.


Lemma raise_robust_functional_ih :
  forall pg z i j A s b v w X Y (hv : v << stop) (hw : w << stop) F,
    v <<= cin pg
    -> w <<= cin pg
    -> extend_urel v stop X = extend_urel w stop Y
    -> (forall i s B,
          basic system pg z i (subst (compose (under (S j) (dot (exttin v X hv) id)) s) b) B
          -> basic system pg z i (subst (compose (under (S j) (dot (exttin w Y hw) id)) s) b) B)
    -> functional system pg z i A (subst (dot (var 0) (compose (under j (dot (exttin v X hv) id)) (compose s sh1))) b) F
    -> functional system pg z i A (subst (dot (var 0) (compose (under j (dot (exttin w Y hw) id)) (compose s sh1))) b) F.
Proof.
intros pg z i k A s b v w X Y hv hw F Hvpg Hwpg Heq IH Hfunct.
invert Hfunct.
intros Hhyg Hceil Hact.
apply functional_i; auto.
  {
  so (hygiene_subst_invert _#4 Hhyg) as Hhygi.
  eapply hygiene_subst; eauto.
  cbn.
  intros x Hx.
  destruct x as [| x].
    {
    simpsub.
    apply hygiene_var.
    split.
    }
  simpsub.
  simpsubin Hx.
  so (Nat.lt_trichotomy x k) as [Hxk | [H | Hkx]].
    {
    rewrite -> project_under_lt in Hx |- *; auto.
    }

    {
    subst x.
    rewrite -> project_under_eq.
    simpsub.
    apply hygiene_auto; cbn; auto.
    }

    {
    rewrite -> project_under_geq in Hx |- *; try omega.
    replace (x - k) with (S (x - k - 1)) in Hx |- * by omega.
    simpsub.
    simpsubin Hx.
    auto.
    }
  }
intros j m p Hj Hmp.
simpsub.
so (Hact _#3 Hj Hmp) as Hint.
simpsubin Hint.
rewrite -> split_dot.
change (varx (obj stop) 0) with (@var (obj stop) 0).
exploit (IH j (dot (if z then m else p) s) (pi1 F (urelspinj A j m p Hmp))) as H.
  {
  simpsub.
  auto.
  }
simpsubin H.
simpsub.
auto.
Qed.


Lemma raise_robust :
  forall pg s i a v w X Y (hv : v << stop) (hw : w << stop) A,
    v <<= cin pg
    -> w <<= cin pg
    -> extend_urel v stop X = extend_urel w stop Y
    -> robust 0 a
    -> basic system pg s i (subst1 (exttin v X hv) a) A
    -> basic system pg s i (subst1 (exttin w Y hw) a) A.
Proof.
intros pg z i a v w X Y hv hw A Hv Hw HeqXY Hrobust Hint.
assert (basic system pg z i (subst (compose (under 0 (dot (exttin v X hv) id)) id) a) A) as Hint'.
  {
  simpsub.
  exact Hint.
  }
renameover Hint' into Hint.
cut (basic system pg z i (subst (compose (under 0 (dot (exttin w Y hw) id)) id) a) A).
  {
  intro H; simpsubin H.
  exact H.
  }
set (j := 0) in Hrobust, Hint |- *.
set (s := id) in Hint at 2 |- * at 2.
clearbody j s.
revert i s A Hint.
induct Hrobust.

(* var *)
{
intros k i s A Hint.
simpsub.
simpsubin Hint.
rewrite -> project_under_eq in Hint |- *.
simpsub.
simpsubin Hint.
invert (basic_value_inv _#6 value_extt Hint).
intros u R hu Hu Heq <-.
so (objin_inj _ _ _ Heq) as Heq'.
clear Heq.
injectionc Heq'.
intros Heq ->.
injectionT Heq.
intros ->.
so (proof_irrelevance _ hv hu); subst hu.
clear Hint.
so (interp_extt system pg z i w (iubase Y) hw Hw) as H.
rewrite -> iutruncate_iubase in H |- *.
rewrite -> extend_iubase in H |- *.
rewrite <- ceiling_extend_urel in H |- *.
rewrite -> HeqXY.
apply interp_eval_refl.
exact H.
}

(* const *)
{
intros k a i s A Hint.
rewrite <- subst_compose in Hint |- *.
rewrite <- compose_assoc in Hint |- *.
rewrite <- compose_under in Hint |- *.
simpsub.
simpsubin Hint.
exact Hint.
}

(* prod *)
{
intros k a b _ IH1 _ IH2 i s R Hint.
simpsub.
simpsubin Hint.
invert (basic_value_inv _#6 value_prod Hint).
intros A B Ha Hb <-.
apply interp_eval_refl.
apply interp_prod; eauto.
}

(* pi *)
{
intros j a b _ IH1 _ IH2 i s R Hint.
simpsub.
simpsubin Hint.
invert (basic_value_inv _#6 value_pi Hint).
intros A B Ha Hb <-.
apply interp_eval_refl.
apply interp_pi; eauto.
exact (raise_robust_functional_ih _#14 Hv Hw HeqXY IH2 Hb).
}

(* sigma *)
{
intros j a b _ IH1 _ IH2 i s R Hint.
simpsub.
simpsubin Hint.
invert (basic_value_inv _#6 value_sigma Hint).
intros A B Ha Hb <-.
apply interp_eval_refl.
apply interp_sigma; eauto.
exact (raise_robust_functional_ih _#14 Hv Hw HeqXY IH2 Hb).
}

(* fut *)
{
intros k a _ IH1 i s R Hint.
simpsub.
simpsubin Hint.
invert (basic_value_inv _#6 value_fut Hint).
  {
  intros Hhyg <- <-.
  apply interp_eval_refl.
  apply interp_fut_zero; auto.
  rewrite -> subst_compose in Hhyg.
  so (hygiene_subst_invert _#4 Hhyg) as Hhyg'.
  so (hygiene_subst_under_invert _#5 Hhyg') as Hhyg''.
  eapply hygiene_subst; eauto.
  cbn.
  intros i Hi.
  destruct Hi as [(Hlt & Hi) | (Hi & H)].
    {
    rewrite -> project_compose.
    rewrite -> project_under_lt; auto.
    simpsub.
    exact Hi.
    }

    {
    rewrite -> project_compose.
    rewrite -> project_under_geq; auto.
    remember (i - k) as j in H |- *.
    destruct j as [| j].
      {
      simpsub.
      apply hygiene_auto; cbn.
      trivial.
      }
    simpsub.
    simpsubin H.
    cbn [Nat.add] in H.
    invert H.
    intro H'.
    force_exact H'.
    f_equal.
    f_equal.
    omega.
    }
  }

  {
  intros i' A Ha <- <-.
  apply interp_eval_refl.
  apply interp_fut; eauto.
  }
}

(* mu *)
{
intros j a _ IH i s R Hint.
simpsub.
simpsubin Hint.
invert (basic_value_inv _#6 value_mu Hint).
intros u F Hu Hact Hne Hmono Hrobust <-.
apply interp_eval_refl.
eapply interp_mu; eauto.
  {
  intros Z h.
  so (Hact Z h) as HintZ.
  exploit (IH i (dot (exttin u Z h) s) (extend_iurel (lt_ord_impl_le_ord u stop h) (F Z))) as H.
    {
    simpsub.
    simpsubin HintZ.
    auto.
    }
  simpsub.
  simpsubin H.
  auto.
  }

  {
  set (o1 := (objin (objsome (expair (qtype v) (iubase X)) hv))).
  set (o2 := (objin (objsome (expair (qtype w) (iubase Y)) hw))).
  set (f := fun x => match x with | Some y => y | None => o1 end).
  set (g := fun x => match x with | Some y => y | None => o2 end).
  replace
    (subst (dot (var 0) (compose (under j (dot (exttin v X hv) id)) (compose s sh1))) a)
    with
    (map_term f
       (subst
          (dot (var 0) (compose 
                          (under j (dot (extt None) id))
                          (compose (map_sub Some s) sh1)))
          (map_term Some a))) in Hrobust.
  2:{
    simpmap.
    rewrite -> map_sub_compose.
    rewrite -> map_term_compose.
    subst f.
    cbn.
    rewrite -> map_sub_id.
    rewrite -> map_term_id.
    auto.
    }
  so (map_robust_conv _#5 Hrobust) as Hrobust'.
  so (map_robust _#3 g _ Hrobust') as H.
  simpmapin H.
  rewrite -> map_sub_compose in H.
  rewrite -> map_term_compose in H.
  subst g.
  cbn.
  rewrite -> map_sub_id in H.
  rewrite -> map_term_id in H.
  auto.
  }
}

(* bite *)
{
intros k m a b _ IH1 _ IH2 i s R Hint.
simpsub.
simpsubin Hint.
invertc Hint.
intros c Hhyg Hsteps Hint.
so (basicv_value _#6 Hint) as Hval.
so (hygiene_invert_auto _#5 Hhyg) as H; cbn in H.
destruct H as (Hclm & Hcla & Hclb & _).
assert (hygiene clo (subst (compose (under k (dot (exttin w Y hw) id)) s) a)) as Hcla'.
  {
  eapply subst_under_extt_hygiene; eauto.
  }
assert (hygiene clo (subst (compose (under k (dot (exttin w Y hw) id)) s) b)) as Hclb'.
  {
  eapply subst_under_extt_hygiene; eauto.
  }
so (eval_bite_invert _#5 (conj Hsteps Hval)) as [(Hstepm & Hstepsa) | (Hstepm & Hstepsb)].
  {
  assert (basic system pg z i (subst (compose (under k (dot (exttin v X hv) id)) s) a) R) as Hintv.
    {
    eapply interp_eval; eauto.
    }
  so (IH1 _#3 Hintv) as Hintw.
  refine (basic_unstep _#7 _ _ Hintw).
    {
    apply hygiene_auto; cbn.
    do2 3 split; auto.
    rewrite <- compose_assoc in Hclm |- *.
    rewrite <- compose_under in Hclm |- *.
    simpsub.
    simpsubin Hclm.
    exact Hclm.
    }

    {
    rewrite <- compose_assoc in Hstepm |- *.
    rewrite <- compose_under in Hstepm |- *.
    simpsub.
    simpsubin Hstepm.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun Z => bite Z _ _)); eauto using step_bite1.
      }
    apply star_one.
    apply step_bite2.
    }
  }

  {
  assert (basic system pg z i (subst (compose (under k (dot (exttin v X hv) id)) s) b) R) as Hintv.
    {
    eapply interp_eval; eauto.
    }
  so (IH2 _#3 Hintv) as Hintw.
  refine (basic_unstep _#7 _ _ Hintw).
    {
    apply hygiene_auto; cbn.
    do2 3 split; auto.
    rewrite <- compose_assoc in Hclm |- *.
    rewrite <- compose_under in Hclm |- *.
    simpsub.
    simpsubin Hclm.
    exact Hclm.
    }

    {
    rewrite <- compose_assoc in Hstepm |- *.
    rewrite <- compose_under in Hstepm |- *.
    simpsub.
    simpsubin Hstepm.
    eapply star_trans.
      {
      apply (star_map' _ _ (fun Z => bite Z _ _)); eauto using step_bite1.
      }
    apply star_one.
    apply step_bite3.
    }
  }
}

(* weaken *)
{
intros k a _ IH i s A Hint.
simpsub.
simpsubin Hint.
rewrite <- compose_assoc in Hint |- *.
rewrite -> compose_sh_under_eq in Hint |- *.
simpsub.
simpsubin Hint.
exploit (IH i (compose (sh k) s) A) as H.
  {
  simpsub; auto.
  }
simpsubin H.
auto.
}

(* reduce *)
{
intros k a b Hab _ IH i s R Hint.
so (basic_closed _#6 Hint) as Hclas.
so (reduce_hygiene _#4 (reduce_subst _#4 Hab) Hclas) as Hclbs.
exploit (IH i s R) as H.
  {
  eapply basic_equiv; eauto.
  apply equiv_subst.
  apply reduce_equiv; auto.
  }
refine (basic_equiv _#7 _ _ H).
  {
  eapply subst_under_extt_hygiene; eauto.
  }

  {
  apply equiv_subst.
  apply equiv_symm.
  apply reduce_equiv; auto.
  }
}
Qed.


Lemma semantics_fun :
  (forall pg s i a X X',
     kbasic system pg s i a X
     -> kbasic system pg s i a X'
     -> X = X')
  /\
  (forall pg s i a X X',
     cbasic system pg s i a X
     -> cbasic system pg s i a X'
     -> X = X')
  /\
  (forall pg s i a X X',
     basic system pg s i a X
     -> basic system pg s i a X'
     -> X = X')
  /\
  (forall pg s i A a X X',
     functional system pg s i A a X
     -> functional system pg s i A a X'
     -> X = X').
Proof.
exploit
  (semantics_ind system
     (fun pg s i a X => forall X', kbasicv system pg s i a X' -> X = X')
     (fun pg s i a X => forall X', cbasicv system pg s i a X' -> X = X')
     (fun pg s i a X => forall X', basicv system pg s i a X' -> X = X')
     (fun pg s i a X => forall X', kbasic system pg s i a X' -> X = X')
     (fun pg s i a X => forall X', cbasic system pg s i a X' -> X = X')
     (fun pg s i a X => forall X', basic system pg s i a X' -> X = X')
     (fun pg s i A a X => forall X', functional system pg s i A a X' -> X = X')) as Hind;
try (intros;
     match goal with
     | H : kbasicv _ _ _ _ _ _ |- _ => invert H
     | H : cbasicv _ _ _ _ _ _ |- _ => invert H
     | H : basicv _ _ _ _ _ _ |- _ => invert H
     end;
     intros; subst; f_equal; eauto;
     done).

(* ktarrow *)
{
intros pg s i a k A K HA IH1 _ IH2 X HX.
invertc HX.
intros A' K' Ha Hk <-.
so (IH1 _ Ha) as Heq.
so (extend_iurel_inj _#5 Heq); subst A'.
so (IH2 _ Hk); subst K'.
reflexivity.
}

(* ext *)
{
intros pg s i Q h _ X HX.
invert HX.
intros Q' h' _ Heq <-.
so (f_equal objout Heq) as Heq'.
rewrite -> !objout_objin in Heq'.
injection Heq'.
intros ->.
reflexivity.
}

(* clam *)
{
intros pg s i k a K L A h HeqL Hk _ IH X HX.
invertc HX.
intros K' L' A' h' HeqL' Hk' Ha <-.
so (interp_kext_fun _#5 Hk Hk'); subst K'.
so (proof_irrelevance _ h h'); subst h'.
so (space_inhabitant (approx i K)) as x.
injection (IH i (le_refl _) _ _ (Ha i (le_refl _) x)).
intros _ HeqLs.
clear x.
so (eqtrans HeqL (eq_trans HeqLs (eqsymm HeqL'))); subst L'.
unfold stdc.
cbn.
f_equal.
rewrite -> std_arrow_is.
cbn.
apply nearrow_extensionality.
intro x.
cbn.
fold (std (S i) L).
fold (std (S i) K).
injection (IH i (le_refl _) _ _ (Ha i (le_refl _) (proj i K (std (S i) K x)))).
intros H.
injectionT H.
intros Heq.
setoid_rewrite <- std_idem at 1 2.
so (proj_eq_dist _#4 Heq) as Heq'.
setoid_rewrite -> proj_std in Heq'; auto.
setoid_rewrite -> embed_std in Heq'; auto.
rewrite -> std_idem in Heq'.
setoid_rewrite <- embed_std in Heq'; auto.
rewrite <- proj_std in Heq'; auto.
apply std_collapse.
eapply dist_trans.
  {
  apply std_nonexpansive.
  apply (pi2 A).
  apply dist_symm.
  apply embed_proj.
  }
eapply dist_trans.
  {
  exact Heq'.
  }
apply std_nonexpansive.
apply (pi2 A').
apply embed_proj.
}

(* capp *)
{
intros pg s i a b K L A B _ IH1 _ IH2 X HX.
invertc HX.
intros K' L' A' B' Ha Hb <-.
so (IH1 _ Ha) as Heq1.
injection Heq1.
intros <- <-.
so (expair_injection_2 _#5 Heq1).
subst A'.
so (expair_injection_2 _#5 (IH2 _ Hb)).
subst B'.
reflexivity.
}

(* ctlam *)
{
intros pg s i a b k K A f B _ Ha Hk _ IH Hf X HX.
invertc HX.
intros K' A' f' B' _ Ha' Hk' Hb Hf' <-.
so (interp_uext_fun _#5 Ha Ha'); subst A'.
so (interp_kext_fun _#5 Hk Hk'); subst K'.
f_equal.
apply nearrow_extensionality.
intros C.
so (urelsp_eta _ _ C) as (j & m & p & Hmp & ->).
so (cin_stop pg) as Hlstop.
set (l := cin pg) in Hlstop.
assert (rel (extend_urel l stop A) j (map_term (extend l stop) m) (map_term (extend l stop) p)) as Hmp'.
  {
  cbn.
  rewrite -> !extend_term_cancel; auto.
  }
so (Hf _ _ _ Hmp') as H.
rewrite -> (urelspinj_equal _#4 m _ p _ Hmp) in H.
2:{
  rewrite -> extend_term_cancel; auto.
  }
rewrite -> H; clear H.
so (Hf' _ _ _ Hmp') as H.
rewrite -> (urelspinj_equal _#4 m _ p _ Hmp) in H.
2:{
  rewrite -> extend_term_cancel; auto.
  }
rewrite -> H; clear H.
f_equal.
so (IH _#3 Hmp' _ (Hb _#3 Hmp')) as Heq'.
eapply expair_injection_2; eauto.
}

(* ctapp *)
{
intros pg s i b m l A K B n p Hnp Hm _ IH X HX.
invertc HX.
intros l' A' K' B' n' p' Hnp' Hm' Hb <-.
so (IH _ Hb) as Heq.
injection Heq.
intros <- H <-.
injectionT H.
intros <-.
injectionT Heq.
intros <-.
rewrite -> Hm' in Hm.
f_equal.
f_equal.
apply urelspinj_equal.
destruct s; subst; eapply urel_zigzag; eauto.
}

(* cpair *)
{
intros pg s i a b K L x y _ IH1 _ IH2 X HX.
invertc HX.
intros K' L' x' y' Ha Hb <-.
injection (IH1 _ Ha).
intros H <-.
injectionT H.
intros <-.
injection (IH2 _ Hb).
intros H <-.
injectionT H.
intros <-.
reflexivity.
}

(* cpi1 *)
{
intros pg s i a K L x _ IH X HX.
invertc HX.
intros K' L' x' Ha <-.
injection (IH _ Ha).
intros H <- <-.
injectionT H.
intros <-.
reflexivity.
}

(* cpi2 *)
{
intros pg s i a K L x _ IH X HX.
invertc HX.
intros K' L' x' Ha <-.
injection (IH _ Ha).
intros H <- <-.
injectionT H.
intros <-.
reflexivity.
}

(* cnext *)
{
intros pg s i a K x _ IH X HX.
invertc HX.
intros K' x' Ha <-.
so (IH _ Ha) as Heq.
injectionc Heq.
intros H <-.
injectionT H.
intros <-.
reflexivity.
}

(* cprev *)
{
intros pg s i a K x _ IH X HX.
invertc HX.
intros K' x' Ha <-.
so (IH _ Ha) as Heq.
injectionc Heq.
intros H <-.
injectionT H.
intros <-.
reflexivity.
}

(* cty *)
{
intros pg s i a R _ IH X HX.
invertc HX.
intros R' Ha <-.
so (IH _ Ha) as Heq.
so (extend_iurel_inj _#5 Heq); subst R'.
reflexivity.
}

(* con *)
{
intros pg s i lv a gpg R Hlv _ _ IH X HX.
invertc HX.
intros gpg' R' Hlv' _ Ha <-.
so (pginterp_fun _#3 Hlv Hlv'); subst gpg'.
so (IH _ Ha) as Heq.
injectionT Heq.
intros <-.
reflexivity.
}

(* pi *)
{
intros pg s i a b A B _ IH1 _ IH2 X HX.
invertc HX.
intros A' B' Ha Hb <-.
so (IH1 _ Ha); subst A'.
so (IH2 _ Hb); subst B'.
reflexivity.
}

(* intersect *)
{
intros pg s i a b A B _ IH1 _ IH2 X HX.
invertc HX.
intros A' B' Ha Hb <-.
so (IH1 _ Ha); subst A'.
so (IH2 _ Hb); subst B'.
reflexivity.
}

(* union *)
{
intros pg s i a b A B _ IH1 _ IH2 X HX.
invertc HX.
intros A' B' Ha Hb <-.
so (IH1 _ Ha); subst A'.
so (IH2 _ Hb); subst B'.
reflexivity.
}

(* sigma *)
{
intros pg s i a b A B _ IH1 _ IH2 X HX.
invertc HX.
intros A' B' Ha Hb <-.
so (IH1 _ Ha); subst A'.
so (IH2 _ Hb); subst B'.
reflexivity.
}

(* set *)
{
intros pg s i a b A B _ IH1 _ IH2 X HX.
invertc HX.
intros A' B' Ha Hb <-.
so (IH1 _ Ha); subst A'.
so (IH2 _ Hb); subst B'.
reflexivity.
}

(* iset *)
{
intros pg s i a b A B _ IH1 _ IH2 X HX.
invertc HX.
intros A' B' Ha Hb <-.
so (IH1 _ Ha); subst A'.
so (IH2 _ Hb); subst B'.
reflexivity.
}

(* quotient *)
{
intros pg s i a b A B hs ht _ IH1 _ IH2 X HX.
invertc HX.
intros A' B' hs' ht' Ha Hb <-.
so (IH1 _ Ha); subst A'.
so (IH2 _ Hb); subst B'.
so (proof_irrelevance _ hs hs'); subst hs'.
so (proof_irrelevance _ ht ht'); subst ht'.
reflexivity.
}

(* guard *)
{
intros pg s i a b A B _ IH1 _ IH2 X HX.
invertc HX.
intros A' B' Ha Hb <-.
so (IH1 _ Ha).
subst A'.
f_equal.
apply IH2; auto.
}

(* coguard *)
{
intros pg s i a b A B _ IH1 _ IH2 X HX.
invertc HX.
intros A' B' Ha Hb <-.
so (IH1 _ Ha).
subst A'.
f_equal.
apply IH2; auto.
}

(* wt *)
{
intros pg s i a b A B _ IH1 _ IH2 X HX.
invertc HX.
intros A' B' Ha Hb <-.
so (IH1 _ Ha); subst A'.
so (IH2 _ Hb); subst B'.
reflexivity.
}

(* equal *)
{
intros pg s i a m n p q A Hmp Hnq _ IH X HX.
invertc HX.
intros p' q' A' Hmp' Hnq' Ha' <-.
so (IH _ Ha'); subst A'.
apply iuequal_equal; auto.
}

(* all *)
{
intros pg s i lv k a gpg K A h Hlv _ IH1 _ _ IH2 X HX.
invertc HX.
intros gpg' K' A' h' Hlv' Hk _ Ha <-.
so (pginterp_fun _#3 Hlv Hlv'); subst gpg'.
so (IH1 _ Hk); subst K'.
so (proof_irrelevance _ h h'); subst h'.
f_equal.
rewrite -> std_arrow_is; cbn.
apply nearrow_extensionality.
intro x.
cbn.
change (std (S i) (qtype stop) (pi1 A (std (S i) K x))
        =
        std (S i) (qtype stop) (pi1 A' (std (S i) K x))).
rewrite -> std_type_is.
so (IH2 i (le_refl _) (proj i K x) _ (Ha i (le_refl _) (proj i K x))) as Heq.
etransitivity.
  {
  etransitivity.
  2:{ exact Heq. }
  symmetry.
  f_equal.
  f_equal.
  apply std_collapse.
  apply embed_proj.
  }

  {
  f_equal.
  f_equal.
  apply std_collapse.
  apply embed_proj.
  }
}

(* alltp *)
{
intros pg s i a A _ IH X HX.
invertc HX.
intros A' Ha <-.
f_equal.
apply nearrow_extensionality.
intro X.
exact (IH i (le_refl _) X _ (Ha i (le_refl _) X)).
}

(* exist *)
{
intros pg s i lv k a gpg K A h Hlv _ IH1 _ _ IH2 X HX.
invertc HX.
intros gpg' K' A' h' Hlv' Hk _ Ha <-.
so (pginterp_fun _#3 Hlv Hlv'); subst gpg'.
so (IH1 _ Hk); subst K'.
so (proof_irrelevance _ h h'); subst h'.
f_equal.
rewrite -> std_arrow_is; cbn.
apply nearrow_extensionality.
intro x.
cbn.
change (std (S i) (qtype stop) (pi1 A (std (S i) K x))
        =
        std (S i) (qtype stop) (pi1 A' (std (S i) K x))).
rewrite -> std_type_is.
so (IH2 i (le_refl _) (proj i K x) _ (Ha i (le_refl _) (proj i K x))) as Heq.
etransitivity.
  {
  etransitivity.
  2:{ exact Heq. }
  symmetry.
  f_equal.
  f_equal.
  apply std_collapse.
  apply embed_proj.
  }

  {
  f_equal.
  f_equal.
  apply std_collapse.
  apply embed_proj.
  }
}

(* extt *)
{
intros pg s i w R h Hw X HX.
invertc HX.
intros w' R' h' Hw' Heq <-.
so (objin_inj _ _ _ Heq) as Heq'.
injectionc Heq'; clear Heq.
intros Heq ->.
injectionT Heq.
intros ->.
so (proof_irrelevance _ h h'); subst h'.
reflexivity.
}

(* mu *)
{
intros pg v s i a F Hv _ IH Hne HmonoF Hrobust X HX.
invertc HX.
intros w G Hw Hact _ HmonoG _ <-.
assert (v << stop) as hv.
  {
  eapply le_lt_ord_trans; eauto.
  apply (le_lt_ord_trans _ top); auto using cin_top.
  apply succ_increase.
  }
assert (w << stop) as hw.
  {
  eapply le_lt_ord_trans; eauto.
  apply (le_lt_ord_trans _ top); auto using cin_top.
  apply succ_increase.
  }
so (le_lt_ord_dec v w) as [Hvw | Hlt].
  {
  assert (forall X,
            extend_urel v w (den (F X))
            =
            den (G (extend_urel v w X))) as Heq.
    {
    intro X.
    rewrite <- (den_extend_iurel _ _ Hvw).
    f_equal.
    so (Hact (extend_urel v w X) hw) as Hint.
    fold (exttin w (extend_urel v w X) hw) in Hint.
    exploit (IH X hv (extend_iurel (lt_ord_impl_le_ord _ _ hw) (G (extend_urel v w X)))) as Heq.
      {
      fold (exttin v X hv).
      eapply raise_robust; eauto.
      rewrite <- extend_urel_compose_up; eauto.
      }
    replace (lt_ord_impl_le_ord _ _ hv) with (le_ord_trans _#3 Hvw (lt_ord_impl_le_ord _ _ hw)) in Heq.
    2:{
      apply proof_irrelevance.
      }
    rewrite -> extend_iurel_compose in Heq.
    exact (extend_iurel_inj _#5 Heq).
    }
  rewrite -> (extend_urel_compose_up v w stop); auto.
  do 2 f_equal.
  rewrite -> extend_mu; auto.
  transitivity (mu_urel w (fun X => den (G (blur v w X)))).
    {
    f_equal.
    fextensionality 1.
    intro X.
    apply Heq.
    }
  apply (blur_vanish _ _ (fun X => den (G X))); auto.
  intro X.
  unfold blur.
  rewrite <- !Heq.
  rewrite <- (extend_urel_compose_up v w); auto.
  rewrite -> extend_urel_id; auto.
  }

  {
  rename v into u; rename w into v; rename u into w.
  rename Hv into Hu; rename Hw into Hv; rename Hu into Hw.
  rename hv into hu; rename hw into hv; rename hu into hw.
  rename F into H; rename G into F; rename H into G.
  rename HmonoF into HmonoH; rename HmonoG into HmonoF; rename HmonoH into HmonoG.
  so (lt_ord_impl_le_ord _ _ Hlt) as Hvw; clear Hlt.
  assert (forall X,
            extend_urel v w (den (F (extend_urel w v X)))
            =
            den (G (blur v w X))) as Heq.
    {
    intro X.
    rewrite <- (den_extend_iurel _ _ Hvw).
    f_equal.
    so (Hact (extend_urel w v X) hv) as Hint.
    fold (exttin v (extend_urel w v X) hv) in Hint.
    exploit (IH (blur v w X) hw (extend_iurel (lt_ord_impl_le_ord _ _ hv) (F (extend_urel w v X)))) as Heq.
      {
      fold (exttin w (blur v w X) hw).
      eapply raise_robust; eauto.
      rewrite -> (extend_urel_compose_up v w stop); auto.
      }
    replace (lt_ord_impl_le_ord _ _ hv) with (le_ord_trans _#3 Hvw (lt_ord_impl_le_ord _ _ hw)) in Heq.
    2:{
      apply proof_irrelevance.
      }
    rewrite -> extend_iurel_compose in Heq.
    symmetry.
    exact (extend_iurel_inj _#5 Heq).
    }
  rewrite -> (extend_urel_compose_up v w stop); auto.
  do 2 f_equal.
  rewrite -> extend_mu; auto.
  symmetry.
  transitivity (mu_urel w (fun X => den (G (blur v w X)))).
    {
    f_equal.
    fextensionality 1.
    auto.
    }
  apply (blur_vanish _ _ (fun X => den (G X))); auto.
  intro X.
  rewrite <- !Heq.
  unfold blur.
  rewrite <- (extend_urel_compose_up v w); auto.
  rewrite -> extend_urel_id; auto.
  }
}

(* univ *)
{
intros pg s i m gpg Hm _ _ X HX.
invertc HX.
intros gpg' Hm' _ _ <-.
so (pginterp_fun _#3 Hm Hm'); subst gpg'.
reflexivity.
}

(* kuniv *)
{
intros pg s i m gpg h Hm _ X HX.
invertc HX.
intros gpg' h' Hm' _ <-.
so (pginterp_fun _#3 Hm Hm'); subst gpg'.
so (proof_irrelevance _ h h'); subst h'.
reflexivity.
}

(* padmiss *)
{
intros pg s i a b A B _ IH1 _ IH2 X HX.
invertc HX.
intros A' B' Ha Hb <-.
so (IH1 _ Ha); subst A'.
so (IH2 _ Hb); subst B'.
reflexivity.
}

(* kbasic *)
{
intros pg s i k l K _ Hsteps Hl IH X HX.
invertc HX.
intros l' _ Hsteps' Hl'.
so (determinism_eval _#4 (conj Hsteps (kbasicv_value _#6 Hl)) (conj Hsteps' (kbasicv_value _#6 Hl'))).
subst l'.
apply IH; auto.
}

(* cbasic *)
{
intros pg s i c d Q _ Hsteps Hd IH Q' H.
invertc H.
intros d' _ Hsteps' Hd'.
so (determinism_eval _#4 (conj Hsteps (cbasicv_value _#6 Hd)) (conj Hsteps' (cbasicv_value _#6 Hd'))).
subst d'.
apply IH; auto.
}

(* basic *)
{
intros pg s i c d R _ Hsteps Hd IH R' H.
invertc H.
intros d' _ Hsteps' Hd'.
so (determinism_eval _#4 (conj Hsteps (basicv_value _#6 Hd)) (conj Hsteps' (basicv_value _#6 Hd'))).
subst d'.
eapply IH; eauto.
}

(* functional *)
{
intros pg s i A b B _ Hcoarse Hb IH B' H.
revert B Hcoarse Hb IH.
cases H.
intros pg s i A b B' _ _ Hb' B Hcoarse Hb IH.
apply nearrow_extensionality.
intros C.
so (urelsp_eta _ A C) as (j & m & p & Hmp & ->).
destruct (transport Hcoarse (fun R => rel R j m p) Hmp) as (Hj & _).
apply IH; auto.
  {
  omega.
  }
apply Hb'.
omega.
}

(* wrapup *)
{
do 6 (destruct Hind as (? & Hind)).
do2 3 split; intros; eauto.
}
Qed.


Lemma kbasic_fun :
  forall pg s i k K K',
    kbasic system pg s i k K
    -> kbasic system pg s i k K'
    -> K = K'.
Proof.
exact (semantics_fun andel).
Qed.


Lemma cbasic_fun :
  forall pg s i a Q Q',
    cbasic system pg s i a Q
    -> cbasic system pg s i a Q'
    -> Q = Q'.
Proof.
exact (semantics_fun anderl).
Qed.


Lemma basic_fun :
  forall pg s i a R R',
    basic system pg s i a R
    -> basic system pg s i a R'
    -> R = R'.
Proof.
exact (semantics_fun anderrl).
Qed.


Lemma functional_fun :
  forall pg s i A b B B',
    functional system pg s i A b B
    -> functional system pg s i A b B'
    -> B = B'.
Proof.
exact (semantics_fun anderrr).
Qed.


End semantics.
