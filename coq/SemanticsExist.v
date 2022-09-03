
Require Import Axioms.
Require Import Tactics.
Require Import Sigma.
Require Import Equality.
Require Import Relation.
Require Import Syntax.
Require Import Ofe.
Require Import Uniform.
Require Import Spaces.
Require Import Dynamic.
Require Import Hygiene.
Require Import Equivalence.
Require Import Urelsp.
Require Import Intensional.
Require Import Ordinal.
Require Import Candidate.
Require Import Ceiling.
Require Import Truncate.
Require Import MapTerm.
Require Import Extend.
Require Import Model.
Require Import Page.
Require Import PreSpacify.
Require Import Standard.

Require Import Equivalences.
Require Import SemanticsPi.
Require Import ExtendTruncate.


Definition exist_action
  (w : ordinal) (K : qkind) (B : spcar K -> wurel w)
  : nat -> relation (wterm w)
  :=
  fun i m m' =>
    hygiene clo m
    /\ hygiene clo m'
    /\ (exists x n, rel (B x) i m n)
    /\ (exists x n, rel (B x) i n m')
    /\ forall j n n' (C : wurel stop),
         j <= i
         -> (forall (x : spcar (approx j K)),
               rel (arrow_urel stop j (extend_urel w stop (B (embed j K x))) C) j n n')
         -> rel C j (app n (map_term (extend w stop) m)) (app n' (map_term (extend w stop) m')).


Lemma exist_uniform :
  forall w K B, uniform _ (exist_action w K B).
Proof.
intros w K B.
do2 3 split.

(* closed *)
{
intros i' m n H.
decompose H; auto.
}

(* equiv *)
{
intros i' m m' n n' Hclm' Hcln' Hequivm Hequivn H.
destruct H as (_ & _ & (x & q' & Hmq) & (x' & q & Hqm) & Hact).
do2 4 split; auto.
  {
  exists x, q'.
  eapply urel_equiv; eauto using equiv_refl.
  eapply urel_closed_2; eauto.
  }

  {
  exists x', q.
  eapply urel_equiv; eauto using equiv_refl.
  eapply urel_closed_1; eauto.
  }
intros j p p' C Hj Hp.
so (Hact _#4 Hj Hp) as Hrel.
so (urel_closed _#5 (Hp (space_inhabitant (approx j K)))) as (Hclp & Hclp').
eapply urel_equiv; eauto.
  {
  apply hygiene_auto; cbn; auto using map_hygiene.
  }

  {
  apply hygiene_auto; cbn; auto using map_hygiene.
  }

  {
  apply equiv_app; auto using equiv_refl, map_equiv.
  }

  {
  apply equiv_app; auto using equiv_refl, map_equiv.
  }
}

(* zigzag *)
{
intros i' m n p q Hmn Hpn Hpq.
destruct Hmn as (Hclm & _ & Hm & _ & Hmn).
destruct Hpn as (_ & _ & _ & _ & Hpn).
destruct Hpq as (_ & Hclq & _ & Hq & Hpq).
do2 4 split; auto.
intros j r t C Hj Hrt.
so (Hmn _#4 Hj Hrt) as Hmnrt.
so (Hpn _#4 Hj Hrt) as Hpnrt.
so (Hpq _#4 Hj Hrt) as Hpqrt.
eapply urel_zigzag; eauto.
}

(* downward *)
{
intros i' m n H.
destruct H as (Hclm & Hcln & Hm & Hn & Hact).
do2 4 split; auto.
  {
  destruct Hm as (x & q & H).
  exists x, q.
  apply urel_downward; auto.
  }

  {
  destruct Hn as (x & q & H).
  exists x, q.
  apply urel_downward; auto.
  }
}
Qed.


Definition exist_urel w K B :=
  mk_urel (exist_action w K B) (exist_uniform _ _ _).


Lemma extend_exist_urel :
  forall v w K B,
    v <<= w
    -> w <<= stop
    -> @nonexpansive (space K) (wurel_ofe v) B
    -> extend_urel v w (exist_urel v K B)
       =
       exist_urel w K (fun x => extend_urel v w (B x)).
Proof.
intros v w K B Hvw Hwstop Hne.
apply urel_extensionality.
fextensionality 3.
intros i' m n.
cbn.
pextensionality.
  {
  intro H.
  destruct H as (Hclm & Hclmn & (y & r & Hmr) & (y' & t & Htn) & Hact).
  do2 4 split; eauto using map_hygiene_conv.
    {
    exists y, (map_term (extend v w) r).
    cbn.
    rewrite -> extend_term_cancel; auto.
    }

    {
    exists y', (map_term (extend v w) t).
    cbn.
    rewrite -> extend_term_cancel; auto.
    }
  intros j p q C Hj Hpq.
  apply (urel_zigzag _#4 (app q (map_term (extend v stop) r)) (app p (map_term (extend v stop) (map_term (extend w v) m)))).
    {
    refine (arrow_action_app _#9 (Hpq (proj j K y)) _).
    cbn.
    rewrite -> extend_term_cancel; auto.
    rewrite -> (extend_term_compose_up v stop w); eauto using le_ord_trans.
    rewrite -> extend_term_cancel; auto.
    refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hmr)).
    apply Hne.
    apply dist_symm.
    apply embed_proj.
    }

    {
    refine (arrow_action_app _#9 (Hpq (proj j K y)) _).
    cbn.
    rewrite -> !(extend_term_compose_up v stop w); eauto using le_ord_trans.
    rewrite -> !extend_term_cancel; auto.
    refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hmr)).
    apply Hne.
    apply dist_symm.
    apply embed_proj.
    }
  apply (urel_zigzag _#4 (app q (map_term (extend v stop) (map_term (extend w v) n))) (app p (map_term (extend v stop) t))).
    {
    exploit (Hact j p q C); auto.
    intro x.
    so (Hpq x) as H.
    rewrite <- extend_urel_compose_up in H; auto.
    }

    {
    refine (arrow_action_app _#9 (Hpq (proj j K y')) _).
    cbn.
    rewrite -> (extend_term_compose_up v stop w); eauto using le_ord_trans.
    rewrite -> (extend_term_compose_up v stop w); eauto using le_ord_trans.
    rewrite -> !extend_term_cancel; auto.
    refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Htn)).
    apply Hne.
    apply dist_symm.
    apply embed_proj.
    }

    {
    refine (arrow_action_app _#9 (Hpq (proj j K y')) _).
    cbn.
    rewrite -> (extend_term_compose_up v stop w); eauto using le_ord_trans.
    rewrite -> !extend_term_cancel; auto.
    refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Htn)).
    apply Hne.
    apply dist_symm.
    apply embed_proj.
    }
  }

  {
  intro H.
  destruct H as (Hclm & Hclmn & (y & r & Hmr) & (y' & t & Htn) & Hact).
  do2 4 split; auto using map_hygiene.
    {
    exists y, (map_term (extend w v) r).
    exact Hmr.
    }

    {
    exists y', (map_term (extend w v) t).
    exact Htn.
    }
  intros j p q C Hj Hpq.
  apply (urel_zigzag _#4 (app q (map_term (extend w stop) r)) (app p (map_term (extend w stop) m))).
    {
    refine (arrow_action_app _#9 (Hpq (proj j K y)) _).
    cbn.
    rewrite -> extend_term_cancel; eauto using le_ord_trans.
    rewrite -> extend_term_compose_down; eauto using le_ord_trans.
    cbn in Hmr.
    refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hmr)).
    apply Hne.
    apply dist_symm.
    apply embed_proj.
    }

    {
    refine (arrow_action_app _#9 (Hpq (proj j K y)) _).
    cbn.
    rewrite -> !extend_term_compose_down; eauto using le_ord_trans.
    cbn in Hmr.
    refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hmr)).
    apply Hne.
    apply dist_symm.
    apply embed_proj.
    }
  apply (urel_zigzag _#4 (app q (map_term (extend w stop) n)) (app p (map_term (extend w stop) t))).
    {
    exploit (Hact j p q C) as H; auto.
    intro x.
    rewrite <- extend_urel_compose_up; auto.
    }
    
    {
    refine (arrow_action_app _#9 (Hpq (proj j K y')) _).
    cbn.
    rewrite -> !extend_term_compose_down; eauto using le_ord_trans.
    cbn in Htn.
    refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Htn)).
    apply Hne.
    apply dist_symm.
    apply embed_proj.
    }

    {
    refine (arrow_action_app _#9 (Hpq (proj j K y')) _).
    cbn.
    rewrite -> extend_term_cancel; eauto using le_ord_trans.
    rewrite -> extend_term_compose_down; eauto using le_ord_trans.
    cbn in Htn.
    refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Htn)).
    apply Hne.
    apply dist_symm.
    apply embed_proj.
    }
  }
Qed.


Lemma ceiling_exist_urel :
  forall n w K (B : car (space K) -> car (wurel_ofe w)),
    @nonexpansive (space K) (wurel_ofe w) B
    -> ceiling (S n) (exist_urel w K B)
       =
       exist_urel w
         (approx n K)
         (fun x => ceiling (S n) (B (embed n K x))).
Proof.
intros n w K B Hne.
apply urel_extensionality.
fextensionality 3.
intros i m p.
cbn.
pextensionality.
  {
  intros (Hin & Hclm & Hclp & (y & c & Hmc) & (y' & d & Hdp) & Hact).
  do2 4 split; auto.
    {
    exists (proj n K y), c.
    split; auto.
    refine (rel_from_dist _#6 _ Hmc).
    apply Hne.
    apply dist_symm.
    apply (dist_downward_leq _ _ (S n)); auto.
    apply embed_proj.
    }

    {
    exists (proj n K y'), d.
    split; auto.
    refine (rel_from_dist _#6 _ Hdp).
    apply Hne.
    apply dist_symm.
    apply (dist_downward_leq _ _ (S n)); auto.
    apply embed_proj.
    }
  intros j q r C Hj Hqr.
  assert (j <= n) as Hjn by omega.
  exploit (Hact j q r C) as H; auto.
  intro x.
  so (Hqr (transport (eqsymm (approx_combine_le _#3 Hjn)) spcar x)) as Hqr'.
  rewrite <- ceiling_extend_urel in Hqr'.
  cbn in Hqr'.
  decompose Hqr'.
  intros l l' _ Hclq Hclr Hstepsq Hstepsr Hactqr.
  exists l, l'.
  do2 5 split; auto.
  intros j' t u Hj' Htu.
  exploit (Hactqr j' t u) as H; auto.
  split; [omega |].
  rewrite -> embed_combine_le'.
  exact Htu.
  }

  {
  intros (Hclm & Hclp & (y & c & Hmc) & (y' & d & Hdp) & Hact).
  so Hmc as (Hin & _).
  split; auto.
  do2 4 split; auto.
    {
    exists (embed n K y), c.
    destruct Hmc; auto.
    }

    {
    exists (embed n K y'), d.
    destruct Hdp; auto.
    }
  intros j q r C Hj Hqr.
  assert (j <= n) as Hjn by omega.
  exploit (Hact j q r C) as H; auto.
  intro x.
  so (Hqr (transport (approx_combine_le _#3 Hjn) spcar x)) as Hqr'.
  rewrite <- ceiling_extend_urel.
  cbn in Hqr'.
  decompose Hqr'.
  intros l l' _ Hclq Hclr Hstepsq Hstepsr Hactqr.
  exists l, l'.
  do2 5 split; auto.
  intros j' t u Hj' Htu.
  exploit (Hactqr j' t u) as H; auto.
  destruct Htu as (_ & Htu).
  rewrite <- embed_combine_le.
  exact Htu.
  }
Qed.


Definition iuexist w (K : qkind) (B : space K -n> wiurel_ofe w) : wiurel w
  :=
  iubase (exist_urel w K (fun x => den (pi1 B x))).


Lemma extend_iuexist :
  forall v w (h : v <<= w) K B,
    w <<= stop
    -> extend_iurel h (iuexist v K B)
       =
       iuexist w K (nearrow_compose (extend_iurel_ne h) B).
Proof.
intros v w h K B Hwstop.
unfold iuexist, extend_iurel, extend_iurel, iubase.
cbn.
f_equal.
  {
  apply extend_exist_urel; auto.
  exact (compose_ne_ne _#5 (pi2 den_ne) (pi2 B)).
  }

  {
  apply extend_meta_null.
  }
Qed.


Lemma iutruncate_iuexist :
  forall n w K (B : space K -n> wiurel_ofe w),
    iutruncate (S n) (iuexist w K B)
    =
    iuexist w (approx n K)
      (nearrow_compose2 
         (embed_ne n K) (iutruncate_ne (S n)) B).
Proof.
intros n w K B.
unfold iuexist, iutruncate, iubase.
f_equal.
  {
  apply ceiling_exist_urel.
  exact (compose_ne_ne _#5 (pi2 den_ne) (pi2 B)).
  }

  {
  apply meta_truncate_null.
  }
Qed.
