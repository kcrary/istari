
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


Definition union_action
  (w : ordinal) (A : wurel w) (B : urelsp_car A -> wurel w)
  : nat -> relation (wterm w)
  :=
  fun i m m' =>
    (exists r r' (Hr : rel A i r r') n, rel (B (urelspinj A i r r' Hr)) i m n)
    /\ (exists r r' (Hr : rel A i r r') n, rel (B (urelspinj A i r r' Hr)) i n m')
    /\ forall j n n' (C : wurel stop),
         j <= i
         -> (forall p p' (Hp : rel A j p p'),
               rel (arrow_urel stop j (extend_urel w stop (B (urelspinj A j p p' Hp))) C) j n n')
         -> rel C j (app n (map_term (extend w stop) m)) (app n' (map_term (extend w stop) m')).


Lemma union_uniform :
  forall w A (B : urelsp A -n> wurel_ofe w), uniform _ (union_action w A (pi1 B)).
Proof.
intros w A B.
do2 3 split.

(* closed *)
{
intros i' m n H.
destruct H as (Hm & Hn & _).
split.
  {
  destruct Hm as (r & r' & Hr & m' & Hm).
  refine (urel_closed _#5 Hm andel).
  }

  {
  destruct Hn as (r & r' & Hr & n' & Hn).
  refine (urel_closed _#5 Hn ander).
  }
}

(* equiv *)
{
intros i' m m' n n' Hclm' Hcln' Hequivm Hequivn H.
destruct H as ((x & y & Hxy & r & Hmr) & (x' & y' & Hxy' & t & Htn) & Hact).
do2 2 split; eauto.
  {
  exists x, y, Hxy, r.
  eapply urel_equiv; eauto using equiv_refl.
  eapply urel_closed_2; eauto.
  }

  {
  exists x', y', Hxy', t.
  eapply urel_equiv; eauto using equiv_refl.
  eapply urel_closed_1; eauto.
  }
intros j p p' C Hj Hp.
so (urel_closed _#5 (Hp _ _ (urel_downward_leq _#6 Hj Hxy))) as (Hclp & Hclp').
so (Hact _#4 Hj Hp) as Hrel.
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
destruct Hmn as (Hm & _ & Hmn).
destruct Hpn as (_ & _ & Hpn).
destruct Hpq as (_ & Hq & Hpq).
do2 2 split; auto.
intros j r t C Hj Hrt.
so (Hmn _#4 Hj Hrt) as Hmnrt.
so (Hpn _#4 Hj Hrt) as Hpnrt.
so (Hpq _#4 Hj Hrt) as Hpqrt.
eapply urel_zigzag; eauto.
}

(* downward *)
{
intros i m n H.
destruct H as (Hm & Hn & Hact).
do2 2 split; auto.
  {
  destruct Hm as (x & y & Hxy & q & H).
  exists x, y, (urel_downward _#5 Hxy), q.
  refine (rel_from_dist _#6 _ (urel_downward _#5 H)).
  apply (pi2 B).
  apply dist_symm.
  apply urelspinj_dist.
  omega.
  }

  {
  destruct Hn as (x & y & Hxy & q & H).
  exists x, y, (urel_downward _#5 Hxy), q.
  refine (rel_from_dist _#6 _ (urel_downward _#5 H)).
  apply (pi2 B).
  apply dist_symm.
  apply urelspinj_dist.
  omega.
  }
}
Qed.


Definition union_urel w A (B : urelsp A -n> wurel_ofe w) :=
  mk_urel (union_action w A (pi1 B)) (union_uniform _ _ _).


Lemma extend_union_urel :
  forall v w (h : v <<= w) A B,
    w <<= stop
    -> extend_urel v w (union_urel v A B)
       =
       union_urel w 
         (extend_urel v w A)
         (nearrow_compose2 (deextend_urelsp_ne h A) (extend_urel_ne v w) B).
Proof.
intros v w h A B Hwstop.
apply urel_extensionality.
fextensionality 3.
intros i m n.
cbn.
pextensionality.
  {
  intro H.
  destruct H as ((x & y & Hxy & r & Hmr) & (x' & y' & Hxy' & t & Htn) & Hact).
  assert (rel (extend_urel v w A) i (map_term (extend v w) x) (map_term (extend v w) y)) as Hxyw.
    {
    cbn.
    rewrite -> !extend_term_cancel; auto.
    }
  assert (rel (extend_urel v w A) i (map_term (extend v w) x') (map_term (extend v w) y')) as Hxyw'.
    {
    cbn.
    rewrite -> !extend_term_cancel; auto.
    }
  do2 2 split.
    {
    exists (map_term (extend v w) x), (map_term (extend v w) y), Hxyw.
    exists (map_term (extend v w) r).
    cbn.
    rewrite -> extend_term_cancel; auto.
    rewrite -> deextend_urelsp_urelspinj.
    force_exact Hmr.
    f_equal.
    f_equal.
    apply urelspinj_equal.
    rewrite -> extend_term_cancel; auto.
    }

    {
    exists (map_term (extend v w) x'), (map_term (extend v w) y'), Hxyw'.
    exists (map_term (extend v w) t).
    cbn.
    rewrite -> extend_term_cancel; auto.
    rewrite -> deextend_urelsp_urelspinj.
    force_exact Htn.
    f_equal.
    f_equal.
    apply urelspinj_equal.
    rewrite -> extend_term_cancel; auto.
    }
  intros j p q C Hj Hpq.
  (* Can't do it directly, because going down to v and back up to w loses information. *)
  apply (urel_zigzag _#4 (app q (map_term (extend v stop) r)) (app p (map_term (extend v stop) (map_term (extend w v) m)))).
    {
    refine (arrow_action_app _#9 (Hpq _ _ (urel_downward_leq _#6 Hj Hxyw)) _).
    cbn.
    rewrite -> extend_term_cancel; auto.
    rewrite -> (extend_term_compose_up v stop w); eauto using le_ord_trans.
    rewrite -> extend_term_cancel; auto.
    rewrite -> deextend_urelsp_urelspinj.
    refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hmr)).
    apply (pi2 B).
    apply dist_symm.
    apply urelspinj_dist_diff; auto.
    rewrite -> extend_term_cancel; auto.
    eapply urel_downward_leq; eauto.
    }

    {
    refine (arrow_action_app _#9 (Hpq _ _ (urel_downward_leq _#6 Hj Hxyw)) _).
    cbn.
    rewrite -> !(extend_term_compose_up v stop w); eauto using le_ord_trans.
    rewrite -> !extend_term_cancel; auto.
    rewrite -> deextend_urelsp_urelspinj.
    refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hmr)).
    apply (pi2 B).
    apply dist_symm.
    apply urelspinj_dist_diff; auto.
    rewrite -> extend_term_cancel; auto.
    eapply urel_downward_leq; eauto.
    }
  apply (urel_zigzag _#4 (app q (map_term (extend v stop) (map_term (extend w v) n))) (app p (map_term (extend v stop) t))).
    {
    exploit (Hact j p q C); auto.
    intros a b Hab.
    assert (rel (extend_urel v w A) j (map_term (extend v w) a) (map_term (extend v w) b)) as Habw.
      {
      cbn.
      rewrite -> !extend_term_cancel; auto.
      }
    so (Hpq _ _ Habw) as H.
    rewrite <- extend_urel_compose_up in H; auto.
    rewrite -> deextend_urelsp_urelspinj in H.
    force_exact H.
    f_equal.
    f_equal.
    f_equal.
    f_equal.
    apply urelspinj_equal.
    rewrite -> extend_term_cancel; auto.
    }

    {
    refine (arrow_action_app _#9 (Hpq _ _ (urel_downward_leq _#6 Hj Hxyw')) _).
    cbn.
    rewrite -> (extend_term_compose_up v stop w); eauto using le_ord_trans.
    rewrite -> (extend_term_compose_up v stop w); eauto using le_ord_trans.
    rewrite -> !extend_term_cancel; auto.
    rewrite -> deextend_urelsp_urelspinj.
    refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Htn)).
    apply (pi2 B).
    apply dist_symm.
    apply urelspinj_dist_diff; auto.
    rewrite -> extend_term_cancel; auto.
    eapply urel_downward_leq; eauto.
    }

    {
    refine (arrow_action_app _#9 (Hpq _ _ (urel_downward_leq _#6 Hj Hxyw')) _).
    cbn.
    rewrite -> (extend_term_compose_up v stop w); eauto using le_ord_trans.
    rewrite -> !extend_term_cancel; auto.
    rewrite -> deextend_urelsp_urelspinj.
    refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Htn)).
    apply (pi2 B).
    apply dist_symm.
    apply urelspinj_dist_diff; auto.
    rewrite -> extend_term_cancel; auto.
    eapply urel_downward_leq; eauto.
    }
  }

  {
  intro H.
  destruct H as ((x & y & Hxy & r & Hmr) & (x' & y' & Hxy' & t & Htn) & Hact).
  do2 2 split.
    {
    exists (map_term (extend w v) x), (map_term (extend w v) y), Hxy, (map_term (extend w v) r).
    rewrite -> deextend_urelsp_urelspinj in Hmr.
    exact Hmr.
    }

    {
    exists (map_term (extend w v) x'), (map_term (extend w v) y'), Hxy', (map_term (extend w v) t).
    rewrite -> deextend_urelsp_urelspinj in Htn.
    exact Htn.
    }
  intros j p q C Hj Hpq.
  apply (urel_zigzag _#4 (app q (map_term (extend w stop) r)) (app p (map_term (extend w stop) m))).
    {
    refine (arrow_action_app _#9 (Hpq _ _ (urel_downward_leq _#6 Hj Hxy)) _).
    cbn.
    rewrite -> extend_term_cancel; eauto using le_ord_trans.
    rewrite -> extend_term_compose_down; eauto using le_ord_trans.
    rewrite -> deextend_urelsp_urelspinj in Hmr.
    cbn in Hmr.
    refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hmr)).
    apply (pi2 B).
    apply dist_symm.
    apply urelspinj_dist_diff; auto.
    eapply urel_downward_leq; eauto.
    }

    {
    refine (arrow_action_app _#9 (Hpq _ _ (urel_downward_leq _#6 Hj Hxy)) _).
    cbn.
    rewrite -> !extend_term_compose_down; eauto using le_ord_trans.
    rewrite -> deextend_urelsp_urelspinj in Hmr.
    cbn in Hmr.
    refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hmr)).
    apply (pi2 B).
    apply dist_symm.
    apply urelspinj_dist_diff; auto.
    eapply urel_downward_leq; eauto.
    }
  apply (urel_zigzag _#4 (app q (map_term (extend w stop) n)) (app p (map_term (extend w stop) t))).
    {
    exploit (Hact j p q C) as H; auto.
    intros a b Hab.
    rewrite <- extend_urel_compose_up; auto.
    rewrite -> deextend_urelsp_urelspinj.
    apply Hpq.
    }
    
    {
    refine (arrow_action_app _#9 (Hpq _ _ (urel_downward_leq _#6 Hj Hxy')) _).
    cbn.
    rewrite -> !extend_term_compose_down; eauto using le_ord_trans.
    rewrite -> deextend_urelsp_urelspinj in Htn.
    cbn in Htn.
    refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Htn)).
    apply (pi2 B).
    apply dist_symm.
    apply urelspinj_dist_diff; auto.
    eapply urel_downward_leq; eauto.
    }

    {
    refine (arrow_action_app _#9 (Hpq _ _ (urel_downward_leq _#6 Hj Hxy')) _).
    cbn.
    rewrite -> extend_term_cancel; eauto using le_ord_trans.
    rewrite -> extend_term_compose_down; eauto using le_ord_trans.
    rewrite -> deextend_urelsp_urelspinj in Htn.
    cbn in Htn.
    refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Htn)).
    apply (pi2 B).
    apply dist_symm.
    apply urelspinj_dist_diff; auto.
    eapply urel_downward_leq; eauto.
    }
  }
Qed.


Lemma ceiling_union :
  forall n w A B,
    ceiling (S n) (union_urel w A B)
    =
    union_urel w
      (ceiling (S n) A)
      (nearrow_compose2 (embed_ceiling_ne (S n) A) (ceiling_ne (S n)) B).
Proof.
intros n w A B.
apply urel_extensionality.
fextensionality 3.
intros i m p.
cbn.
pextensionality.
  {
  intros (Hin & Hm & Hn & Hact).
  do2 2 split; auto.
    {
    destruct Hm as (x & y & Hxy & r & Hmr).
    exists x, y, (conj Hin Hxy), r.
    split; auto.
    rewrite -> embed_ceiling_urelspinj.
    auto.
    }

    {
    destruct Hn as (x' & y' & Hxy' & t & Htn).
    exists x', y', (conj Hin Hxy'), t.
    split; auto.
    rewrite -> embed_ceiling_urelspinj.
    auto.
    }
  intros j q r C Hj Hqr.
  assert (j < S n) as Hjn by omega.
  exploit (Hact j q r C) as H; auto.
  intros x y Hxy.
  so (Hqr x y (conj Hjn Hxy)) as Hqr'.
  rewrite -> embed_ceiling_urelspinj in Hqr'.
  rewrite <- ceiling_extend_urel in Hqr'.
  (* There ought to be a nicer way to do this. *)
  cbn in Hqr'.
  decompose Hqr'.
  intros l l' _ Hclq Hclr Hstepsq Hstepsr Hactqr.
  exists l, l'.
  do2 5 split; auto.
  intros j' t u Hj' Htu.
  exploit (Hactqr j' t u) as H; auto.
  split; [omega |].
  auto.
  }

  {
  intros (Hm & Hn & Hact).
  so Hm as (_ & _ & (Hin & _) & _).
  split; auto.
  do2 2 split; auto.
    {
    destruct Hm as (x & y & (Hin' & Hxy) & r & Hmr).
    exists x, y, Hxy, r.
    destruct Hmr as (_ & Hmr); auto.
    rewrite -> embed_ceiling_urelspinj in Hmr.
    auto.
    }

    {
    destruct Hn as (x' & y' & (Hin' & Hxy') & t & Htn).
    exists x', y', Hxy', t.
    destruct Htn as (_ & Htn); auto.
    rewrite -> embed_ceiling_urelspinj in Htn.
    auto.
    }
  intros j q r C Hj Hqr.
  assert (j < S n) as Hjn by omega.
  exploit (Hact j q r C) as H; auto.
  intros x y (Hin' & Hxy).
  so (Hqr x y Hxy) as Hqr'.
  rewrite -> embed_ceiling_urelspinj.
  rewrite <- ceiling_extend_urel.
  cbn in Hqr'.
  decompose Hqr'.
  intros l l' _ Hclq Hclr Hstepsq Hstepsr Hactqr.
  exists l, l'.
  do2 5 split; auto.
  intros j' t u Hj' Htu.
  exploit (Hactqr j' t u) as H; auto.
  destruct Htu as (_ & Htu).
  exact Htu.
  }
Qed.


Definition iuunion (w : ordinal) (A : wiurel w) (B : urelsp (den A) -n> wiurel_ofe w) : wiurel w
  :=
  (union_urel w (den A) (nearrow_compose den_ne B),
   meta_pair (meta_iurel A) 
     (meta_fn (den A) 
      (nearrow_compose meta_iurel_ne B))).


Lemma extend_iuunion :
  forall v w (h : v <<= w) A B,
    w <<= stop
    -> extend_iurel h (iuunion v A B)
       =
       iuunion w (extend_iurel h A)
         (nearrow_compose
            (nearrow_compose (extend_iurel_ne h) B)
            (deextend_urelsp_ne h (den A))).
Proof.
intros v w h A B Hwstop.
unfold iuunion, extend_iurel.
cbn.
f_equal.
  {
  rewrite -> (extend_union_urel _ _ h); auto.
  f_equal.
  apply nearrow_extensionality; auto.
  }
unfold meta_iurel.
cbn.
rewrite -> !extend_meta_pair.
rewrite -> extend_meta_urel.
rewrite -> extend_meta_fn.
f_equal.
f_equal.
f_equal.
apply exT_extensionality_prop.
cbn.
fextensionality 1.
intro x.
rewrite -> extend_meta_iurel.
reflexivity.
Qed.


Lemma iutruncate_iuunion :
  forall n w A B,
    iutruncate (S n) (iuunion w A B)
    =
    iuunion w 
      (iutruncate (S n) A)
      (nearrow_compose
         (nearrow_compose (iutruncate_ne (S n)) B)
         (embed_ceiling_ne (S n) (den A))).
Proof.
intros n w A B.
assert (S n > 0) as Hpos by omega.
unfold iuunion.
unfold iutruncate.
unfold den.
cbn [fst snd].
f_equal.
  {
  rewrite -> ceiling_union.
  f_equal.
  apply nearrow_extensionality.
  auto.
  }

  {
  rewrite -> !meta_truncate_pair; auto.
  f_equal.
    {
    apply meta_truncate_iurel; auto.
    }
  rewrite -> meta_truncate_fn; auto.
  f_equal.
  apply nearrow_extensionality.
  intro C.
  cbn -[meta_truncate].
  apply meta_truncate_iurel; auto.
  }
Qed.


Lemma iuunion_inj :
  forall w A A' B B',
    iuunion w A B = iuunion w A' B'
    -> eq_dep (wiurel w) (fun r => urelsp (den r) -n> wiurel_ofe w) A B A' B'.
Proof.
intros w A A' B B' Heq.
unfold iuunion in Heq.
so (f_equal (fun z => snd z) Heq) as Heq'.
cbn in Heq'.
so (meta_pair_inj _#5 Heq') as (H3 & H4).
so (meta_iurel_inj _#3 H3); subst A'.
so (meta_fn_inj _#5 H4) as H5.
apply eq_impl_eq_dep_snd.
clear Heq Heq' H3 H4.
so (eq_dep_impl_eq_snd _#5 H5) as Heq.
apply nearrow_extensionality.
intro x.
so (f_equal (fun z => pi1 z x) Heq) as Heq'.
cbn in Heq'.
eapply meta_iurel_inj; eauto.
Qed.
