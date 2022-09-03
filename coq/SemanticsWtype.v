
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
Require Import Standard.
Require Import Equivalences.


Inductive wt_action_ind w (A : wurel w) (B : urelsp_car A -> wurel w)
  : nat -> wterm w -> wterm w -> Prop
  :=
| wt_action_ind_i :
    forall i m m' n n' p p' l l' (Hn : rel A i n n'),
      star step m (ppair n p)
      -> star step m' (ppair n' p')
      -> star step p (lam l)
      -> star step p' (lam l')
      -> (forall j q q',
            j <= i
            -> rel (B (urelspinj A i n n' Hn)) j q q'
            -> wt_action_ind w A B j (app p q) (app p' q'))
      -> wt_action_ind w A B i m m'
.


Definition wt_action (w : ordinal) (A : wurel w) (B : urelsp A -n> wurel_ofe w) 
  : nat -> relation (wterm w)
  :=
  fun i m m' =>
    hygiene clo m
    /\ hygiene clo m'
    /\ wt_action_ind w A (pi1 B) i m m'.


Lemma wt_action_ind_equiv :
  forall w A B i m m' n n',
    hygiene clo m'
    -> hygiene clo n'
    -> equiv m m'
    -> equiv n n'
    -> wt_action_ind w A B i m n
    -> wt_action_ind w A B i m' n'.
Proof.
intros w A B i m r m' r' Hclr Hclr' Hequiv Hequiv' H.
revert r r' Hclr Hclr' Hequiv Hequiv'.
induct H.
intros i m m' n n' p p' l l' Hn Hstepsm Hstepsm' Hl Hl' HH IH r r' Hclr Hclr' Hequiv Hequiv'.
so (equiv_eval _#4 Hequiv (conj Hstepsm value_ppair)) as (t & (Hstepsr & _) & Ht).
invertc_mc Ht.
intros a Hna b Hpb <-.
fold (ppair a b) in *.
so (equiv_eval _#4 Hequiv' (conj Hstepsm' value_ppair)) as (t' & (Hstepsr' & _) & Ht').
invertc_mc Ht'.
intros a' Hna' b' Hpb' <-.
fold (ppair a' b') in *.
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsr Hclr)) as H; cbn in H.
destruct H as (Hcla & Hclb & _).
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsr' Hclr')) as H; cbn in H.
destruct H as (Hcla' & Hclb' & _).
so (urel_equiv _#7 Hcla Hcla' Hna Hna' Hn) as Ha.
so (equiv_eval _#4 Hpb (conj Hl value_lam)) as (? & (Hu & _) & Hmc).
invertc_mc Hmc.
intros u Hequivu <-.
fold (lam u) in Hu.
so (equiv_eval _#4 Hpb' (conj Hl' value_lam)) as (? & (Hu' & _) & Hmc).
invertc_mc Hmc.
intros u' Hequivu' <-.
fold (lam u') in Hu'.
eapply (wt_action_ind_i _#10 u u' Ha); eauto.
intros j c c' Hj Hc.
so (urel_closed _#5 Hc) as (Hclc & Hclc').
apply (IH _ c c'); auto using equiv_refl, equiv_app;
try (apply hygiene_auto; cbn; auto).
force_exact Hc.
f_equal.
f_equal.
apply urelspinj_equal.
refine (urel_equiv_2 _#6 _ (equiv_symm _#3 Hna') Ha).
eapply urel_closed_2; eauto.
Qed.


Lemma wt_action_ind_zigzag :
  forall w A B i m n p q,
    wt_action_ind w A B i m n
    -> wt_action_ind w A B i p n
    -> wt_action_ind w A B i p q
    -> wt_action_ind w A B i m q.
Proof.
intros w A B i m n p q Hmn Hpn Hpq.
revert p q Hpn Hpq.
induct Hmn.
intros i m n m1 n1 m2 n2 m3 _ Hmn1 Hstepsm Hstepsn Hm3 _ _ IH.
intros p q Hpn Hpq.
invertc Hpn.
intros p1 n1' p2 n2' _ _ Hpn1 Hstepsp Hstepsn' _ _ Hactpn.
invertc Hpq.
intros p1' q1 p2' q2 _ q3 Hpq1 Hstepsp' Hstepsq _ Hq3 Hactpq.
so (determinism_eval _#4 (conj Hstepsn value_ppair) (conj Hstepsn' value_ppair)) as H.
injectionc H.
intros <- <-.
so (determinism_eval _#4 (conj Hstepsp value_ppair) (conj Hstepsp' value_ppair)) as H.
injectionc H.
intros <- <-.
so (urel_zigzag _#7 Hmn1 Hpn1 Hpq1) as Hmq1.
eapply (wt_action_ind_i _#10 m3 q3 Hmq1); eauto.
intros j r r' Hj Hr.
eapply (IH j r r'); eauto.
  {
  force_exact Hr.
  f_equal; f_equal.
  apply urelspinj_equal; auto.
  }

  {
  apply Hactpn; auto.
  force_exact Hr.
  f_equal; f_equal.
  apply urelspinj_equal; auto.
  }

  {
  apply Hactpq; auto.
  force_exact Hr.
  f_equal; f_equal.
  apply urelspinj_equal; auto.
  }
Qed.


Lemma wt_action_ind_downward :
  forall w A (B : urelsp A -n> wurel_ofe w) i j m m',
    j <= i
    -> wt_action_ind w A (pi1 B) i m m'
    -> wt_action_ind w A (pi1 B) j m m'.
Proof.
intros w A B i j m m' Hj Hact.
invertc Hact.
intros n n' p p' l l' Hn Hsteps Hsteps' Hl Hl' Hact.
eapply (wt_action_ind_i _#10 l l' (urel_downward_leq _#6 Hj Hn)); eauto.
intros j' q q' Hj' Hq.
apply Hact; [omega |].
assert (dist (S j') (urelspinj A i n n' Hn) (urelspinj A j n n' (urel_downward_leq _#6 Hj Hn))) as Hdist.
  {
  apply urelspinj_dist_diff; try omega.
  apply (urel_downward_leq _ _ _ i); auto; omega.
  }
rewrite -> (pi2 B _ _ _ Hdist j' (Nat.lt_succ_diag_r j')).
exact Hq.
Qed.


Lemma wt_uniform : 
  forall w A B, uniform _ (wt_action w A B).
Proof.
intros w A B.
do2 3 split.

(* closed *)
{
intros i m n H.
decompose H; auto.
}

(* equiv *)
{
intros i m m' n n' Hclm' Hcln' Hequivm Hequivn H.
decompose H.
intros _ _ Hact.
do2 2 split; auto.
eapply wt_action_ind_equiv; eauto.
}

(* zigzag *)
{
intros i m n p q Hmn Hpn Hpq.
decompose Hmn.
intros Hclm _ Hmn.
decompose Hpn.
intros _ _ Hpn.
decompose Hpq.
intros _ Hclq Hpq.
do2 2 split; auto.
eapply wt_action_ind_zigzag; eauto.
}

(* downward *)
{
intros i m n H.
decompose H.
intros Hclm Hclm' Hact.
do2 2 split; auto.
apply (wt_action_ind_downward _#3 (S i)); eauto.
}
Qed.


Definition wt_urel w A B :=
  mk_urel (wt_action w A B) (wt_uniform _ _ _).


Definition iuwt w A B :=
  (wt_urel w (den A) (nearrow_compose den_ne B),
   meta_pair (meta_iurel A)
     (meta_fn (den A)
        (nearrow_compose meta_iurel_ne B))).


Lemma den_iuwt :
  forall w A B,
    den (iuwt w A B) = wt_urel w (den A) (nearrow_compose den_ne B).
Proof.
reflexivity.
Qed.


Lemma iuwt_inj :
  forall w A A' B B',
    iuwt w A B = iuwt w A' B'
    -> eq_dep (wiurel w) (fun r => urelsp (den r) -n> wiurel_ofe w) A B A' B'.
Proof.
intros w A A' B B' Heq.
unfold iuwt in Heq.
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


Lemma ceiling_wt_action_ind :
  forall w n A B j m p,
    j < n
    -> wt_action_ind w A (pi1 B) j m p
       <->
       wt_action_ind w (ceiling n A) (pi1 (nearrow_compose2 (embed_ceiling_ne n A) (ceiling_ne n) B)) j m p.
Proof.
intros w n A B j m p Hjn.
split.
  {
  intros Hact.
  revert Hjn.
  induct Hact.
  intros j m p m1 p1 m2 p2 m3 p3 Hmp Hstepsm Hstepsp Hm3 Hp3 _ IH Hjn.
  eapply (wt_action_ind_i _ (ceiling n A) _#8 m3 p3 (conj Hjn Hmp)); eauto.
  intros j' q r Hj' Hqr.
  apply IH; auto; try omega.
  cbn in Hqr.
  destruct Hqr as (_ & Hqr).
  rewrite -> embed_ceiling_urelspinj in Hqr.
  exact Hqr.
  }

  {
  intros Hact.
  revert Hjn.
  induct Hact.
  intros i m p m1 p1 m2 p2 m3 p3 Hmp Hstepsm Hstepsp Hm3 Hp3 _ IH Hjn.
  so Hmp as (_ & Hmp').
  eapply (wt_action_ind_i _#10 m3 p3 Hmp'); eauto.
  intros j q r Hj Hqr.
  apply IH; auto; try omega.
  cbn.
  split; [omega |].
  destruct Hmp as (Hi' & Hmp).
  rewrite -> embed_ceiling_urelspinj.
  so (proof_irrelevance _ Hmp Hmp'); subst Hmp'.
  exact Hqr.
  }
Qed.


Lemma ceiling_wt :
  forall n w A B,
    ceiling (S n) (wt_urel w A B)
    =
    wt_urel w
      (ceiling (S n) A)
      (nearrow_compose2 (embed_ceiling_ne (S n) A) (ceiling_ne (S n)) B).
Proof.
intros n w A B.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros (Hjn & Hact).
  decompose Hact.
  intros Hclm Hclp Hact.
  do2 2 split; auto.
  clear Hclm Hclp.
  apply ceiling_wt_action_ind; auto.
  }

  {
  intros Hact.
  decompose Hact.
  intros Hclm Hclp Hact.
  assert (j < S n) as Hjn.
    {
    invertc Hact.
    intros ? ? _ _ _ _ Hn _ _ _ _ _.
    destruct Hn; auto.
    }
  split; auto.
  do2 2 split; auto.
  refine (ceiling_wt_action_ind _#7 Hjn ander _); auto.
  }
Qed.


Lemma iutruncate_iuwt :
  forall n w A B,
    iutruncate (S n) (iuwt w A B)
    =
    iuwt w 
      (iutruncate (S n) A)
      (nearrow_compose
         (nearrow_compose (iutruncate_ne (S n)) B)
         (embed_ceiling_ne (S n) (den A))).
Proof.
intros n w A B.
assert (S n > 0) as Hpos by omega.
unfold iuwt.
unfold iutruncate.
cbn [fst snd].
f_equal.
  {
  rewrite -> ceiling_wt.
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


Lemma extend_wt :
  forall v w (h : v <<= w) A B,
    extend_urel v w (wt_urel v A B)
    =
    wt_urel w 
      (extend_urel v w A)
      (nearrow_compose2 (deextend_urelsp_ne h A) (extend_urel_ne v w) B).
Proof.
intros v w h A B.
apply urel_extensionality.
fextensionality 3.
intros i m m'.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros Hclm Hclm' Hact.
  do2 2 split; eauto using map_hygiene_conv.
  remember (map_term (extend w v) m) as mm eqn:Heqm.
  remember (map_term (extend w v) m') as mm' eqn:Heqm'.
  revert m m' Heqm Heqm'.
  clear Hclm Hclm'.
  induct Hact.
  intros i mm mm' nn nn' pp pp' ll ll' Hnn Hstepsmm Hstepsmm' Hll Hll' _ IH.
  intros m m' -> ->.
  so (map_steps_form _#5 Hstepsmm) as (np & Heq & Hstepsm).
  so (map_steps_form _#5 Hstepsmm') as (np' & Heq' & Hstepsm').
  so (map_eq_ppair_invert _#6 (eqsymm Heq)) as (n & p & -> & <- & <-); clear Heq.
  so (map_eq_ppair_invert _#6 (eqsymm Heq')) as (n' & p' & -> & <- & <-); clear Heq'.
  so (map_steps_form _#5 Hll) as (? & Heq & Hl).
  so (map_steps_form _#5 Hll') as (? & Heq' & Hl').
  so (map_eq_lam_invert _#5 (eqsymm Heq)) as (l & -> & <-).
  so (map_eq_lam_invert _#5 (eqsymm Heq')) as (l' & -> & <-).
  eapply wt_action_ind_i; eauto.
Unshelve.
  2:{
    cbn.
    exact Hnn.
    }
  intros j q q' Hj Hact.
  eapply IH; eauto.
  2:{
    simpmap.
    reflexivity.
    }

  2:{
    simpmap.
    reflexivity.
    }
  cbn in Hact.
  force_exact Hact.
  do 2 f_equal.
  rewrite -> deextend_urelsp_urelspinj.
  reflexivity.
  }

  {
  intro H.
  decompose H.
  intros Hclm Hclm' Hact.
  do2 2 split; eauto using map_hygiene.
  clear Hclm Hclm'.
  induct Hact.
  intros i m m' n n' p p' l l' Hn Hsteps Hsteps' Hl Hl' _ IH.
  eapply wt_action_ind_i.
    {
    relquest.
      {
      eapply map_steps; eauto.
      }
    simpmap.
    reflexivity.
    }

    {
    relquest.
      {
      eapply map_steps; eauto.
      }
    simpmap.
    reflexivity.
    }

    {
    relquest.
      {
      eapply map_steps; eauto.
      }
    simpmap.
    reflexivity.
    }

    {
    relquest.
      {
      eapply map_steps; eauto.
      }
    simpmap.
    reflexivity.
    }
Unshelve.
  2:{
    cbn in Hn.
    exact Hn.
    }
  intros j q q' Hj Hq.
  exploit (IH j (map_term (extend v w) q) (map_term (extend v w) q') Hj) as H.
    {
    cbn.
    rewrite -> !extend_term_cancel; auto.
    rewrite -> deextend_urelsp_urelspinj.
    exact Hq.
    }
  simpmapin H.
  rewrite -> !extend_term_cancel in H; auto.
  }
Qed.


Lemma extend_iuwt :
  forall v w (h : v <<= w) A B,
    extend_iurel h (iuwt v A B)
    =
    iuwt w (extend_iurel h A)
      (nearrow_compose
         (nearrow_compose (extend_iurel_ne h) B)
         (deextend_urelsp_ne h (den A))).
Proof.
intros v w h A B.
unfold iuwt, extend_iurel.
cbn.
f_equal.
  {
  rewrite -> (extend_wt _ _ h).
  f_equal.
  apply nearrow_extensionality.
  auto.
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


Lemma wt_action_ppair :
  forall w A B i m m' n n' l l' (Hm : rel A i m m'),
    hygiene clo (ppair m n)
    -> hygiene clo (ppair m' n')
    -> star step n (lam l)
    -> star step n' (lam l')
    -> (forall j p p',
          j <= i
          -> rel (pi1 B (urelspinj A i m m' Hm)) j p p'
          -> rel (wt_urel w A B) j (app n p) (app n' p'))
    -> wt_action w A B i (ppair m n) (ppair m' n').
Proof.
intros w A B i m m' n n' l l' Hm Hcl Hcl' Hl Hl' Hact.
do2 2 split; auto.
eapply (wt_action_ind_i _#10 l l' Hm); eauto using star_refl.
intros j p p' Hj Hp.
apply Hact; auto.
Qed.
