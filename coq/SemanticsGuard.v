
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
Require Import ExtendTruncate.
Require Import SemanticsProperty.



Local Ltac prove_hygiene :=
  repeat (first [ apply hygiene_shift_permit
                | apply hygiene_sumbool
                | apply hygiene_auto; cbn [row_rect nat_rect]; repeat2 split; auto
                ]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1;
  try (apply hygiene_var; cbn; auto; done).


(* We could define this using set types, but it is much less messy to avoid dependent types. *)

Lemma squash_downward :
  forall w (A : wurel w) i,
    (exists m p, rel A (S i) m p)
    -> (exists m p, rel A i m p).
Proof.
intros w A i H.
destruct H as (m & p & H).
exists m, p.
apply urel_downward; auto.
Qed.


Definition squash_urel
  (w : ordinal) (A : wurel w) (i : nat)
  :=
  property_urel (fun j => exists m p, rel A j m p) w i (squash_downward w A).


Lemma ceiling_squash :
  forall w A n i,
    ceiling (S n) (squash_urel w A i)
    =
    squash_urel w A (min i n).
Proof.
intros w A n i.
apply ceiling_property.
Qed.


Lemma ceiling_squash_inner :
  forall w A i j,
    j < i
    -> squash_urel w A j = squash_urel w (ceiling i A) j.
Proof.
intros w A i j Hji.
unfold squash_urel.
apply property_urel_extensionality; auto.
intros k Hk.
split.
  {
  intros (m & p & H).
  exists m, p.
  split; auto.
  omega.
  }

  {
  intros (m & p & H).
  exists m, p.
  destruct H.
  auto.
  }
Qed.


Lemma ceiling_squash_both :
  forall w A n i,
    n <= i
    -> squash_urel w (ceiling (S n) A) n
       =
       ceiling (S n) (squash_urel w A i).
Proof.
intros w A n i Hle.
rewrite -> ceiling_squash.
rewrite -> Nat.min_r; auto.
symmetry.
apply ceiling_squash_inner.
omega.
Qed.


Definition embed_ceiling_squash_ne w (n i : nat) (A : wurel w) (h : n <= i) :
  urelsp (squash_urel w (ceiling (S n) A) n) -n> urelsp (squash_urel w A i)
  :=
  nearrow_compose
    (embed_ceiling_ne (S n) (squash_urel w A i))
    (transport_ne (ceiling_squash_both w A n i h) urelsp).


Lemma extend_squash :
  forall v w A i,
    v <<= w
    -> extend_urel v w (squash_urel v A i)
      =
      squash_urel w (extend_urel v w A) i.
Proof.
intros v w A i Hle.
unfold squash_urel.
rewrite -> extend_property; auto.
apply urel_extensionality.
cbn.
f_equal.
fextensionality 1.
intro j.
pextensionality.
  {
  intros (m & p & H).
  exists (map_term (extend v w) m).
  exists (map_term (extend v w) p).
  rewrite -> !extend_term_cancel; auto.
  }

  {
  intros (m & p & H).
  exists (map_term (extend w v) m).
  exists (map_term (extend w v) p).
  auto.
  }
Qed.


Lemma squash_intro :
  forall w (A : wurel w) i j m p,
    j <= i
    -> rel A j m p
    -> rel (squash_urel w A i) j triv triv.
Proof.
intros w A i j m p Hj Hmp.
do2 5 split; eauto using star_refl; try prove_hygiene.
Qed.


Definition guard_action
  (w : ordinal) i (A : wurel w) (B : urelsp_car (squash_urel w A i) -> wurel w)
  : nat -> relation (wterm w)
  :=
  fun i' m n =>
    exists (Hi' : i' <= i),
      hygiene clo m
      /\ hygiene clo n
      /\ forall j p q (Hj : j <= i') (Hrel : rel A j p q),
            rel (B (urelspinj (squash_urel w A i) j triv triv (squash_intro _#6 (le_trans _#3 Hj Hi') Hrel))) j m n.


Lemma guard_uniform :
  forall w i A B, uniform _ (guard_action w i A B).
Proof.
intros w i A B.
do2 3 split.

(* closed *)
{
intros i' m n H.
decompose H; auto.
}

(* equiv *)
{
intros i' m m' n n' Hclm' Hcln' Hm Hn H.
decompose H.
intros Hi' Hclm Hcln Hact.
exists Hi'.
do2 2 split; auto.
intros j p q Hj Hpq.
so (Hact _#3 Hj Hpq) as H.
eapply urel_equiv; eauto.
}

(* zigzag *)
{
intros i' m n p q Hmn Hpn Hpq.
destruct Hmn as (Hi' & Hclm & _ & Hmn).
destruct Hpn as (H & _ & _ & Hpn).
so (proof_irrelevance _ Hi' H); subst H.
destruct Hpq as (H & _ & Hclq & Hpq).
so (proof_irrelevance _ Hi' H); subst H.
exists Hi'.
do2 2 split; auto.
intros j r t Hj Hrt.
so (Hmn _#3 Hj Hrt) as H1.
so (Hpn _#3 Hj Hrt) as H2.
so (Hpq _#3 Hj Hrt) as H3.
eapply urel_zigzag; eauto.
}

(* downward *)
{
intros i' m n Hmn.
decompose Hmn.
intros Hi' Hclm Hcln Hact.
assert (i' <= i) as Hle by omega.
exists Hle.
do2 2 split; eauto.
intros j p q Hj Hpq.
assert (j <= S i') as Hj' by omega.
so (Hact _#3 Hj' Hpq) as H.
force_exact H; clear H.
f_equal.
f_equal.
apply urelspinj_equal.
eapply squash_intro; eauto.
omega.
}
Qed.


Definition guard_urel w i A B :=
  mk_urel (guard_action w i A B) (guard_uniform _ _ _ _).


Lemma ceiling_guard :
  forall n w i (A : wurel w) (B : car (urelsp (squash_urel w A i)) -> car (wurel_ofe w)) (h : n <= i),
    nonexpansive B
    -> ceiling (S n) (guard_urel w i A B)
       =
       guard_urel w n (ceiling (S n) A)
         (fun C => ceiling (S n) (B (embed_ceiling (S n) (squash_urel w A i)
                                       (transport (ceiling_squash_both w A n i h) urelsp_car C)))).
Proof.
intros n w i A B h Hne.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros (Hj_n & H).
  decompose H.
  intros Hji Hclm Hclp Hact.
  assert (j <= n) as Hjn by omega.
  exists Hjn.
  do2 2 split; auto.
  intros k q r Hk Hqr.
  destruct Hqr as (Hk_n & Hqr).
  cbn.
  split; [omega |].
  so (Hact k q r Hk Hqr) as Hmp.
  force_exact Hmp.
  f_equal.
  f_equal.
  erewrite -> transport_urelspinj.
Unshelve.
  2:{
    exact (conj Hk_n (squash_intro _#6 (le_trans _#3 Hk Hji) Hqr)).
    }
  rewrite -> embed_ceiling_urelspinj.
  reflexivity.
  }

  {
  intros H.
  decompose H.
  intros Hjn Hclm Hclp Hact.
  split; [omega |].
  assert (j <= i) as Hji by omega.
  exists Hji.
  do2 2 split; auto.
  intros k q r Hk Hqr.
  assert (k < S n) as Hk_n by omega.
  so (Hact k q r Hk (conj Hk_n Hqr)) as Hmp.
  destruct Hmp as (_ & Hmp).
  force_exact Hmp.
  f_equal.
  f_equal.
  erewrite -> transport_urelspinj.
Unshelve.
  2:{
    exact (conj Hk_n (squash_intro _#6 (le_trans _#3 Hk Hji) Hqr)).
    }
  rewrite -> embed_ceiling_urelspinj.
  reflexivity.
  }
Qed.


Lemma extend_guard :
  forall v w (h : v <<= w) i A B,
    extend_urel v w (guard_urel v i A B)
    =
    guard_urel w i (extend_urel v w A)
      (fun C => extend_urel v w 
                  (B (deextend_urelsp h (squash_urel v A i)
                        (transport (eqsymm (extend_squash v w A i h)) urelsp_car C)))).
Proof.
intros v w h i A B.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros Hj Hclm Hcln Hact.
  exists Hj.
  do2 2 split; eauto using map_hygiene_conv.
  intros k n q Hk Hnq.
  so (Hact _#3 Hk Hnq) as H.
  cbn.
  force_exact H; clear H.
  f_equal.
  f_equal.
  assert (rel (extend_urel v w (squash_urel v A i)) k triv triv) as Htriv.
    {
    eapply squash_intro; try omega.
    exact Hnq.
    }
  rewrite -> (transport_urelspinj _#3 (eqsymm (extend_squash v w A i h)) _#4 Htriv).
  rewrite -> deextend_urelsp_urelspinj.
  apply urelspinj_equal.
  exact Htriv.
  }

  {
  intro H.
  decompose H.
  intros Hj Hclm Hcln Hact.
  exists Hj.
  do2 2 split; eauto using map_hygiene.
  intros k n q Hk Hnq.
  assert (rel (extend_urel v w A) k (map_term (extend v w) n) (map_term (extend v w) q)) as Hnq'.
    {
    cbn.
    rewrite -> !extend_term_cancel; auto.
    }
  so (Hact k (map_term (extend v w) n) (map_term (extend v w) q) Hk Hnq') as H.
  cbn in H.
  force_exact H; clear H.
  f_equal.
  f_equal.
  assert (rel (extend_urel v w (squash_urel v A i)) k triv triv) as Htriv.
    {
    eapply squash_intro; try omega.
    exact Hnq.
    }
  rewrite -> (transport_urelspinj _#3 (eqsymm (extend_squash v w A i h)) _#4 Htriv).
  rewrite -> deextend_urelsp_urelspinj.
  apply urelspinj_equal.
  exact Htriv.
  }
Qed.


Lemma maximum_element :
  forall (P : nat -> Prop),
    (exists i, forall k, P k -> k < i)
    -> (forall i, ~ P i) \/ (exists i, P i /\ (forall j, P j -> j <= i)).
Proof.
intros P (i & Hi).
revert Hi.
induct i.

(* 0 *)
{
intro Hi.
left.
intros j Hj.
so (Hi j Hj).
omega.
}

(* S *)
{
intros i IH Hi.
so (excluded_middle (P i)) as [Hyes | Hno].  (* EXCLUDED MIDDLE *)
  {
  right.
  exists i.
  split; auto.
  intros j Hj.
  so (Hi j Hj).
  omega.
  }

  {
  apply IH.
  intros k Hk.
  so (eq_nat_dec i k) as [Heq | Hneq].
    {
    subst k.
    contradiction.
    }

    {
    so (Hi k Hk) as H.
    omega.
    }
  }
}
Qed.


Lemma unguard_prop :
  forall (T : ofe) w (A : wurel w) i (B : urelsp (squash_urel w A i) -n> T) (x : car T),
    exists (y : car T),
      forall j m p (Hj : j <= i) (Hmp : rel A j m p),
        dist (S j) y (pi1 B (urelspinj (squash_urel w A i) j triv triv (squash_intro _#6 Hj Hmp))).
Proof.
intros T w A i B x.
exploit (maximum_element (fun j => j <= i /\ exists m p, rel A j m p)) as H.
  {
  exists (S i).
  intros k (H & _).
  omega.
  }
destruct H as [Hnone | Hsome].
  {
  exists x.
  intros j m p Hj Hmp.
  exfalso.
  refine (Hnone j _).
  eauto.
  }

  {
  destruct Hsome as (j & (Hji & m & p & Hmp) & Hmax).
  exists (pi1 B (urelspinj (squash_urel w A i) j triv triv (squash_intro _#6 Hji Hmp))).
  intros k n q Hk Hnq.
  exploit (Hmax k) as Hkj; eauto.
  apply (pi2 B).
  apply dist_symm.
  apply urelspinj_dist; auto.
  }
Qed.


Lemma unguard_prop_unique :
  forall w (A : wurel w) i (B : urelsp (squash_urel w A i) -n> wiurel_ofe w),
    exists! (x : car (wiurel_ofe w)),
      (forall j, 
         (forall k m p, k <= i -> rel A k m p -> k < j)
         -> x = iutruncate j x)
      /\
      (forall j m p (Hj : j <= i) (Hmp : rel A j m p),
         dist (S j) x (pi1 B (urelspinj (squash_urel w A i) j triv triv (squash_intro _#6 Hj Hmp)))).
Proof.
intros w A i B.
exploit (maximum_element (fun j => j <= i /\ exists m p, rel A j m p)) as H.
  {
  exists (S i).
  intros k (H & _).
  omega.
  }
destruct H as [Hnone | Hsome].
  {
  exists (iubase empty_urel).
  split.
    {
    split.
      {
      intros j Hj.
      rewrite -> iutruncate_iubase.
      rewrite -> ceiling_empty_urel.
      reflexivity.
      }

      {
      intros j m p Hj Hmp.
      exfalso.
      refine (Hnone j _).
      eauto.
      }
    }

    {
    intros y (Hy & _).
    exploit (Hy 0) as Heq.
      {
      intros k m p Hki Hmp.
      exfalso.
      refine (Hnone 0 _).
      split; [omega |].
      exists m, p.
      apply (urel_downward_leq _#3 k); auto.
      omega.
      }

      {
      rewrite -> Heq.
      symmetry.
      apply iutruncate_zero.
      }
    }
  }

  {
  destruct Hsome as (j & (Hji & m & p & Hmp) & Hbound).
  exists (iutruncate (S j) (pi1 B (urelspinj (squash_urel w A i) j triv triv (squash_intro _#6 Hji Hmp)))).
  split.
    {
    split.
      {
      intros k Hk.
      rewrite -> iutruncate_combine.
      so (Hk j m p Hji Hmp) as Hjk.
      rewrite -> Nat.min_r; auto.
      }

      {
      intros k n q Hk Hnq.
      exploit (Hbound k) as Hkj; eauto.
      eapply dist_trans.
        {
        apply (dist_downward_leq _ _ (S j)); [omega |].
        apply iutruncate_near.
        }
        
        {
        apply (pi2 B).
        apply dist_symm.
        apply urelspinj_dist; auto.
        }
      }
    }

    {
    intros y (Htrunc & Hdist).
    exploit (Htrunc (S j)) as Heq.
      {
      intros k n q Hki Hnq.
      cut (k <= j); [omega |].
      apply Hbound; eauto.
      }
    rewrite -> Heq.
    apply iutruncate_collapse.
    apply dist_symm.
    apply Hdist.
    }
  }
Qed.


Lemma unguard :
  forall w (A : wurel w) i (B : urelsp (squash_urel w A i) -n> wiurel_ofe w),
    existsT (x : car (wiurel_ofe w)),
      (forall j, 
         (forall k m p, k <= i -> rel A k m p -> k < j)
         -> x = iutruncate j x)
      /\
      (forall j m p (Hj : j <= i) (Hmp : rel A j m p),
         dist (S j) x (pi1 B (urelspinj (squash_urel w A i) j triv triv (squash_intro _#6 Hj Hmp)))).
Proof.
intros w A i B.
exact (description _ _ (unguard_prop_unique w A i B)).
Qed.


Lemma iutruncate_unguard :
  forall n w i A B (h : n <= i),
    iutruncate (S n) (pi1 (unguard w A i B))
    =
    pi1 (unguard w (ceiling (S n) A) n
           (nearrow_compose 
              (nearrow_compose (iutruncate_ne (S n)) B)
              (embed_ceiling_squash_ne w n i A h))).
Proof.
intros n w i A B h.
set (X := unguard w A i B).
destruct X as (C & HtruncC & HC).
match goal with
| |- _ = pi1 ?Y => set (X := Y)
end.
destruct X as (D & HtruncD & HD).
cbn [pi1].
exploit (maximum_element (fun j => exists m p, j <= i /\ rel A j m p)) as H.
  {
  exists (S i).
  intros k (_ & _ & H & _).
  omega.
  }
destruct H as [Hnone | Hsome].
  {
  clear HC HD.
  exploit (HtruncC 0) as HeqC.
    {
    intros k m p Hk Hmp.
    exfalso.
    refine (Hnone k _).
    eauto.
    }
  exploit (HtruncD 0) as HeqD.
    {
    intros k m p Hk Hmp.
    destruct Hmp as (_ & Hmp).
    exfalso.
    refine (Hnone k _).
    exists m, p.
    split; auto.
    omega.
    }
  rewrite -> HeqC, -> HeqD.
  rewrite -> iutruncate_combine.
  rewrite -> Nat.min_r; [| omega].
  rewrite -> !iutruncate_zero.
  reflexivity.
  }

  {
  destruct Hsome as (j & (m & p & Hji & Hmp) & Hmax).
  exploit (HtruncC (S j)) as HeqC.
    {
    intros k q r Hk Hqr.
    cut (k <= j); [omega |].
    apply Hmax; eauto.
    }
  exploit (HtruncD (min (S n) (S j))) as HeqD.
    {
    intros k q r Hk Hqr.
    destruct Hqr as (_ & Hqr).
    rewrite <- Nat.succ_min_distr.
    apply le_lt_n_Sm.
    apply Nat.min_glb; auto.
    apply Hmax.
    exists q, r.
    split; auto.
    omega.
    }
  rewrite -> HeqC, -> HeqD.
  clear HeqC HeqD.
  cbn [snd iutruncate].
  rewrite -> iutruncate_combine.
  clear Hji Hmax.
  rewrite <- Nat.succ_min_distr.
  so (Nat.le_min_l n j) as Hkn.
  set (k := min n j) in Hkn |- *.
  assert (rel A k m p) as Hmp'.
    {
    so (Nat.le_min_r n j).
    eapply urel_downward_leq; eauto.
    }
  clearbody k.
  clear j Hmp.
  rename Hmp' into Hmp.
  apply iutruncate_collapse.
  assert (rel (ceiling (S n) A) k m p) as Hmpn.
    {
    split; auto.
    omega.
    }
  eapply dist_trans.
    {
    apply (HC k m p (le_trans _#3 Hkn h) Hmp).
    }
  apply dist_symm.
  eapply dist_trans.
    {
    apply (HD k m p Hkn Hmpn).
    }
  cbn -[dist].
  eapply dist_trans.
    {
    apply (dist_downward_leq _ _ (S n)); [omega |].
    apply iutruncate_near.
    }
  apply (pi2 B).
  assert (k < S n) as Hkn' by omega.
  assert (rel (squash_urel w A i) k triv triv) as Htriv.
    {
    eapply squash_intro; eauto.
    omega.
    }
  erewrite -> transport_urelspinj.
Unshelve.
  2:{
    exact (conj Hkn' Htriv).
    }
  rewrite -> embed_ceiling_urelspinj.
  apply urelspinj_dist.
  auto.
  }
Qed.


Lemma extend_unguard :
  forall v w (h : v <<= w) i A B,
    extend_iurel h (pi1 (unguard v A i B))
    =
    pi1 (unguard w (extend_urel v w A) i
           (nearrow_compose
              (extend_iurel_ne h)
              (nearrow_compose B
                 (nearrow_compose 
                    (deextend_urelsp_ne h (squash_urel v A i))
                    (transport_ne (eqsymm (extend_squash v w A i h)) urelsp))))).
Proof.
intros v w h i A B.
set (X := unguard v A i B).
destruct X as (C & HtruncC & HC).
match goal with
| |- _ = pi1 ?Y => set (X := Y)
end.
destruct X as (D & HtruncD & HD).
cbn.
exploit (maximum_element (fun j => exists m p, j <= i /\ rel A j m p)) as H.
  {
  exists (S i).
  intros k (_ & _ & H & _).
  omega.
  }
destruct H as [Hnone | Hsome].
  {
  clear HC HD.
  exploit (HtruncC 0) as HeqC.
    {
    intros k m p Hk Hmp.
    exfalso.
    refine (Hnone k _).
    eauto.
    }
  exploit (HtruncD 0) as HeqD.
    {
    intros k m p Hk Hmp.
    cbn in Hmp.
    exfalso.
    refine (Hnone k _).
    exists (map_term (extend w v) m), (map_term (extend w v) p).
    split; auto.
    }
  rewrite -> HeqC, -> HeqD.
  rewrite -> !iutruncate_zero.
  cbn.
  rewrite -> extend_iubase.
  rewrite -> extend_empty_urel; auto.
  }

  {
  destruct Hsome as (j & (m & p & Hji & Hmp) & Hmax).
  exploit (HtruncC (S j)) as HeqC.
    {
    intros k q r Hk Hqr.
    cut (k <= j); [omega |].
    apply Hmax; eauto.
    }
  exploit (HtruncD (S j)) as HeqD.
    {
    intros k q r Hk Hqr.
    cbn in Hqr.
    apply le_lt_n_Sm.
    apply Hmax.
    do 2 eexists.
    eauto.
    }
  rewrite -> HeqC, -> HeqD.
  clear HeqC HeqD.
  rewrite <- iutruncate_extend_iurel.
  apply iutruncate_collapse.
  assert (rel (extend_urel v w A) j (map_term (extend v w) m) (map_term (extend v w) p)) as Hmp'.
    {
    cbn.
    rewrite -> !extend_term_cancel; auto.
    }
  eapply dist_trans.
  2:{
    eapply dist_symm.
    so (HD j (map_term (extend v w) m) (map_term (extend v w) p) Hji Hmp') as H.
    exact H.
    }
  apply extend_iurel_nonexpansive.
  eapply dist_trans.
    {
    so (HC j m p Hji Hmp) as H.
    exact H.
    }
  apply dist_refl'.
  cbn.
  f_equal.
  erewrite -> (transport_urelspinj _#3 (eqsymm (extend_squash v w A i h))).
Unshelve.
  2:{
    eapply squash_intro; eauto.
    }
  rewrite -> deextend_urelsp_urelspinj.
  reflexivity.
  }
Qed.


Definition iuguard (w : ordinal) i (A : wiurel w) (B : urelsp (squash_urel w (den A) i) -n> wiurel_ofe w) : wiurel w
  :=
  (guard_urel w i (den A) (fun C => den (pi1 B C)),
   snd (pi1 (unguard w (den A) i B))).


Lemma iutruncate_iuguard :
  forall n w i (A : wiurel w) (B : urelsp (squash_urel w (den A) i) -n> wiurel_ofe w) (h : n <= i),
    iutruncate (S n) (iuguard w i A B)
    =
    iuguard w n
      (iutruncate (S n) A)
      (nearrow_compose
         (nearrow_compose (iutruncate_ne (S n)) B)
         (embed_ceiling_squash_ne w n i (den A) h)).
Proof.
intros n w i A B h.
unfold iuguard.
unfold iutruncate.
cbn [den fst snd].
f_equal.
  {
  rewrite -> (ceiling_guard _#5 h); auto.
  exact (pi2 (nearrow_compose den_ne B)).
  }

  {
  exact (f_equal snd (iutruncate_unguard n w i (den A) B h)).
  }
Qed.


Lemma extend_iuguard :
  forall v w (h : v <<= w) i A B,
    extend_iurel h (iuguard v i A B)
    =
    iuguard w i (extend_iurel h A)
      (nearrow_compose (extend_iurel_ne h)
         (nearrow_compose B
            (nearrow_compose
               (deextend_urelsp_ne h (squash_urel v (den A) i))
               (transport_ne (eqsymm (extend_squash v w (den A) i h)) urelsp)))).
Proof.
intros v w h i A B.
unfold iuguard, extend_iurel.
cbn.
f_equal.  (* Why slow? *)
  {
  rewrite -> (extend_guard _ _ h).
  reflexivity.
  }

  {
  exact (f_equal snd (extend_unguard _ _ h i (den A) B)).
  }
Qed.


Lemma guard_urel_satisfied_eq :
  forall w 
    (A : wurel w) 
    i 
    (B : car (urelsp (squash_urel w A i)) -> car (wurel_ofe w))
    j m p
    (Hj : j <= i)
    (Hmp : rel A j m p),
      nonexpansive B
      -> ceiling (S j) (B (urelspinj _#4 (squash_intro _#6 Hj Hmp)))
         = 
         ceiling (S j) (guard_urel w i A B).

Proof.
intros w A i B j m p Hj Hmp Hne.
apply urel_extensionality.
fextensionality 3.
intros k n q.
cbn.
pextensionality.
  {
  intros (Hk & Hnq).
  split; auto.
  assert (k <= i) as Hki by omega.
  exists Hki.
  so (urel_closed _#5 Hnq) as (Hcln & Hclq).
  do2 2 split; auto.
  intros l r t Hl Hrt.
  eapply rel_from_dist.
  2:{
    apply (urel_downward_leq _#3 k); eauto.
    }
  apply Hne.
  apply dist_symm.
  apply urelspinj_dist.
  omega.
  }

  {
  intros (Hk & Hnq).
  split; auto.
  destruct Hnq as (Hki & _ & _ & Hact).
  assert (k <= j) as Hkj by omega.
  so (urel_downward_leq _#6 Hkj Hmp) as Hmp'.
  so (Hact k m p (le_refl _) Hmp') as Hnq.
  eapply rel_from_dist; eauto.
  apply Hne.
  apply urelspinj_dist; auto.
  }
Qed.


Lemma iuguard_satisfied_eq :
  forall w
    (A : wiurel w)
    i
    (B : urelsp (squash_urel w (den A) i) -n> wiurel_ofe w)
    j m p
    (Hj : j <= i)
    (Hmp : rel (den A) j m p),
      iutruncate (S j) (pi1 B (urelspinj _#4 (squash_intro _#6 Hj Hmp)))
      =
      iutruncate (S j) (iuguard w i A B).
Proof.
intros w A i B j m p Hj Hmp.
unfold iutruncate, iuguard.
cbn [fst snd].
f_equal.
  {
  eapply (guard_urel_satisfied_eq _#3 (fun C => den (pi1 B C))).
  apply compose_ne_ne.
    {
    apply den_nonexpansive.
    }

    {
    exact (pi2 B).
    }
  }

  {
  apply meta_truncate_collapse.
  apply dist_prod_snd.
  set (X := unguard w (den A) i B).
  destruct X as (C & Htrunc & HC).
  cbn [pi1].
  apply dist_symm.
  auto.
  }
Qed.


Definition coguard_action
  (w : ordinal) i (A : wurel w) (B : urelsp (squash_urel w A i) -n> wurel_ofe w)
  : nat -> relation (wterm w)
  :=
  fun i' m n =>
    exists p q (Hi' : i' <= i) (Hrel : rel A i' p q),
      rel (pi1 B (urelspinj (squash_urel w A i) i' triv triv (squash_intro _#6 Hi' Hrel))) i' m n.


Lemma coguard_uniform :
  forall w i A B, uniform _ (coguard_action w i A B).
Proof.
intros w i A B.
do2 3 split.
  {
  intros j m n Hmn.
  decompose Hmn.
  intros p q Hj Hpq Hmn.
  eapply urel_closed; eauto.
  }

  {
  intros j m m' n n' Hclm' Hcln' Hm Hn H.
  decompose H.
  intros p q Hj Hpq Hmn.
  exists p, q, Hj, Hpq.
  eapply urel_equiv; eauto.
  }

  {
  intros j m p n q Hmp Hnp Hnq.
  decompose Hmp.
  intros r t Hj Hrt Hmp.
  decompose Hnp.
  intros r' t' Hj' Hrt' Hnp.
  so (proof_irrelevance _ Hj Hj').
  subst Hj'.
  decompose Hnq.
  intros r'' t'' Hj' Hrt'' Hnq.
  so (proof_irrelevance _ Hj Hj').
  subst Hj'.
  exists r, t, Hj, Hrt.
  apply (urel_zigzag _#4 p n); auto.
    {
    force_exact Hnp.
    f_equal.
    f_equal.
    apply urelspinj_equal.
    cbn.
    apply property_action_triv; auto.
    exists r, t.
    auto.
    }

    {
    force_exact Hnq.
    f_equal.
    f_equal.
    apply urelspinj_equal.
    cbn.
    apply property_action_triv; auto.
    exists r, t.
    auto.
    }
  }

  {
  intros j m n Hmn.
  decompose Hmn.
  intros p q Hj Hpq Hmn.
  assert (j <= i) as Hj' by omega.
  exists p, q, Hj', (urel_downward _#5 Hpq).
  refine (rel_from_dist _#6 _ (urel_downward _#5 Hmn)).
  apply (pi2 B).
  apply dist_symm.
  apply urelspinj_dist.
  omega.
  }
Qed.


Definition coguard_urel w i A B :=
  mk_urel (coguard_action w i A B) (coguard_uniform _ _ _ _).


Lemma ceiling_coguard :
  forall n w i (A : wurel w) (B : urelsp (squash_urel w A i) -n> wurel_ofe w) (h : n <= i),
    ceiling (S n) (coguard_urel w i A B)
    =
    coguard_urel w n (ceiling (S n) A)
      (nearrow_compose
         (ceiling_ne (S n))
         (nearrow_compose
            B
            (nearrow_compose
               (embed_ceiling_ne (S n) (squash_urel w A i))
               (transport_ne (ceiling_squash_both w A n i h) urelsp)))).
Proof.
intros n w i A B h.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros (Hj_n & H).
  decompose H.
  intros q r Hj Hqr Hmp.
  assert (j <= n) as Hj_n' by omega.
  exists q, r, Hj_n', (conj Hj_n Hqr).
  cbn.
  split; auto.
  eapply rel_from_dist; eauto.
  apply (pi2 B).
  cbn.
  intros k Hk.
  fextensionality 1.
  intro t.
  cbn.
  rewrite -> (pi1_transport_lift _ _ urelsp_car_rhs _ _ (ceiling_squash_both w A n i h)).
  pextensionality.
    {
    intros (Hk' & H).
    cbn.
    split; auto.
    decompose H.
    intros x y.
    intros.
    do2 5 split; auto.
      {
      exists x, y.
      split; auto.
      omega.
      }

      {
      omega.
      }
    }

    {
    intros H.
    cbn in H.
    destruct H as (Hk' & H).
    split; auto.
    decompose H.
    intros x y.
    intros.
    do2 5 split; auto.
      {
      exists x, y.
      auto.
      }

      {
      omega.
      }
    }
  }

  {
  intro H.
  decompose H.
  intros q r Hj Hqr Hmp.
  cbn in Hmp.
  destruct Hmp as (Hj' & Hmp).
  split; auto.
  assert (j <= i) as Hj_i by omega.
  exists q, r, Hj_i.
  destruct Hqr as (Hj'' & Hqr).
  exists Hqr.
  eapply rel_from_dist; eauto.
  apply (pi2 B).
  cbn.
  intros k Hk.
  fextensionality 1.
  intros t.
  cbn.
  rewrite -> (pi1_transport_lift _ _ urelsp_car_rhs _ _ (ceiling_squash_both w A n i h)).
  pextensionality.
    {
    intro H.
    cbn in H.
    destruct H as (Hk' & H).
    split; auto.
    decompose H.
    intros x y.
    intros.
    do2 5 split; auto.
      {
      exists x, y.
      auto.
      }

      {
      omega.
      }
    }

    {
    intros (Hk' & H).
    decompose H.
    intros x y.
    intros.
    cbn.
    split; auto.
    do2 5 split; auto.
      {
      exists x, y.
      split; auto.
      omega.
      }

      {
      omega.
      }
    }
  }
Qed.


Lemma extend_coguard :
  forall v w (h : v <<= w) i A B,
    extend_urel v w (coguard_urel v i A B)
    =
    coguard_urel w i (extend_urel v w A)
      (nearrow_compose
         (extend_urel_ne v w)
         (nearrow_compose
            B
            (nearrow_compose
               (deextend_urelsp_ne h (squash_urel v A i))
               (transport_ne (eqsymm (extend_squash v w A i h)) urelsp)))).
Proof.
intros v w h i A B.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros H.
  decompose H.
  intros q r Hj Hqr Hmp.
  exists (map_term (extend v w) q), (map_term (extend v w) r), Hj.
  cbn.
  assert (rel A j (map_term (extend w v) (map_term (extend v w) q)) (map_term (extend w v) (map_term (extend v w) r))) as Hqr'.
    {
    rewrite -> !extend_term_cancel; auto.
    }
  exists Hqr'.
  eapply rel_from_dist; eauto.
  apply (pi2 B).
  cbn.
  intros k Hk.
  fextensionality 1.
  intros t.
  cbn.
  rewrite -> (pi1_transport_lift _ _ urelsp_car_rhs _ _ (eqsymm (extend_squash v w A i h))).
  cbn.
  pextensionality.
    {
    intros (Hk' & H).
    split; auto.
    decompose H.
    intros x y.
    intros.
    do2 5 split; auto.
      {
      exists (map_term (extend v w) x), (map_term (extend v w) y).
      rewrite -> !extend_term_cancel; auto.
      }
    
      {
      apply map_hygiene; auto.
      }
      
      {
      apply hygiene_auto; cbn.
      auto.
      }

      {
      replace triv with (map_term (extend v w) triv) by reflexivity.
      apply map_steps; auto.
      }

      {
      apply star_refl.
      }
    }

    {
    intros (Hk' & H).
    split; auto.
    decompose H.
    intros x y.
    intros.
    do2 5 split; auto.
      {
      exists (map_term (extend w v) x), (map_term (extend w v) y).
      auto.
      }
    
      {
      eapply map_hygiene_conv; eauto.
      }
      
      {
      apply hygiene_auto; cbn.
      auto.
      }

      {
      replace triv with (map_term (extend w v) triv) by reflexivity.
      rewrite <- (extend_term_cancel _ _ h t).
      apply map_steps; auto.
      }

      {
      apply star_refl.
      }
    }
  }

  {
  intros H.
  decompose H.
  intros q r Hj Hqr Hmp.
  cbn in Hqr.
  exists (map_term (extend w v) q), (map_term (extend w v) r), Hj, Hqr.
  cbn in Hmp.
  eapply rel_from_dist; eauto.
  apply (pi2 B).
  cbn.
  intros k Hk.
  fextensionality 1.
  intros t.
  cbn.
  rewrite -> (pi1_transport_lift _ _ urelsp_car_rhs _ _ (eqsymm (extend_squash v w A i h))).
  cbn.
  pextensionality.
    {
    intros (Hk' & H).
    split; auto.
    decompose H.
    intros x y.
    intros.
    do2 5 split; auto.
      {
      exists (map_term (extend w v) x), (map_term (extend w v) y); auto.
      }
    
      {
      eapply map_hygiene_conv; eauto.
      }
      
      {
      apply hygiene_auto; cbn.
      auto.
      }

      {
      replace triv with (map_term (extend w v) triv) by reflexivity.
      rewrite <- (extend_term_cancel _ _ h t).
      apply map_steps; auto.
      }

      {
      apply star_refl.
      }
    }

    {
    intros (Hk' & H).
    split; auto.
    decompose H.
    intros x y.
    intros.
    do2 5 split; auto.
      {
      exists (map_term (extend v w) x), (map_term (extend v w) y).
      rewrite -> !extend_term_cancel; auto.
      }
    
      {
      eapply map_hygiene; eauto.
      }
      
      {
      apply hygiene_auto; cbn.
      auto.
      }

      {
      replace triv with (map_term (extend v w) triv) by reflexivity.
      apply map_steps; auto.
      }

      {
      apply star_refl.
      }
    }
  }
Qed.


Definition iucoguard (w : ordinal) i (A : wiurel w) (B : urelsp (squash_urel w (den A) i) -n> wiurel_ofe w) : wiurel w
  :=
  (coguard_urel w i (den A) (nearrow_compose den_ne B),
   snd (pi1 (unguard w (den A) i B))).


Lemma iutruncate_iucoguard :
  forall n w i (A : wiurel w) (B : urelsp (squash_urel w (den A) i) -n> wiurel_ofe w) (h : n <= i),
    iutruncate (S n) (iucoguard w i A B)
    =
    iucoguard w n
      (iutruncate (S n) A)
      (nearrow_compose
         (nearrow_compose (iutruncate_ne (S n)) B)
         (embed_ceiling_squash_ne w n i (den A) h)).
Proof.
intros n w i A B h.
unfold iucoguard.
unfold iutruncate.
cbn [den fst snd].
f_equal.
  {
  rewrite -> (ceiling_coguard _#5 h); auto.
  apply urel_extensionality.
  fextensionality 3.
  intros j m p.
  cbn.
  f_equal.
  apply nearrow_extensionality.
  intro x.
  cbn.
  reflexivity.
  }

  {
  exact (f_equal snd (iutruncate_unguard n w i (den A) B h)).
  }
Qed.


Lemma extend_iucoguard :
  forall v w (h : v <<= w) i A B,
    extend_iurel h (iucoguard v i A B)
    =
    iucoguard w i (extend_iurel h A)
      (nearrow_compose (extend_iurel_ne h)
         (nearrow_compose B
            (nearrow_compose
               (deextend_urelsp_ne h (squash_urel v (den A) i))
               (transport_ne (eqsymm (extend_squash v w (den A) i h)) urelsp)))).
Proof.
intros v w h i A B.
unfold iucoguard, extend_iurel.
cbn.
f_equal.  (* Why slow? *)
  {
  rewrite -> (extend_coguard _ _ h).
  apply urel_extensionality.
  fextensionality 3.
  intros j m p.
  cbn.
  f_equal.
  apply nearrow_extensionality.
  intro x.
  cbn.
  reflexivity.
  }

  {
  exact (f_equal snd (extend_unguard _ _ h i (den A) B)).
  }
Qed.


Lemma coguard_urel_satisfied_eq :
  forall w 
    (A : wurel w) 
    i 
    (B : urelsp (squash_urel w A i) -n> wurel_ofe w)
    j m p
    (Hj : j <= i)
    (Hmp : rel A j m p),
      ceiling (S j) (pi1 B (urelspinj _#4 (squash_intro _#6 Hj Hmp)))
      = 
      ceiling (S j) (coguard_urel w i A B).
Proof.
intros w A i B j m p Hj Hmp.
apply urel_extensionality.
fextensionality 3.
intros k n q.
cbn.
pextensionality.
  {
  intros (Hk & Hnq).
  split; auto.
  assert (k <= i) as Hki by omega.
  assert (k <= j) as Hkj by omega.
  exists m, p, Hki, (urel_downward_leq _#6 Hkj Hmp).
  eapply rel_from_dist; eauto.
  apply (pi2 B).
  apply dist_symm.
  apply urelspinj_dist; auto.
  }

  {
  intros (Hk & Hnq).
  split; auto.
  decompose Hnq.
  intros x y Hki Hxy Hnq.
  eapply rel_from_dist; eauto.
  apply (pi2 B).
  apply urelspinj_dist.
  omega.
  }
Qed.


Lemma iucoguard_satisfied_eq :
  forall w
    (A : wiurel w)
    i
    (B : urelsp (squash_urel w (den A) i) -n> wiurel_ofe w)
    j m p
    (Hj : j <= i)
    (Hmp : rel (den A) j m p),
      iutruncate (S j) (pi1 B (urelspinj _#4 (squash_intro _#6 Hj Hmp)))
      =
      iutruncate (S j) (iucoguard w i A B).
Proof.
intros w A i B j m p Hj Hmp.
unfold iutruncate, iucoguard.
cbn [fst snd].
f_equal.
  {
  rewrite <- (coguard_urel_satisfied_eq _ (den A) _ (nearrow_compose den_ne B) _#3 Hj Hmp).
  reflexivity.
  }

  {
  apply meta_truncate_collapse.
  apply dist_prod_snd.
  set (X := unguard w (den A) i B).
  destruct X as (C & Htrunc & HC).
  cbn [pi1].
  apply dist_symm.
  auto.
  }
Qed.
