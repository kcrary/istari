
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
Require Import Approximation.
Require Import Compactness.
Require Import Defined.
Require Import Page.


Lemma equiv_converges :
  forall object (m n : @term object),
    equiv m n
    -> converges m
    -> converges n.
Proof.
intros object m n Hequiv (v & Heval).
so (equiv_eval _#4 Hequiv Heval) as (w & Heval' & _).
exists w; auto.
Qed.


(* Need the i index for ceiling_partial to be true. *)

Definition partial_action
  (w : ordinal) i (A : wurel w)
  : nat -> relation (wterm w)
  :=
  fun i' m n =>
    i' <= i
    /\ hygiene clo m
    /\ hygiene clo n
    /\ (converges m <-> converges n)
    /\ (converges m -> rel A i' m n).


Lemma partial_uniform :
  forall w i A, uniform _ (partial_action w i A).
Proof.
intros w i A.
do2 3 split.
  (* closed *)
  {
  intros j m n H.
  decompose H; auto.
  }

  (* equiv *)
  {
  intros j m m' n n' Hclm' Hcln' Hm Hn H.
  decompose H.
  intros Hj _ _ Hiff Hmn.
  do2 4 split; auto.
    {
    split.
      {
      intro Hm'.
      apply (equiv_converges _ n); auto.
      apply Hiff.
      apply (equiv_converges _ m'); auto using equiv_symm.
      }

      {
      intro Hn'.
      apply (equiv_converges _ m); auto.
      apply Hiff.
      apply (equiv_converges _ n'); auto using equiv_symm.
      }
    }
  
    {
    intro Hm'.
    eapply urel_equiv; eauto.
    apply Hmn.
    eapply equiv_converges; eauto using equiv_symm.
    }
  }

  (* zigzag *)
  {
  intros j m p n q Hmp Hnp Hnq.
  decompose Hmp.
  intros Hj Hclm _ Hmpiff Hmp.
  decompose Hnp.
  intros _ _ _ Hnpiff Hnp.
  decompose Hnq.
  intros _ _ Hclq Hnqiff Hnq.
  do2 4 split; auto.
    {
    tauto.
    }

    {
    intro Hm.
    apply (urel_zigzag _#3 m p n q); auto.
      {
      apply Hnp.
      tauto.
      }

      {
      apply Hnq.
      tauto.
      }
    }
  }

  (* downward *)
  {
  intros j m n H.
  decompose H.
  intros Hj Hclm Hcln Hiff Hmn.
  do2 4 split; auto.
    {
    omega.
    }

    {
    intro Hm.
    apply urel_downward.
    auto.
    }
  }
Qed.


Definition partial_urel w i A :=
  mk_urel (partial_action w i A) (partial_uniform _ _ _).


Definition iupartial w i (A : wiurel w) : wiurel w
  :=
  (partial_urel w i (den A),
   meta_iurel A).


Lemma den_iupartial :
  forall w i A,
    den (iupartial w i A) = partial_urel w i (den A).
Proof.
reflexivity.
Qed.


Lemma iupartial_inj :
  forall w i A A',
    iupartial w i A = iupartial w i A'
    -> A = A'.
Proof.
intros w i A A' Heq.
unfold iupartial in Heq.
so (f_equal (fun z => snd z) Heq) as Heq'.
cbn in Heq'.
exact (meta_iurel_inj _#3 Heq').
Qed.


Lemma ceiling_partial :
  forall n w i A,
    ceiling (S n) (partial_urel w i A)
    =
    partial_urel w (min i n) (ceiling (S n) A).
Proof.
intros n w i A.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros (Hi & Hact).
  decompose Hact.
  intros Hj Hclm Hclp Hiff Hmp.
  do2 4 split; auto.
    {
    so (Min.min_glb i n j).
    omega.
    }

    {
    intro Hm.
    split; auto.
    }
  }

  {
  intros Hact.
  decompose Hact.
  intros Hj Hclm Hclp Hiff Hmp.
  split.
    {
    so (Nat.le_min_r i n).
    omega.
    }

    {
    do2 4 split; auto.
      {
      so (Nat.le_min_l i n).
      omega.
      }

      {
      intro Hm.
      destruct (Hmp Hm) as (_ & H).
      exact H.
      }
    }
  }
Qed.


Lemma iutruncate_iupartial :
  forall n w i A,
    iutruncate (S n) (iupartial w i A)
    =
    iupartial w
      (min i n)
      (iutruncate (S n) A).
Proof.
intros n w i A.
unfold iupartial.
unfold iutruncate.
cbn [fst snd].
f_equal.
  {
  apply ceiling_partial.
  }

  {
  fold (iutruncate (S n) A).
  rewrite -> meta_truncate_iurel; auto.
  omega.
  }
Qed.


Lemma map_converges :
  forall A B (f : A -> B) (m : term A),
    converges m
    -> converges (map_term f m).
Proof.
intros A B f m (v & (Hsteps & Hval)).
exists (map_term f v).
split.
  {
  apply map_steps; auto.
  }

  {
  apply map_value; auto.
  }
Qed.


Lemma anti_map_converges :
  forall A B (f : A -> B) (m : term A),
    converges (map_term f m)
    -> converges m.
Proof.
intros A B f m (v & (Hsteps & Hval)).
so (map_steps_form _#5 Hsteps) as (w & -> & Hsteps').
exists w.
split; auto.
eapply anti_map_value; eauto.
Qed.


Lemma map_converges_iff :
  forall A B (f : A -> B) (m : term A),
    converges m <-> converges (map_term f m).
Proof.
intros A B f m.
split.
  {
  apply map_converges.
  }

  {
  apply anti_map_converges.
  }
Qed.


Lemma extend_partial :
  forall v w (h : v <<= w) i A,
    extend_urel v w (partial_urel v i A)
    =
    partial_urel w i (extend_urel v w A).
Proof.
intros v w h i A.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros Hj Hclm Hclp Hiff Hmp.
  do2 4 split; eauto using map_hygiene_conv.
    {
    split.
      {
      intro Hm.
      apply (anti_map_converges _ _ (extend w v)).
      apply Hiff.
      apply map_converges; auto.
      }

      {
      intro Hp.
      apply (anti_map_converges _ _ (extend w v)).
      apply Hiff.
      apply map_converges; auto.
      }
    }

    {
    intro Hm.
    cbn.
    exact (Hmp (map_converges _#4 Hm)).
    }
  }

  {
  intro H.
  decompose H.
  intros Hj Hclm Hclp Hiff Hmp.
  do2 4 split; auto using map_hygiene.
    {
    split.
      {
      intro Hm.
      apply map_converges.
      apply Hiff.
      eapply anti_map_converges; eauto.
      }

      {
      intro Hp.
      apply map_converges.
      apply Hiff.
      eapply anti_map_converges; eauto.
      }
    }

    {
    intro Hm.
    exact (Hmp (anti_map_converges _#4 Hm)).
    }
  }
Qed.


Lemma extend_iupartial :
  forall v w (h : v <<= w) i A,
    extend_iurel h (iupartial v i A)
    =
    iupartial w i (extend_iurel h A).
Proof.
intros v w h i A.
unfold iupartial, extend_iurel.
cbn.
f_equal.
  {
  apply extend_partial; auto.
  }
rewrite -> extend_meta_iurel.
unfold extend_iurel.
reflexivity.
Qed.


Require Import SemanticsProperty.


Definition halts_urel (w : ordinal) (i : nat) (m : wterm w) : wurel w :=
  property_urel
    (fun _ => converges m)
    w i
    (fun _ h => h).


Definition admissible w (A : wurel w) : Prop :=
  forall f g i m p j,
    hygiene clo f
    -> hygiene clo g
    -> hygiene (permit clo) m
    -> hygiene (permit clo) p
    -> (forall k,
          j <= k
          -> rel A i (subst1 (afix k f) m) (subst1 (afix k g) p))
    -> rel A i (subst1 (app theta f) m) (subst1 (app theta g) p).


Definition admiss_property w (A : wurel w) : nat -> Prop :=
  fun i =>
    admissible w (ceiling (S i) A).


Lemma admiss_property_downward :
  forall w A i,
    admiss_property w A (S i)
    -> admiss_property w A i.
Proof.
intros w A i Hadmiss.
unfold admiss_property in Hadmiss |- *.
intros f g i' m p j Hclf Hclg Hclm Hclp Hact.
destruct (Hact j (le_refl _)) as (Hi' & _).
split; auto.
exploit (Hadmiss f g i' m p j) as Hrel; auto.
  {
  intros k Hk.
  split.
    {
    omega.
    }
  apply Hact; auto.
  }
destruct Hrel as (_ & Hrel).
exact Hrel.
Qed.


Definition admiss_urel (w : ordinal) (i : nat) (A : wurel w) : wurel w :=
  property_urel
    (admiss_property w A)
    w i
    (admiss_property_downward w A).


Lemma ceiling_admiss_internal :
  forall w i A,
    admiss_urel w i A = admiss_urel w i (ceiling (S i) A).
Proof.
intros w i A.
unfold admiss_urel.
apply property_urel_extensionality; auto.
intros j Hj.
unfold admiss_property.
rewrite -> ceiling_combine.
rewrite -> Nat.min_l; [reflexivity | omega].
Qed.


Lemma ceiling_admiss :
  forall n w i A,
    ceiling (S n) (admiss_urel w i A)
    =
    admiss_urel w (min i n) (ceiling (S n) A).
Proof.
intros n w i A.
unfold admiss_urel.
apply urel_extensionality.
fextensionality 3.
intros j m p.
pextensionality.
  {
  intros Hmp.
  destruct Hmp as (Hjn & Hmp).
  destruct Hmp as (Hadmiss & Hji & Hclm & Hclp & Hm & Hp).
  do2 5 split; auto.
  2:{
    so (Min.min_glb i n j).
    omega.
    }
  unfold admiss_property in Hadmiss |- *.
  rewrite -> ceiling_combine_le; auto.
  }

  {
  intros Hmp.
  destruct Hmp as (Hadmiss & Hj & Hclm & Hclp & Hm & Hp).
  split.
    {
    so (Nat.min_glb_r i n j).
    omega.
    }
  do2 5 split; auto.
  2:{
    so (Nat.min_glb_l i n j).
    omega.
    }
  unfold admiss_property in Hadmiss |- *.
  rewrite -> ceiling_combine_le in Hadmiss; auto.
  so (Nat.min_glb_r i n j).
  omega.
  }
Qed.


Lemma extend_admissible :
  forall v w (A : wurel v),
    v <<= w
    -> admissible w (extend_urel v w A) <-> admissible v A.
Proof.
intros v w A Hvw.
split.
  {
  intro Hadmiss.
  intros f g i m p j Hclf Hclg Hclm Hclp Hact.
  exploit (Hadmiss (map_term (extend v w) f) (map_term (extend v w) g) i (map_term (extend v w) m) (map_term (extend v w) p) j) as Hrel; auto using map_hygiene.
    {
    intros k Hk.
    cbn.
    simpmap.
    rewrite -> !extend_term_cancel; auto.
    }
  cbn in Hrel.
  simpmapin Hrel.
  rewrite -> !extend_term_cancel in Hrel; auto.
  }

  {
  intro Hadmiss.
  intros f g i m p j Hclf Hclg Hclm Hclp Hact.
  exploit (Hadmiss (map_term (extend w v) f) (map_term (extend w v) g) i (map_term (extend w v) m) (map_term (extend w v) p) j) as Hrel; auto using map_hygiene.
    {
    intros k Hk.
    so (Hact k Hk) as H.
    cbn in H.
    simpmapin H.
    auto.
    }
  cbn.
  simpmap.
  auto.
  }
Qed.


Lemma extend_admiss :
  forall v w (h : v <<= w) i A,
    extend_urel v w (admiss_urel v i A)
    =
    admiss_urel w i (extend_urel v w A).
Proof.
intros v w h i A.
unfold admiss_urel.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros Hadmiss Hj Hclm Hclp Hstepsm Hstepsp.
  do2 5 split; eauto using map_hygiene_conv.
    {
    unfold admiss_property.
    rewrite -> ceiling_extend_urel.
    rewrite -> extend_admissible; auto.
    }

    {
    so (map_steps_form _#5 Hstepsm) as (q & Heq & Hstepsm').
    so (map_eq_triv_invert _#4 (eqsymm Heq)); subst q.
    auto.
    }

    {
    so (map_steps_form _#5 Hstepsp) as (q & Heq & Hstepsp').
    so (map_eq_triv_invert _#4 (eqsymm Heq)); subst q.
    auto.
    }
  }

  {
  intro H.
  decompose H.
  intros Hadmiss Hj Hclm Hclp Hstepsm Hstepsp.
  do2 5 split; eauto using map_hygiene.
    {
    unfold admiss_property in Hadmiss.
    rewrite -> ceiling_extend_urel in Hadmiss.
    rewrite -> extend_admissible in Hadmiss; auto.
    }

    {
    so (map_steps _ _ (extend w v) _ _ Hstepsm) as H.
    simpmapin H.
    auto.
    }

    {
    so (map_steps _ _ (extend w v) _ _ Hstepsp) as H.
    simpmapin H.
    auto.
    }
  }
Qed.


Definition iuadmiss w i A
  :=
  (admiss_urel w i (den A),
   meta_iurel A).


Lemma iutruncate_iuadmiss :
  forall n w i A,
    iutruncate (S n) (iuadmiss w i A)
    =
    iuadmiss w
      (min i n)
      (iutruncate (S n) A).
Proof.
intros n w i A.
unfold iuadmiss.
unfold iutruncate.
unfold den.
cbn [fst snd].
f_equal.
  {
  apply ceiling_admiss.
  }

  {
  fold (iutruncate (S n) A).
  rewrite -> meta_truncate_iurel; auto.
  omega.
  }
Qed.


Lemma extend_iuadmiss :
  forall v w (h : v <<= w) i A,
    extend_iurel h (iuadmiss v i A)
    =
    iuadmiss w i (extend_iurel h A).
Proof.
intros v w h i A.
unfold iuadmiss, extend_iurel.
cbn.
f_equal.
  {
  apply extend_admiss; auto.
  }

  {
  rewrite -> extend_meta_iurel.
  unfold extend_iurel.
  reflexivity.
  }
Qed.


Lemma iuadmiss_inj :
  forall w i A A',
    iuadmiss w i A = iuadmiss w i A'
    -> A = A'.
Proof.
intros w i A A' Heq.
unfold iupartial in Heq.
so (f_equal (fun z => snd z) Heq) as Heq'.
cbn in Heq'.
exact (meta_iurel_inj _#3 Heq').
Qed.


(* We need to use sapprox to make extend_upward work. *)
Definition upward w (A : wurel w) : Prop :=
  forall i m m' p p',
    sapprox m m'
    -> sapprox p p'
    -> rel A i m p
    -> rel A i m' p'.


Definition uptype_property w (A : wurel w) : nat -> Prop :=
  fun i =>
    upward w (ceiling (S i) A).


Lemma uptype_property_downward :
  forall w A i,
    uptype_property w A (S i)
    -> uptype_property w A i.
Proof.
intros w A i Hupward.
unfold uptype_property in Hupward |- *.
intros i' m m' p p' Hm Hp Hmp.
destruct Hmp as (Hi' & Hmp).
split; auto.
exploit (Hupward i' m m' p p') as H; auto.
  {
  split; auto.
  }
destruct H as (_ & H).
exact H.
Qed.


Definition uptype_urel (w : ordinal) (i : nat) (A : wurel w) : wurel w :=
  property_urel
    (uptype_property w A)
    w i
    (uptype_property_downward w A).


Lemma ceiling_uptype_internal :
  forall w i A,
    uptype_urel w i A = uptype_urel w i (ceiling (S i) A).
Proof.
intros w i A.
unfold admiss_urel.
apply property_urel_extensionality; auto.
intros j Hj.
unfold uptype_property.
rewrite -> ceiling_combine.
rewrite -> Nat.min_l; [reflexivity | omega].
Qed.


Lemma ceiling_uptype :
  forall n w i A,
    ceiling (S n) (uptype_urel w i A)
    =
    uptype_urel w (min i n) (ceiling (S n) A).
Proof.
intros n w i A.
unfold uptype_urel.
apply urel_extensionality.
fextensionality 3.
intros j m p.
pextensionality.
  {
  intros Hmp.
  destruct Hmp as (Hjn & Hmp).
  destruct Hmp as (Huptype & Hji & Hclm & Hclp & Hm & Hp).
  do2 5 split; auto.
  2:{
    so (Min.min_glb i n j).
    omega.
    }
  unfold uptype_property in Huptype |- *.
  rewrite -> ceiling_combine_le; auto.
  }

  {
  intros Hmp.
  destruct Hmp as (Huptype & Hj & Hclm & Hclp & Hm & Hp).
  split.
    {
    so (Nat.min_glb_r i n j).
    omega.
    }
  do2 5 split; auto.
  2:{
    so (Nat.min_glb_l i n j).
    omega.
    }
  unfold uptype_property in Huptype |- *.
  rewrite -> ceiling_combine_le in Huptype; auto.
  so (Nat.min_glb_r i n j).
  omega.
  }
Qed.


Lemma extend_upward :
  forall v w (A : wurel v),
    v <<= w
    -> upward w (extend_urel v w A) <-> upward v A.
Proof.
intros v w A Hvw.
split.
  {
  intro Hupward.
  intros i m m' p p' Happrox Happrox' Hmp.
  exploit (Hupward i (map_term (extend v w) m) (map_term (extend v w) m') (map_term (extend v w) p) (map_term (extend v w) p')) as H.
    {
    intros T f.
    rewrite -> !map_term_compose; auto.
    }

    {
    intros T f.
    rewrite -> !map_term_compose; auto.
    }

    {
    cbn.
    rewrite -> !extend_term_cancel; auto.
    }
  cbn in H.
  rewrite -> !extend_term_cancel in H; auto.
  }

  {
  intro Hupward.
  intros i m m' p p' Happrox Happrox' Hmp.
  cbn in Hmp.
  cbn.
  exploit (Hupward i (map_term (extend w v) m) (map_term (extend w v) m') (map_term (extend w v) p) (map_term (extend w v) p')) as H; auto.
    {
    intros T f.
    rewrite -> !map_term_compose; auto.
    }

    {
    intros T f.
    rewrite -> !map_term_compose; auto.
    }
  }
Qed.


Lemma extend_uptype :
  forall v w (h : v <<= w) i A,
    extend_urel v w (uptype_urel v i A)
    =
    uptype_urel w i (extend_urel v w A).
Proof.
intros v w h i A.
unfold uptype_urel.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros Huptype Hj Hclm Hclp Hstepsm Hstepsp.
  do2 5 split; eauto using map_hygiene_conv.
    {
    unfold uptype_property.
    rewrite -> ceiling_extend_urel.
    rewrite -> extend_upward; auto.
    }

    {
    so (map_steps_form _#5 Hstepsm) as (q & Heq & Hstepsm').
    so (map_eq_triv_invert _#4 (eqsymm Heq)); subst q.
    auto.
    }

    {
    so (map_steps_form _#5 Hstepsp) as (q & Heq & Hstepsp').
    so (map_eq_triv_invert _#4 (eqsymm Heq)); subst q.
    auto.
    }
  }

  {
  intro H.
  decompose H.
  intros Huptype Hj Hclm Hclp Hstepsm Hstepsp.
  do2 5 split; eauto using map_hygiene.
    {
    unfold uptype_property in Huptype.
    rewrite -> ceiling_extend_urel in Huptype.
    rewrite -> extend_upward in Huptype; auto.
    }

    {
    so (map_steps _ _ (extend w v) _ _ Hstepsm) as H.
    simpmapin H.
    auto.
    }

    {
    so (map_steps _ _ (extend w v) _ _ Hstepsp) as H.
    simpmapin H.
    auto.
    }
  }
Qed.


Definition iuuptype w i A
  :=
  (uptype_urel w i (den A),
   meta_iurel A).


Lemma iutruncate_iuuptype :
  forall n w i A,
    iutruncate (S n) (iuuptype w i A)
    =
    iuuptype w
      (min i n)
      (iutruncate (S n) A).
Proof.
intros n w i A.
unfold iuuptype.
unfold iutruncate.
unfold den.
cbn [fst snd].
f_equal.
  {
  apply ceiling_uptype.
  }

  {
  fold (iutruncate (S n) A).
  rewrite -> meta_truncate_iurel; auto.
  omega.
  }
Qed.


Lemma extend_iuuptype :
  forall v w (h : v <<= w) i A,
    extend_iurel h (iuuptype v i A)
    =
    iuuptype w i (extend_iurel h A).
Proof.
intros v w h i A.
unfold iuuptype, extend_iurel.
cbn.
f_equal.
  {
  apply extend_uptype; auto.
  }

  {
  rewrite -> extend_meta_iurel.
  unfold extend_iurel.
  reflexivity.
  }
Qed.


Lemma iuuptype_inj :
  forall w i A A',
    iuuptype w i A = iuuptype w i A'
    -> A = A'.
Proof.
intros w i A A' Heq.
unfold iupartial in Heq.
so (f_equal (fun z => snd z) Heq) as Heq'.
cbn in Heq'.
exact (meta_iurel_inj _#3 Heq').
Qed.
