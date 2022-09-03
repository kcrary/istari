
Require Import Axioms.
Require Import Tactics.
Require Import Sigma.
Require Import Equality.
Require Import Ofe.
Require Import Syntax.
Require Import Ofe.
Require Import Uniform.
Require Import Spaces.
Require Import Urelsp.
Require Import Ordinal.
Require Import Candidate.
Require Import Model.
Require Import Intensional.
Require Import Ceiling.
Require Import Truncate.
Require Import Ordinal.


Definition std_one_and_dist :
  existsT (st : nat -> car (nearrow_ofe (space qone) (space qone))),
    forall i j, i <= j -> dist i (st i) (st j)
    :=
    expair (fun _ => nearrow_const unit_ofe unit_ofe tt) (fun i j _ => dist_refl _ i).


Lemma std_type_dist :
  forall w i j,
    i <= j
    -> @dist (nearrow_ofe (wiurel_ofe w) (wiurel_ofe w)) i (iutruncate_ne i) (iutruncate_ne j).
Proof.
intros w i j Hj.
intros a.
eapply dist_trans.
  {
  apply iutruncate_near.
  }
apply dist_symm.
eapply dist_downward_leq; eauto.
apply iutruncate_near.
Qed.


Definition std_type_and_dist w :
  existsT (st : nat -> car (nearrow_ofe (space (qtype w)) (space (qtype w)))),
    forall i j, i <= j -> dist i (st i) (st j)
    :=
    expair (@iutruncate_ne w) (std_type_dist w).


Definition std_tarrow_action (i : nat) w (A : wurel w) (k2 : qkind)
  (st : nat -> space k2 -n> space k2)
  (f : urelsp A -n> space k2) (P : urelsp_car A)
  : spcar k2
  := pi1 (st (min i (S (urelsp_index A P)))) (pi1 f P).


Lemma std_tarrow_action_nonexpansive :
  forall i w A k2 (st : nat -> car (nearrow_ofe (space k2) (space k2))),
    (forall i j, i <= j -> dist i (st i) (st j))
    -> forall (f : urelsp A -n> space k2),
         @nonexpansive (urelsp A) (space k2) (std_tarrow_action i w A k2 st f).
Proof.
intros n w A k2 st Hdistst f.
intros i P Q Hdist.
so (urelsp_eta _ A P) as (j & m & p & Hmp & HeqP).
so (urelsp_eta _ A Q) as (j' & m' & p' & Hmp' & HeqQ).
subst P Q.
unfold std_tarrow_action.
rewrite -> !urelsp_index_inj.
apply (dist_trans _#3 (pi1 (st (min n (S j))) (pi1 f (urelspinj A j' m' p' Hmp')))).
  {
  apply (pi2 (st (min n (S j)))).
  apply (pi2 f).
  exact Hdist.
  }
set (x := (pi1 f (urelspinj A j' m' p' Hmp'))).
clearbody x.
so (lt_eq_lt_dec j j') as [[Hlt | Heq] | Hlt].
  {
  so (le_dec n (S j)) as [Hlen | Hnlen].
    {
    replace (min n (S j)) with n by (symmetry; apply min_l; omega).
    replace (min n (S j')) with n by (symmetry; apply min_l; omega).
    apply dist_refl.
    }
  replace (min n (S j)) with (S j) by (symmetry; apply min_r; omega).
  so (urelspinj_dist_index _#11 Hlt Hdist) as Hle.
  eapply dist_downward_leq; eauto.
  apply Hdistst.
  apply Nat.min_glb; omega.
  }

  {
  subst j'.
  apply dist_refl.
  }

  {
  so (le_dec n (S j')) as [Hlen | Hnlen].
    {
    replace (min n (S j)) with n by (symmetry; apply min_l; omega).
    replace (min n (S j')) with n by (symmetry; apply min_l; omega).
    apply dist_refl.
    }
  replace (min n (S j')) with (S j') by (symmetry; apply min_r; omega).
  so (urelspinj_dist_index _#11 Hlt (dist_symm _ _ _ _ Hdist)) as Hle.
  eapply dist_downward_leq; eauto.
  apply dist_symm.
  apply Hdistst.
  apply Nat.min_glb; omega.
  }
Qed.


Definition std_tarrow_car (i : nat) w (A : wurel w) (k2 : qkind) 
  (st : nat -> car (nearrow_ofe (space k2) (space k2)))
  (Hdistst : forall i j, i <= j -> dist i (st i) (st j))
  (f : urelsp A -n> space k2)
  : urelsp A -n> space k2
  :=
  expair (std_tarrow_action i w A k2 st f) (std_tarrow_action_nonexpansive i w A k2 st Hdistst f).


Lemma std_tarrow_nonexpansive :
  forall i w A k2
    (st : nat -> car (nearrow_ofe (space k2) (space k2)))
    (Hdistst : forall i j, i <= j -> dist i (st i) (st j)),
      @nonexpansive (nearrow_ofe (urelsp A) (space k2)) (nearrow_ofe (urelsp A) (space k2))
        (std_tarrow_car i w A k2 st Hdistst).
Proof.
intros i w A k2 st Hdistst.
intros n f g Hdist.
unfold std_tarrow_car.
cbn.
intros P.
cbn.
unfold std_tarrow_action.
apply (pi2 (st (min i (S (urelsp_index A P))))).
apply Hdist.
Qed.


Definition std_tarrow (i : nat) w (A : wurel w) (k2 : qkind)
  (st : nat -> car (nearrow_ofe (space k2) (space k2)))
  (Hdistst : forall i j, i <= j -> dist i (st i) (st j))
  : car (nearrow_ofe (nearrow_ofe (urelsp A) (space k2)) (nearrow_ofe (urelsp A) (space k2)))
  :=
  expair
    (std_tarrow_car i w A k2 st Hdistst)
    (std_tarrow_nonexpansive i w A k2 st Hdistst).


Lemma std_tarrow_dist :
  forall w A k2
    (st : nat -> car (nearrow_ofe (space k2) (space k2)))
    (Hdistst : forall i j, i <= j -> dist i (st i) (st j))
    i j,
      i <= j
      -> dist i (std_tarrow i w A k2 st Hdistst) (std_tarrow j w A k2 st Hdistst).
Proof.
intros w A k2 st Hdistst i j Hle.
intros f x.
cbn in f.
cbn.
unfold std_tarrow_action.
set (k := S (urelsp_index A x)).
eassert _ as H; [refine (Hdistst (min i k) (min j k) _ (pi1 f x)) |].
  {
  so (Nat.le_min_l i k).
  so (Nat.le_min_r i k).
  apply Nat.min_glb; omega.
  }
so (le_dec i k) as [Hik | Hnik].
  {
  rewrite -> (Nat.min_l _ _ Hik) in H at 1.
  exact H.
  }

  {
  assert (k <= i) as Hki by omega.
  rewrite -> (Nat.min_r _ _ Hki).
  rewrite -> (Nat.min_r _ _ (le_trans _ _ _ Hki Hle)).
  apply dist_refl.
  }
Qed.


Definition std_tarrow_and_dist w
  (A : wurel w) (k2 : qkind)
  (f : existsT (st : nat -> car (nearrow_ofe (space k2) (space k2))),
        forall i j, i <= j -> dist i (st i) (st j))
  :
  existsT (st : nat -> car (nearrow_ofe (nearrow_ofe (urelsp A) (space k2)) (nearrow_ofe (urelsp A) (space k2)))),
    forall i j, i <= j -> dist i (st i) (st j)
  :=
  expair
    (fun i => std_tarrow i w A k2 (pi1 f) (pi2 f))
    (std_tarrow_dist w A k2 (pi1 f) (pi2 f)).


Definition std_arrow (i : nat) (k1 k2 : qkind)
  (st1 : nat -> car (nearrow_ofe (space k1) (space k1)))
  (st2 : nat -> car (nearrow_ofe (space k2) (space k2)))
  : car (nearrow_ofe (nearrow_ofe (space k1) (space k2)) (nearrow_ofe (space k1) (space k2)))
  :=
  @nearrow_compose2_ne (space k1) (space k1) (space k2) (space k2) (st1 i) (st2 i).


Lemma std_arrow_dist :
  forall k1 k2
    (st1 : nat -> car (nearrow_ofe (space k1) (space k1)))
    (st2 : nat -> car (nearrow_ofe (space k2) (space k2)))
    (Hdistst1 : forall i j, i <= j -> dist i (st1 i) (st1 j))
    (Hdistst2 : forall i j, i <= j -> dist i (st2 i) (st2 j))
    i j,
      i <= j
      -> dist i (std_arrow i k1 k2 st1 st2) (std_arrow j k1 k2 st1 st2).
Proof.
intros k1 k2 st1 st2 Hdistst1 Hdistst2 i j Hle.
intros f x.
cbn in f.
cbn.
eapply dist_trans.
  {
  apply Hdistst2; eauto.
  }

  {
  apply (pi2 (st2 j)).
  apply (pi2 f).
  apply Hdistst1; eauto.
  }
Qed.


Definition std_arrow_and_dist
  (k1 k2 : qkind)
  (f : existsT (st : nat -> car (nearrow_ofe (space k1) (space k1))),
        forall i j, i <= j -> dist i (st i) (st j))
  (g : existsT (st : nat -> car (nearrow_ofe (space k2) (space k2))),
        forall i j, i <= j -> dist i (st i) (st j))
  :
  existsT (st : nat -> car (nearrow_ofe (nearrow_ofe (space k1) (space k2)) (nearrow_ofe (space k1) (space k2)))),
    forall i j, i <= j -> dist i (st i) (st j)
  :=
  expair 
    (fun i => std_arrow i k1 k2 (pi1 f) (pi1 g))
    (std_arrow_dist k1 k2 (pi1 f) (pi1 g) (pi2 f) (pi2 g)).


Definition std_prod (i : nat) (k1 k2 : qkind)
  (st1 : nat -> car (nearrow_ofe (space k1) (space k1)))
  (st2 : nat -> car (nearrow_ofe (space k2) (space k2)))
  : car (nearrow_ofe (prod_ofe (space k1) (space k2)) (prod_ofe (space k1) (space k2)))
  :=
  mpair_ne (st1 i) (st2 i).


Lemma std_prod_dist :
  forall k1 k2
    (st1 : nat -> car (nearrow_ofe (space k1) (space k1)))
    (st2 : nat -> car (nearrow_ofe (space k2) (space k2)))
    (Hdistst1 : forall i j, i <= j -> dist i (st1 i) (st1 j))
    (Hdistst2 : forall i j, i <= j -> dist i (st2 i) (st2 j))
    i j,
      i <= j
      -> dist i (std_prod i k1 k2 st1 st2) (std_prod j k1 k2 st1 st2).
Proof.
intros k1 k2 st1 st2 Hdistst1 Hdistst2 i j Hle.
split.
  {
  cbn.
  apply Hdistst1; auto.
  }

  {
  cbn.
  apply Hdistst2; auto.
  }
Qed.


Definition std_prod_and_dist
  (k1 k2 : qkind)
  (f : existsT (st : nat -> car (nearrow_ofe (space k1) (space k1))),
         forall i j, i <= j -> dist i (st i) (st j))
  (g : existsT (st : nat -> car (nearrow_ofe (space k2) (space k2))),
         forall i j, i <= j -> dist i (st i) (st j))
  :
  existsT (st : nat -> car (nearrow_ofe (prod_ofe (space k1) (space k2)) (prod_ofe (space k1) (space k2)))),
    forall i j, i <= j -> dist i (st i) (st j)
  :=
  expair
    (fun i => std_prod i k1 k2 (pi1 f) (pi1 g))
    (std_prod_dist k1 k2 (pi1 f) (pi1 g) (pi2 f) (pi2 g)).


Definition std_fut (i : nat) (k : qkind)
  (st : nat -> car (nearrow_ofe (space k) (space k)))
  : car (nearrow_ofe (half (space k)) (half (space k)))
  :=
  nearrow_half (space k) (space k) (st (pred i)).


Lemma std_fut_dist :
  forall k
    (st : nat -> car (nearrow_ofe (space k) (space k)))
    (Hdistst : forall i j, i <= j -> dist i (st i) (st j))
    i j,
      i <= j
      -> dist i (std_fut i k st) (std_fut j k st).
Proof.
intros k st Hdistst i j Hle.
intros x.
cbn in x.
cbn.
exploit (Hdistst (pred i) (pred j)) as H.
  {
  omega.
  }
apply H.
Qed.


Definition std_fut_and_dist
  (k : qkind)
  (f : existsT (st : nat -> car (nearrow_ofe (space k) (space k))),
        forall i j, i <= j -> dist i (st i) (st j))
  :
  existsT (st : nat -> car (nearrow_ofe (half (space k)) (half (space k)))),
    forall i j, i <= j -> dist i (st i) (st j)
  :=
  expair 
    (fun i => std_fut i k (pi1 f))
    (std_fut_dist k (pi1 f) (pi2 f)).


Fixpoint std_and_dist (k : qkind)
  : existsT (st : nat -> car (nearrow_ofe (space k) (space k))),
      forall i j, i <= j -> dist i (st i) (st j)
  :=
  match k with
  | qone => std_one_and_dist

  | qtype w => std_type_and_dist w

  | qarrow k1 k2 => std_arrow_and_dist k1 k2 (std_and_dist k1) (std_and_dist k2)

  | qtarrow w A k2 => std_tarrow_and_dist w A k2 (std_and_dist k2)

  | qprod k1 k2 => std_prod_and_dist k1 k2 (std_and_dist k1) (std_and_dist k2)

  | qfut k2 => std_fut_and_dist k2 (std_and_dist k2)
  end.


Definition std_ne (i : nat) (k : qkind) : car (nearrow_ofe (space k) (space k))
  := pi1 (std_and_dist k) i.


Definition std (i : nat) (k : qkind) : car (space k) -> car (space k)
  := pi1 (std_ne i k).


Definition std_nonexpansive (i : nat) (k : qkind) : nonexpansive (std i k)
  := pi2 (std_ne i k).


Lemma std_dist :
  forall k i j,
    i <= j
    -> dist i (std_ne i k) (std_ne j k).
Proof.
intros k i j Hle.
exact (pi2 (std_and_dist k) i j Hle).
Qed.


Lemma std_one_is :
  forall i, std i qone = (fun _ => tt).
Proof.
intros i.
cbn.
reflexivity.
Qed.


Lemma std_type_is :
  forall i w, std i (qtype w) = iutruncate i.
Proof.
intros i w.
cbn.
reflexivity.
Qed.


Lemma std_arrow_is :
  forall i k1 k2, std i (qarrow k1 k2) = pi1 (std_arrow i k1 k2 (fun i => std_ne i k1) (fun i => std_ne i k2)).
Proof.
intros i A k2.
cbn.
reflexivity.
Qed.


Lemma std_tarrow_is :
  forall i w A k2, std i (qtarrow w A k2) = pi1 (std_tarrow i w A k2 (fun i => std_ne i k2) (std_dist k2)).
Proof.
intros i w A k2.
cbn.
f_equal.
apply proof_irrelevance.
Qed.


Lemma std_prod_is :
  forall i k1 k2, std i (qprod k1 k2) = pi1 (std_prod i k1 k2 (fun i => std_ne i k1) (fun i => std_ne i k2)).
Proof.
intros i A k2.
cbn.
reflexivity.
Qed.


Lemma std_fut_is :
  forall i k, std i (qfut k) = pi1 (std_fut i k (fun i => std_ne i k)).
Proof.
intros i k.
cbn.
reflexivity.
Qed.


Global Opaque std_ne.


Lemma std_collapse :
  forall i k (x y : spcar k),
    dist i x y
    -> std i k x = std i k y.
Proof.
intros i k.
revert i.
induct k.

(* one *)
{
intros i x y _.
cbn.
reflexivity.
}

(* type *)
{
intros w i A B Hdist.
cbn.
rewrite -> std_type_is.
apply iutruncate_collapse; auto.
}

(* arrow *)
{
intros k1 _ k2 IH i f g Hfg.
rewrite -> !std_arrow_is.
cbn.
apply exT_extensionality_prop.
fextensionality 1.
intro x.
cbn.
apply IH.
apply Hfg.
}

(* tarrow *)
{
intros w A k2 IH i f g Hfg.
rewrite -> !std_tarrow_is.
cbn.
apply exT_extensionality_prop.
fextensionality 1.
intro P.
cbn.
unfold std_tarrow_action.
apply IH.
apply (dist_downward_leq _ _ i).
  {
  apply Nat.le_min_l.
  }
apply Hfg.
}

(* prod *)
{
intros k1 IH1 k2 IH2 i x y Hxy.
rewrite -> !std_prod_is.
destruct x as (x1, x2).
destruct y as (y1, y2).
destruct Hxy as (Hxy1, Hxy2).
cbn.
f_equal; [apply IH1 | apply IH2]; auto.
}

(* fut *)
{
intros k IH i x y Hxy.
rewrite -> !std_fut_is.
cbn.
cbn in Hxy.
apply IH.
exact Hxy.
}
Qed.


Lemma std_inhabitant :
  forall i k, std i k (space_inhabitant k) = space_inhabitant k.
Proof.
intros i k.
revert i.
induct k.

(* one *)
{
intros i.
cbn.
reflexivity.
}

(* type *)
{
intros w i.
cbn.
rewrite -> std_type_is.
unfold iutruncate.
cbn.
rewrite -> meta_truncate_nats.
f_equal.
  {
  apply urel_extensionality.
  cbn.
  fextensionality 3.
  intros j m p.
  pextensionality; [intros (? & H) | intro H]; destruct H.
  }

  {
  f_equal.
  apply exT_extensionality_prop.
  fextensionality 1.
  intros j.
  cbn.
  pextensionality; omega.
  }
}

(* arrow *)
{
intros k1 _ k2 IH i.
rewrite -> std_arrow_is.
apply exT_extensionality_prop.
fextensionality 1.
intro x.
change (spcar k1) in x.
cbn.
apply IH.
}

(* tarrow *)
{
intros w A k2 IH i.
rewrite -> std_tarrow_is.
apply exT_extensionality_prop.
fextensionality 1.
intro P.
cbn.
unfold std_tarrow_action.
cbn.
apply IH.
}

(* prod *)
{
intros k1 IH1 k2 IH2 i.
rewrite -> std_prod_is.
cbn.
f_equal; [apply IH1 | apply IH2].
}

(* fut *)
{
intros k IH i.
rewrite -> std_fut_is.
cbn.
apply IH.
}
Qed.


Lemma proj_std_and_embed_std :
  (forall i j k (x : spcar k),
     j <= S i
     -> proj i k (std j k x) = std j (approx i k) (proj i k x))
  /\
  (forall i j k (x : spcar (approx i k)),
     j <= S i
     -> embed i k (std j (approx i k) x) = std j k (embed i k x)).
Proof.
cut (forall k,
       (forall i j (x : spcar k),
          j <= S i
          -> proj i k (std j k x) = std j (approx i k) (proj i k x))
       /\
       (forall i j (x : spcar (approx i k)),
          j <= S i
          -> embed i k (std j (approx i k) x) = std j k (embed i k x))).
  {
  intros Hind.
  split; intros; apply Hind ; auto.
  }
intro k.
induct k.

(* one *)
{
split.
  {
  intros i j x _.
  cbn.
  reflexivity.
  }

  {
  intros i j x _.
  cbn.
  reflexivity.
  }
}

(* type *)
{
intros w.
split.
  {
  intros i j A _.
  cbn.
  reflexivity.
  }

  {
  intros i j A _.
  cbn.
  reflexivity.
  }
}

(* arrow *)
{
intros k1 IH1 k2 IH2.
split.
  {
  intros i j f Hji.
  cbn [approx].
  rewrite -> !std_arrow_is.
  cbn.
  apply exT_extensionality_prop.
  fextensionality 1.
  intro x.
  cbn.
  etransitivity.
    {
    apply IH2; auto.
    }
  unfold std.
  f_equal.
  unfold proj.
  f_equal.
  f_equal.
  symmetry.
  apply IH1; auto.
  }

  {
  intros i j f Hji.
  cbn [approx].
  rewrite -> !std_arrow_is.
  cbn.
  apply exT_extensionality_prop.
  fextensionality 1.
  intro x.
  cbn.
  etransitivity.
    {
    apply IH2; auto.
    }
  unfold std.
  f_equal.
  unfold embed.
  f_equal.
  f_equal.
  symmetry.
  apply IH1; auto.
  }
}

(* tarrow *)
{
intros w A k2 IH.
split.
  {
  intros i j f Hji.
  cbn [approx].
  rewrite -> !std_tarrow_is.
  cbn.
  apply exT_extensionality_prop.
  fextensionality 1.
  intro P.
  cbn.
  unfold std_tarrow_action.
  cbn.
  match goal with
  | |- pi1 _ (pi1 _ ?X) = _ => set (x := X)
  end.
  clearbody x.
  so (urelsp_eta _ _ P) as (h & m & p & Hmp & ->).
  rewrite -> urelsp_index_embed_ceiling.
  rewrite -> !urelsp_index_inj.
  fold (proj i k2).
  fold (std (min j (S h)) k2).
  fold (std (min j (S h)) (approx i k2)).
  apply IH.
  so (Nat.le_min_l j (S h)); omega.
  }

  {
  intros i j f Hle.
  cbn [approx].
  rewrite -> !std_tarrow_is.
  cbn.
  apply exT_extensionality_prop.
  fextensionality 1.
  intro P.
  cbn.
  unfold std_tarrow_action.
  cbn.
  match goal with
  | |- pi1 _ (pi1 _ ?X) = _ => set (x := X)
  end.
  clearbody x.
  so (urelsp_eta _ _ P) as (h & m & p & Hmp & ->).
  rewrite -> urelsp_index_proj_ceiling.
  rewrite -> !urelsp_index_inj.
  rewrite -> Nat.succ_min_distr.
  rewrite -> Nat.min_assoc.
  cbn.
  rewrite -> (min_l _ _ Hle).
  apply IH.
  so (Nat.le_min_l j (S h)).
  omega.
  }
}

(* prod *)
{
intros k1 IH1 k2 IH2.
split.
  {
  intros i j x Hj.
  destruct x as (x, y).
  cbn [approx].
  rewrite -> !std_prod_is.
  cbn.
  f_equal; [apply IH1 | apply IH2]; auto.
  }

  {
  intros i j x Hj.
  destruct x as (x, y).
  cbn [approx].
  rewrite -> !std_prod_is.
  cbn.
  f_equal; [apply IH1 | apply IH2]; auto.
  }
}

(* fut *)
{
intros k IH.
split.
  {
  intros i j x Hj.
  destruct i as [| i].
    {
    cbn.
    reflexivity.
    }
  cbn [approx].
  rewrite -> std_fut_is.
  apply IH.
  omega.
  }

  {
  intros i j x Hle.
  destruct i as [| i].
    {
    cbn [approx].
    rewrite -> !std_fut_is.
    cbn.
    replace (pi1 (std_ne (pred j) k)) with (std (pred j) k) by reflexivity.
    rewrite -> std_inhabitant.
    reflexivity.
    }
  cbn [approx].
  rewrite -> std_fut_is.
  apply IH.
  omega.
  }
}
Qed.


Lemma proj_std :
  forall i j k (x : spcar k),
    j <= S i
    -> proj i k (std j k x) = std j (approx i k) (proj i k x).
Proof.
intros i j k x Hji.
apply proj_std_and_embed_std; auto.
Qed.


Lemma embed_std :
  forall i j k (x : spcar (approx i k)),
    j <= S i
    -> embed i k (std j (approx i k) x) = std j k (embed i k x).
Proof.
intros i j k x Hji.
apply proj_std_and_embed_std; auto.
Qed.


Lemma std_combine :
  forall i j k x,
    std i k (std j k x)
    =
    std (min i j) k x.
Proof.
intros i j k.
revert i j.
induct k.

(* one *)
{
intros i j x.
cbn.
reflexivity.
}

(* type *)
{
intros w i j x.
rewrite -> !std_type_is.
apply iutruncate_combine.
}

(* arrow *)
{
intros k1 IH1 k2 IH2 i j f.
rewrite -> !std_arrow_is.
cbn.
apply exT_extensionality_prop.
fextensionality 1.
intro x.
cbn.
etransitivity.
  {
  apply IH2.
  }
unfold std.
f_equal.
f_equal.
rewrite -> Nat.min_comm.
apply IH1.
}

(* tarrow *)
{
intros w A k2 IH i j f.
rewrite -> !std_tarrow_is.
cbn.
apply exT_extensionality_prop.
fextensionality 1.
intro P.
cbn.
unfold std_tarrow_action.
cbn.
unfold std_tarrow_action.
unfold std in IH.
rewrite -> IH.
f_equal.
f_equal.
set (h := S (urelsp_index A P)).
clearbody h.
rewrite -> Nat.min_assoc.
setoid_rewrite <- Nat.min_assoc at 2.
setoid_rewrite -> Nat.min_comm at 3.
rewrite -> Nat.min_assoc.
rewrite <- Nat.min_assoc.
rewrite -> Nat.min_id.
reflexivity.
}

(* arrow *)
{
intros k1 IH1 k2 IH2 i j x.
destruct x as (x, y).
rewrite -> !std_prod_is.
cbn.
f_equal; [apply IH1 | apply IH2].
}

(* fut *)
{
intros k IH i j x.
rewrite -> !std_fut_is.
cbn.
unfold std in IH.
replace (pred (min i j)) with (min (pred i) (pred j)); auto.
so (Nat.sub_min_distr_r i j 1) as H.
rewrite <- !pred_of_minus in H.
exact H.
}
Qed.


Lemma std_combine_le :
  forall i j k x,
    i <= j
    -> std i k (std j k x)
       =
       std i k x.
Proof.
intros i j k x Hle.
replace (std i k) with (std (min i j) k) at 2.
  {
  rewrite -> std_combine.
  rewrite -> min_l; auto.
  }
rewrite -> min_l; auto.
Qed.


Lemma std_combine_ge :
  forall i j k x,
    j <= i
    -> std i k (std j k x)
       =
       std j k x.
Proof.
intros i j k x Hle.
rewrite -> std_combine.
rewrite -> Nat.min_r; auto.
Qed.


Lemma std_idem :
  forall i k x,
    std i k (std i k x)
    =
    std i k x.
Proof.
intros i k x.
apply std_combine_le; auto.
Qed.


Definition stdc (i : nat) (Q : candidate) : candidate
  :=
  expair (pi1 Q) (std i (pi1 Q) (pi2 Q)).


Lemma stdc_combine_le :
  forall i j (Q : candidate),
    i <= j
    -> stdc i (stdc j Q) = stdc i Q.
Proof.
intros i j Q Hle.
unfold stdc.
cbn.
f_equal.
destruct Q as (k & A).
cbn.
apply std_combine_le; auto.
Qed.


Lemma stdc_idem :
  forall i Q,
    stdc i (stdc i Q) = stdc i Q.
Proof.
intros i Q.
apply stdc_combine_le; auto.
Qed.


Lemma projc_stdc :
  forall i j Q,
    j <= S i
    -> projc i (stdc j Q) = stdc j (projc i Q).
Proof.
intros i j Q Hji.
destruct Q as (k & x).
unfold projc, stdc.
cbn.
f_equal.
apply proj_std; auto.
Qed.


Lemma projc_stdc_coalesce :
  forall i j Q,
    j <= i
    -> projc j (stdc (S j) (projc i (stdc (S i) Q))) = projc j (stdc (S j) Q).
Proof.
intros i j Q Hj.
rewrite <- projc_stdc; [| omega].
rewrite -> projc_combine_le; auto.
rewrite -> stdc_combine_le; auto.
omega.
Qed.


Lemma std_transport :
  forall i (k l : qkind) (h : k = l) (x : spcar k),
    std i l (transport h spcar x) = transport h spcar (std i k x).
Proof.
intros i k l h x.
subst l.
reflexivity.
Qed.
