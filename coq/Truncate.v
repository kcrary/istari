
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
Require Import Ceiling.
Require Import Candidate.
Require Import Intensional.
Require Import IntensionalNerect.
Require Import Ordinal.
Require Import Candidate.


Section level.


Variable cur : ordinal.


Definition meta_truncate_main (a : car (meta_ofe (obj cur))) : car (pi_ofe nat (fun _ => meta_ofe (obj cur))).
Proof.
apply
   (meta_nerect cur (pi_ofe nat (fun _ => meta_ofe (obj cur)))
      (fun I n => meta_nats (nats_min I (nat_nats (S n))))
      (fun R f g n =>
         meta_fn
           (ceiling (S n) R)
           (nearrow_compose
              (neapi g n)
              (embed_ceiling_ne (S n) R)))
      (fun _ x _ y n => meta_pair (x n) (y n))
      (fun _ x n =>
         meta_half
           (match n with
            | 0 => meta_nats (nat_nats 0)
            | S n' => x n'
            end))
      (fun pg n => meta_page pg)).

(* nats *)
{
intros i I J Hdist.
intro n.
apply meta_dist_nats.
intros j Hj.
cbn.
split; intro H; destruct H; split; auto; apply Hdist; auto.
}

(* fn *)
{
intros i A B e f g h HAB Hef Hgh n.
apply meta_dist_fn.
  {
  apply ceiling_nonexpansive; auto.
  }

  {
  intros C D HCD.
  cbn.
  apply Hgh; auto.
  }
}

(* pair *)
{
intros i p p' q q' x x' y y' _ _ Hx Hy n.
apply meta_dist_pair; auto.
}

(* half *)
{
intros i p p' x x' _ Hx n.
apply meta_dist_half.
destruct n as [| n].
  {
  apply dist_refl.
  }

  {
  apply Hx.
  }
}

(* argument *)
{
exact a.
}
Defined.


Lemma meta_truncate_main_nonexpansive :
  nonexpansive meta_truncate_main.
Proof.
apply meta_nerect_nonexpansive.
Qed.


Definition meta_truncate (n : nat) (a : car (meta_ofe (obj cur))) : car (meta_ofe (obj cur))
  :=
  match n with
  | 0 => meta_nats (nat_nats 0)
  | S n' => meta_truncate_main a n'
  end.


Lemma meta_truncate_nonexpansive :
  forall n, nonexpansive (meta_truncate n).
Proof.
intro n.
unfold meta_truncate, meta_truncate_main.
destruct n as [| n'].
  {
  apply const_nonexpansive.
  }

  {
  intros i x y Hxy.
  exact (meta_truncate_main_nonexpansive i x y Hxy n').
  }
Qed.


Definition meta_truncate_ne (n : nat) : meta_ofe (obj cur) -n> meta_ofe (obj cur)
  :=
  expair (meta_truncate n) (meta_truncate_nonexpansive n).


Lemma meta_truncate_zero :
  forall a, meta_truncate 0 a = meta_nats (nat_nats 0).
Proof.
intros a.
unfold meta_truncate.
reflexivity.
Qed.


Lemma meta_truncate_nats :
  forall n I, meta_truncate n (meta_nats I) = meta_nats (nats_min I (nat_nats n)).
Proof.
intros n I.
unfold meta_truncate.
destruct n as [| n].
  {
  f_equal.
  apply exT_extensionality_prop.
  cbn.
  fextensionality 1.
  intro i.
  pextensionality; omega.
  }
unfold meta_truncate_main.
rewrite -> meta_nerect_nats.
reflexivity.
Qed.


Lemma meta_truncate_fn :
  forall n R f (Hpos : n > 0),
    meta_truncate n (meta_fn R f)
    =
    meta_fn
      (ceiling n R)
      (nearrow_compose
         (meta_truncate_ne n)
         (nearrow_compose f (embed_ceiling_ne n R))).
Proof.
intros n R f Hpos.
unfold meta_truncate.
destruct n as [| n].
  {
  omega.
  }
unfold meta_truncate_main.
rewrite -> meta_nerect_fn.
f_equal.
apply exT_extensionality_prop.
reflexivity.
Qed.


Lemma meta_truncate_term :
  forall n R C (Hpos : n > 0),
    meta_truncate n (meta_term R C)
    =
    meta_term (ceiling n R) (proj_ceiling n Hpos R C).
Proof.
intros k R C Hpos.
unfold meta_term.
rewrite -> meta_truncate_fn; auto.
f_equal.
apply nearrow_extensionality.
intro D.
cbn.
rewrite -> meta_truncate_nats.
f_equal.
apply exT_extensionality_prop.
fextensionality 1.
intro i.
cbn.
unfold urelsp_sim_pred.
pextensionality.
  {
  intros ((m & HCm & HDm) & Hi).
  cbn.
  eauto.
  }

  {
  intros (m & HCm & HDm).
  destruct HCm as (Hi & HCm).
  cbn.
  eauto.
  }
Qed.



Lemma meta_truncate_pair :
  forall n x y (Hpos : n > 0),
    meta_truncate n (meta_pair x y)
    =
    meta_pair (meta_truncate n x) (meta_truncate n y).
Proof.
intros n x y Hpos.
unfold meta_truncate.
destruct n as [| n].
  {
  omega.
  }
unfold meta_truncate_main.
rewrite -> meta_nerect_pair.
reflexivity.
Qed.


Lemma meta_truncate_half :
  forall n x (Hpos : n > 0),
    meta_truncate n (meta_half x)
    =
    meta_half (meta_truncate (pred n) x).
Proof.
intros n x Hpos.
unfold meta_truncate.
destruct n as [| n].
  {
  omega.
  }
unfold meta_truncate_main.
rewrite -> meta_nerect_half.
cbn.
reflexivity.
Qed.


Lemma meta_truncate_page :
  forall n pg (Hpos : n > 0),
    meta_truncate n (meta_page pg)
    =
    meta_page pg.
Proof.
intros n pg Hpos.
unfold meta_truncate.
destruct n as [| n].
  {
  omega.
  }
unfold meta_truncate_main.
rewrite -> meta_nerect_page.
reflexivity.
Qed.


Hint Rewrite meta_truncate_zero meta_truncate_nats meta_truncate_fn meta_truncate_pair meta_truncate_half meta_truncate_page : meta_truncate.


Lemma meta_truncate_near :
  forall n (a : car (meta_ofe (obj cur))), dist n (meta_truncate n a) a.
Proof.
intros n a.
revert n.
pattern a.
apply meta_rect; clear a.

(* nats *)
{
intros I n.
rewrite -> meta_truncate_nats.
apply meta_dist_nats.
intros i Hi.
cbn.
split; intro H; [destruct H | split]; auto.
}

(* fn *)
{
intros R f IH n.
apply dist_if_pos.
intro Hpos.
rewrite -> (meta_truncate_fn _#3 Hpos).
apply meta_dist_fn.
  {
  apply ceiling_near.
  }
intros C D HCD.
eapply dist_trans.
2:{
  apply IH.
  }
cbn -[dist].
apply meta_truncate_nonexpansive.
apply (pi2 f).
intros i Hi.
cbn.
apply HCD; auto.
}

(* pair *)
{
intros x IH1 y IH2 n.
apply dist_if_pos.
intro Hpos.
rewrite -> meta_truncate_pair; auto.
apply meta_dist_pair; auto.
}

(* half *)
{
intros x IH n.
apply dist_if_pos.
intro Hpos.
rewrite -> meta_truncate_half; auto.
destruct n as [| n].
  {
  omega.
  }
apply meta_dist_half; auto.
}

(* page *)
{
intros pg n.
apply dist_if_pos.
intro Hpos.
rewrite -> meta_truncate_page; auto.
apply dist_refl.
}
Qed.


Definition iutruncate (n : nat) (r : car (wiurel_ofe cur)) : car (wiurel_ofe cur)
  :=
  (ceiling n (fst r), meta_truncate n (snd r)).


Lemma iutruncate_nonexpansive :
  forall n, nonexpansive (iutruncate n).
Proof.
intros n.
intros i r s Hrs.
destruct Hrs as (H1 & H2).
split.
  {
  cbn.
  apply ceiling_nonexpansive; auto.
  }

  {
  cbn.
  apply meta_truncate_nonexpansive; auto.
  }
Qed.


Definition iutruncate_ne (n : nat) : wiurel_ofe cur -n> wiurel_ofe cur
  :=
  expair (iutruncate n) (iutruncate_nonexpansive n).


Lemma iutruncate_near :
  forall n (r : car (wiurel_ofe cur)),
    dist n (iutruncate n r) r.
Proof.
intros n r.
split.
  {
  apply ceiling_near.
  }

  {
  apply meta_truncate_near.
  }
Qed.


Lemma ceiling_collapse :
  forall i (A B : car (wurel_ofe cur)),
    dist i A B
    -> ceiling i A = ceiling i B.
Proof.
intros i A B Hdist.
apply urel_extensionality.
fextensionality 3.
intros j m n.
cbn.
pextensionality.
  {
  intros (Hj & Hmn).
  split; auto.
  rewrite <- Hdist; auto.
  }

  {
  intros (Hj & Hmn).
  split; auto.
  rewrite -> Hdist; auto.
  }
Qed.


Lemma meta_truncate_collapse :
  forall i (a b : car (meta_ofe (obj cur))),
    dist i a b
    -> meta_truncate i a = meta_truncate i b.
Proof.
intros i a b Hdist.
so (lt_dec 0 i) as [Hpos | Hnpos].
2:{
  assert (i = 0) by omega; subst i.
  rewrite -> !meta_truncate_zero.
  reflexivity.
  }
revert i b Hdist Hpos.
pattern a.
apply meta_rect; clear a.

(* nats *)
{
intros I i b Hdist Hpos.
so (meta_dist_nats_invert _#4 Hpos Hdist) as (J & -> & Hdist').
rewrite -> !meta_truncate_nats.
f_equal.
apply exT_extensionality_prop.
fextensionality 1.
intro n.
cbn.
pextensionality.
  {
  intros (H, Hn).
  split; auto.
  rewrite <- (Hdist' n); auto.
  }

  {
  intros (H, Hn).
  split; auto.
  rewrite -> (Hdist' n); auto.
  }
}

(* fn *)
{
intros A f IH i b Hdist Hpos.
so (meta_dist_fn_invert _#5 Hpos Hdist) as (B & g & -> & HAB & Hfg).
rewrite -> !meta_truncate_fn; auto.
so (ceiling_collapse _#3 HAB) as Heq.
apply meta_fn_extensionality.
apply (eq_impl_eq_dep _#6 Heq).
apply nearrow_extensionality.
intro C.
rewrite -> (pi1_transport_dep_lift _ _ (fun R h => @nonexpansive (urelsp R) (meta_ofe (obj cur)) h) _ _ Heq).
rewrite -> app_transport_dom.
cbn.
apply IH; auto.
apply Hfg.
intros j Hj.
cbn.
rewrite -> (pi1_transport_dep_lift _ _ urelsp_car_rhs _ _ (eqsymm Heq)).
rewrite -> transport_const.
reflexivity.
}

(* pair *)
{
intros x IH1 y IH2 i b Hdist Hpos.
so (meta_dist_pair_invert _#5 Hpos Hdist) as (x' & y' & -> & Hx & Hy).
rewrite -> !meta_truncate_pair; auto.
f_equal; auto.
}

(* half *)
{
intros x IH i b Hdist Hpos.
so (meta_dist_half_invert _#4 Hpos Hdist) as (x' & -> & Hx).
rewrite -> !meta_truncate_half; auto.
f_equal.
remember (pred i) as j eqn:Heq.
destruct j as [| j].
  {
  rewrite -> !meta_truncate_zero.
  reflexivity.
  }
apply IH; auto.
omega.
}

(* page *)
{
intros pg i b Hdist Hpos.
so (meta_dist_page_invert _#4 Hpos Hdist); subst b.
reflexivity.
}
Qed.


Lemma iutruncate_collapse :
  forall n a b,
    dist n a b
    -> iutruncate n a = iutruncate n b.
Proof.
intros n a b Hdist.
destruct Hdist as (Hdist1, Hdist2).
apply prod_extensionality.
  {
  cbn.
  apply ceiling_collapse; auto.
  }

  {
  cbn.
  apply meta_truncate_collapse; auto.
  }
Qed.


Lemma den_iutruncate :
  forall n a,
    den (iutruncate n a) = ceiling n (den a).
Proof.
intros n a.
reflexivity.
Qed.


Lemma meta_truncate_combine :
  forall i j (a : meta (obj cur)),
    meta_truncate i (meta_truncate j a)
    = meta_truncate (min i j) a.
Proof.
intros i j a.
so (lt_dec 0 i) as [Hposi | Hnpos].
2:{
  assert (i = 0) by omega; subst i.
  rewrite -> Nat.min_0_l.
  rewrite -> !meta_truncate_zero.
  reflexivity.
  }
so (lt_dec 0 j) as [Hposj | Hnpos].
2:{
  assert (j = 0) by omega; subst j.
  rewrite -> Nat.min_0_r.
  rewrite -> !meta_truncate_zero.
  rewrite -> meta_truncate_nats.
  rewrite -> nats_min_min.
  cbn.
  reflexivity.
  }
assert (min i j > 0) as Hposij.
  {
  apply Nat.min_glb_lt; auto.
  }
revert i j Hposi Hposj Hposij.
pattern a.
apply meta_rect; clear a.

(* nats *)
{
intros I i j _ _ _.
rewrite -> !meta_truncate_nats.
rewrite <- nats_min_assoc.
rewrite -> nats_min_min.
rewrite -> Nat.min_comm.
reflexivity.
}

(* fn *)
{
intros A f IH i j Hposi Hposj Hposij.
rewrite -> !meta_truncate_fn; auto.
apply meta_fn_extensionality.
so (ceiling_combine _ i j A) as Heq.
apply (eq_impl_eq_dep _#6 Heq).
apply nearrow_extensionality.
intro C.
rewrite -> (pi1_transport_dep_lift _ _ (fun R h => @nonexpansive (urelsp R) (meta_ofe (obj cur)) h) _ _ Heq).
rewrite -> app_transport_dom.
cbn.
rewrite -> IH; auto.
f_equal.
f_equal.
apply exT_extensionality_prop.
cbn.
fextensionality 2.
intros k m.
rewrite -> (pi1_transport_dep_lift _ _ urelsp_car_rhs _ _ (eqsymm Heq)).
rewrite -> transport_const.
reflexivity.
}

(* pair *)
{
intros x IH1 y IH2 i j Hposi Hposj Hposij.
rewrite -> !meta_truncate_pair; auto.
f_equal; auto.
}

(* half *)
{
intros x IH i j Hposi Hposj Hposij.
rewrite -> !meta_truncate_half; auto.
f_equal.
destruct i as [| i].
  {
  omega.
  }
destruct j as [| j].
  {
  omega.
  }
cbn.
destruct i as [| i].
  {
  rewrite -> Nat.min_0_l.
  cbn.
  reflexivity.
  }
destruct j as [| j].
  {
  rewrite -> Nat.min_0_r.
  rewrite -> meta_truncate_zero.
  rewrite -> meta_truncate_nats.
  rewrite -> nats_min_min.
  reflexivity.
  }
apply IH; try omega.
apply Nat.min_glb_lt; omega.
}

(* page *)
{
intros pg i j Hposi Hposj Hposij.
rewrite -> !meta_truncate_page; auto.
}
Qed.


Lemma iutruncate_combine :
  forall i j a,
    iutruncate i (iutruncate j a) = iutruncate (min i j) a.
Proof.
intros i j a.
apply prod_extensionality; cbn.
  {
  apply ceiling_combine.
  }

  {
  apply meta_truncate_combine.
  }
Qed.    


Lemma iutruncate_combine_le :
  forall i j (a : wiurel cur),
    i <= j
    -> iutruncate i (iutruncate j a) = iutruncate i a.
Proof.
intros i j a Hle.
rewrite -> iutruncate_combine.
rewrite -> Nat.min_l; auto.
Qed.


Lemma iutruncate_combine_ge :
  forall i j (a : wiurel cur),
    j <= i
    -> iutruncate i (iutruncate j a) = iutruncate j a.
Proof.
intros i j a Hle.
rewrite -> iutruncate_combine.
rewrite -> Nat.min_r; auto.
Qed.


Lemma iutruncate_idem :
  forall i (A : wiurel cur), iutruncate i (iutruncate i A) = iutruncate i A.
Proof.
intros i A.
rewrite -> iutruncate_combine_le; auto.
Qed.


Lemma meta_truncate_null :
  forall n,
    meta_truncate n meta_null = meta_null.
Proof.
intros n.
unfold meta_null.
rewrite -> meta_truncate_nats.
f_equal.
apply exT_extensionality_prop.
cbn.
fextensionality 1.
intro i.
pextensionality; omega.
Qed.


Lemma meta_truncate_urel :
  forall n (R : wurel cur) (Hpos : n > 0),
    meta_truncate n (meta_urel R)
    =
    meta_urel (ceiling n R).
Proof.
intros n R Hpos.
unfold meta_urel.
rewrite -> meta_truncate_fn; auto.
f_equal.
apply nearrow_extensionality.
intro x.
cbn.
apply meta_truncate_null.
Qed.


Lemma meta_truncate_iurel :
  forall n (r : wiurel cur) (Hpos : n > 0),
    meta_truncate n (meta_iurel r)
    =
    meta_iurel (iutruncate n r).
Proof.
intros n r Hpos.
unfold meta_iurel.
rewrite -> meta_truncate_pair; auto.
f_equal.
apply meta_truncate_urel; auto.
Qed.


Lemma iutruncate_iubase :
  forall n (R : wurel cur),
    iutruncate n (iubase R) = iubase (ceiling n R).
Proof.
intros n R.
unfold iutruncate, iubase.
f_equal.
apply meta_truncate_null.
Qed.


Lemma iutruncate_zero :
  forall A,
    iutruncate 0 A = iubase empty_urel.
Proof.
intros A.
unfold iutruncate, iubase.
f_equal.
apply ceiling_zero.
Qed.


End level.


(* Truncate has to be 0-indexed.  If we used 1-indexing, the qfut case
   wouldn't work because truncating at (pred i) would fail to trivialize the
   object.
*)

Fixpoint truncate_ne (i : nat) (k : qkind) { struct k } : space k -n> space k
  :=
  match k with
  | qone =>
      nearrow_const unit_ofe unit_ofe tt

  | qtype w =>
      iutruncate_ne w i

  | qarrow k1 k2 =>
      composer (space k1) (space k2) (space k2) (truncate_ne i k2)

  | qtarrow w A k2 =>
      composer (urelsp A) (space k2) (space k2) (truncate_ne i k2)

  | qprod k1 k2 =>
      mpair_ne (truncate_ne i k1) (truncate_ne i k2)

  | qfut k =>
      nearrow_half _ _ (truncate_ne (pred i) k)
  end.


Definition truncate (i : nat) (k : qkind) : car (space k) -> car (space k)
  := pi1 (truncate_ne i k).


Definition truncate_nonexpansive (i : nat) (k : qkind) : nonexpansive (truncate i k)
  :=
  pi2 (truncate_ne i k).


Lemma truncate_near :
  forall i k (x : spcar k),
    dist i (truncate i k x) x.
Proof.
intros i k.
revert i.
induct k.

(* one *)
{
intros i x.
cbn.
trivial.
}

(* type *)
{
intros w i A.
cbn [truncate].
apply iutruncate_near.
}

(* arrow *)
{
intros k1 _ k2 IH i f.
intros x.
cbn.
apply IH.
}

(* tarrow *)
{
intros w A k IH i f.
intros C.
cbn.
apply IH.
}

(* prod *)
{
intros k1 IH1 k IH2 i x.
destruct x as (x, y).
cbn.
split; cbn; [apply IH1 | apply IH2].
}

(* fut *)
{
intros k IH i x.
cbn.
destruct i as [| i].
  {
  apply dist_zero.
  }
cbn.
apply IH.
}
Qed.


Lemma truncate_collapse :
  forall i k (x y : spcar k),
    dist i x y
    -> truncate i k x = truncate i k y.
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
apply iutruncate_collapse; auto.
}

(* arrow *)
{
intros k1 _ k2 IH i f g Hfg.
apply exT_extensionality_prop.
cbn.
fextensionality 1.
intro x.
fold (space k1) in x.
apply IH.
apply Hfg.
}

(* tarrow *)
{
intros w A k2 IH i f g Hfg.
apply exT_extensionality_prop.
cbn.
fextensionality 1.
intro x.
apply IH.
apply Hfg.
}

(* prod *)
{
intros k1 IH1 k2 IH2 i x y Hxy.
destruct x as (x1, x2).
destruct y as (y1, y2).
destruct Hxy as (Hxy1, Hxy2).
cbn.
f_equal; [apply IH1 | apply IH2]; auto.
}

(* fut *)
{
intros k IH i x y Hxy.
apply IH.
destruct i as [| i].
  {
  cbn.
  apply dist_zero.
  }
cbn in Hxy |- *.
exact Hxy.
}
Qed.


Lemma truncate_idem :
  forall i k (x : spcar k),
    truncate i k (truncate i k x) = truncate i k x.
Proof.
intros i k x.
apply truncate_collapse.
apply truncate_near.
Qed.


Lemma extract_nonexpansive :
  forall i K (l : qkind) (f : car K -> spcar l),
    (forall j x y, j <= i -> dist j x y -> dist j (f x) (f y))
    -> existsT (f' : K -n> space l),
         forall x, dist i (f x) (pi1 f' x).
Proof.
intros i K l f Hsim.
assert (nonexpansive (fun x => truncate i l (f x))) as Hne.
  {
  intros j x y Hxy.
  so (le_ge_dec j i) as [Hji | Hij].
    {
    apply (truncate_nonexpansive i l).
    apply Hsim; auto.
    }

    {
    apply dist_refl'.
    apply truncate_collapse.
    apply Hsim; auto.
    eapply dist_downward_leq; eauto.
    }
  }
exists (expair _ Hne).
intro x.
cbn.
apply dist_symm.
apply truncate_near.
Qed.


(* This ought to be an instance of something more general, but the more general thing
   doesn't seem to be as good for rewriting.
*)
Lemma transport_truncate :
  forall i k k' (h : k = k') (x : spcar k),
    transport h spcar (truncate i k x) = truncate i k' (transport h spcar x).
Proof.
intros i k k' h x.
subst k'.
cbn.
reflexivity.
Qed.


Arguments meta_truncate {cur}.
Arguments meta_truncate_ne {cur}.
Arguments iutruncate {cur}.
Arguments iutruncate_ne {cur}.
