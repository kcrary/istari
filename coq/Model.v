
Require Import Axioms.
Require Import Tactics.
Require Import Equality.
Require Import Sigma.
Require Import Syntax.
Require Import Ofe.
Require Import Uniform.
Require Import Spaces.
Require Import Urelsp.
Require Import Ceiling.
Require Import Intensional.
Require Import Candidate.
Require Import Ordinal.


Lemma proj_embed_nearrow :
  forall (K1 K1' K2 K2' : ofe)
    (proj1 : K1 -n> K1') (embed1 : K1' -n> K1)
    (proj2 : K2 -n> K2') (embed2 : K2' -n> K2),
      (forall x, pi1 proj1 (pi1 embed1 x) = x)
      -> (forall x, pi1 proj2 (pi1 embed2 x) = x)
      -> forall f,
           nearrow_compose2 embed1 proj2 (nearrow_compose2 proj1 embed2 f) = f.
Proof.
intros K1 K1' K2 K2' proj1 embed1 proj2 embed2 Hpe1 Hpe2 f.
apply exT_extensionality_prop.
cbn.
fextensionality 1.
intro x.
rewrite -> Hpe2.
rewrite -> Hpe1.
reflexivity.
Qed.


Lemma embed_proj_nearrow :
  forall (K1 K1' K2 K2' : ofe)
    (proj1 : K1 -n> K1') (embed1 : K1' -n> K1)
    (proj2 : K2 -n> K2') (embed2 : K2' -n> K2)
    n,
      (forall x, dist n (pi1 embed1 (pi1 proj1 x)) x)
      -> (forall x, dist n (pi1 embed2 (pi1 proj2 x)) x)
      -> forall f,
           @dist (nearrow_ofe K1 K2) n (nearrow_compose2 proj1 embed2 (nearrow_compose2 embed1 proj2 f)) f.
Proof.
intros K1 K1' K2 K2' proj1 embed1 proj2 embed2 n Hep1 Hep2 f.
intros x.
cbn.
eapply dist_trans.
  {
  apply Hep2.
  }
apply (pi2 f).
apply Hep1.
Qed.


Definition space_inhabitant (k : qkind) : car (space k)
  :=
  qkind_rect spcar
    tt
    (fun w => (empty_urel, meta_nats (nat_nats 0)))
    (fun k1 _ k2 x => nearrow_const (space k1) (space k2) x)
    (fun w A k2 x => nearrow_const (urelsp A) (space k2) x)
    (fun _ x _ y => (x, y))
    (fun _ x => x)
    k.


(* 1-indexed *)
Fixpoint approx (i : nat) (k : qkind) { struct k } : qkind :=
  match k with
  | qone => qone
  | qtype w => qtype w
  | qarrow k1 k2 => qarrow (approx i k1) (approx i k2)
  | qtarrow w A k2 => qtarrow w (ceiling (S i) A) (approx i k2)
  | qprod k1 k2 => qprod (approx i k1) (approx i k2)
  | qfut k1 => 
      match i with
      | 0 => qfut qone
      | S i' => qfut (approx i' k1)
      end
  end
.


(* 1-indexed *)
Fixpoint embed_ne (i : nat) (k : qkind) { struct k } : space (approx i k) -n> space k
  :=
  match k with
  | qone =>
      expair (fun _ => tt) (const_nonexpansive _ _ _)

  | qtype w =>
      idne

  | qarrow k1 k2 =>
      nearrow_compose2_ne (proj_ne i k1) (embed_ne i k2)

  | qtarrow w A k2 =>
      nearrow_compose2_ne (proj_ceiling_ne (S i) (Nat.lt_0_succ i) A) (embed_ne i k2)

  | qprod k1 k2 =>
      mpair_ne (embed_ne i k1) (embed_ne i k2)

  | qfut k1 =>
      match i with
      | 0 =>
          nearrow_const _ _ (space_inhabitant _)

      | S i' =>
          nearrow_half _ _ (embed_ne i' k1)
      end
  end

with proj_ne (i : nat) (k : qkind) { struct k } : space k -n> space (approx i k)
  :=
  match k with
  | qone =>
      expair (fun _ => tt) (const_nonexpansive _ _ _)

  | qtype w =>
      idne

  | qarrow k1 k2 =>
      nearrow_compose2_ne (embed_ne i k1) (proj_ne i k2)

  | qtarrow w A k2 =>
      nearrow_compose2_ne (embed_ceiling_ne (S i) A) (proj_ne i k2)

  | qprod k1 k2 =>
      mpair_ne (proj_ne i k1) (proj_ne i k2)

  | qfut k1 =>
      match i with
      | 0 =>
           expair (fun _ => tt) (const_nonexpansive _ _ _)

      | S i' =>
          nearrow_half _ _ (proj_ne i' k1)
      end
  end.
  

Definition embed (i : nat) (k : qkind) := pi1 (embed_ne i k).
Definition proj (i : nat) (k : qkind) := pi1 (proj_ne i k).


Lemma embed_inhabitant :
  forall k i,
    embed i k (space_inhabitant (approx i k)) = space_inhabitant k.
Proof.
intro k.
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
reflexivity.
}

(* arrow *)
{
intros k1 _ k2 IH i.
apply exT_extensionality_prop.
fextensionality 1.
intro x.
change (car (space k1)) in x.
cbn.
apply IH.
}

(* tarrow *)
{
intros w A K IH i.
apply exT_extensionality_prop.
fextensionality 1.
intro x.
cbn.
apply IH.
}

(* prod *)
{
intros k1 IH1 k2 IH2 i.
cbn.
f_equal; [apply IH1 | apply IH2].
}

(* fut *)
{
intros k IH i.
destruct i as [| i].
  {
  cbn.
  reflexivity.
  }

  {
  cbn.
  apply IH.
  }
}
Qed.


Lemma proj_inhabitant :
  forall k i,
    proj i k (space_inhabitant k) = space_inhabitant (approx i k).
Proof.
intros k.
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
reflexivity.
}

(* arrow *)
{
intros k1 _ k2 IH i.
apply (exT_extensionality_prop (car (space (approx i k1)) -> car (space (approx i k2))) nonexpansive).
fextensionality 1.
intro x.
cbn.
apply IH.
}

(* tarrow *)
{
intros w A K IH i.
apply exT_extensionality_prop.
fextensionality 1.
intro x.
cbn.
apply IH.
}

(* prod *)
{
intros k1 IH1 k2 IH2 i.
cbn.
f_equal; [apply IH1 | apply IH2].
}

(* fut *)
{
intros k IH i.
destruct i as [| i].
  {
  cbn.
  reflexivity.
  }
cbn.
apply IH.
}
Qed.


Lemma proj_embed :
  forall i k x,
    proj i k (embed i k x) = x.
Proof.
intros i k.
revert i.
induct k.

(* one *)
{
intros i x.
cbn.
destruct x.
reflexivity.
}

(* type *)
{
intros w i x.
cbn.
reflexivity.
}

(* arrow *)
{
intros k1 IH1 k2 IH2 i x.
unfold proj, embed in IH1, IH2 |- *.
cbn.
apply proj_embed_nearrow; auto.
}

(* tarrow *)
{
intros w A k2 IH i f.
unfold proj, embed in IH |- *.
cbn [proj_ne embed_ne].
apply proj_embed_nearrow; auto.
intro x.
apply proj_embed_ceiling.
}

(* prod *)
{
intros k1 IH1 k2 IH2 i x.
destruct x as (x, y).
cbn.
fold (proj i k1).
fold (embed i k1).
fold (proj i k2).
fold (embed i k2).
rewrite -> IH1.
rewrite -> IH2.
reflexivity.
}

(* fut *)
{
intros k IH i x.
unfold proj, embed in IH |- *.
destruct i as [| i].
  {
  cbn [proj embed pi1].
  destruct x.
  reflexivity.
  }

  {
  cbn [proj embed].
  unfold nearrow_half.
  cbn [pi1].
  apply IH.
  }
}
Qed.


Lemma embed_proj :
  forall i k x,
    dist (S i) (embed i k (proj i k x)) x.
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
intros w i x.
cbn [embed proj idne pi1].
apply dist_refl.
}

(* arrow *)
{
intros k1 IH1 k2 IH2 i f.
unfold proj, embed in IH1, IH2 |- *.
cbn [embed_ne proj_ne].
apply embed_proj_nearrow; auto.
}

(* tarrow *)
{
intros w A k2 IH i f.
unfold proj, embed in IH |- *.
cbn [embed_ne proj_ne].
apply embed_proj_nearrow; auto.
intro x.
apply embed_proj_ceiling.
}

(* prod *)
{
intros k1 IH1 k2 IH2 i x.
destruct x as (x, y).
cbn.
fold (proj i k1).
fold (embed i k1).
fold (proj i k2).
fold (embed i k2).
split; cbn; auto.
}

(* fut *)
{
intros k IH i x.
destruct i as [| i ].
  {
  cbn.
  apply dist_zero.
  }

  {
  cbn.
  apply IH.
  }
}
Qed.


Lemma ceiling_combine :
  forall w i j (A : wurel w),
    ceiling i (ceiling j A) = ceiling (min i j) A.
Proof.
intros w i j A.
apply urel_extensionality.
cbn.
fextensionality 3.
intros k m n.
pextensionality.
  {
  intros (Hki & Hkh & Hmn).
  split; auto.
  apply Nat.min_glb; auto.
  }

  {
  intros (Hk & Hmn).
  so (Nat.min_glb_iff _#3 andel Hk) as (Hki & Hkj).
  auto.
  }
Qed.


Lemma ceiling_combine_le :
  forall w i j (A : wurel w),
    i <= j
    -> ceiling i (ceiling j A) = ceiling i A.
Proof.
intros w  i j A Hle.
rewrite <- (Min.min_l _ _ Hle) at 2.
apply ceiling_combine.
Qed.


Lemma ceiling_idem :
  forall w i (A : wurel w),
    ceiling i (ceiling i A) = ceiling i A.
Proof.
intros w i A.
apply ceiling_combine_le; auto.
Qed.


Lemma approx_combine :
  forall i j k,
    approx i (approx j k) = approx (min i j) k.
Proof.
intros i j k.
revert i j.
induct k; auto.

(* arrow *)
{
intros k1 IH1 k2 IH2 i j.
cbn.
f_equal; auto.
}

(* tarrow *)
{
intros w A k IH i j.
cbn.
f_equal; auto.
apply ceiling_combine.
}

(* prod *)
{
intros k1 IH1 k2 IH2 i j.
cbn.
f_equal; auto.
}

(* fut *)
{
intros k IH i j.
destruct i as [| i]; destruct j as [| j]; auto.
cbn.
f_equal; auto.
}
Qed.


Lemma approx_combine_le :
  forall i j k,
    i <= j
    -> approx i (approx j k) = approx i k.
Proof.
intros i j k Hle.
rewrite <- (Min.min_l _ _ Hle) at 2.
apply approx_combine.
Qed.


Lemma approx_idem :
  forall i k,
    approx i (approx i k) = approx i k.
Proof.
intros i k.
rewrite -> approx_combine.
rewrite -> Min.min_idempotent.
reflexivity.
Qed.


Lemma embed_ceiling_combine :
  forall w i j R x,
    embed_ceiling j R (embed_ceiling i (ceiling j R) x)
    =
    embed_ceiling (min i j) R (transport (ceiling_combine w i j R) urelsp_car x).
Proof.
intros w i j R x.
apply exT_extensionality_prop.
cbn.
destruct x as (P & HP).
cbn.
fextensionality 2.
revert P HP.
cut (forall A B (h : A = B) P HP k m,
       P k m
       =
       pi1 (transport h (@urelsp_car (obj w)) (expair P HP)) k m).
  {
  intros Hprop P HP k m.
  apply (Hprop (ceiling i (ceiling j R)) (ceiling (min i j) R)).
  }
intros A B h P HP k m.
subst B.
cbn.
reflexivity.
Qed.


Lemma proj_ceiling_combine :
  forall w i j hi hj R x,
    proj_ceiling i hi (ceiling j R) (proj_ceiling j hj R x)
    =
    transport (eqsymm (ceiling_combine w i j R)) urelsp_car (proj_ceiling (min i j) (Nat.min_glb _ _ _ hi hj) R x).
Proof.
intros w i j hi hj R x.
apply exT_extensionality_prop.
cbn.
destruct x as (P & HP).
cbn.
fextensionality 2.
rewrite -> (pi1_transport_lift (wurel w) (nat -> term (obj w) -> Prop) urelsp_car_rhs (ceiling (min i j) R) (ceiling i (ceiling j R))).
intros k m.
cbn.
pextensionality.
  {
  intros (Hki & Hkj & Hm).
  split; auto.
  apply Nat.min_glb; auto.
  }

  {
  intros (Hk & Hm).
  rewrite -> Nat.min_glb_lt_iff in Hk.
  destruct Hk.
  do2 2 split; auto.
  }
Qed.


Lemma embed_ceiling_combine_le :
  forall w i j R x (h : i <= j),
    embed_ceiling j R (embed_ceiling i (ceiling j R) x)
    =
    embed_ceiling i R (transport (ceiling_combine_le w i j R h) urelsp_car x).
Proof.
intros w i j R x h.
apply exT_extensionality_prop.
cbn.
destruct x as (P & HP).
cbn.
fextensionality 2.
revert P HP.
cut (forall A B (h : A = B) P HP k m,
       P k m
       =
       pi1 (transport h (@urelsp_car (obj w)) (expair P HP)) k m).
  {
  intros Hprop P HP k m.
  apply (Hprop (ceiling i (ceiling j R)) (ceiling i R)).
  }
intros A B h' P HP k m.
subst B.
cbn.
reflexivity.
Qed.


Lemma embed_ceiling_combine_ge :
  forall w i j R x (h : j <= i),
    embed_ceiling j R (embed_ceiling i (ceiling j R) x)
    =
    embed_ceiling j R (transport (ceiling_combine_ge w i j R h) urelsp_car x).
Proof.
intros w i j R x h.
apply exT_extensionality_prop.
cbn.
destruct x as (P & HP).
cbn.
fextensionality 2.
revert P HP.
cut (forall A B (h : A = B) P HP k m,
       P k m
       =
       pi1 (transport h (@urelsp_car (obj w)) (expair P HP)) k m).
  {
  intros Hprop P HP k m.
  apply (Hprop (ceiling i (ceiling j R)) (ceiling j R)).
  }
intros A B h' P HP k m.
subst B.
cbn.
reflexivity.
Qed.


Lemma proj_embed_combine :
  (forall i j k x,
     proj i (approx j k) (proj j k x)
     =
     transport (eqsymm (approx_combine i j k)) spcar (proj (min i j) k x))
  /\
  (forall i j k x,
     embed j k (embed i (approx j k) x)
     =
     embed (min i j) k (transport (approx_combine i j k) spcar x)).
Proof.
cut (forall k,
       (forall i j x,
          proj i (approx j k) (proj j k x)
          =
          transport (eqsymm (approx_combine i j k)) spcar (proj (min i j) k x))
       /\
       (forall i j x,
          embed j k (embed i (approx j k) x)
          =
          embed (min i j) k (transport (approx_combine i j k) spcar x))).
  {
  intros Hprop.
  split.
    {
    intros i j k x.
    apply (Hprop k).
    }

    {
    intros i j k x.
    apply (Hprop k).
    }
  }
intro k.
induct k.

(* one *)
{
split; intros; cbn; trivial.
replace (approx_combine i j qone) with (eq_refl qone) by (apply proof_irrelevance).
cbn.
reflexivity.
}

(* type *)
{
intro w.
split.
  {
  intros i j R.
  cbn in R.
  cbn.
  symmetry.
  apply heq_impl_eq.
  apply (heq_transport _ spcar _ _ (eqsymm (approx_combine i j (qtype w)))).
  }

  {
  intros i j R.
  cbn in R.
  cbn.
  apply heq_impl_eq.
  apply heq_symm.
  apply (heq_transport _ spcar _ _ (approx_combine i j (qtype w))).
  }
}

(* arrow *)
{
intros k1 IH1 k2 IH2.
split.
  {
  intros i j f.
  cbn in f.
  cbn [approx].
  apply exT_extensionality_prop.
  fextensionality 1.
  intro x.
  change (spcar (approx i (approx j k1))) in x.
  cbn.
  unfold proj, embed in IH1, IH2.
  rewrite -> (IH1 ander).
  rewrite -> (IH2 andel).
  revert f x.
  cut (forall (l1 l1' l1'' l2 l2' l2'' : qkind)
         (h1 : l1'' = l1')
         (h2 : l2' = l2'')
         (h : qarrow l1' l2' = qarrow l1'' l2'')
         (g1 : space l1' -n> space l1)
         (g2 : space l2 -n> space l2')
         (f : space l1 -n> space l2)
         (x : spcar l1''),
               transport h2 spcar (pi1 g2 (pi1 f (pi1 g1 (transport h1 spcar x))))
               =
               pi1 (transport h spcar (nearrow_compose2 g1 g2 f)) x).
    {
    intros Hprop f x.
    apply Hprop.
    }
  intros l1 l1' l1'' l2 l2' l2'' h1 h2 h g1 g2 f x.
  subst l1'' l2''.
  substrefl h.
  cbn.
  reflexivity.
  }

  {
  intros i j f.
  cbn in f.
  cbn [approx].
  apply exT_extensionality_prop.
  fextensionality 1.
  intro x.
  change (spcar k1) in x.
  cbn.
  unfold proj, embed in IH1, IH2.
  rewrite -> (IH1 andel).
  rewrite -> (IH2 ander).
  f_equal.
  set (y := pi1 (proj_ne (min i j) k1) x).
  clearbody y.
  clear x.
  revert f y.
  cut (forall (l1 l1' l2 l2' : qkind)
         (h1 : l1' = l1)
         (h2 : l2 = l2')
         (h : qarrow l1 l2 = qarrow l1' l2')
         (f : space l1 -n> space l2)
           (x : spcar l1'),
             transport h2 spcar (pi1 f (transport h1 spcar x))
             =
             pi1 (transport h spcar f) x).
    {
    intros Hprop f x.
    apply Hprop.
    }
  intros l1 l1' l2 l2' h1 h2 h f x.
  subst l1' l2'.
  substrefl h.
  reflexivity.
  }
}

(* tarrow *)
{
intros w A k IH.
split.
  {
  intros i j f.
  cbn in f.
  cbn [approx].
  apply exT_extensionality_prop.
  fextensionality 1.
  intro x.
  cbn.
  unfold proj, embed in IH.
  rewrite -> (IH andel).
  rewrite -> embed_ceiling_combine.
  revert f x.
  cut (forall (R1 R2 R3 : wurel w) (l1 l2 l3 : qkind)
         (h1 : R3 = R2)
         (h2 : l2 = l3)
         (h : qtarrow w R2 l2 = qtarrow w R3 l3)
         (g1 : urelsp R2 -n> urelsp R1)
         (g2 : space l1 -n> space l2)
         (f : urelsp R1 -n> space l1)
         (x : urelsp_car R3),
           transport h2 spcar (pi1 g2 (pi1 f (pi1 g1 (transport h1 urelsp_car x))))
           =
           pi1 (transport h spcar (nearrow_compose2 g1 g2 f)) x).
    {
    intros Hprop f x.
    apply (Hprop _#9 (embed_ceiling_ne (S (min i j)) A)).
    }
  intros R1 R2 R3 l1 l2 l3 h1 h2 h g1 g2 f x.
  subst R3 l3.
  substrefl h.
  cbn.
  reflexivity.
  }

  {
  intros i j f.
  cbn in f.
  cbn [approx].
  apply exT_extensionality_prop.
  fextensionality 1.
  intro x.
  cbn.
  unfold proj, embed in IH.
  rewrite -> (IH ander).
  rewrite -> proj_ceiling_combine.
  f_equal.
  rewrite -> (proof_irrelevance _
                (Nat.min_glb _#3 (Nat.lt_0_succ i) (Nat.lt_0_succ j))
                (Nat.lt_0_succ (min i j))).
  cbn.
  set (y := proj_ceiling (S (min i j)) (Nat.lt_0_succ (min i j)) A x).
  clearbody y.
  clear x.
  revert f y.
  cut (forall (R R' : wurel w) (l l' : qkind)
         (h1 : R' = R)
         (h2 : l = l')
         (h : qtarrow w R l = qtarrow w R' l')
         (f : urelsp R -n> space l)
         (x : urelsp_car R'),
           transport h2 spcar (pi1 f (transport h1 urelsp_car x))
           =
           pi1 (transport h spcar f) x).
    {
    intros Hprop f x.
    apply Hprop.
    }
  intros R R' l l' h1 h2 h f x.
  subst R' l'.
  substrefl h.
  cbn.
  reflexivity.
  }
}

(* prod *)
{
intros k1 IH1 k2 IH2.
split.
  {
  intros i j x.
  destruct x as (x, y).
  cbn.
  fold (proj i (approx j k1)).
  fold (proj j k1).
  fold (proj i (approx j k2)).
  fold (proj j k2).
  fold (proj (min i j) k1).
  fold (proj (min i j) k2).
  rewrite -> (IH1 andel).
  rewrite -> (IH2 andel).
  revert x y.
  cut (forall l1 l1' l2 l2'
         (h1 : l1 = l1')
         (h2 : l2 = l2')
         (h : qprod l1 l2 = qprod l1' l2')
         (x : spcar l1)
         (y : spcar l2),
           (transport h1 spcar x, transport h2 spcar y)
           =
           transport h spcar (x, y)).
    {
    intros Hprop x y.
    apply Hprop.
    }
  intros l1 l1' l2 l2' h1 h2 h x y.
  subst l1' l2'.
  substrefl h.
  reflexivity.
  }

  {
  intros i j x.
  destruct x as (x, y).
  cbn.
  fold (embed j k1).
  fold (embed i (approx j k1)).
  fold (embed j k2).
  fold (embed i (approx j k2)).
  fold (embed (min i j) k1).
  fold (embed (min i j) k2).
  rewrite -> (IH1 ander).
  rewrite -> (IH2 ander).
  f_equal.
    {
    f_equal.
    revert x y.
    cut (forall l1 l1' l2 l2'
           (h1 : l1 = l1')
           (h2 : l2 = l2')
           (h : qprod l1 l2 = qprod l1' l2')
           (x : spcar l1)
           (y : spcar l2),
             transport h1 spcar x
             =
             fst (transport h spcar (x, y))).
      {
      intros Hprop x y.
      apply Hprop.
      apply approx_combine.
      }
    intros l1 l1' l2 l2' h1 h2 h x y.
    subst l1' l2'.
    substrefl h.
    reflexivity.
    }

    {
    f_equal.
    revert x y.
    cut (forall l1 l1' l2 l2'
           (h1 : l1 = l1')
           (h2 : l2 = l2')
           (h : qprod l1 l2 = qprod l1' l2')
           (x : spcar l1)
           (y : spcar l2),
             transport h2 spcar y
             =
             snd (transport h spcar (x, y))).
      {
      intros Hprop x y.
      apply Hprop.
      apply approx_combine.
      }
    intros l1 l1' l2 l2' h1 h2 h x y.
    subst l1' l2'.
    substrefl h.
    reflexivity.
    }
  }
}

(* fut *)
{
intros k IH.
split.
  {
  intros i j x.
  cbn in x.
  cbn [approx].
  destruct i as [| i]; destruct j as [| j]; cbn.
    {
    replace (approx_combine 0 0 (qfut k)) with (eq_refl (qfut qone)) by (apply proof_irrelevance).
    cbn.
    reflexivity.
    }

    {
    replace (approx_combine 0 (S j) (qfut k)) with (eq_refl (qfut qone)) by (apply proof_irrelevance).
    cbn.
    reflexivity.
    }

    {
    replace (approx_combine (S i) 0 (qfut k)) with (eq_refl (qfut qone)) by (apply proof_irrelevance).
    cbn.
    reflexivity.
    }
  unfold proj, embed in IH.
  rewrite -> (IH andel).
  set (y := pi1 (proj_ne (min i j) k) x).
  clearbody y.
  clear x.
  revert y.
  cut (forall (l l' : qkind)
         (h : l = l')
         (h' : qfut l = qfut l')
         (x : spcar l),
           transport h spcar x
           =
           transport h' spcar x).
    {
    intros Hprop x.
    apply Hprop.
    }
  intros l l' h h' x.
  subst l'.
  substrefl h'.
  reflexivity.
  }

  {
  intros i j x.
  cbn in x.
  cbn [approx].
  destruct i as [| i]; destruct j as [| j]; cbn; auto.
    {
    apply embed_inhabitant.
    }
  unfold proj, embed in IH.
  rewrite -> (IH ander).
  f_equal.
  revert x.
  cut (forall (l l' : qkind)
         (h : l = l')
         (h' : qfut l = qfut l')
         (x : spcar l),
           transport h spcar x
           =
           transport h' spcar x).
    {
    intros Hprop x.
    apply Hprop.
    }
  intros l l' h h' x.
  subst l'.
  substrefl h'.
  reflexivity.
  }
}
Qed.


Lemma proj_combine :
  forall i j k x,
    proj i (approx j k) (proj j k x)
    =
    transport (eqsymm (approx_combine i j k)) spcar (proj (min i j) k x).
Proof.
exact (proj_embed_combine andel).
Qed.


Lemma embed_combine :
  forall i j k x,
    embed j k (embed i (approx j k) x)
    =
    embed (min i j) k (transport (approx_combine i j k) spcar x).
Proof.
exact (proj_embed_combine ander).
Qed.


Lemma proj_combine_le :
  forall i j k x (Hle : i <= j),
    proj i (approx j k) (proj j k x)
    =
    transport (eqsymm (approx_combine_le i j k Hle)) spcar (proj i k x).
Proof.
intros i j k x Hle.
rewrite -> proj_combine.
set (h := approx_combine i j k).
clearbody h.
set (i' := min i j) in * |- *.
assert (i' = i).
  {
  apply Nat.min_l; auto.
  }
clearbody i'.
subst i'.
f_equal.
apply UIP.
Qed.


Lemma proj_combine_le' :
  forall i j k x (Hle : i <= j),
    transport (approx_combine_le i j k Hle) spcar (proj i (approx j k) (proj j k x))
    =
    proj i k x.
Proof.
intros i j k x Hle.
so (proj_combine_le i j k x Hle) as H1.
so (f_equal (fun z => transport (approx_combine_le i j k Hle) spcar z) H1) as H2.
cbn in H2.
rewrite -> transport_compose in H2.
replace (eqtrans (eqsymm (approx_combine_le i j k Hle)) (approx_combine_le i j k Hle)) with (eq_refl (approx i k)) in H2 by (apply UIP).
cbn in H2.
exact H2.
Qed.


Lemma embed_combine_le :
  forall i j k x (Hle : i <= j),
    embed j k (embed i (approx j k) x)
    =
    embed i k (transport (approx_combine_le i j k Hle) spcar x).
Proof.
intros i j k x Hle.
rewrite -> embed_combine.
set (h := approx_combine i j k).
clearbody h.
set (i' := min i j) in * |- *.
assert (i' = i).
  {
  apply Nat.min_l; auto.
  }
clearbody i'.
subst i'.
f_equal.
f_equal.
apply UIP.
Qed.


Lemma embed_combine_le' :
  forall i j k x (Hle : i <= j),
    embed j k (embed i (approx j k) (transport (eqsymm (approx_combine_le i j k Hle)) spcar x))
    =
    embed i k x.
Proof.
intros i j k x Hle.
so (embed_combine_le _#3 (transport (eqsymm (approx_combine_le i j k Hle)) spcar x) Hle) as H.
rewrite -> transport_compose in H.
replace (eqtrans (eqsymm (approx_combine_le i j k Hle)) (approx_combine_le i j k Hle)) with (eq_refl (approx i k)) in H by (apply UIP).
exact H.
Qed.


Lemma proj_idem :
  forall i k x,
    proj i (approx i k) (proj i k x)
    =
    transport (eqsymm (approx_idem i k)) spcar (proj i k x).
Proof.
intros i k x.
rewrite -> (proj_combine_le _#4 (le_refl _)).
f_equal.
apply UIP.
Qed.


Lemma proj_idem' :
  forall i k x,
    proj i k x
    =
    transport (approx_idem i k) spcar (proj i (approx i k) (proj i k x)).
Proof.
intros i k x.
apply (transport_symm' _ spcar).
symmetry.
apply proj_idem.
Qed.


Lemma embed_idem :
  forall i k x,
    embed i k (embed i (approx i k) x)
    =
    embed i k (transport (approx_idem i k) spcar x).
Proof.
intros i k x.
rewrite -> (embed_combine_le _#4 (le_refl _)).
f_equal.
f_equal.
apply UIP.
Qed.


Lemma proj_near :
  forall k i (x : spcar (approx i k)),
    transport (approx_idem i k) spcar (proj i (approx i k) x) = x.
Proof.
intros k i x.
symmetry.
rewrite <- (proj_embed i k x).
rewrite -> proj_idem' at 1.
reflexivity.
Qed.


Lemma proj_transport :
  forall i k l (h : k = l) (x : spcar k),
    proj i l (transport h spcar x)
    =
    transport (f_equal (approx i) h) spcar (proj i k x).
Proof.
intros i k l h x.
subst .
cbn.
reflexivity.
Qed.


Lemma transport_embed :
  forall i k l (h : k = l) x,
    transport h spcar (embed i k x)
    =
    embed i l (transport (f_equal (approx i) h) spcar x).
Proof.
intros i k l h x.
subst l.
reflexivity.
Qed.


Lemma proj_near' :
  forall k i (x : spcar k) (h : approx i k = k),
    transport h spcar (proj i k x) = x.
Proof.
intros k i x h.
replace x with (transport h spcar (transport (eqsymm h) spcar x)).
2:{
  rewrite -> transport_compose.
  replace (eqtrans (eqsymm h) h) with (eq_refl k) by (apply UIP).
  cbn.
  reflexivity.
  }
set (y := transport (eqsymm h) spcar x).
clearbody y.
f_equal.
rewrite -> proj_transport.
replace (f_equal (approx i) h) with (approx_idem i k) by (apply UIP).
apply proj_near.
Qed.    


Lemma proj_approx_inj :
  forall i K x y,
    K = approx i K
    -> proj i K x = proj i K y
    -> x = y.
Proof.
intros i K x y HeqK Heq.
rewrite <- (proj_near' K i x (eqsymm HeqK)).
rewrite <- (proj_near' K i y (eqsymm HeqK)).
f_equal; auto.
Qed.


Lemma proj_embed_down :
  forall i j k (x : spcar (approx i k)) (Hle : j <= i),
    proj j k (embed i k x)
    =
    transport (approx_combine_le j i k Hle) spcar (proj j (approx i k) x).
Proof.
intros i j k x Hle.
rewrite <- (proj_combine_le' j i k (embed i k x) Hle).
f_equal.
rewrite -> proj_embed.
reflexivity.
Qed.


Lemma proj_embed_up :
  forall i j k (x : spcar (approx i k)) (Hle : i <= j),
    proj j k (embed i k x)
    =
    embed i (approx j k) (transport (eqsymm (approx_combine_le i j k Hle)) spcar x).
Proof.
intros i j k x Hle.
rewrite <- (embed_combine_le' i j k x Hle).
rewrite -> proj_embed.
reflexivity.
Qed.


Lemma embed_ceiling_urelspinj :
  forall w i (A : wurel w) j m n Hmn Hle,
    embed_ceiling i A (urelspinj (ceiling i A) j m n (conj Hle Hmn))
    =
    urelspinj A j m n Hmn.
Proof.
intros w i A j m n Hmn Hle.
apply exT_extensionality_prop.
cbn.
fextensionality 2.
intros j' p.
pextensionality; intro H; destruct_all H; repeat2 split; auto; omega.
Qed.


Lemma proj_ceiling_urelspinj :
  forall w i (A : wurel w) j m n Hmn (Hlt : j < i),
    proj_ceiling i (Nat.lt_lt_0 _ _ Hlt) A (urelspinj A j m n Hmn)
    =
    urelspinj (ceiling i A) j m n (conj Hlt Hmn).
Proof.
intros w i A j m n Hmn Hle.
apply exT_extensionality_prop.
cbn.
fextensionality 2.
intros j' p.
pextensionality; intro H; destruct_all H; repeat2 split; auto; omega.
Qed.


Lemma proj_eq_dist :
  forall k i x y,
    proj i k x = proj i k y
    -> dist (S i) x y.
Proof.
intros k i x y Heq.
eapply dist_trans.
  {
  apply dist_symm.
  apply embed_proj.
  }
eapply dist_trans.
2:{
  apply embed_proj.
  }
apply dist_refl'.
f_equal; auto.
Qed.


Lemma proj_dist_dist :
  forall k i x y,
    dist (S i) (proj i k x) (proj i k y)
    -> dist (S i) x y.
Proof.
intros k i x y Heq.
eapply dist_trans.
  {
  apply dist_symm.
  apply embed_proj.
  }
eapply dist_trans.
2:{
  apply embed_proj.
  }
apply (pi2 (embed_ne i k)).
auto.
Qed.



Lemma embed_approx :
  forall i K (x : spcar (approx i K)) (h : approx i K = K),
    embed i K x = transport h spcar x.
Proof.
intros i K x h.
assert (approx i K = approx i (approx i K)) as h'.
  {
  f_equal; auto.
  }
assert (embed i K (embed i (approx i K) (transport h' spcar x)) = embed i K x) as Heq.
  {
  rewrite -> embed_idem.
  f_equal.
  rewrite -> transport_compose.
  rewrite -> (proof_irrelevance _ _ (eq_refl (approx i K))).
  reflexivity.
  }
so (f_equal (proj i K) Heq) as Heq1.
rewrite -> !proj_embed in Heq1.
so (f_equal (transport h spcar) Heq1) as Heq2.
rewrite <- Heq2.
clear Heq Heq1 Heq2.
revert h h'.
cut (forall K' (h : K' = K) (h' : approx i K = approx i K'),
       embed i K x = transport h spcar (embed i K' (transport h' spcar x))).
  {
  intro Hcond.
  apply Hcond.
  }
intros K' h h'.
subst K'.
substrefl h'.
cbn.
reflexivity.
Qed.    


Lemma embed_approx' :
  forall i K (x : spcar K) (h : K = approx i K),
    embed i K (transport h spcar x) = x.
Proof.
intros i K x h.
rewrite -> (embed_approx _#3 (eqsymm h)).
rewrite -> transport_compose.
rewrite -> (proof_irrelevance _ _ (eq_refl _)).
reflexivity.
Qed.


Lemma approx_level :
  forall i k,
    level (approx i k) <<= level k.
Proof.
intros i k.
revert i.
induct k; try (intros; cbn; eauto using le_ord_refl, max_ord_mono; done).

(* fut *)
{
intros k IH i.
cbn.
destruct i as [| i]; cbn; auto.
apply le_ord_zero.
}
Qed.


Lemma approx_level_lt :
  forall i k w,
    level k << w
    -> level (approx i k) << w.
Proof.
intros i k w Hlt.
eapply le_lt_ord_trans; eauto.
apply approx_level.
Qed.


Definition projc (i : nat) (Q : candidate) : candidate
  :=
  expair (approx i (pi1 Q)) (proj i (pi1 Q) (pi2 Q)).


Lemma projc_combine_le :
  forall i j (Q : candidate),
    i <= j
    -> projc i (projc j Q) = projc i Q.
Proof.
intros i j Q Hle.
unfold projc.
cbn.
symmetry.
cut (forall K K' (h : K = K') (x : spcar K) (x' : spcar K'),
       transport h spcar x = x'
       -> @expair _ spcar K (x) = expair K' (x')).
  {
  intros H.
  apply (H _ _ (eqsymm (approx_combine_le _#3 Hle))).
  symmetry.
  apply proj_combine_le.
  }
intros K K' h x x' ?.
subst K'.
subst x'.
reflexivity.
Qed.


Lemma projc_idem :
  forall i (Q : candidate),
    projc i (projc i Q) = projc i Q.
Proof.
intros i Q.
apply projc_combine_le.
apply le_refl.
Qed.


Lemma projc_expair_approx :
  forall i K x,
    projc i (expair (approx i K) x) = expair (approx i K) x.
Proof.
intros i K x.
unfold projc.
cbn.
apply expair_compat_dep.
apply (eq_impl_eq_dep _#6 (approx_idem i K)).
apply proj_near.
Qed.
