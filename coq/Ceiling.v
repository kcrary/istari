
Require Import Axioms.
Require Import Tactics.
Require Import Equality.
Require Import Sigma.
Require Import Syntax.
Require Import Ofe.
Require Import Uniform.
Require Import Urelsp.
Require Import Ordinal.
Require Import Candidate.


Section level.


Arguments operator {object}.
Arguments term {object}.
Arguments row {object}.
Arguments urel {object}.
Arguments urel_ofe {object}.


Variable cur : ordinal.


Lemma ceiling_uniform :
  forall (R : wurel cur) i,
    @uniform (obj cur) (fun j m n => j < i /\ rel R j m n).
Proof.
intros R i.
do2 3 split.
  {
  intros j m n (_ & Hmn).
  eapply urel_closed; eauto.
  }

  {
  intros j m m' n n' Hclm Hcln Heqm Heqn (Hle & Hmn).
  split; auto; [].
  eapply urel_equiv; eauto.
  }

  {
  intros j m n p q (Hle & Hmn) (_ & Hpn) (_ & Hpq).
  split; auto; [].
  eapply urel_zigzag; eauto.
  }

  {
  intros j m n (Hlt & Hmn).
  split; [omega |].
  eapply urel_downward; eauto.
  }
Qed.


Definition ceiling (i : nat) (R : wurel cur) : wurel cur :=
  mk_urel _ (ceiling_uniform R i).


Lemma ceiling_nonexpansive :
  forall n, @nonexpansive (wurel_ofe cur) (wurel_ofe cur) (ceiling n).
Proof.
intros n i A B Hdist.
intros j Hj.
fextensionality 2.
intros m p.
cbn.
pextensionality; intros (Hj' & H); split; auto.
  {
  rewrite <- Hdist; auto.
  }

  {
  rewrite -> Hdist; auto.
  }
Qed.


Definition ceiling_ne (n : nat) : wurel_ofe cur -n> wurel_ofe cur
  :=
  expair (ceiling n) (ceiling_nonexpansive n).


Definition embed_ceiling (i : nat) (R : wurel cur) (P : car (urelsp (ceiling i R))) : car (urelsp R).
Proof.
refine (expair (pi1 P) _).
destruct P as (P & H).
destruct H as (j & m & p & Hmp & HP).
cbn.
exists j, m, p.
split.
  {
  destruct Hmp as (Hji & Hmp).
  exact Hmp.
  }

  {
  intros k n.
  split.
    {
    intro Hn.
    so (HP k n andel Hn) as (Hkj & Hnp).
    split; auto.
    destruct Hnp.
    auto.
    }

    {
    intros (Hkj & Hnp).
    exploit (HP k n ander); auto.
    split; auto.
    split; auto.
    destruct Hmp.
    omega.
    }
  }
Defined.


Lemma embed_ceiling_nonexpansive :
  forall i R,
    nonexpansive (embed_ceiling i R).
Proof.
intros R i.
intros j x y Hxy.
intros k Hkj.
cbn.
apply Hxy; auto.
Qed.


Definition embed_ceiling_ne (i : nat) (R : wurel cur) : urelsp (ceiling i R) -n> urelsp R
  :=
  expair (embed_ceiling i R) (embed_ceiling_nonexpansive i R).


(* This positivity premise is the unfortunate consequence of 1-indexing urelsp. *)
Definition proj_ceiling (i : nat) (Hpos : i > 0) (R : wurel cur) (C : car (urelsp R)) 
  : car (urelsp (ceiling i R)).
Proof.
exists (fun j m => j < i /\ pi1 C j m).
destruct C as (P & H).
destruct H as (j & m & p & Hmp & HP).
cbn.
so (le_lt_dec i j) as [Hij | Hji].
2:{
  exists j, m, p.
  split; [split |]; auto.
  intros k n.
  split.
    {
    intros (Hki & Hn).
    so (HP _ _ andel Hn) as (Hkj & Hnp).
    auto.
    }

    {
    intros (Hkj & Hki & Hnp).
    split; auto.
    apply HP.
    auto.
    }
  }

  {
  exists (pred i), m, p.
  split; [split |]; auto.
    {
    omega.
    }

    {
    apply (urel_downward_leq _ _ _ j); eauto.
    omega.
    }

    {
    intros k n.
    split.
      {
      intros (Hki & Hn).
      so (HP _ _ andel Hn) as (Hkj & Hnp).
      do2 2 split; auto.
      omega.
      }

      {
      intros (Hki & _ & Hnp).
      split; [omega |].
      apply HP.
      split; auto.
      omega.
      }
    }
  }
Defined.


Lemma proj_ceiling_nonexpansive :
  forall i h R,
    nonexpansive (proj_ceiling i h R).
Proof.
intros i h R.
intros j x y Hxy.
intros k Hkj.
cbn.
fextensionality 1.
intro m.
pextensionality.
  {
  intros (Hki & Hm).
  split; auto.
  rewrite <- (Hxy k Hkj).
  exact Hm.
  }

  {
  intros (Hki & Hm).
  split; auto.
  rewrite -> (Hxy k Hkj).
  exact Hm.
  }
Qed.


Definition proj_ceiling_ne (i : nat) (h : i > 0) (R : wurel cur) : urelsp R -n> urelsp (ceiling i R)
  :=
  expair (proj_ceiling i h R) (proj_ceiling_nonexpansive i h R).


Lemma proj_embed_ceiling :
  forall i h R (P : car (urelsp (ceiling i R))),
    proj_ceiling i h R (embed_ceiling i R P) = P.
Proof.
intros i h R P.
apply exT_extensionality_prop.
cbn.
fextensionality 2.
intros j m.
pextensionality.
  {
  intros (_ & ?); auto.
  }

  {
  intro Hm.
  destruct P as (P & H).
  destruct H as (k & n & p & Hnp & HP).
  cbn in Hm |- *.
  destruct Hnp as (Hki & Hnp).
  so (HP _ _ andel Hm) as (Hjk & _).
  split; auto.
  omega.
  }
Qed.


Lemma embed_proj_ceiling :
  forall i h R (P : car (urelsp R)),
    dist i (embed_ceiling i R (proj_ceiling i h R P)) P.
Proof.
intros i h R P.
destruct P as (P & H).
destruct H as (j & m & p & Hmp & HP).
intros k Hki.
cbn.
fextensionality 1.
intros n.
pextensionality.
  {
  intros (_ & ?); auto.
  }

  {
  intros Hkn.
  split; auto.
  }
Qed.


Lemma urelsp_index_embed_ceiling :
  forall i (A : wurel cur) P,
    urelsp_index A (embed_ceiling i A P) = urelsp_index (ceiling i A) P.
Proof.
intros i A P.
unfold urelsp_index.
set (X := urelsp_index_unique _ A (embed_ceiling i A P)).
destruct X as (h & Hh & Hhonly).
rewrite -> description_beta.
set (X := urelsp_index_unique _ (ceiling i A) P).
destruct X as (j' & Hh' & Hhonly').
rewrite -> description_beta.
apply Hhonly.
destruct Hh' as (m & p & Hmp & ->).
destruct Hmp as (Hle & Hmp).
exists m, p, Hmp.
apply exT_extensionality_prop.
cbn.
fextensionality 2.
intros j n.
pextensionality.
  {
  intros (H1 & _ & H2); auto.
  }

  {
  intros (H1 & H2); do2 2 split; auto; omega.
  }
Qed.


Lemma urelsp_index_proj_ceiling :
  forall i (Hpos : i > 0) (A : wurel cur) P,
    urelsp_index (ceiling i A) (proj_ceiling i Hpos A P) = min (pred i) (urelsp_index A P).
Proof.
intros i Hpos A P.
unfold urelsp_index.
set (X := urelsp_index_unique _ (ceiling i A) (proj_ceiling i Hpos A P)).
destruct X as (j & Hj & Honlyj).
set (X := urelsp_index_unique _ A P).
destruct X as (j' & Hj' & Honlyj').
rewrite -> !description_beta.
destruct Hj as (m & p & Hmp & Heq).
destruct Hmp as (Hj & Hmp).
destruct Hj' as (m' & p' & Hmp' & ->).
apply Honlyj.
assert (min (pred i) j' < i) as Hminlt.
  {
  so (Nat.le_min_l (pred i) j').
  omega.
  }
so (urel_downward_leq _ _ (min (pred i) j') _#3 (Nat.le_min_r _ _) Hmp') as Hmp''.
exists m', p', (conj Hminlt Hmp'').
apply exT_extensionality_prop.
cbn.
fextensionality 2.
intros k n.
pextensionality.
  {
  intros (Hki & Hkj & H).
  do2 2 split; auto.
  apply Nat.min_glb; auto.
  omega.
  }

  {
  intros (Hk & Hki & H).
  do2 2 split; auto.
  so (Nat.le_min_r (pred i) j').
  omega.
  }
Qed.


Lemma ceiling_combine :
  forall i j A,
    ceiling i (ceiling j A) = ceiling (min i j) A.
Proof.
intros i j A.
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
  forall i j A,
    i <= j
    -> ceiling i (ceiling j A) = ceiling i A.
Proof.
intros i j A Hle.
rewrite -> ceiling_combine.
rewrite -> min_l; auto.
Qed.


Lemma ceiling_combine_ge :
  forall i j A,
    j <= i
    -> ceiling i (ceiling j A) = ceiling j A.
Proof.
intros i j A Hle.
rewrite <- (Min.min_r _ _ Hle) at 2.
apply ceiling_combine.
Qed.


Lemma ceiling_idem :
  forall i A,
    ceiling i (ceiling i A) = ceiling i A.
Proof.
intros i A.
rewrite -> ceiling_combine.
rewrite -> min_l; auto.
Qed.


Lemma ceiling_near :
  forall n (A : car (wurel_ofe cur)),
    @dist (wurel_ofe cur) n (ceiling n A) A.
Proof.
intros n A.
intros i Hi.
fextensionality 2.
intros m p.
cbn.
pextensionality; intro H; [destruct H | split]; auto.
Qed.


Lemma ceiling_dist :
  forall i j, i <= j -> @dist (nearrow_ofe (wurel_ofe cur) (wurel_ofe cur)) i (ceiling_ne i) (ceiling_ne j).
Proof.
intros i j Hle.
intros R.
eapply dist_trans.
  {
  apply ceiling_near.
  }
apply dist_symm.
apply (dist_downward_leq _ _ j); auto.
apply ceiling_near.
Qed.


Lemma proj_ceiling_near :
  forall n (A : car (wurel_ofe cur)) (C : car (urelsp A)) Hpos,
    urelsp_dist_dep (ceiling n A) A n (proj_ceiling n Hpos A C) C.
Proof.
intros n A C Hpos.
intros i Hi.
cbn.
fextensionality 1.
intro m.
pextensionality; intro H; [destruct H | split]; auto.
Qed.


Lemma embed_ceiling_urelspinj :
  forall i (A : wurel cur) j m n Hmn Hle,
    embed_ceiling i A (urelspinj (ceiling i A) j m n (conj Hle Hmn))
    =
    urelspinj A j m n Hmn.
Proof.
intros i A j m n Hmn Hle.
apply exT_extensionality_prop.
cbn.
fextensionality 2.
intros j' p.
pextensionality; intro H; destruct_all H; repeat2 split; auto; omega.
Qed.


Lemma proj_ceiling_urelspinj :
  forall i j (A : wurel cur) m p Hpos Hmp Hmp',
    proj_ceiling (S i) Hpos A (urelspinj A j m p Hmp)
    =
    urelspinj (ceiling (S i) A) (min j i) m p Hmp'.
Proof.
intros i j A m p Hpos Hmp Hmp'.
apply exT_extensionality_prop.
cbn.
fextensionality 2.
intros k n.
pextensionality.
  {
  intros (Hki & Hkj & Hnp).
  do2 2 split; auto.
  apply Nat.min_glb; omega.
  }

  {
  intros (Hk & Hk' & Hnp).
  do2 2 split; auto.
  so (Nat.le_min_l j i); omega.
  }
Qed.


Lemma ceiling_zero :
  forall R,
    ceiling 0 R = empty_urel.
Proof.
intros R.
apply urel_extensionality.
fextensionality 3.
intros j m p.
pextensionality.
  {
  intro H.
  destruct H.
  omega.
  }

  {
  intro H; destruct H.
  }
Qed.


Lemma ceiling_empty_urel :
  forall i,
    ceiling i empty_urel = empty_urel.
Proof.
intros i.
apply urel_extensionality.
fextensionality 3.
intros j m p.
pextensionality.
  {
  intros (_ & H); destruct H.
  }

  {
  intro H; destruct H.
  }
Qed.


End level.


Arguments ceiling {cur}.
Arguments embed_ceiling {cur}.
Arguments embed_ceiling_ne {cur}.
Arguments proj_ceiling {cur}.
Arguments proj_ceiling_ne {cur}.
Arguments ceiling_ne {cur}.
Arguments proj_ceiling {cur}.
