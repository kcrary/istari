
Require Import Axioms.

Require Import Tactics.
Require Import Sigma.
Require Import Equality.
Require Import Ofe.
Require Import Syntax.
Require Import Uniform.
Require Import Spaces.
Require Import Equivalence.
Require Import Hygiene.


Section object.


Arguments operator {object}.
Arguments term {object}.
Arguments row {object}.
Arguments urel {object}.
Arguments urel_ofe {object}.


Variable object : Type.


(* Uniform relations as spaces *)

(* 1-indexed *)
Definition urelsp_car (R : @urel object) : Type
  :=
  existsT (P : nat -> term -> Prop),
    exists i m p,
      rel R i m p
      /\ forall j n,
           P j n <-> (j <= i /\ rel R j n p).


(* Sometimes useful to be able to refer to this independently. *)
(* 1-indexed *)
Definition urelsp_car_rhs : @urel object -> (nat -> term -> Prop) -> Prop :=
  (fun R P => exists i m p, rel R i m p /\ forall j n, P j n <-> (j <= i /\ rel R j n p)).


Definition urelsp_dist (R : urel) (i : nat) (P Q : urelsp_car R) : Prop
  :=
  forall j, j < i -> pi1 P j = pi1 Q j.


Definition urelsp (R : @urel object) : ofe.
Proof.
apply (mk_ofe (urelsp_car R) (urelsp_dist R)).

(* eqrel *)
{
intro i.
do2 2 split.
  {
  intros m j Hji.
  reflexivity.
  }

  {
  intros l m n Hlm Hmn j Hji.
  transitivity (pi1 m j).
    { apply Hlm; auto. }

    { apply Hmn; auto. }
  }

  {
  intros m n Hmn j Hji.
  symmetry.
  apply Hmn; auto.
  }
}

(* limeq *)
{
intros P Q Hlimeq.
apply exT_extensionality_prop.
fextensionality 2.
intros i m.
rewrite <- (Hlimeq (S i)); auto.
}

(* downward *)
{
intros i P Q HPQ.
intros j Hji.
apply HPQ.
auto.
}

(* zero *)
{
intros P Q i Hi.
omega.
}
Defined.


Definition urelspinj (A : urel) (i : nat) (m p : term) (H : rel A i m p) : car (urelsp A).
Proof.
exists (fun j n => j <= i /\ rel A j n p).
exists i, m, p.
split; auto.
intros j n.
split; auto.
Defined.


Lemma urelsp_index_unique :
  forall (A : urel) (P : car (urelsp A)),
    exists! i, exists m p Hmp, P = urelspinj A i m p Hmp.
Proof.
intros A P.
destruct P as (P & HP).
destruct HP as (i & m & p & Hmp & HP).
exists i.
split.
  {
  exists m, p, Hmp.
  apply exT_extensionality_prop.
  cbn.
  fextensionality 2.
  intros j n.
  pextensionality.
    {
    intros Hn.
    apply HP; auto.
    }

    {
    intros Hn.
    apply HP; auto.
    }
  }

  {
  intros i'.
  intro H.
  destruct H as (m' & p' & Hmp' & Heq).
  so (eq_fn_apply pi1 Heq) as Heq'.
  cbn in Heq'.
  clear Heq.
  apply le_antisym.
    {
    so (HP i m ander (conj (le_refl _) Hmp)) as H.
    rewrite -> Heq' in H.
    destruct H; auto.
    }

    {
    lapply (HP i' m' andel).
      {
      intros (? & _); auto.
      }
    rewrite -> Heq'.
    split; auto.
    }
  }
Qed.


Lemma urelsp_eta :
  forall (A : urel) (P : car (urelsp A)),
    exists i m p (Hmp : rel A i m p),
      P = urelspinj A i m p Hmp.
Proof.
intros A P.
destruct P as (P & HP).
destruct HP as (i & m & p & Hmp & HP).
exists i, m, p, Hmp.
apply exT_extensionality_prop.
cbn.
fextensionality 2.
intros j n.
pextensionality.
  {
  intros Hn.
  apply HP; auto.
  }

  {
  intros Hn.
  apply HP; auto.
  }
Qed.


Lemma urelspinj_inject :
  forall A i i' m m' p p' Hmp Hmp',
    urelspinj A i m p Hmp = urelspinj A i' m' p' Hmp'
    -> i = i' /\ rel A i m p' /\ rel A i m' p.
Proof.
intros A i i' m m' p p' Hmp Hmp' Heq.
so (eq_fn_apply (fun z => pi1 z i m) Heq) as Heq'.
cbn in Heq'.
assert (i <= i /\ rel A i m p) as H by auto.
rewrite -> Heq' in H.
destruct H as (Hle & Hm_p').
clear Heq'.
so (eq_fn_apply (fun z => pi1 z i' m') Heq) as Heq'.
cbn in Heq'.
assert (i' <= i' /\ rel A i' m' p') as H by auto.
rewrite <- Heq' in H.
destruct H as (Hge & Hm'_p).
assert (i = i') by (apply le_antisym; auto).
subst i'.
do2 2 split; auto.
Qed.


Lemma urelspinj_equal :
  forall A i m m' p p' H H',
    rel A i m p'
    -> urelspinj A i m p H = urelspinj A i m' p' H'.
Proof.
intros A i m m' p p' Hmp Hmp' Hmp''.
apply exT_extensionality_prop.
cbn.
fextensionality 2.
intros j n.
pextensionality.
  {
  intros (Hji & Hnp).
  split; auto.
  apply (urel_zigzag _ _ _ n p m p'); eauto using urel_downward_leq.
  }

  {
  intros (Hji & Hnp').
  split; auto.
  apply (urel_zigzag _ _ _ n p' m p); eauto using urel_downward_leq.
  }
Qed.


Lemma urelspinj_equal' :
  forall A i i' m m' p p' H H',
    i = i'
    -> rel A i m p'
    -> urelspinj A i m p H = urelspinj A i' m' p' H'.
Proof.
intros A i i' m m' p p' H H' Heqi Hrel.
subst i'.
apply urelspinj_equal; auto.
Qed.


Lemma urelspinj_equal_invert :
  forall A i j m m' p p' (H : rel A i m p) (H' : rel A j m' p'),
    urelspinj A i m p H = urelspinj A j m' p' H'
    -> i = j /\ rel A i m p'.
Proof.
intros A i j m m' p p' Hmp Hmp' Heq.
assert (pi1 (urelspinj A i m p Hmp) i m) as H.
  {
  cbn.
  auto.
  }
rewrite -> Heq in H.
cbn in H.
destruct H as (Hij & Hrel).
assert (pi1 (urelspinj A j m' p' Hmp') j m') as H.
  {
  cbn.
  auto.
  }
rewrite <- Heq in H.
cbn in H.
destruct H as (Hji & _).
split; auto.
omega.
Qed.


Lemma urelspinj_dist_index :
  forall (A : @urel object) i j j' m m' p p' (Hmp : rel A j m p) (Hmp' : rel A j' m' p'),
    j < j'
    -> dist i (urelspinj A j m p Hmp) (urelspinj A j' m' p' Hmp')
    -> i <= S j.
Proof.
intros A i j j' m m' p p' Hmp Hmp' Hlt Hdist.
apply not_gt.
intros Hgt.
cbn in Hdist.
unfold urelsp_dist in Hdist.
so (le_lt_dec i j') as [Hle | Hgt'].
  {
  exploit (Hdist (pred i)) as Heq; [omega |].
  cbn in Heq.
  so (f_equal (fun z => z m') Heq) as Heq'.
  cbn in Heq'.
  assert (pred i <= j' /\ rel A (pred i) m' p') as H.
    {
    split; [omega |].
    apply (urel_downward_leq _ _ _ j'); auto.
    omega.
    }
  rewrite <- Heq' in H.
  destruct H as (H & _).
  omega.
  }

  {
  so (Hdist j' Hgt') as Heq.
  cbn in Heq.
  so (f_equal (fun z => z m') Heq) as Heq'.
  cbn in Heq'.
  assert (j' <= j' /\ rel A j' m' p') as H by auto.
  rewrite <- Heq' in H.
  destruct H as (H & _).
  omega.
  }
Qed.


Lemma urelspinj_dist_index' :
  forall (A : @urel object) i j j' m m' p p' (Hmp : rel A j m p) (Hmp' : rel A j' m' p'),
    dist i (urelspinj A j m p Hmp) (urelspinj A j' m' p' Hmp')
    -> (j = j' /\ S j < i) \/ (i <= S j /\ i <= S j').
Proof.
intros A i j j' m m' p p' Hmp Hmp' Hdist.
so (lt_eq_lt_dec j j') as [[Hlt | Heq]|Hlt].
  {
  right.
  so (urelspinj_dist_index _#8 Hmp Hmp' Hlt Hdist).
  omega.
  }

  {
  subst j'.
  so (le_dec i (S j)) as [Hle | Hnle].
    {
    right.
    auto.
    }

    {
    left.
    omega.
    }
  }

  {
  right.
  so (urelspinj_dist_index _#8 Hmp' Hmp Hlt (dist_symm _#4 Hdist)).
  omega.
  }
Qed.


Lemma urelspinj_dist_invert :
  forall A i j j' m p n q (Hmp : rel A j m p) (Hnq : rel A j' n q),
    dist (S i) (urelspinj A j m p Hmp) (urelspinj A j' n q Hnq)
    -> rel A (min i j) m q.
Proof.
intros A i j j' m p n q Hmp Hnq Hdist.
set (k := min i j).
assert (k <= j) as Hkj.
  {
  so (Nat.le_min_r i j).
  auto.
  }
assert (k < S i) as Hki.
  {
  so (Nat.le_min_l i j).
  omega.
  }
assert (pi1 (urelspinj A j m p Hmp) k m) as H.
  {
  cbn.
  split; auto.
  eapply urel_downward_leq; eauto.
  }
rewrite -> (Hdist k Hki) in H.
cbn in H.
destruct H; auto.
Qed.


Lemma urelspinj_equal_impl :
  forall A i m m' p p' (H : rel A i m p) (H' : rel A i m' p'),
    urelspinj A i m p H = urelspinj A i m' p' H'
    -> rel A i m p'.
Proof.
intros A i m m' p p' Hmp Hmp' Heq.
exact (urelspinj_equal_invert _#9 Heq ander).
Qed.


Lemma urelspinj_dist_diff :
  forall A i j k m m' p p' (H : rel A j m p) (H' : rel A k m' p'),
    i <= j
    -> i <= k
    -> rel A i m p'
    -> dist (S i) (urelspinj A j m p H) (urelspinj A k m' p' H').
Proof.
intros A i j k m n p q Hmp Hnq Hj Hk Hmq.
intros l H.
cbn.
fextensionality 1.
intros r.
assert (l <= i) as Hli by omega.
assert (l <= j) as Hlj by omega.
assert (l <= k) as Hlk by omega.
pextensionality.
  {
  intros (_ & Hrp).
  split; [omega |].
  apply (urel_zigzag _ _ _ r p m q); eauto using urel_downward_leq.
  }

  {
  intros (_ & Hrq).
  split; auto.
  apply (urel_zigzag _ _ _ r q m p); eauto using urel_downward_leq.
  }
Qed.


Lemma urelspinj_dist :
  forall A i j m p (H : rel A i m p) (H' : rel A j m p),
    i <= j
    -> dist (S i) (urelspinj A i m p H) (urelspinj A j m p H').
Proof.
intros A i j m p Hreli Hrelj Hle.
apply urelspinj_dist_diff; auto.
Qed.


Lemma transport_urelspinj :
  forall A A' (h : A = A') j m n (H : rel A j m n) (H' : rel A' j m n),
    transport h urelsp_car (urelspinj A j m n H)
    =
    urelspinj A' j m n H'.
Proof.
intros A A' h j m n H H'.
subst A'.
cbn.
f_equal.
apply proof_irrelevance.
Qed.


Lemma coerce_urelsp_rhs :
  forall n (R R' : car urel_ofe),
    n > 0
    -> dist n R R'
    -> forall (P : urelsp_car R),
         urelsp_car_rhs R' (fun j m => j < n /\ pi1 P j m).
Proof.
intros n R R' Hpos Hdist P.
destruct n as [| n].
  { omega. }
destruct P as (P & j & m & p & Hmp & HP).
cbn.
exists (min j n), m, p.
split.
  {
  rewrite <- Hdist.
  2:{
    so (Nat.le_min_r j n).
    omega.
    }
  apply (urel_downward_leq _ _ _ j); auto.
  so (Nat.le_min_l j n).
  omega.
  }

  {
  intros i r.
  split.
    {
    intros (Hin & Hr).
    so (HP _ _ andel Hr) as (Hij & Hrp).
    split.
      {
      apply Nat.min_glb; auto; omega.
      }

      {
      rewrite <- Hdist; auto; omega.
      }
    }

    {
    intros (Hi & Hrp).
    split.
      {
      so (Nat.le_min_r j n).
      omega.
      }

      {
      apply HP.
      split.
        {
        so (Nat.le_min_l j n); omega.
        }

        {
        rewrite -> Hdist; auto.
        so (Nat.le_min_r j n); omega.
        }
      }
    }
  }
Qed.


Definition coerce_urelsp (n : nat) (R R' : car urel_ofe)
  (Hpos : n > 0) (Hdist : dist n R R')
  : urelsp_car R -> urelsp_car R'
  :=
  fun P => expair
             (fun j m => j < n /\ pi1 P j m) 
             (coerce_urelsp_rhs n R R' Hpos Hdist P).


Lemma coerce_urelsp_nonexpansive :
  forall n (R R' : car urel_ofe) (Hpos : n > 0) (Hdist : dist n R R'),
    @nonexpansive (urelsp R) (urelsp R') (coerce_urelsp n R R' Hpos Hdist).
Proof.
intros n R R' Hpos Hdist.
intros i P Q HPQ.
intros j Hji.
cbn.
fextensionality 1.
intros m.
pextensionality.
  {
  intros (Hjn & Hm).
  split; auto.
  rewrite <- HPQ; auto.
  }

  {
  intros (Hjn & Hm).
  split; auto.
  rewrite -> HPQ; auto.
  }
Qed.


Definition coerce_urelsp_ne (n : nat) (R R' : car urel_ofe) (Hpos : n > 0) (Hdist : dist n R R')
  : urelsp R -n> urelsp R'
  :=
  expair 
    (coerce_urelsp n R R' Hpos Hdist)
    (coerce_urelsp_nonexpansive n R R' Hpos Hdist).


Definition urelsp_dist_dep (R R' : @urel object) (i : nat) (P : urelsp_car R) (Q : urelsp_car R') : Prop
  :=
  forall j, j < i -> pi1 P j = pi1 Q j.


Lemma urelsp_dofe :
  dofe (@urel_ofe object) urelsp.
Proof.
refine
  (mk_dofe urel_ofe urelsp urelsp_dist_dep _ _ _ _ _).

(* eq_dist *)
{
intros a.
reflexivity.
}

(* symm *)
{
intros i a a' b b' H.
intros j Hj.
symmetry.
apply H; auto.
}

(* trans *)
{
intros i a1 a2 a3 b1 b2 b3 H12 H23.
intros j Hj.
transitivity (pi1 b2 j); auto.
}

(* downward *)
{
intros i a a' b b' H.
intros j Hj.
apply H; auto.
}

(* zero *)
{
intros a a' b b'.
intros j Hj.
omega.
}
Defined.


Lemma urelspinj_dist_dep_index :
  forall (A B : @urel object) i j j' m m' p p' (Hmp : rel A j m p) (Hmp' : rel B j' m' p'),
    j < j'
    -> urelsp_dist_dep A B i (urelspinj A j m p Hmp) (urelspinj B j' m' p' Hmp')
    -> i <= S j.
Proof.
intros A B i j j' m m' p p' Hmp Hmp' Hlt Hdist.
apply not_gt.
intros Hgt.
unfold urelsp_dist_dep in Hdist.
so (le_lt_dec i j') as [Hle | Hgt'].
  {
  exploit (Hdist (pred i)) as Heq; [omega |].
  cbn in Heq.
  so (f_equal (fun z => z m') Heq) as Heq'.
  cbn in Heq'.
  assert (pred i <= j' /\ rel B (pred i) m' p') as H.
    {
    split; [omega |].
    apply (urel_downward_leq _ _ _ j'); auto.
    omega.
    }
  rewrite <- Heq' in H.
  destruct H as (H & _).
  omega.
  }

  {
  so (Hdist j' Hgt') as Heq.
  cbn in Heq.
  so (f_equal (fun z => z m') Heq) as Heq'.
  cbn in Heq'.
  assert (j' <= j' /\ rel B j' m' p') as H by auto.
  rewrite <- Heq' in H.
  destruct H as (H & _).
  omega.
  }
Qed.


Lemma urelspinj_dist_dep_index' :
  forall (A B : @urel object) i j j' m m' p p' (Hmp : rel A j m p) (Hmp' : rel B j' m' p'),
    urelsp_dist_dep A B i (urelspinj A j m p Hmp) (urelspinj B j' m' p' Hmp')
    -> (j = j' /\ S j < i) \/ (i <= S j /\ i <= S j').
Proof.
intros A B i j j' m m' p p' Hmp Hmp' Hdist.
so (lt_eq_lt_dec j j') as [[Hlt | Heq]|Hlt].
  {
  right.
  so (urelspinj_dist_dep_index _#9 Hmp Hmp' Hlt Hdist).
  omega.
  }

  {
  subst j'.
  so (le_dec i (S j)) as [Hle | Hnle].
    {
    right.
    auto.
    }

    {
    left.
    omega.
    }
  }

  {
  right.
  so (dist_dep_symm _ _ urelsp_dofe _#5 Hdist) as Hdist'.
  so (urelspinj_dist_dep_index _#9 Hmp' Hmp Hlt Hdist').
  omega.
  }
Qed.


Lemma urelsp_dist_dep_refl_ext :
  forall A B n (P : urelsp_car A) (Q : urelsp_car B),
    pi1 P = pi1 Q
    -> urelsp_dist_dep A B n P Q.
Proof.
intros A B n P Q Heq.
destruct P as [P HP].
destruct Q as [Q HQ].
cbn in Heq.
subst Q.
intros j Hj.
cbn.
reflexivity.
Qed.


Lemma urelsp_dist_dep_snd :
  forall (A : @urel object) n (C D : car (urelsp A)),
    urelsp_dist_dep A A n C D <-> dist n C D.
Proof.
intros A n C D.
split.
  {
  intros H j Hj.
  apply H; auto.
  }

  {
  intros H j Hj.
  apply H; auto.
  }
Qed.


Lemma urelsp_member_coerce :
  forall n (A : @urel object) B (P : urelsp_car A),
    urel_dist (S n) A B
    -> urelsp_car_rhs B (fun j m => j <= n /\ pi1 P j m).
Proof.
intros n A B P Hdist.
destruct P as (P & HP).
destruct HP as (i & m & p & Hmp & HP).
exists (min n i), m, p.
split.
  {
  rewrite <- (Hdist (min n i)).
  2:{
    so (Nat.le_min_l n i).
    omega.
    }
  apply (urel_downward_leq _ _ _ i); auto.
  so (Nat.le_min_r n i).
  omega.
  }

  {
  intros j r.
  split.
    {
    intro HQr.
    destruct HQr as (Hj_n & HPr).
    split.
      {
      apply Nat.min_glb; auto.
      exact (HP _ _ andel HPr andel).
      }

      {
      rewrite <- (Hdist j); [| omega].
      apply HP; auto.
      }
    }

    {
    intros (Hj & Hrp).
    split.
      {
      eapply Nat.min_glb_l; eauto.
      }

      {
      apply HP.
      split.
        {
        eapply Nat.min_glb_r; eauto.
        }

        {
        rewrite -> (Hdist j); auto.
        so (Nat.min_glb_l _#3 Hj).
        omega.
        }
      }
    }
  }
Qed.


Lemma urelsp_neighbor : neighborly urelsp_dofe.
Proof.
intros n A B P Hpos Hdist.
destruct n as [| n]; [omega |].
destruct P as (P & HP).
set (Q := fun j m => j <= n /\ P j m).
assert (urelsp_car_rhs B Q) as HQ.
  {
  apply (urelsp_member_coerce _#3 (expair P HP)); auto.
  }
exists (expair Q HQ).
intros j Hj.
cbn.
fextensionality 1.
intros m.
pextensionality.
  {
  intros HPm.
  split; auto; omega.
  }

  {
  intros HQm.
  destruct HQm.
  auto.
  }
Qed.


Lemma urelsp_dist_dep_transport :
  forall (A A' B B' : @urel object) (Ha : A = A') (Hb : B = B')
    n (P : car (urelsp A)) (Q : car (urelsp B)),
      urelsp_dist_dep A B n P Q
      -> urelsp_dist_dep A' B' n (transport Ha urelsp_car P) (transport Hb urelsp_car Q).
Proof.
intros A A' B B' Ha Hb n P Q H.
subst A' B'.
cbn.
exact H.
Qed.    


Lemma urelsp_equiv :
  forall (R : @urel object) (C : urelsp_car R) i m n,
    equiv m n
    -> hygiene clo n
    -> pi1 C i m -> pi1 C i n.
Proof.
intros R C i n r Hnr Hcl Hn.
destruct C as [C HC].
destruct HC as (j & m & p & Hmp & HC).
cbn in Hn.
cbn.
rewrite -> HC in Hn |- *.
destruct Hn as (Hi & Hnp).
split; auto.
eapply urel_equiv_1; eauto using equiv_refl, equiv_symm.
Qed.


Lemma urelsp_downward :
  forall R (C : urelsp_car R) j i m,
    j <= i
    -> pi1 C i m
    -> pi1 C j m.
Proof.
intros R C j i n Hj Hn.
so (urelsp_eta _ C) as (k & m & p & Hmp & ->).
cbn in Hn.
cbn.
destruct Hn as (Hi & Hnp).
split; [omega |].
eapply urel_downward_leq; eauto.
Qed.


Lemma urelsp_trans :
  forall (A : @urel object) (C D : urelsp_car A) i m n,
    pi1 C i m
    -> pi1 C i n
    -> pi1 D i m
    -> pi1 D i n.
Proof.
intros A C D i m n HPm HPn HQm.
destruct C as (P & j & r & s & Hrs & HP).
destruct D as (Q & j' & t & u & Htu & HQ).
cbn in HPm, HPn, HQm |- *.
rewrite -> HP in HPm, HPn.
rewrite -> HQ in HQm |- *.
destruct HPm as (_ & Hms).
destruct HPn as (_ & Hns).
destruct HQm as (Hi & Hmu).
split; auto.
apply (urel_zigzag _#4 s m); auto.
Qed.


Definition urelsp_index (A : @urel object) (P : urelsp_car A) : nat
  := pi1 (description _ _ (urelsp_index_unique A P)).


Lemma urelsp_index_inj :
  forall (A : @urel object) (i : nat) (m p : term) (H : rel A i m p),
    urelsp_index A (urelspinj A i m p H) = i.
Proof.
intros A i m p Hmp.
unfold urelsp_index.
match goal with
| |- pi1 ?Y = _ => set (X := Y)
end.
clearbody X.
destruct X as (i' & m' & p' & Hmp' & Heq).
cbn.
so (urelspinj_inject _#9 Heq) as (H & _).
subst i'.
reflexivity.
Qed.


Lemma urelsp_index_transport :
  forall (A B : @urel object) (C : urelsp_car A) (h : A = B),
    urelsp_index B (transport h urelsp_car C)
    =
    urelsp_index A C.
Proof.
intros A B C h.
subst B.
cbn.
reflexivity.
Qed.


End object.


Arguments urelsp_car {object}.
Arguments urelsp_car_rhs {object}.
Arguments urelsp_dist {object}.
Arguments urelsp {object}.
Arguments urelspinj {object}.
Arguments coerce_urelsp {object}.
Arguments coerce_urelsp_ne {object}.
Arguments urelsp_dist_dep {object}.
Arguments urelsp_dofe {object}.
Arguments urelsp_neighbor {object}.
Arguments urelsp_index {object}.
