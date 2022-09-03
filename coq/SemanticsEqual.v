
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
Require Import Extend.
Require Export SemanticsProperty.


(* Disoriented rel *)

Definition srel {object} (s : bool) (A : @urel object) i m n :=
  if s then
    rel A i m n
  else
    rel A i n m.


Lemma srel_closed :
  forall object s (A : urel object) i m n,
    srel s A i m n
    -> hygiene clo m /\ hygiene clo n.
Proof.
intros object s A i m n H.
destruct s; so (urel_closed _#5 H) as (? & ?); auto.
Qed.


Lemma srel_equiv :
  forall object s (A : urel object) i m m' n n',
    hygiene clo m'
    -> hygiene clo n'
    -> equiv m m'
    -> equiv n n'
    -> srel s A i m n
    -> srel s A i m' n'.
Proof.
intros object s A i m m' n n' H H0 H1 H2 H3.
destruct s; eapply urel_equiv; eauto.
Qed.


Lemma srel_zigzag :
  forall object s (R : urel object) i m n p q,
    srel s R i m n
    -> srel s R i p n
    -> srel s R i p q
    -> srel s R i m q.
Proof.
intros object s R i m n p q Hmn Hpn Hpq.
destruct s; cbn in *; eapply urel_zigzag; eauto.
apply (urel_zigzag _#4 p n); auto.
Qed.


Lemma srel_downward :
  forall object s A i m n,
    @srel object s A (S i) m n
    -> srel s A i m n.
Proof.
intros object s A i m n H.
destruct s; apply urel_downward; auto.
Qed.


Lemma srel_downward_leq :
  forall object s A i j m n,
    i <= j
    -> @srel object s A j m n
    -> srel s A i m n.
Proof.
intros object s A i m n H.
destruct s; apply urel_downward_leq; auto.
Qed.


Lemma srel_ceiling_intro :
  forall w s i (A : wurel w) j m n,
    j < i
    -> srel s A j m n
    -> srel s (ceiling i A) j m n.
Proof.
intros w s i A j m n Hji Hrel.
destruct s; cbn; cbn in Hrel; auto.
Qed.


Lemma srel_ceiling_elim :
  forall w s i (A : wurel w) j m n,
    srel s (ceiling i A) j m n
    -> srel s A j m n.
Proof.
intros w s i A j m n Hrel.
destruct s; cbn; cbn in Hrel; destruct Hrel; auto.
Qed.


Lemma surel_updown :
  forall v w s (A : wurel v) i m p,
    v <<= w
    -> srel s A i m p
    -> srel s (extend_urel v w A) i (map_term (extend v w) m) (map_term (extend v w) p).
Proof.
intros v w s A i m p Hvw H.
destruct s; apply urel_updown; auto.
Qed.


Definition surelspinj {object} (s : bool) (A : urel object) i m p 
  : srel s A i m p -> car (urelsp A)
  :=
  match s
    as s
    return srel s A i m p -> car (urelsp A)
  with
  | true => fun Hmp => urelspinj A i m p Hmp
  | false => fun Hmp => urelspinj A i p m Hmp
  end.


Lemma surelspinj_equal :
  forall object s (A : urel object) i m m' p p' H H',
    srel s A i m p'
    -> surelspinj s A i m p H = surelspinj s A i m' p' H'.
Proof.
intros object s A i m m' p p' Hmp Hmp' H.
destruct s; apply urelspinj_equal; auto.
eapply urel_zigzag; eauto.
Qed.


Lemma surelspinj_equal_impl :
  forall object s (A : urel object) i m m' p p' (H : srel s A i m p) (H' : srel s A i m' p'),
    surelspinj s A i m p H = surelspinj s A i m' p' H'
    -> srel s A i m p'.
Proof.
intros object s A i m m' p p' Hmp Hmp' Heq.
destruct s.
  {
  apply (urelspinj_equal_impl _#7 Hmp Hmp'); auto.
  }

  {
  cbn in * |- *.
  so (urelspinj_equal_impl _#9 Heq).
  eapply urel_zigzag; eauto.
  }
Qed.


Lemma proj_ceiling_surelspinj :
  forall w i j s (A : wurel w) m p Hpos Hmp Hmp',
    proj_ceiling (S i) Hpos A (surelspinj s A j m p Hmp)
    =
    surelspinj s (ceiling (S i) A) (min j i) m p Hmp'.
Proof.
intros w i j s A m p Hpos Hmp Hmp'.
destruct s; cbn; erewrite -> proj_ceiling_urelspinj; eauto.
Qed.


Lemma extend_srel :
  forall v w s A i m p,
    srel s (extend_urel v w A) i m p
    <->
    srel s A i (map_term (extend w v) m) (map_term (extend w v) p).
Proof.
intros v w s A i m p.
destruct s; cbn; split; auto.
Qed.


Lemma extend_surelspinj :
  forall v w (h : v <<= w) s (A : wurel v) i m p Hmp Hmp',
    extend_urelsp h A (surelspinj s A i m p Hmp)
    =
    surelspinj s (extend_urel v w A) i (map_term (extend v w) m) (map_term (extend v w) p) Hmp'.
Proof.
intros v w h s A i m p Hmp Hmp'.
destruct s; apply extend_urelspinj.
Qed.


(* Equality *)

Definition equal_property w (s : bool) (A : wurel w) m n : nat -> Prop :=
  fun i =>
    exists p,
      srel s A i m p
      /\ srel s A i n p.


Lemma equal_property_downward :
  forall w s A m n i,
    equal_property w s A m n (S i)
    -> equal_property w s A m n i.
Proof.
intros w s A m n i H.
destruct H as (p & Hmp & Hnp).
exists p; auto using srel_downward.
Qed.


(* Using a nat instead of a nats will cause trouble if I ever want to make iurels complete. *)

Definition equal_urel (w : ordinal) (s : bool) (i : nat) (A : wurel w) (m n : wterm w) : wurel w :=
  property_urel
    (fun j =>
       exists p,
         srel s A j m p
         /\ srel s A j n p)
    w i
    (equal_property_downward w s A m n).


Lemma equal_urel_equal :
  forall w s i A m m' n n' p q,
    srel s A i m p
    -> srel s A i m' p
    -> srel s A i n q
    -> srel s A i n' q
    -> equal_urel w s i A m n = equal_urel w s i A m' n'.
Proof.
intros w s i A m m' n n' p q Hmp Hmp' Hnq Hnq'.
unfold equal_urel.
apply property_urel_extensionality; auto.
intros j Hj.
cbn in Hj.
assert (j <= i) as Hj' by omega.
split.
  {
  intros (r & Hmr & Hnr).
  exists r.
  split.
    {
    apply (srel_zigzag _#5 p m); eauto using srel_downward_leq.
    }

    {
    apply (srel_zigzag _#5 q n); eauto using srel_downward_leq.
    }
  }

  {
  intros (r & Hmr & Hnr).
  exists r.
  split.
    {
    apply (srel_zigzag _#5 p m'); eauto using srel_downward_leq.
    }

    {
    apply (srel_zigzag _#5 q n'); eauto using srel_downward_leq.
    }
  }
Qed.


Lemma extend_equal_urel :
  forall v w s i A m n,
    v <<= w
    -> extend_urel v w (equal_urel v s i A m n)
       =
       equal_urel w s i (extend_urel v w A) (map_term (extend v w) m) (map_term (extend v w) n).
Proof.
intros v w s i A m n Hle.
unfold equal_urel.
rewrite -> extend_property; auto.
apply property_urel_extensionality; auto.
intros j Hj.
split.
  {
  intros (r & Hmr & Hnr).
  exists (map_term (extend v w) r).
  rewrite -> !extend_srel.
  rewrite -> !extend_term_cancel; auto.
  }

  {
  intros (r & Hmr & Hnr).
  exists (map_term (extend w v) r).
  rewrite -> extend_srel in Hmr, Hnr.
  rewrite -> !extend_term_cancel in Hmr, Hnr; auto.
  }
Qed.


Definition iuequal (w : ordinal) (s : bool) (i : nat) (A : wiurel w) (m n p q : wterm w)
  (Hmp : srel s (den A) i m p) (Hnq : srel s (den A) i n q)
  : wiurel w
  :=
  (equal_urel w s i (den A) m n,
   meta_pair (meta_iurel A)
     (meta_pair 
        (meta_term (den A) (surelspinj s (den A) i m p Hmp))
        (meta_term (den A) (surelspinj s (den A) i n q Hnq)))).
     

(* Trivial, but helpful to control rewriting. *)
Lemma den_iuequal :
  forall w s i A m n p q Hmp Hnq,
    den (iuequal w s i A m n p q Hmp Hnq) = equal_urel w s i (den A) m n.
Proof.
auto.
Qed.


Lemma iuequal_equal :
  forall w s i A m m' n n' p p' q q' Hmp Hmp' Hnq Hnq',
    srel s (den A) i m p'
    -> srel s (den A) i n q'
    -> iuequal w s i A m n p q Hmp Hnq = iuequal w s i A m' n' p' q' Hmp' Hnq'.
Proof.
intros w s i A m m' n n' p p' q q' Hmp Hmp' Hnq Hnq' Hmp'' Hnq''.
unfold iuequal.
f_equal.
  {
  eapply equal_urel_equal; eauto.
  }
f_equal.
f_equal.
  {
  f_equal.
  apply surelspinj_equal.
  eapply srel_zigzag; eauto.
  }

  {
  f_equal.
  apply surelspinj_equal.
  eapply srel_zigzag; eauto.
  }
Qed.


Lemma iuequal_equal' :
  forall w s i A A' m m' n n' p p' q q' Hmp Hmp' Hnq Hnq',
    A = A'
    -> srel s (den A) i m p'
    -> srel s (den A) i n q'
    -> iuequal w s i A m n p q Hmp Hnq = iuequal w s i A' m' n' p' q' Hmp' Hnq'.
Proof.
intros w s i A A' m m' n n' p p' q q' Hmp Hmp' Hnq Hnq' Heq Hmp'' Hnq''.
subst A'.
apply iuequal_equal; auto.
Qed.


Lemma iuequal_inj :
  forall w s i A A' m m' n n' p p' q q' Hmp Hmp' Hnq Hnq',
    iuequal w s i A m n p q Hmp Hnq = iuequal w s i A' m' n' p' q' Hmp' Hnq'
    -> A = A'
       /\ srel s (den A) i m p'
       /\ srel s (den A) i n q'.
Proof.
intros w s i A A' m m' n n' p p' q q' Hmp Hmp' Hnq Hnq' Heq.
unfold iuequal in Heq.
so (f_equal snd Heq) as Heq'.
cbn in Heq'.
so (meta_pair_inj _#5 Heq') as (Heq1 & Heq23).
clear Heq Heq'.
so (meta_iurel_inj _#3 Heq1); subst A'.
so (meta_pair_inj _#5 Heq23) as (Heq2 & Heq3).
clear Heq1 Heq23.
so (meta_term_inj _#5 Heq2) as H.
injectionT H.
intro Heqmp.
so (meta_term_inj _#5 Heq3) as H.
injectionT H.
intro Heqnq.
clear Heq2 Heq3.
do2 2 split; eauto using surelspinj_equal_impl.
Qed.    


Lemma iutruncate_iuequal :
  forall w j s i A m n p q Hmp Hnq Hmp' Hnq',
    iutruncate (S j) (iuequal w s i A m n p q Hmp Hnq)
    =
    iuequal w s (min i j) (iutruncate (S j) A) m n p q Hmp' Hnq'.
Proof.
intros w j s i A m n p q Hmp Hnq Hmp' Hnq'.
unfold iuequal, iutruncate.
destruct A as (A & meta).
unfold den.
cbn [fst snd].
f_equal.
  {
  unfold equal_urel.
  cbn [fst].
  rewrite -> ceiling_property.
  apply property_urel_extensionality.
    {
    reflexivity.
    }
  intros k Hk.
  so (Nat.min_glb_r _#3 Hk) as Hkj.
  split.
    {
    intros (r & Hmr & Hnr).
    exists r.
    split; apply srel_ceiling_intro; auto; omega.
    }

    {
    intros (r & Hmr & Hnr).
    exists r.
    eauto using srel_ceiling_elim.
    }
  }

  {
  assert (S j > 0) as Hpos by omega.
  rewrite -> !meta_truncate_pair; auto.
  rewrite -> !(meta_truncate_term _#4 Hpos).
  rewrite -> meta_truncate_iurel; auto.
  f_equal.
  f_equal.
    {
    f_equal.
    apply proj_ceiling_surelspinj.
    }

    {
    f_equal.
    apply proj_ceiling_surelspinj.
    }
  }
Qed.


Lemma extend_iuequal :
  forall v w (h : v <<= w) s i A m n p q Hmp Hmp' Hnq Hnq',
    extend_iurel h (iuequal v s i A m n p q Hmp Hnq)
    =
    iuequal w s i (extend_iurel h A)
      (map_term (extend v w) m)
      (map_term (extend v w) n)
      (map_term (extend v w) p)
      (map_term (extend v w) q)
      Hmp' Hnq'.
Proof.
intros v w h s i A m n p q Hmp Hmp' Hnq Hnq'.
unfold iuequal, extend_iurel.
cbn.
f_equal.
  {
  apply extend_equal_urel; auto.
  }

  {
  rewrite -> !extend_meta_pair.
  rewrite -> extend_meta_iurel.
  rewrite -> !extend_meta_term.
  f_equal.
  f_equal.
    {
    f_equal.
    apply extend_surelspinj.
    }

    {
    f_equal.
    assert (srel s (extend_urel v w (den A)) i (map_term (extend v w) n) (map_term (extend v w) q)) as Hnq''.
      {
      fold (extend_urel v w).
      rewrite -> extend_srel.
      rewrite -> !extend_term_cancel; auto.
      }
    rewrite -> (extend_surelspinj _#9 Hnq'').
    apply surelspinj_equal; auto.
    }
  }
Qed.


Lemma extend_iuequal' :
  forall v w (h : v <<= w) s i A m n p q Hmp Hnq,
    extend_iurel h (iuequal v s i A m n p q Hmp Hnq)
    =
    iuequal w s i (extend_iurel h A)
      (map_term (extend v w) m)
      (map_term (extend v w) n)
      (map_term (extend v w) p)
      (map_term (extend v w) q)
      (surel_updown _#7 h Hmp)
      (surel_updown _#7 h Hnq).
Proof.
intros v w h s i A m n p q Hmp Hnq.
apply extend_iuequal.
Qed.


Lemma srel_swap :
  forall object s (A : urel object) i m n,
    srel s A i m n 
    -> srel (negb s) A i n m.
Proof.
intros object s A i m n H.
destruct s; auto.
Qed.


Lemma srel_unswap :
  forall object s (A : urel object) i m n,
    srel (negb s) A i n m
    -> srel s A i m n.
Proof.
intros object s A i m n H.
destruct s; auto.
Qed.


Lemma surelspinj_swap :
  forall object s (A : urel object) i m p Hmp Hpm,
    surelspinj s A i m p Hmp
    =
    surelspinj (negb s) A i p m Hpm.
Proof.
intros object s A i m p Hmp Hpm.
destruct s; cbn.
  {
  f_equal.
  apply proof_irrelevance.
  }

  {
  f_equal.
  apply proof_irrelevance.
  }
Qed.


Lemma iuequal_swap :
  forall w s i A m n p q Hmp Hnq,
    iuequal w s i A m n p q Hmp Hnq
    =
    iuequal w (negb s) i A p q m n (srel_swap _#6 Hmp) (srel_swap _#6 Hnq).
Proof.
intros w s i A m n p q Hmp Hnq.
unfold iuequal.
f_equal.
  {
  apply property_urel_extensionality; auto.
  intros j Hj.
  cbn in Hj.
  assert (j <= i) as Hj' by omega.
  split.
    {
    intros (r & Hmr & Hnr).
    exists m; split; apply srel_swap.
      {
      exact (srel_downward_leq _#7 Hj' Hmp).
      }

      {
      refine (srel_zigzag _#8 Hmr Hnr _).
      exact (srel_downward_leq _#7 Hj' Hnq).
      }
    }

    {
    intros (r & Hpr & Hqr).
    so (srel_unswap _#6 Hpr) as Hrp.
    so (srel_unswap _#6 Hqr) as Hrq.
    exists p.
    split.
      {
      exact (srel_downward_leq _#7 Hj' Hmp).
      }

      {
      refine (srel_zigzag _#8 _ Hrq Hrp).
      exact (srel_downward_leq _#7 Hj' Hnq).
      }
    }
  }

  {
  f_equal.
  f_equal.
    {
    f_equal.
    apply surelspinj_swap.
    }

    {
    f_equal.
    apply surelspinj_swap.
    }
  }
Qed.
