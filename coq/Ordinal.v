
Require Import Coq.Arith.Compare_dec.

Require Import Axioms.
Require Import Sigma.
Require Import Tactics.


(* We only use ordinals up to omega+2 or so, but it's cleaner to define them under omega^2. *)


Definition ordinal : Type := nat * nat.


Definition fin (i : nat) : ordinal := (0, i).
Definition omegaplus (i : nat) : ordinal := (1, i).
Definition omega : ordinal := omegaplus 0.
Definition omegaplus1 : ordinal := omegaplus 1.


Definition succ (w : ordinal) : ordinal := (fst w, S (snd w)).


Lemma succ_fin :
  forall i, succ (fin i) = fin (S i).
Proof.
intros i.
reflexivity.
Qed.


Inductive le_ord : ordinal -> ordinal -> Prop :=
| le_ord_fst :
    forall i j k l, i < k -> le_ord (i, j) (k, l)

| le_ord_snd :
    forall i j k, j <= k -> le_ord (i, j) (i, k)
.


Definition lt_ord (a b : ordinal) := le_ord (succ a) b.


Notation "a <<= b" := (le_ord a b)
  (at level 70, right associativity) : ordinal_scope.


Notation "a << b" := (lt_ord a b)
  (at level 70, right associativity) : ordinal_scope.


Open Scope ordinal_scope.


Lemma le_fin :
  forall i j, i <= j -> fin i <<= fin j.
Proof.
intros i j Hij.
apply le_ord_snd; auto.
Qed.


Lemma lt_fin :
  forall i j, i < j -> fin i << fin j.
Proof.
intros i j Hij.
apply le_ord_snd.
cbn.
omega.
Qed.


Lemma le_ord_zero :
  forall w, fin 0 <<= w.
Proof.
intros w.
destruct w as (i, j).
destruct i as [| i].
  {
  apply le_ord_snd; omega.
  }

  {
  apply le_ord_fst.
  omega.
  }
Qed.


Lemma le_fin_omega :
  forall i j, fin i <<= omegaplus j.
Proof.
intros i j.
apply le_ord_fst.
omega.
Qed.


Lemma lt_fin_omega :
  forall i j, fin i << omegaplus j.
Proof.
intros i j.
apply le_ord_fst.
cbn.
omega.
Qed.


Lemma lt_omega_fin :
  forall w, w << omega -> existsT i, w = fin i.
Proof.
intros w Hlt.
destruct w as (i, j).
exists j.
invert Hlt; try (intros; omega).
intros Hi.
assert (i = 0) by omega; subst i.
reflexivity.
Qed.


Lemma omega_limit :
  forall w,
    w << omega
    -> succ w << omega.
Proof.
intros w Hlt.
so (lt_omega_fin _ Hlt) as (i & ->).
rewrite -> succ_fin.
apply lt_fin_omega.
Qed.


Lemma lt_ord_impl_le_ord :
  forall v w, v << w -> v <<= w.
Proof.
intros (i, j) (k, l) Hvw.
invert Hvw.
  {
  intro.
  apply le_ord_fst; auto.
  }

  {
  intros H <-.
  apply le_ord_snd.
  omega.
  }
Qed.


Lemma le_ord_refl :
  forall w, w <<= w.
Proof.
intros w.
destruct w as (i, j).
apply le_ord_snd.
auto.
Qed.


Lemma le_ord_refl' :
  forall w w', w = w' -> w <<= w'.
Proof.
intros w w' H.
subst w'.
apply le_ord_refl.
Qed.


Lemma le_ord_antisymm :
  forall v w, v <<= w -> w <<= v -> v = w.
Proof.
intros v w Hvw Hwv.
invertc Hvw.
  {
  intros i j k l Hik <- <-.
  invertc Hwv.
    {
    intro Hki.
    omega.
    }

    {
    intros Hlj ->.
    f_equal.
    omega.
    }
  }

  {
  intros i j k Hjk <- <-.
  invertc Hwv.
    {
    intros H.
    omega.
    }

    {
    intros Hkj.
    f_equal.
    omega.
    }
  }
Qed.


Lemma le_ord_trans :
  forall u v w, u <<= v -> v <<= w -> u <<= w.
Proof.
intros u v w Huv Hvw.
invertc Huv.
  {
  intros a b c d Hac <- <-.
  invertc Hvw.
    {
    intros e f Hce <-.
    apply le_ord_fst.
    omega.
    }

    {
    intros e Hde <-.
    apply le_ord_fst; auto.
    }
  }

  {
  intros a b c Hbc <- <-.
  invertc Hvw.
    {
    intros d e Had <-.
    apply le_ord_fst; auto.
    }

    {
    intros d Hcd <-.
    apply le_ord_snd.
    omega.
    }
  }
Qed.


Lemma le_ord_succ :
  forall v w, v <<= w -> succ v <<= succ w.
Proof.
intros v w H.
invertc H.
  {
  intros a b c d Hac <- <-.
  apply le_ord_fst; auto.
  }

  {
  intros a b c Hbc <- <-.
  apply le_ord_snd.
  cbn.
  omega.
  }
Qed.


Lemma lt_ord_succ :
  forall v w,
    v << w
    -> succ v << succ w.
Proof.
intros v w H.
apply le_ord_succ; auto.
Qed.


Lemma lt_ord_0_succ :
  forall w,
    fin 0 << succ w.
Proof.
intros w.
unfold lt_ord.
apply le_ord_succ.
apply le_ord_zero.
Qed.


Lemma succ_increase :
  forall w, w << succ w.
Proof.
intro w.
apply le_ord_succ.
apply le_ord_refl.
Qed.


Lemma succ_nodecrease :
  forall w, w <<= succ w.
Proof.
intro w.
apply lt_ord_impl_le_ord.
apply succ_increase.
Qed.


Lemma le_lt_ord_trans :
  forall u v w, u <<= v -> v << w -> u << w.
Proof.
unfold lt_ord.
intros u v w Huv Hvw.
eapply le_ord_trans; eauto.
apply le_ord_succ; auto.
Qed.


Lemma lt_le_ord_trans :
  forall u v w, u << v -> v <<= w -> u << w.
Proof.
unfold lt_ord.
intros u v w Huv Hvw.
eapply le_ord_trans; eauto.
Qed.


Lemma lt_ord_trans :
  forall u v w, u << v -> v << w -> u << w.
Proof.
intros u v w Huv Hvw.
eapply lt_le_ord_trans; eauto.
apply lt_ord_impl_le_ord; auto.
Qed.


Lemma lt_ord_irrefl :
  forall w, ~ w << w.
Proof.
intros w H.
unfold lt_ord in H.
destruct w as (i, j).
unfold succ in H.
cbn in H.
invert H; intros; omega.
Qed.


Lemma lt_ord_wf :
  forall w, Acc lt_ord w.
Proof.
intros w.
destruct w as (i, j).
revert j.
wfinduct i using lt_wf.
intros i IHi.
intro j.
wfinduct j using lt_wf.
intros j IHj.
apply Acc_intro.
intros (k, l) H.
invertc H.
  {
  intros Hki.
  apply IHi; auto.
  }

  {
  intros Hlj ->.
  apply IHj; auto.
  }
Qed.


Lemma eq_ord_dec :
  forall (v w : ordinal), {v = w} + {v <> w}.
Proof.
intros (a, b) (c, d).
so (eq_nat_dec a c) as [| Hneq].
2:{
  right.
  intro H.
  injection H.
  intros; contradiction.
  }
subst c.
so (eq_nat_dec b d) as [| Hneq].
2:{
  right.
  intro H.
  injection H.
  intros; contradiction.
  }
subst d.
left; reflexivity.
Qed.


Lemma lt_eq_lt_ord_dec :
  forall v w, {v << w} + {v = w} + {w << v}.
Proof.
intros (a, b) (c, d).
so (lt_eq_lt_dec a c) as [[Hac | Heq] | Hca].
  {
  left; left.
  apply le_ord_fst; auto.
  }

  {
  subst c.
  so (lt_eq_lt_dec b d) as [[Hbd | Heq] | Hdb].
    {
    left; left.
    apply le_ord_snd.
    cbn.
    omega.
    }

    {
    subst d.
    left; right.
    reflexivity.
    }

    {
    right.
    apply le_ord_snd.
    cbn.
    omega.
    }
  }

  {
  right.
  apply le_ord_fst; auto.
  }
Qed.


Lemma le_ord_dec :
  forall v w, {v <<= w} + {~ v <<= w}.
Proof.
intros v w.
so (lt_eq_lt_ord_dec v w) as [[H | H]|H].
  {
  left.
  apply lt_ord_impl_le_ord; auto.
  }

  {
  subst w.
  left.
  apply le_ord_refl.
  }

  {
  right.
  intros H'.
  apply (lt_ord_irrefl v).
  eapply le_lt_ord_trans; eauto.
  }
Qed.


Lemma lt_ord_dec :
  forall v w, {v << w} + {~ v << w}.
Proof.
intros v w.
so (lt_eq_lt_ord_dec v w) as [[H | H]|H].
  {
  left; auto.
  }

  {
  subst w.
  right.
  apply lt_ord_irrefl.
  }

  {
  right.
  intros H'.
  apply (lt_ord_irrefl v).
  eapply lt_ord_trans; eauto.
  }
Qed.


Lemma le_lt_ord_dec :
  forall v w, {v <<= w} + {w << v}.
Proof.
intros v w.
so (lt_eq_lt_ord_dec v w) as [[Hlt | Heq]|Hlt]; subst; auto using le_ord_refl, lt_ord_impl_le_ord.
Qed.


Lemma lt_ord_dec_is :
  forall v w (h : v << w),
    lt_ord_dec v w = left h.
Proof.
intros v w h.
set (X := lt_ord_dec v w).
destruct X as [h' | Hnlt].
  {
  f_equal.
  apply proof_irrelevance.
  }

  {
  contradiction.
  }
Qed.


Lemma le_ord_dec_is :
  forall v w (h : v <<= w),
    le_ord_dec v w = left h.
Proof.
intros v w h.
set (X := le_ord_dec v w).
destruct X as [h' | Hnlt].
  {
  f_equal.
  apply proof_irrelevance.
  }

  {
  contradiction.
  }
Qed.


Lemma lt_ord_dec_is_not :
  forall v w (h : ~ v << w),
    lt_ord_dec v w = right h.
Proof.
intros v w h.
set (X := lt_ord_dec v w).
destruct X as [Hlt | h'].
  {
  contradiction.
  }

  {
  f_equal.
  apply proof_irrelevance.
  }
Qed.


Lemma le_lt_eq_ord_dec :
  forall v w, v <<= w -> {v << w} + {v = w}.
Proof.
intros v w Hvw.
so (lt_eq_lt_ord_dec v w) as [[H | H]|H]; auto.
destruct (lt_ord_irrefl v).  
eapply le_lt_ord_trans; eauto.
Qed.


Lemma le_ord_nlt_impl_eq :
  forall v w, v <<= w -> ~ v << w -> v = w.
Proof.
intros v w Hle Hnlt.
so (le_lt_eq_ord_dec v w Hle) as [Hlt | Heq]; auto.
contradiction.
Qed.


Lemma not_le_ord_impl_lt_ord :
  forall v w,
    ~ v <<= w -> w << v.
Proof.
intros v w Hnle.
so (lt_eq_lt_ord_dec v w) as [[H | H]|H]; auto.
  {
  destruct Hnle.
  apply lt_ord_impl_le_ord; auto.
  }
 
  {
  subst v.
  destruct Hnle.
  apply le_ord_refl.
  }
Qed.


Lemma not_lt_ord_impl_le_ord :
  forall v w, ~ v << w -> w <<= v.
Proof.
intros v w H.
so (le_ord_dec w v) as [| Hnle]; auto.
destruct H.
apply not_le_ord_impl_lt_ord; auto.
Qed.


Lemma not_le_ord_impl_le_ord :
  forall v w,
    ~ v <<= w -> w <<= v.
Proof.
intros v w Hnle.
apply lt_ord_impl_le_ord.
apply not_le_ord_impl_lt_ord; auto.
Qed.


Lemma le_ord_succ_cancel :
  forall v w, succ v <<= succ w -> v <<= w.
Proof.
intros v w H.
so (le_ord_dec v w) as [| Hnle]; auto.
exfalso.
apply (lt_ord_irrefl (succ w)).
eapply lt_le_ord_trans; eauto.
apply lt_ord_succ.
apply not_le_ord_impl_lt_ord; auto.
Qed.


Definition min_ord (v w : ordinal) : ordinal :=
  match le_ord_dec w v with
  | left _ => w
  | right _ => v
  end.


Definition max_ord (v w : ordinal) : ordinal :=
  match le_ord_dec v w with
  | left _ => w
  | right _ => v
  end.


Lemma min_ord_id :
  forall w, min_ord w w = w.
Proof.
intros w.
unfold min_ord.
set (X := le_ord_dec w w).
destruct X as [H | H]; auto.
Qed.


Lemma max_ord_id :
  forall w, max_ord w w = w.
Proof.
intros w.
unfold max_ord.
set (X := le_ord_dec w w).
destruct X as [H | H]; auto.
Qed.


Lemma min_ord_l :
  forall v w, v <<= w -> min_ord v w = v.
Proof.
intros v w Hwv.
unfold min_ord.
set (X := le_ord_dec w v).
destruct X as [H | H]; auto.
apply le_ord_antisymm; auto.
Qed.


Lemma max_ord_l :
  forall v w, w <<= v -> max_ord v w = v.
Proof.
intros v w Hwv.
unfold max_ord.
set (X := le_ord_dec v w).
destruct X as [H | H]; auto.
apply le_ord_antisymm; auto.
Qed.


Lemma min_ord_r :
  forall v w, w <<= v -> min_ord v w = w.
Proof.
intros v w Hvw.
unfold min_ord.
set (X := le_ord_dec w v).
destruct X as [H | H]; auto.
contradiction.
Qed.


Lemma max_ord_r :
  forall v w, v <<= w -> max_ord v w = w.
Proof.
intros v w Hvw.
unfold max_ord.
set (X := le_ord_dec v w).
destruct X as [H | H]; auto.
contradiction.
Qed.


Lemma le_ord_min_l :
  forall v w, min_ord v w <<= v.
Proof.
intros v w.
so (le_ord_dec w v) as [H | H].
  {
  rewrite -> min_ord_r; auto.
  }

  {
  rewrite -> min_ord_l; auto using le_ord_refl.
  apply not_le_ord_impl_le_ord; auto.
  }
Qed.


Lemma le_ord_max_l :
  forall v w, v <<= max_ord v w.
Proof.
intros v w.
so (le_ord_dec v w) as [H | H].
  {
  rewrite -> max_ord_r; auto.
  }

  {
  rewrite -> max_ord_l; auto using le_ord_refl.
  apply not_le_ord_impl_le_ord; auto.
  }
Qed.


Lemma le_ord_min_r :
  forall v w, min_ord v w <<= w.
Proof.
intros v w.
so (le_ord_dec v w) as [H | H].
  {
  rewrite -> min_ord_l; auto.
  }

  {
  rewrite -> min_ord_r; auto using le_ord_refl.
  apply not_le_ord_impl_le_ord; auto.
  }
Qed.


Lemma le_ord_max_r :
  forall v w, w <<= max_ord v w.
Proof.
intros v w.
so (le_ord_dec w v) as [H | H].
  {
  rewrite -> max_ord_l; auto.
  }

  {
  rewrite -> max_ord_r; auto using le_ord_refl.
  apply not_le_ord_impl_le_ord; auto.
  }
Qed.


Lemma min_ord_glb :
  forall u v w,
    w <<= u
    -> w <<= v
    -> w <<= min_ord u v.
Proof.
intros u v w Huw Hvw.
so (le_ord_dec v u) as [H | H].
  {
  rewrite -> min_ord_r; auto.
  }

  {
  rewrite -> min_ord_l; auto.
  apply not_le_ord_impl_le_ord; auto.
  }
Qed.


Lemma max_ord_lub :
  forall u v w,
    u <<= w
    -> v <<= w
    -> max_ord u v <<= w.
Proof.
intros u v w Huw Hvw.
so (le_ord_dec u v) as [H | H].
  {
  rewrite -> max_ord_r; auto.
  }

  {
  rewrite -> max_ord_l; auto.
  apply not_le_ord_impl_le_ord; auto.
  }
Qed.


Lemma min_ord_glb_l :
  forall u v w, w <<= min_ord u v -> w <<= u.
Proof.
intros u v w Hle.
eapply le_ord_trans; eauto.
apply le_ord_min_l.
Qed.


Lemma max_ord_lub_l :
  forall u v w, max_ord u v <<= w -> u <<= w.
Proof.
intros u v w Hle.
eapply le_ord_trans; eauto.
apply le_ord_max_l.
Qed.


Lemma min_ord_glb_r :
  forall u v w, w <<= min_ord u v -> w <<= v.
Proof.
intros u v w Hle.
eapply le_ord_trans; eauto.
apply le_ord_min_r.
Qed.


Lemma max_ord_lub_r :
  forall u v w, max_ord u v <<= w -> v <<= w.
Proof.
intros u v w Hle.
eapply le_ord_trans; eauto.
apply le_ord_max_r.
Qed.


Lemma succ_min_ord :
  forall v w, succ (min_ord v w) = min_ord (succ v) (succ w).
Proof.
intros v w.
so (le_ord_dec w v) as [Hvw | Hnvw].
  {
  rewrite -> !min_ord_r; auto.
  apply le_ord_succ; auto.
  }

  {
  so (not_le_ord_impl_le_ord _ _ Hnvw) as Hwv.
  rewrite -> !min_ord_l; auto.
  apply le_ord_succ; auto.
  }
Qed.


Lemma succ_max_ord :
  forall v w, succ (max_ord v w) = max_ord (succ v) (succ w).
Proof.
intros v w.
so (le_ord_dec v w) as [Hvw | Hnvw].
  {
  rewrite -> !max_ord_r; auto.
  apply le_ord_succ; auto.
  }

  {
  so (not_le_ord_impl_le_ord _ _ Hnvw) as Hwv.
  rewrite -> !max_ord_l; auto.
  apply le_ord_succ; auto.
  }
Qed.


Lemma min_ord_glb_strict :
  forall u v w,
    w << u
    -> w << v
    -> w << min_ord u v.
Proof.
intros u v w Huw Hvw.
apply min_ord_glb; auto.
Qed.


Lemma max_ord_lub_strict :
  forall u v w,
    u << w
    -> v << w
    -> max_ord u v << w.
Proof.
intros u v w Huw Hvw.
unfold lt_ord.
rewrite -> succ_max_ord.
apply max_ord_lub; auto.
Qed.


Lemma min_ord_glb_strict_l :
  forall u v w, w << min_ord u v -> w << u.
Proof.
intros u v w H.
eapply min_ord_glb_l; eauto.
Qed.


Lemma max_ord_lub_strict_l :
  forall u v w, max_ord u v << w -> u << w.
Proof.
intros u v w H.
eapply le_lt_ord_trans; eauto.
apply le_ord_max_l.
Qed.


Lemma min_ord_glb_strict_r :
  forall u v w, w << min_ord u v -> w << v.
Proof.
intros u v w H.
eapply min_ord_glb_r; eauto.
Qed.


Lemma max_ord_lub_strict_r :
  forall u v w, max_ord u v << w -> v << w.
Proof.
intros u v w H.
eapply le_lt_ord_trans; eauto.
apply le_ord_max_r.
Qed.


Lemma min_ord_comm :
  forall v w, min_ord v w = min_ord w v.
Proof.
intros v w.
so (le_ord_dec w v) as [H | H].
  {
  rewrite -> min_ord_r; auto.
  rewrite -> min_ord_l; auto.
  }

  {
  so (not_le_ord_impl_le_ord _ _ H) as H'.
  rewrite -> min_ord_l; auto.
  rewrite -> min_ord_r; auto.
  }
Qed.


Lemma max_ord_comm :
  forall v w, max_ord v w = max_ord w v.
Proof.
intros v w.
so (le_ord_dec v w) as [H | H].
  {
  rewrite -> max_ord_r; auto.
  rewrite -> max_ord_l; auto.
  }

  {
  so (not_le_ord_impl_le_ord _ _ H) as H'.
  rewrite -> max_ord_l; auto.
  rewrite -> max_ord_r; auto.
  }
Qed.


Lemma min_ord_assoc :
  forall u v w, min_ord u (min_ord v w) = min_ord (min_ord u v) w.
Proof.
intros u v w.
so (le_ord_dec w v) as [Hvw | Hnvw].
  {
  rewrite -> (min_ord_r v w); auto.
  so (le_ord_dec v u) as [Huv | Hnuv].
    {
    rewrite -> (min_ord_r u v); auto.
    rewrite -> (min_ord_r v w); auto.
    rewrite -> (min_ord_r u w); auto.
    eapply le_ord_trans; eauto.
    }

    {
    so (not_le_ord_impl_le_ord _ _ Hnuv) as Hvu.
    rewrite -> (min_ord_l u v); auto.
    }
  }

  {
  so (not_le_ord_impl_le_ord _ _ Hnvw) as Hwv.
  rewrite -> (min_ord_l v w); auto.
  so (le_ord_dec v u) as [Huv | Hnuv].
    {
    rewrite -> (min_ord_r u v); auto.
    rewrite -> min_ord_l; auto.
    }

    {
    so (not_le_ord_impl_le_ord _ _ Hnuv) as Hvu.
    rewrite -> (min_ord_l u v); auto.
    rewrite -> min_ord_l; auto.
    eapply le_ord_trans; eauto.
    }
  }
Qed.


Lemma max_ord_assoc :
  forall u v w, max_ord u (max_ord v w) = max_ord (max_ord u v) w.
Proof.
intros u v w.
so (le_ord_dec v w) as [Hvw | Hnvw].
  {
  rewrite -> (max_ord_r v w); auto.
  so (le_ord_dec u v) as [Huv | Hnuv].
    {
    rewrite -> (max_ord_r u v); auto.
    rewrite -> (max_ord_r v w); auto.
    rewrite -> (max_ord_r u w); auto.
    eapply le_ord_trans; eauto.
    }

    {
    so (not_le_ord_impl_le_ord _ _ Hnuv) as Hvu.
    rewrite -> (max_ord_l u v); auto.
    }
  }

  {
  so (not_le_ord_impl_le_ord _ _ Hnvw) as Hwv.
  rewrite -> (max_ord_l v w); auto.
  so (le_ord_dec u v) as [Huv | Hnuv].
    {
    rewrite -> (max_ord_r u v); auto.
    rewrite -> max_ord_l; auto.
    }

    {
    so (not_le_ord_impl_le_ord _ _ Hnuv) as Hvu.
    rewrite -> (max_ord_l u v); auto.
    rewrite -> max_ord_l; auto.
    eapply le_ord_trans; eauto.
    }
  }
Qed.


Lemma min_ord_mono :
  forall v v' w w',
    v <<= v'
    -> w <<= w'
    -> min_ord v w <<= min_ord v' w'.
Proof.
intros v v' w w' Hv Hw.
so (le_lt_ord_dec w v) as [Hvw | Hwv].
  {
  rewrite -> (min_ord_r v w); auto.
  apply min_ord_glb; eauto using le_ord_trans.
  }

  {
  so (lt_ord_impl_le_ord _ _ Hwv) as Hwv'.
  rewrite -> (min_ord_l v w); auto.
  apply min_ord_glb; eauto using le_ord_trans.
  }
Qed.


Lemma max_ord_mono :
  forall v v' w w',
    v <<= v'
    -> w <<= w'
    -> max_ord v w <<= max_ord v' w'.
Proof.
intros v v' w w' Hv Hw.
so (le_lt_ord_dec v' w') as [Hvw | Hwv].
  {
  rewrite -> (max_ord_r v' w'); auto.
  apply max_ord_lub; eauto using le_ord_trans.
  }

  {
  so (lt_ord_impl_le_ord _ _ Hwv) as Hwv'.
  rewrite -> (max_ord_l v' w'); auto.
  apply max_ord_lub; eauto using le_ord_trans.
  }
Qed.


Definition limitord w : Prop
  :=
  fin 0 << w
  /\
  forall v, v << w -> succ v << w.


Lemma limitord_lub :
  forall w v,
    limitord w
    -> (forall u, u << w -> u <<= v)
    -> w <<= v.
Proof.
intros w v Hlimit Hv.
so (le_ord_dec w v) as [| Hnle]; auto.
destruct (lt_ord_irrefl v).
so (not_le_ord_impl_lt_ord _ _ Hnle) as Hlt.
so (Hlimit ander _ Hlt) as Hlt'.
so (Hv _ Hlt') as Hle.
eapply le_lt_ord_trans; eauto.
Qed.


Lemma ordinal_trichot :
  forall w,
    { w = fin 0 } + { exists v, w = succ v } + { limitord w }.
Proof.
intros w.
destruct w as (i, j).
destruct j as [| j].
  {
  destruct i as [| j].
    {
    left; left.
    reflexivity.
    }
  
    {
    right.
    split.
      {
      apply le_ord_fst.
      cbn.
      omega.
      }

      {
      intros v Hv.
      destruct v as (k, l).
      unfold lt_ord in Hv.
      invertc Hv.
        {
        intro H; apply le_ord_fst; auto.
        }

        {
        intros; omega.
        }
      }
    }
  }

  {
  left; right.
  exists (i, j).
  reflexivity.
  }
Qed.
