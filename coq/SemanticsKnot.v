
Require Import Tactics.
Require Import Axioms.
Require Import Sigma.
Require Import Equality.
Require Import Relation.
Require Import Syntax.
Require Import SimpSub.
Require Import Dynamic.
Require Import Ofe.
Require Import Spaces.
Require Import Uniform.
Require Import Urelsp.
Require Import Intensional.
Require Import Ordinal.
Require Import Truncate.
Require Import Candidate.
Require Import System.
Require Import Extend.
Require Import Hygiene.
Require Import Equivalence.
Require Import Possible.
Require Import MapTerm.
Require Import Model.

Require Export Semantics.
Require Import SemanticsUniv.
Require Import ProperClosed.
Require Import ProperEquiv.
Require Import ProperFun.
Require Import ProperDownward.
Require Import ProperMono.


Lemma agree_refl :
  forall pg system,
    agree pg system system.
Proof.
intros pg system.
split; auto.
Qed.


Lemma agree_symm :
  forall pg system system',
    agree pg system system'
    -> agree pg system' system.
Proof.
intros pg system system' H.
destruct H.
split; auto.
Qed.


Lemma agree_trans :
  forall pg s1 s2 s3,
    agree pg s1 s2
    -> agree pg s2 s3
    -> agree pg s1 s3.
Proof.
intros pg s1 s2 s3 (H12 & H12k) (H23 & H23k).
split; etransitivity; eauto.
Qed.


Definition system_le (system system' : System) : Prop
  :=
  (forall w, valid system w -> valid system' w)
  /\
  (forall pg, valid system (str pg) -> agree pg system system').


Lemma system_le_refl :
  forall sys,
    system_le sys sys.
Proof.
intro sys.
split; auto.
intros pg _.
apply agree_refl.
Qed.


Lemma system_le_trans :
  forall s1 s2 s3,
    system_le s1 s2
    -> system_le s2 s3
    -> system_le s1 s3.
Proof.
intros s1 s2 s3 H12 H23.
split.
  {
  intros w Hw.
  apply H23.
  apply H12; auto.
  }

  {
  intros w Hw.
  destruct H12, H23.
  eapply agree_trans; eauto.
  }
Qed.


Record toset : Type :=
mk_toset
  { elem : Type ;
    le_toset : elem -> elem -> Prop ;

    toset_refl : forall x, le_toset x x ;

    toset_total : forall x y, { le_toset x y } + { le_toset y x } ;
  }.


Definition max_toset {T : toset} (x y : elem T) : elem T
  :=
  match toset_total T x y with
  | left _ => y
  | right _ => x
  end.


Lemma le_toset_max_l :
  forall T x y, le_toset T x (max_toset x y).
Proof.
intros T x y.
unfold max_toset.
set (X := toset_total T x y).
destruct X; auto using toset_refl.
Qed.


Lemma le_toset_max_r :
  forall T x y, le_toset T y (max_toset x y).
Proof.
intros T x y.
unfold max_toset.
set (X := toset_total T x y).
destruct X; auto using toset_refl.
Qed.


Lemma chain_valid_agree :
  forall (T : toset) (chain : elem T -> System) x y pg,
    (forall x y, le_toset T x y -> system_le (chain x) (chain y))
    -> valid (chain x) (str pg)
    -> valid (chain y) (str pg)
    -> agree pg (chain x) (chain y).
Proof.
intros T chain x y pg Hall Hxw Hyw.
so (toset_total _ x y) as [Hxy | Hyx].
  {
  so (Hall _ _ Hxy) as Hle.
  exact (Hle ander pg Hxw).
  }

  {
  so (Hall _ _ Hyx) as Hle.
  apply agree_symm.
  exact (Hle ander pg Hyw).
  }
Qed.


Definition system_join_valid (T : toset) (chain : elem T -> System) : ordinal -> Prop
  :=
  fun w => exists x, valid (chain x) w.


Definition system_join_sint (T : toset) (chain : elem T -> System)
  : page -> bool -> nat -> term (obj stop) -> siurel -> Prop
  :=
  fun pg s i a Q => exists x, valid (chain x) (str pg) /\ sint (chain x) pg s i a Q.


Definition system_join_sintk (T : toset) (chain : elem T -> System)
  : page -> bool -> nat -> term (obj stop) -> qkind -> Prop
  :=
  fun pg s i a K => exists x, valid (chain x) (str pg) /\ sintk (chain x) pg s i a K.


Lemma system_join_sint_eq_sint :
  forall T chain pg x,
    (forall x y, le_toset T x y -> system_le (chain x) (chain y))
    -> valid (chain x) (str pg)
    -> system_join_sint T chain pg = sint (chain x) pg.
Proof.
intros T chain pg x Hchain Hxw.
fextensionality 4.
intros s i c Q.
pextensionality.
  {
  intros (y & Hy & Hint).
  exploit (chain_valid_agree T chain x y pg) as H; auto.
  rewrite -> (H andel); auto.
  }

  {
  intros Hint.
  exists x.
  split; auto.
  }
Qed.


Lemma system_join_sintk_eq_sintk :
  forall T chain pg x,
    (forall x y, le_toset T x y -> system_le (chain x) (chain y))
    -> valid (chain x) (str pg)
    -> system_join_sintk T chain pg = sintk (chain x) pg.
Proof.
intros T chain pg x Hchain Hxw.
fextensionality 4.
intros s i c Q.
pextensionality.
  {
  intros (y & Hy & Hint).
  exploit (chain_valid_agree T chain x y pg) as H; auto.
  rewrite -> (H ander); auto.
  }

  {
  intros Hint.
  exists x.
  split; auto.
  }
Qed.


Lemma system_join_valid_downward :
  forall T chain v w,
    v <<= w
    -> system_join_valid T chain w
    -> system_join_valid T chain v.
Proof.
intros T chain v w Hvw (x & Hw).
exists x.
eapply valid_downward; eauto.
Qed.


Lemma system_join_sint_closed :
  forall T chain pg s i c Q,
    system_join_sint T chain pg s i c Q
    -> hygiene clo c.
Proof.
intros T chain pg s i a Q (x & Hvalid & Hint).
eapply sint_closed; eauto.
Qed.


Lemma system_join_sintk_closed :
  forall T chain pg s i c K,
    system_join_sintk T chain pg s i c K
    -> hygiene clo c.
Proof.
intros T chain pg s i a Q (x & Hvalid & Hint).
eapply sintk_closed; eauto.
Qed.


Lemma system_join_sint_equiv :
  forall T chain pg s i c c' Q,
    hygiene clo c'
    -> equiv c c'
    -> system_join_sint T chain pg s i c Q
    -> system_join_sint T chain pg s i c' Q.
Proof.
intros T chain pg s i c c' Q Hcl Hequiv (x & Hxw & Hint).
exists x.
split; auto.
eapply sint_equiv; eauto.
Qed.


Lemma system_join_sintk_equiv :
  forall T chain pg s i c c' Q,
    hygiene clo c'
    -> equiv c c'
    -> system_join_sintk T chain pg s i c Q
    -> system_join_sintk T chain pg s i c' Q.
Proof.
intros T chain pg s i c c' Q Hcl Hequiv (x & Hxw & Hint).
exists x.
split; auto.
eapply sintk_equiv; eauto.
Qed.


Lemma system_join_sint_fun :
  forall T chain,
    (forall x y, le_toset T x y -> system_le (chain x) (chain y))
    -> forall pg s i c Q Q',
         system_join_sint T chain pg s i c Q
         -> system_join_sint T chain pg s i c Q'
         -> Q = Q'.
Proof.
intros T chain Hchain pg s i c Q Q' (x & Hvalidx & Hintx) (y & Hvalidy & Hinty).
set (z := max_toset x y).
eapply (sint_fun (chain z)).
  {
  so (Hchain x z (le_toset_max_l _#3) ander _ Hvalidx) as H; auto.
  rewrite <- (H andel); eauto.
  }

  {
  so (Hchain y z (le_toset_max_r _#3) ander _ Hvalidy) as H; auto.
  rewrite <- (H andel); eauto.
  }
Qed.


Lemma system_join_sintk_fun :
  forall T chain,
    (forall x y, le_toset T x y -> system_le (chain x) (chain y))
    -> forall pg s i c Q Q',
         system_join_sintk T chain pg s i c Q
         -> system_join_sintk T chain pg s i c Q'
         -> Q = Q'.
Proof.
intros T chain Hchain pg s i c Q Q' (x & Hvalidx & Hintx) (y & Hvalidy & Hinty).
set (z := max_toset x y).
eapply (sintk_fun (chain z)).
  {
  so (Hchain x z (le_toset_max_l _#3) ander _ Hvalidx) as H; auto.
  rewrite <- (H ander); eauto.
  }

  {
  so (Hchain y z (le_toset_max_r _#3) ander _ Hvalidy) as H; auto.
  rewrite <- (H ander); eauto.
  }
Qed.


Lemma system_join_sint_downward :
  forall T chain pg s i j c R,
    j <= i
    -> system_join_sint T chain pg s i c R
    -> system_join_sint T chain pg s j c (iutruncate (S j) R).
Proof.
intros T chain pg s i j c Q Hj (x & Hxw & Hint).
exists x.
split; auto.
eapply sint_downward; eauto.
Qed.


Lemma system_join_sintk_downward :
  forall T chain pg s i j c R,
    j <= i
    -> system_join_sintk T chain pg s i c R
    -> system_join_sintk T chain pg s j c (approx j R).
Proof.
intros T chain pg s i j c Q Hj (x & Hxw & Hint).
exists x.
split; auto.
eapply sintk_downward; eauto.
Qed.


Definition system_join
  (T : toset)
  (chain : elem T -> System)
  (Hchain : forall x y, le_toset T x y -> system_le (chain x) (chain y))
  : System
  :=
  mk_system
    (system_join_valid T chain)
    (system_join_sint T chain)
    (system_join_sintk T chain)
    (system_join_valid_downward T chain)
    (system_join_sint_closed T chain)
    (system_join_sintk_closed T chain)
    (system_join_sint_equiv T chain)
    (system_join_sintk_equiv T chain)
    (system_join_sint_fun T chain Hchain)
    (system_join_sintk_fun T chain Hchain)
    (system_join_sint_downward T chain)
    (system_join_sintk_downward T chain).


Lemma system_join_ub :
  forall T chain Hchain x,
    system_le (chain x) (system_join T chain Hchain).
Proof.
intros T chain Hchain x.
split.
  {
  intros w Hw.
  exists x; auto.
  }

  {
  intros pg Hvalid.
  split.
    {
    fextensionality 4.
    intros s i a R.
    pextensionality.
      {
      intro H.
      exists x; auto.
      }
    intro H.
    destruct H as (y & Hy & H).
    exploit (chain_valid_agree T chain x y pg) as Hagree; auto.
    rewrite -> (Hagree andel); auto.
    }

    {
    fextensionality 4.
    intros s i a R.
    pextensionality.
      {
      intro H.
      exists x; auto.
      }
    intro H.
    destruct H as (y & Hy & H).
    exploit (chain_valid_agree T chain x y pg) as Hagree; auto.
    rewrite -> (Hagree ander); auto.
    }
  }
Qed.


Lemma system_join_lub :
  forall T chain Hchain sys,
    (forall x, system_le (chain x) sys)
    -> system_le (system_join T chain Hchain) sys.
Proof.
intros T chain Hchain sys Hall.
split.
  {
  intros w Hw.
  destruct Hw as (x & Hxw).
  apply (Hall x); auto.
  }
intros pg Hvalid.
split.
  {
  fextensionality 4.
  intros s i a R.
  pextensionality.
    {
    intro H.
    destruct H as (x & Hxw & H).
    so (Hall x ander pg Hxw) as Hagree; auto.
    rewrite <- (Hagree andel); auto.
    }
  
    {
    intro H.
    destruct Hvalid as (x & Hxw).
    so (Hall x ander pg Hxw) as Hagree; auto.
    rewrite <- (Hagree andel) in H; auto.
    exists x; auto.
    }
  }

  {
  fextensionality 4.
  intros s i a R.
  pextensionality.
    {
    intro H.
    destruct H as (x & Hxw & H).
    so (Hall x ander pg Hxw) as Hagree; auto.
    rewrite <- (Hagree ander); auto.
    }
  
    {
    intro H.
    destruct Hvalid as (x & Hxw).
    so (Hall x ander pg Hxw) as Hagree; auto.
    rewrite <- (Hagree ander) in H; auto.
    exists x; auto.
    }
  }
Qed.


Definition system_inc_valid (system : System) : ordinal -> Prop
  :=
  fun w => forall v, v << w -> valid system v.


Definition system_inc_sint (system : System)
  : page -> bool -> nat -> term (obj stop) -> siurel -> Prop
  :=
  basic system.


Definition system_inc_sintk (system : System)
  : page -> bool -> nat -> term (obj stop) -> qkind -> Prop
  :=
  kbasic system.


Lemma system_inc_valid_downward :
  forall system v w,
    v <<= w
    -> system_inc_valid system w
    -> system_inc_valid system v.
Proof.
intros system v w Hvw Hvalid.
intros u Huv.
apply Hvalid.
eapply lt_le_ord_trans; eauto.
Qed.


Lemma system_inc_sint_closed :
  forall system pg s i c Q,
    system_inc_sint system pg s i c Q
    -> hygiene clo c.
Proof.
intros system pg s i c Q H.
eapply basic_closed; eauto.
Qed.


Lemma system_inc_sintk_closed :
  forall system pg s i c Q,
    system_inc_sintk system pg s i c Q
    -> hygiene clo c.
Proof.
intros system pg s i c Q H.
eapply kbasic_closed; eauto.
Qed.


Lemma system_inc_sint_equiv :
  forall system pg s i c c' Q,
    hygiene clo c'
    -> equiv c c'
    -> system_inc_sint system pg s i c Q
    -> system_inc_sint system pg s i c' Q.
Proof.
intros system pg s i c c' Q Hcl Hequiv H.
eapply basic_equiv; eauto.
Qed.


Lemma system_inc_sintk_equiv :
  forall system pg s i c c' Q,
    hygiene clo c'
    -> equiv c c'
    -> system_inc_sintk system pg s i c Q
    -> system_inc_sintk system pg s i c' Q.
Proof.
intros system pg s i c c' Q Hcl Hequiv H.
eapply kbasic_equiv; eauto.
Qed.


Lemma system_inc_sint_fun :
  forall system pg s i c Q Q',
    system_inc_sint system pg s i c Q
    -> system_inc_sint system pg s i c Q'
    -> Q = Q'.
Proof.
intros system pg s i c Q Q' H H'.
eapply basic_fun; eauto.
Qed.


Lemma system_inc_sintk_fun :
  forall system pg s i c Q Q',
    system_inc_sintk system pg s i c Q
    -> system_inc_sintk system pg s i c Q'
    -> Q = Q'.
Proof.
intros system pg s i c Q Q' H H'.
eapply kbasic_fun; eauto.
Qed.


Lemma system_inc_sint_downward :
  forall system pg s i j c R,
    j <= i
    -> system_inc_sint system pg s i c R
    -> system_inc_sint system pg s j c (iutruncate (S j) R).
Proof.
intros system pg s i j c R Hj H.
eapply basic_downward; eauto.
Qed.


Lemma system_inc_sintk_downward :
  forall system pg s i j c K,
    j <= i
    -> system_inc_sintk system pg s i c K
    -> system_inc_sintk system pg s j c (approx j K).
Proof.
intros system pg s i j c R Hj H.
eapply kbasic_downward; eauto.
Qed.


Definition system_inc (system : System) : System
  :=
  mk_system
    (system_inc_valid system)
    (system_inc_sint system)
    (system_inc_sintk system)
    (system_inc_valid_downward system)
    (system_inc_sint_closed system)
    (system_inc_sintk_closed system)
    (system_inc_sint_equiv system)
    (system_inc_sintk_equiv system)
    (system_inc_sint_fun system)
    (system_inc_sintk_fun system)
    (system_inc_sint_downward system)
    (system_inc_sintk_downward system).


Lemma system_inc_mono :
  forall sys sys',
    system_le sys sys'
    -> system_le (system_inc sys) (system_inc sys').
Proof.
intros sys sys' Hle.
split.
  {
  cbn.
  unfold system_inc_valid.
  intros w Hw v Hvw.
  apply Hle; auto.
  }
cbn.
unfold system_inc_valid, system_inc_sint.
intros pg Hvalid.
assert (forall i pg', succ (str pg') << str pg -> univ_urel sys i pg' = univ_urel sys' i pg') as Huniv.
  {
  intros i pg' Hv.
  apply urel_extensionality.
  cbn.
  fextensionality 3.
  intros j a b.
  pextensionality.
    {
    intro H.
    decompose H.
    intros Hj R Hl Hr.
    split; auto.
    exists R.
    split.
      {
      exploit (Hle ander pg') as H; auto.
        {
        apply Hvalid.
        eapply lt_ord_trans; eauto.
        apply succ_increase.
        }
      rewrite <- (H andel); auto.
      }

      {
      exploit (Hle ander pg') as H; auto.
        {
        apply Hvalid.
        eapply lt_ord_trans; eauto.
        apply succ_increase.
        }
      rewrite <- (H andel); auto.
      }
    }

    {
    intro H.
    decompose H.
    intros Hj R Hl Hr.
    split; auto.
    exists R.
    split.
      {
      exploit (Hle ander pg') as H; auto.
        {
        apply Hvalid.
        eapply lt_ord_trans; eauto.
        apply succ_increase.
        }
      rewrite -> (H andel); auto.
      }

      {
      exploit (Hle ander pg') as H; auto.
        {
        apply Hvalid.
        eapply lt_ord_trans; eauto.
        apply succ_increase.
        }
      rewrite -> (H andel); auto.
      }
    }
  }
split.
  {
  fextensionality 4.
  intros s i a Q.
  pextensionality.  
    {
    intro H.
    apply (basic_mono sys sys'); auto.
    intros pg' Hv.
    exact (Hle ander pg' (Hvalid _ Hv)).
    }
  
    {
    intro H.
    apply (basic_mono sys' sys); auto.
    intros pg' Hv.
    apply agree_symm.
    exact (Hle ander pg' (Hvalid _ Hv)).
    }
  }

  {
  fextensionality 4.
  intros s i a Q.
  pextensionality.  
    {
    intro H.
    apply (kbasic_mono sys sys'); auto.
    intros pg' Hv.
    exact (Hle ander pg' (Hvalid _ Hv)).
    }
  
    {
    intro H.
    apply (kbasic_mono sys' sys); auto.
    intros pg' Hv.
    apply agree_symm.
    exact (Hle ander pg' (Hvalid _ Hv)).
    }
  }
Qed.


Definition ordinals_toset_under (w : ordinal) : toset.
Proof.
apply
  (mk_toset
     (existsT (v : ordinal), v << w)
     (fun x y => pi1 x <<= pi1 y)).

(* refl *)
{
intros (v & h).
cbn.
apply le_ord_refl.
}

(* total *)
{
intros (u & h) (v & h').
cbn.
destruct (le_lt_ord_dec u v); auto.
right.
apply lt_ord_impl_le_ord; auto.
}
Defined.


Fixpoint pre_systems (w : ordinal) (acc : Acc lt_ord w) {struct acc} : poss System
  :=
  poss_bind
    (poss_lift (fun x => pre_systems (pi1 x) (Acc_inv acc (pi2 x))))
    (fun f =>
       poss_assume _
       (fun p => poss_unit (system_inc (system_join (ordinals_toset_under w) f p)))).


Lemma pre_systems_increasing :
  forall w,
    poss_hyp
      (fun sys => system_le sys (system_inc sys))
      (pre_systems w (lt_ord_wf w)).
Proof.
intro w.
wfinduct w using lt_ord_wf.
intros w IH.
set (X := lt_ord_wf w).
destruct X as [acc].
cbn.
set (P := fun (p : elem (ordinals_toset_under w)) sys => system_le sys (system_inc sys)).
apply (poss_bind_hyp _ _ (fun f => forall p, P p (f p))).
  {
  intros f Hf.
  apply poss_lift_hyp.
  intros p.
  replace (acc (pi1 p) (pi2 p)) with (lt_ord_wf (pi1 p)) by (apply proof_irrelevance).
  apply IH.
  exact (pi2 p).
  }
intros f Hf.
apply poss_assume_hyp.
intros H.
apply poss_unit_hyp.
apply system_inc_mono.
apply system_join_lub.
intro p.
so (Hf p) as Hle.
eapply system_le_trans; eauto.
apply system_inc_mono.
apply system_join_ub.
Qed.


Lemma pre_systems_ordered :
  forall w,
    poss_hyp 
      (fun sys' => forall v, v << w -> poss_hyp (fun sys => system_le sys sys') (pre_systems v (lt_ord_wf v)))
      (pre_systems w (lt_ord_wf w)).
Proof.
intros w.
set (X := lt_ord_wf w).
destruct X as [acc].
cbn.
set (P := fun (p : elem (ordinals_toset_under w)) sys => forall H, sys = pi2 (pre_systems (pi1 p) (lt_ord_wf _)) H).
apply (poss_bind_hyp _ _ (fun f => forall p, P p (f p))).
  {
  intros f.
  apply poss_lift_hyp.
  intros p.
  subst P.
  intros H H'.
  assert (acc = fun v _ => lt_ord_wf v).
    {
    fextensionality 1.
    intro v.
    apply proof_irrelevance.
    }
  subst acc.
  f_equal.
  apply proof_irrelevance.
  }
intros f Heq.
apply poss_assume_hyp.
intros Hf.
apply poss_unit_hyp.
intros v Hvw.
intros Hv.
eapply system_le_trans.
  {
  exact (pre_systems_increasing v Hv).
  }
apply system_inc_mono.
subst P.
cbn in Heq.
so (Heq (expair v Hvw) Hv) as Heq'.
cbn in Heq'.
rewrite <- Heq'.
apply system_join_ub.
Qed.


Lemma pre_systems_sat :
  forall w,
    pi1 (pre_systems w (lt_ord_wf w)).
Proof.
intros w.
wfinduct w using lt_ord_wf.
intros w IH.
set (X := lt_ord_wf w).
destruct X as [acc].
cbn.
eexists.
Unshelve.
2:{
  intros (v & Hvw).
  cbn.
  replace (acc v Hvw) with (lt_ord_wf v) by (apply proof_irrelevance).
  apply IH; auto.
  }
eexists; auto.
intros p q Hle.
destruct p as (u & Huw).
destruct q as (v & Hvw).
cbn in Hle.
cbn.
so (pre_systems_ordered v) as H.
match goal with
| |- system_le _ (pi2 _ ?HH) => set (H2 := HH)
end.
match goal with
| |- system_le (pi2 _ ?HH) _ => set (H1 := HH)
end.
clearbody H1 H2.
cbn in H1, H2.
set (X := acc u Huw) in H1 |- *.
clearbody X.
assert (X = lt_ord_wf u) by (apply proof_irrelevance).
subst X.
set (X := acc v Hvw) in H2 |- *.
clearbody X.
assert (X = lt_ord_wf v) by (apply proof_irrelevance).
subst X.
so (le_lt_eq_ord_dec _ _ Hle) as [Hlt | Heq].
  {
  apply pre_systems_ordered; auto.
  }

  {
  subst v.
  so (proof_irrelevance _ H1 H2); subst H2.
  apply system_le_refl.
  }
Qed.


Definition systems (w : ordinal) : System := pi2 (pre_systems w (lt_ord_wf w)) (pre_systems_sat w).


Lemma systems_ordered :
  forall v w,
    v <<= w
    -> system_le (systems v) (systems w).
Proof.
intros v w Hle.
so (le_lt_eq_ord_dec _ _ Hle) as [Hlt | Heq].
2:{
  subst v.
  apply system_le_refl.
  }
exact (pre_systems_ordered w (pre_systems_sat _) v Hlt (pre_systems_sat _)).
Qed.


Definition ordinals_toset : toset.
Proof.
apply
  (mk_toset ordinal le_ord le_ord_refl).

(* total *)
{
intros u v.
destruct (le_lt_ord_dec u v); auto.
right.
apply lt_ord_impl_le_ord; auto.
}
Defined.


Definition the_system : System
  := system_join ordinals_toset systems systems_ordered.


Lemma systems_all_valid :
  forall w, valid (systems (succ w)) w.
Proof.
intros w.
wfinduct w using lt_ord_wf.
intros w IH.
unfold systems.
generalize (pre_systems_sat (succ w)) as Hsat.
set (X := lt_ord_wf (succ w)).
destruct X as [acc].
intro Hsat.
cbn.
intros v Hvw.
cbn.
exists (expair (succ v) (lt_ord_succ _ _ Hvw)).
cbn.
so (IH v Hvw) as H.
unfold systems in H.
match goal with
| |- valid (pi2 (pre_systems _ ?HH1) ?HH2) _ =>
    set (H2 := HH2)
end.
clearbody H2.
cbn in H2.
match goal with
| |- valid (pi2 (pre_systems _ ?HH1) ?HH2) _ =>
    set (H1 := HH1) in H2 |- *
end.
clearbody H1.
so (proof_irrelevance _ H1 (lt_ord_wf (succ v))); subst H1.
so (proof_irrelevance _ H2 (pre_systems_sat (succ v))); subst H2.
exact H.
Qed.


Lemma the_system_all_valid :
  forall w, valid the_system w.
Proof.
intros w.
exists (succ w).
apply systems_all_valid.
Qed.


Lemma system_extensionality :
  forall sys sys',
    valid sys = valid sys'
    -> sint sys = sint sys'
    -> sintk sys = sintk sys'
    -> sys = sys'.
Proof.
intros sys sys' Heq1 Heq2 Heq3.
destruct sys as [valid sint sintk H1 H2 H3 H4 H5 H6 H7 H8 H9].
destruct sys' as [valid' sint' sintk' H1' H2' H3' H4' H5' H6' H7' H8' H9'].
cbn in Heq1.
subst valid'.
cbn in Heq2.
subst sint'.
cbn in Heq3.
subst sintk'.
so (proof_irrelevance _ H1 H1'); subst H1'.
so (proof_irrelevance _ H2 H2'); subst H2'.
so (proof_irrelevance _ H3 H3'); subst H3'.
so (proof_irrelevance _ H4 H4'); subst H4'.
so (proof_irrelevance _ H5 H5'); subst H5'.
so (proof_irrelevance _ H6 H6'); subst H6'.
so (proof_irrelevance _ H7 H7'); subst H7'.
so (proof_irrelevance _ H8 H8'); subst H8'.
so (proof_irrelevance _ H9 H9'); subst H9'.
reflexivity.
Qed.


Lemma the_system_fix :
  the_system = system_inc the_system.
Proof.
assert (system_le the_system (system_inc the_system)) as Hle.
  {
  apply system_join_lub.
  intros w.
  apply (system_le_trans _ (system_inc (systems w))).
    {
    apply pre_systems_increasing.
    }
  
    {
    apply system_inc_mono.
    apply system_join_ub.
    }
  }
apply system_extensionality.
  {
  fextensionality 1.
  intro w.
  pextensionality.
    {
    intros _.
    intros v Hv.
    exists (succ v).
    apply systems_all_valid.
    }

    {
    intros _.
    apply the_system_all_valid.
    }
  }

  {
  fextensionality 1.
  intros pg.
  exact (Hle ander pg (the_system_all_valid (str pg)) andel).
  }

  {
  fextensionality 1.
  intros pg.
  exact (Hle ander pg (the_system_all_valid (str pg)) ander).
  }
Qed.


Definition kinterpv := kbasicv the_system.
Definition cinterpv := cbasicv the_system.
Definition interpv := basicv the_system.
Definition kinterp := kbasic the_system.
Definition cinterp := cbasic the_system.
Definition interp := basic the_system.


Lemma sint_unroll :
  sint the_system = interp.
Proof.
rewrite -> the_system_fix.
cbn.
unfold system_inc_sint.
reflexivity.
Qed.


Lemma sintk_unroll :
  sintk the_system = kinterp.
Proof.
rewrite -> the_system_fix.
cbn.
unfold system_inc_sintk.
reflexivity.
Qed.
