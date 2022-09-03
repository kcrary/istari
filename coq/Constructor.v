
Require Import Tactics.
Require Import Axioms.
Require Import Sigma.
Require Import Equality.
Require Import Ordinal.
Require Import Relation.
Require Import Ofe.
Require Import Syntax.
Require Import SimpSub.
Require Import Hygiene.
Require Import Uniform.
Require Import Urelsp.
Require Import Intensional.
Require Import Dynamic.
Require Import Candidate.
Require Import Model.
Require Import Ceiling.
Require Import Standard.
Require Import ExtendTruncate.
Require Import MapTerm.
Require Import Extend.
Require Import System.
Require Import Page.
Require Import Spaces.
Require Import Semantics.
Require Import PreSpacify.
Require Import SemanticsKnot.
Require Import ProperClosed.
Require Import ProperEquiv.
Require Import ProperFun.
Require Import ProperDownward.
Require Import ProperLevel.
Require Import Truncate.


Local Ltac prove_hygiene :=
  repeat (apply hygiene_auto; cbn; repeat2 split; auto);
  eauto using hygiene_weaken, clo_min, hygiene_shift';
  try (apply hygiene_var; cbn; auto; done).


Definition tp_action (pg : page)
  : nat -> relation sterm
  :=
  fun j a b =>
    exists (R : siurel),
      interp pg true j a R
      /\ interp pg false j b R.


Definition tp_uniform :
  forall pg, uniform _ (tp_action pg).
Proof.
intros pg.
do2 3 split.
  {
  intros j a b Hab.
  destruct Hab as (x & Hl & Hr).
  split; eapply basic_closed; eauto.
  }

  {
  intros i m n p q Hcln Hclq Hmn Hpq Hmp.
  destruct Hmp as (x & Hm & Hp).
  exists x.
  split; eapply basic_equiv; eauto.
  }

  {
  intros i m n p q Hmn Hpn Hpq.
  destruct Hmn as (x & Hm & Hn).
  destruct Hpn as (x' & Hp & Hn').
  destruct Hpq as (x'' & Hp' & Hq).
  so (basic_fun _#7 Hn Hn'); subst x'.
  so (basic_fun _#7 Hp Hp'); subst x''.
  exists x; auto.
  }

  {
  intros i m n H.
  assert (i <= S i) as Hle by omega.
  destruct H as (x & Hm & Hn).
  so (basic_downward _#7 Hle Hm) as Hm'.
  so (basic_downward _#7 Hle Hn) as Hn'.
  exists (iutruncate (S i) x).
  auto.
  }
Qed.


Definition tp_urel pg : surel :=
  mk_urel (tp_action pg) (tp_uniform _).


Definition kind_action (pg : page)
  : nat -> relation sterm
  :=
  fun j a b =>
    exists (K : qkind) (R : siurel),
      kinterp pg true j a K
      /\ kinterp pg false j b K
      /\ interp toppg true j a R
      /\ interp toppg false j b R.


Definition kind_uniform :
  forall pg, uniform _ (kind_action pg).
Proof.
intros pg.
do2 3 split.
  {
  intros j a b Hab.
  destruct Hab as (x & _ & Hl & Hr & _).
  split; eapply kbasic_closed; eauto.
  }

  {
  intros i m n p q Hcln Hclq Hmn Hpq Hmp.
  destruct Hmp as (x & R & Hm & Hp & Hm' & Hp').
  exists x, R.
  do2 3 split; try (eapply kbasic_equiv; eauto); eapply basic_equiv; eauto.
  }

  {
  intros i m n p q Hmn Hpn Hpq.
  destruct Hmn as (x & R & Hm & Hn & Hmt & Hnt).
  destruct Hpn as (x' & R' & Hp & Hn' & Hpt & Hnt').
  destruct Hpq as (x'' & R'' & Hp' & Hq & Hpt' & Hqt).
  so (kbasic_fun _#7 Hn Hn'); subst x'.
  so (kbasic_fun _#7 Hp Hp'); subst x''.
  so (basic_fun _#7 Hnt Hnt'); subst R'.
  so (basic_fun _#7 Hpt Hpt'); subst R''.
  exists x, R; auto.
  }

  {
  intros i m n H.
  assert (i <= S i) as Hle by omega.
  destruct H as (x & R & Hm & Hn & Hmt & Hnt).
  so (kbasic_downward _#7 Hle Hm) as Hm'.
  so (kbasic_downward _#7 Hle Hn) as Hn'.
  so (basic_downward _#7 Hle Hmt) as Hmt'.
  so (basic_downward _#7 Hle Hnt) as Hnt'.
  exists (approx i x), (iutruncate (S i) R).
  auto.
  }
Qed.


Definition kind_urel pg : surel :=
  mk_urel (kind_action pg) (kind_uniform _).


Definition con_action (pg : page) (K : qkind)
  : nat -> relation sterm
  :=
  fun j a b =>
    exists (x : spcar (approx j K)),
      cinterp pg true j a (expair (approx j K) x)
      /\ cinterp pg false j b (expair (approx j K) x).


Definition con_uniform :
  forall pg K, uniform _ (con_action pg K).
Proof.
intros pg K.
do2 3 split.
  {
  intros j a b Hab.
  destruct Hab as (x & Hl & Hr).
  split; eapply cbasic_closed; eauto.
  }

  {
  intros i m n p q Hcln Hclq Hmn Hpq Hmp.
  destruct Hmp as (x & Hm & Hp).
  exists x.
  split; eapply cbasic_equiv; eauto.
  }

  {
  intros i m n p q Hmn Hpn Hpq.
  destruct Hmn as (x & Hm & Hn).
  destruct Hpn as (x' & Hp & Hn').
  destruct Hpq as (x'' & Hp' & Hq).
  injection (cbasic_fun _#7 Hn Hn').
  intro H.
  injectionT H.
  intros <-.
  injection (cbasic_fun _#7 Hp Hp').
  intro H.
  injectionT H.
  intros <-.
  exists x; auto.
  }

  {
  intros i m n H.
  assert (i <= S i) as Hle by omega.
  destruct H as (x & Hm & Hn).
  so (cbasic_downward _#7 Hle Hm) as Hm'.
  so (cbasic_downward _#7 Hle Hn) as Hn'.
  unfold projc, stdc in Hm', Hn'; cbn in Hm', Hn'.
  exists (transport (approx_combine_le _#3 Hle) spcar (proj i (approx (S i) K) (std (S i) (approx (S i) K) x))).
  split.
    {
    force_exact Hm'.
    unfold cinterp.
    f_equal.
    apply expair_compat_dep.
    apply (eq_impl_eq_dep _#6 (approx_combine_le _#3 Hle)).
    reflexivity.
    }

    {
    force_exact Hn'.
    unfold cinterp.
    f_equal.
    apply expair_compat_dep.
    apply (eq_impl_eq_dep _#6 (approx_combine_le _#3 Hle)).
    reflexivity.
    }
  }
Qed.


Definition con_urel pg K : surel :=
  mk_urel (con_action pg K) (con_uniform _ _).


Lemma con_urel_raise :
  forall pg K i a b,
    rel (con_urel pg (approx i K)) i a b
    -> rel (con_urel pg K) i a b.
Proof.
intros pg K i a b Hab.
destruct Hab as (x & Ha & Hb).
revert x Ha Hb.
rewrite -> approx_idem.
intros x Ha Hb.
exists x.
auto.
Qed.


Lemma con_urel_lower :
  forall pg K i a b,
    rel (con_urel pg K) i a b
    -> rel (con_urel pg (approx i K)) i a b.
Proof.
intros pg K i a b Hab.
cbn.
unfold con_action.
rewrite -> approx_idem.
exact Hab.
Qed.


Lemma con_urel_raise' :
  forall pg K i j a b,
    i <= j
    -> rel (con_urel pg (approx j K)) i a b
    -> rel (con_urel pg K) i a b.
Proof.
intros pg K i j a b Hij Hab.
apply con_urel_raise.
rewrite <- (approx_combine_le _#3 Hij).
apply con_urel_lower; auto.
Qed.  


Lemma con_urel_lower' :
  forall pg K i j a b,
    i <= j
    -> rel (con_urel pg K) i a b
    -> rel (con_urel pg (approx j K)) i a b.
Proof.
intros pg K i j a b Hij Hab.
apply con_urel_raise.
rewrite -> approx_combine_le; auto.
apply con_urel_lower; auto.
Qed.


Lemma interp_clam_invert :
  forall system pg s i k a Q,
    cbasicv system pg s i (clam k a) Q
    -> exists K L A h,
         L = approx i L
         /\ interp_kext pg i k K
         /\ (forall j,
               j <= i
               -> forall (x : spcar (approx j K)),
                    cbasic system pg s j
                      (subst1 
                         (ext (objin (objsome
                                        (expair (approx j K) (std (S j) (approx j K) x))
                                        (le_ord_succ _ _ (le_ord_trans _#3 (approx_level j K) h)))))
                         a)
                      (expair (approx j L) (proj j L (std (S j) L (pi1 A (std (S j) K (embed j K x)))))))
         /\ Q = stdc (S i) (expair (qarrow K L) A).
Proof.
intros system pg s i k a Q H.
remember (clam k a) as b eqn:Heq.
revert Heq.
cases H; try (intros; discriminate Heq).
intros pg s i k' a' K L A h HeqL Hk Hact Heq.
injectionc Heq.
intros -> ->.
exists K, L, A, h.
auto.
Qed.


Lemma nearrow_formation :
  forall pg' pg K L i a b (fit : level K <<= top),
    L = approx i L
    -> level K <<= cin pg'
    -> (forall j c d,
          j <= i
          -> rel (con_urel pg' K) j c d
          -> rel (con_urel pg L) j (subst1 c a) (subst1 d b))
    -> exists (f : space K -n> space L),
         f = std (S i) (qarrow K L) f
         /\
         forall (x : spcar K),
           cinterp pg true i
             (subst1 (ext (objin (objsome (expair K (std (S i) K x)) (le_ord_succ _ _ fit)))) a) 
             (expair L (pi1 f x))
           /\ forall j,
                j <= i
                -> cinterp pg true j
                     (subst1
                        (ext (objin (objsome
                                       (expair 
                                          (approx j K) 
                                          (proj j K (std (S j) K x)))
                                       (le_ord_succ _ _ (le_ord_trans _#3 (approx_level j K) fit)))))
                        a)
                     (expair (approx j L) (proj j L (std (S j) L (pi1 f (std (S j) K x)))))
                   /\
                   cinterp pg false j
                     (subst1
                        (ext (objin (objsome
                                       (expair 
                                          (approx j K) 
                                          (proj j K (std (S j) K x)))
                                       (le_ord_succ _ _ (le_ord_trans _#3 (approx_level j K) fit)))))
                        b)
                     (expair (approx j L) (proj j L (std (S j) L (pi1 f (std (S j) K x))))).
Proof.
intros pg' pg K L i a b h HeqL HlevK Hab.
so (le_ord_succ _ _ h) as fit.
assert (forall j, j <= i -> level (approx j K) << stop) as fitj.
  {
  intros j Hj.
  eapply le_lt_ord_trans; eauto.
  apply approx_level.
  }
set (xt := fun j Hj x => ext (objin (objsome (expair (approx j K) x) (fitj j Hj)))).
set (xt' := fun x => ext (objin (objsome (expair K x) fit))).
assert (forall (x : spcar K), exists! (y : spcar L),
          cinterp pg true i (subst1 (xt' (std (S i) K x)) a) (expair L y)
          /\
          forall j (Hj : j <= i),
            cinterp pg true j (subst1 (xt j Hj (proj j K (std (S j) K x))) a) (projc j (stdc (S j) (expair L y)))
            /\ cinterp pg false j (subst1 (xt j Hj (proj j K (std (S j) K x))) b) (projc j (stdc (S j) (expair L y)))) as Huniq.
  {
  intro x.
  assert (rel (con_urel pg' K) i (xt' (std (S i) K x)) (xt' (std (S i) K x))) as Hxt.
    {
    exists (proj i K (std (S i) K x)).
    split.
      {
      apply cinterp_eval_refl.
      relquest.
        {
        apply interp_ext.
        cbn; auto.
        }
      unfold projc, stdc; cbn.
      rewrite -> std_idem.
      reflexivity.
      }

      {
      apply cinterp_eval_refl.
      relquest.
        {
        apply interp_ext.
        cbn; auto.
        }
      unfold projc, stdc; cbn.
      rewrite -> std_idem.
      reflexivity.
      }
    }
  so (Hab i _ _ (le_refl i) Hxt) as Hxtab.
  destruct Hxtab as (y & Hxta & Hxtb).
  exists (transport (eqsymm HeqL) spcar y).
  split.
    {
    split.
      {
      force_exact Hxta.
      f_equal.
      apply expair_compat_dep.
      apply (eq_impl_eq_dep _#6 (eqsymm HeqL)).
      reflexivity.
      }
    intros j Hj.
    split.
      { 
      assert (rel (con_urel pg' K) j (xt j Hj (proj j K (std (S j) K x))) (xt' (std (S i) K x))) as Hxtj.
        {
        unfold xt, xt'.
        exists (proj j K (std (S j) K x)).
        split.
          {
          relquest.
            {
            apply cinterp_eval_refl.
            apply interp_ext.
            cbn.
            eapply le_ord_trans; eauto.
            apply approx_level.
            }
          unfold projc, stdc; cbn.
          setoid_rewrite -> proj_std at 2; auto.
          rewrite -> std_idem.
          apply expair_compat_dep.
          apply (eq_impl_eq_dep _#6 (approx_idem _ _)).
          rewrite -> proj_near.
          rewrite -> proj_std; auto.
          }

          {
          apply cinterp_eval_refl.
          relquest.
            {
            apply interp_ext; auto.
            }
          unfold projc, stdc; cbn.
          rewrite -> std_combine_le; auto.
          omega.
          }
        }
      so (Hab j _ _ Hj Hxtj) as (z & Hleft & Hright).
      so (cbasic_fun _#7 (cbasic_downward _#7 Hj Hxtb) Hright) as Heq.
      rewrite <- Heq in Hleft.
      force_exact Hleft.
      f_equal.
      unfold projc, stdc; cbn.
      apply expair_compat_dep.
      apply (eq_impl_eq_dep _#6 (approx_combine_le _#3 Hj)).
      rewrite -> std_transport.
      rewrite -> proj_transport.
      f_equal.
      apply proof_irrelevance.
      }

      {
      assert (rel (con_urel pg' K) j (xt' (std (S i) K x)) (xt j Hj (proj j K (std (S j) K x)))) as Hxtj.
        {
        unfold xt, xt'.
        exists (proj j K (std (S j) K x)).
        split.
          {
          apply cinterp_eval_refl.
          relquest.
            {
            apply interp_ext; auto.
            }
          unfold projc, stdc; cbn.
          rewrite -> std_combine_le; auto.
          omega.
          }

          {
          relquest.
            {
            apply cinterp_eval_refl.
            apply interp_ext.
            cbn.
            eapply le_ord_trans; eauto.
            apply approx_level.
            }
          unfold projc, stdc; cbn.
          setoid_rewrite -> proj_std at 2; auto.
          rewrite -> std_idem.
          apply expair_compat_dep.
          apply (eq_impl_eq_dep _#6 (approx_idem _ _)).
          rewrite -> proj_near.
          rewrite -> proj_std; auto.
          }
        }
      so (Hab j _ _ Hj Hxtj) as (z & Hleft & Hright).
      so (cbasic_fun _#7 (cbasic_downward _#7 Hj Hxta) Hleft) as Heq.
      rewrite <- Heq in Hright.
      force_exact Hright.
      f_equal.
      unfold projc, stdc; cbn.
      apply expair_compat_dep.
      apply (eq_impl_eq_dep _#6 (approx_combine_le _#3 Hj)).
      rewrite -> std_transport.
      rewrite -> proj_transport.
      f_equal.
      apply proof_irrelevance.
      }
    }

    {
    intros y' Hy'.
    so (cbasic_fun _#7 Hxta (Hy' andel)) as H.
    so (expair_injection_transport _#6 H) as (HeqL' & Heq).
    so (proof_irrelevance _ (eqsymm HeqL) HeqL'); subst HeqL'.
    subst y'.
    reflexivity.
    }
  }
so (choice _#3 Huniq) as (f & Hf).
clear Huniq.
assert (forall x, f x = std (S i) L (f x)) as Hstdfl.
  {
  intro x.
  so (cbasic_impl_std _#6 (Hf x andel)) as H.
  unfold stdc in H; cbn in H.
  injectionc H.
  intro H.
  injectionT H.
  auto.
  }
assert (forall x, f x = f (std (S i) K x)) as Hstdfr.
  {
  intro x.
  so (Hf x andel) as H1.
  so (Hf (std (S i) K x) andel) as H2.
  rewrite -> std_idem in H2.
  so (cbasic_fun _#7 H1 H2) as Heq.
  injectionc Heq.
  intro H.
  injectionT H; auto.
  }
assert (nonexpansive f) as Hnef.
  {
  intros j x y Hxy.
  destruct j as [| j].
    {
    apply dist_zero.
    }
  so (le_dec j i) as [Hj | Hnle].
    {
    so (Hf x ander j Hj andel) as H.
    so (Hf y ander j Hj andel) as H'.
    replace (std (S j) K y) with (std (S j) K x) in H'.
    2:{
      apply std_collapse; auto.
      }
    so (cbasic_fun _#7 H H') as Heq; clear H H'.
    unfold projc, stdc in Heq; cbn in Heq.
    injectionc Heq.
    intro H.
    injectionT H.
    intros Heq.
    so (proj_eq_dist _#4 Heq) as Hdist; clear Heq.
    setoid_rewrite -> Hstdfl at 1 2.
    eapply dist_trans.
      {
      apply dist_symm.
      apply std_dist; omega.
      }
    eapply dist_trans.
    2:{
      apply std_dist; omega.
      }
    exact Hdist.
    }

    {
    assert (i <= j) as Hi by omega; clear Hnle.
    apply dist_refl'.
    so (Hf x andel) as H.
    so (Hf y andel) as H'.
    replace (std (S i) K y) with (std (S i) K x) in H'.
    2:{
      apply std_collapse.
      refine (dist_downward_leq _#5 _ Hxy).
      omega.
      }
    so (cbasic_fun _#7 H H') as Heq; clear H H'.
    injectionc Heq.
    intro H.
    injectionT H.
    auto.
    }
  }
exists (expair f Hnef).
split.
  {
  apply nearrow_extensionality.
  intro x.
  rewrite -> std_arrow_is.
  cbn.
  fold (std (S i) L).
  fold (std (S i) K).
  rewrite <- Hstdfl.
  rewrite <- Hstdfr.
  reflexivity.
  }
intro x.
split.
  {
  so (Hf x andel) as H.
  cbn.
  force_exact H.
  f_equal.
  unfold xt'.
  f_equal.
  f_equal.
  f_equal.
  apply objsome_compat.
  reflexivity.
  }
intros j Hj.
split.
  {
  so (Hf x ander j Hj andel) as H.
  force_exact H.
  f_equal.
    {
    f_equal.
    unfold xt.
    f_equal.
    f_equal.
    apply objsome_compat.
    reflexivity.
    }
    
    {
    unfold projc, stdc; cbn.
    f_equal.
    f_equal.
    apply std_collapse.
    rewrite -> Hstdfr.
    apply Hnef.
    apply dist_symm.
    apply std_dist.
    omega.
    }
  }

  {
  so (Hf x ander j Hj ander) as H.
  force_exact H.
  f_equal.
    {
    f_equal.
    unfold xt.
    f_equal.
    f_equal.
    apply objsome_compat.
    reflexivity.
    }
    
    {
    unfold projc, stdc; cbn.
    f_equal.
    f_equal.
    apply std_collapse.
    rewrite -> Hstdfr.
    apply Hnef.
    apply dist_symm.
    apply std_dist.
    omega.
    }
  }
Qed.


Lemma clam_formation :
  forall pg K L i k k' a b,
    L = approx i L
    -> interp_kext pg i k K
    -> interp_kext pg i k' K
    -> (forall j c d,
          j <= i
          -> rel (con_urel pg K) j c d
          -> rel (con_urel pg L) j (subst1 c a) (subst1 d b))
    -> rel (con_urel pg (qarrow K L)) i (clam k a) (clam k' b).
Proof.
intros pg K L i k k' a b HeqL Hk Hk' Hab.
cbn.
so (interp_kext_bound _#4 Hk) as HlevK.
assert (level K <<= top) as fit.
  {
  eapply le_ord_trans; eauto.
  apply cin_top.
  }
so (nearrow_formation pg pg K L i a b fit HeqL HlevK Hab) as (f & Hstdf & Hf).
so (interp_kext_impl_approx _#4 Hk) as HeqK.
unfold con_action.
cbn.
rewrite <- HeqL, <- HeqK.
exists f.
rewrite -> Hstdf.
split.
  {
  apply cinterp_eval_refl.
  apply (interp_clam _#9 fit); auto.
  intros j Hj x.
  so (Hf (embed j K x) ander j Hj andel) as H.
  rewrite <- embed_std in H; auto.
  rewrite -> proj_embed in H; auto.
  rewrite <- embed_std; auto.
  }

  {
  apply cinterp_eval_refl.
  apply (interp_clam _#9 fit); auto.
  intros j Hj x.
  so (Hf (embed j K x) ander j Hj ander) as H.
  rewrite <- embed_std in H; auto.
  rewrite -> proj_embed in H; auto.
  rewrite <- embed_std; auto.
  }
Qed.


Lemma capp_formation :
  forall pg K L i a b c d,
    rel (con_urel pg (qarrow K L)) i a b
    -> rel (con_urel pg K) i c d
    -> rel (con_urel pg L) i (capp a c) (capp b d).
Proof.
intros pg K L i a b c d Hab Hcd.
destruct Hab as (f & Ha & Hb).
destruct Hcd as (x & Hc & Hd).
cbn in f.
exists (pi1 f x).
split.
  {
  apply cinterp_eval_refl.
  apply interp_capp; auto.
  }

  {
  apply cinterp_eval_refl.
  apply interp_capp; auto.
  }
Qed.


Lemma capp_clam_beta :
  forall pg K L i k a b c d,
    L = approx i L
    -> interp_kext pg i k K
    -> (forall j c d,
          j <= i
          -> rel (con_urel pg K) j c d
          -> rel (con_urel pg L) j (subst1 c a) (subst1 d b))
    -> rel (con_urel pg K) i c d
    -> rel (con_urel pg L) i (capp (clam k a) c) (subst1 d b).
Proof.
intros pg K L i k a b c d HeqL Hk Hab Hcd.
so (interp_kext_impl_approx _#4 Hk) as HeqK.
so (interp_kext_bound _#4 Hk) as HlevK.
assert (level K << stop) as fit.
  {
  apply le_ord_succ.
  eapply le_ord_trans; eauto.
  apply cin_top.
  }
so (clam_formation _#8 HeqL Hk Hk Hab) as Hclam.
so (capp_formation _#8 Hclam Hcd) as Hcapp.
destruct Hcapp as (y & Hleft & Hright).
exists y.
revert y Hleft Hright.
rewrite <- HeqL.
intros y Hleft Hright.
split; auto.
clear Hclam Hleft.
(* Root around in Hright to get what we need. *)
so (cbasic_value_inv _#6 value_capp Hright) as H.
clear Hright.
invertc H.
intros K' x f' Hclam Hd <-.
so Hcd as (x' & _ & Hd').
so (cbasic_fun _#7 Hd Hd') as H.
injectionc H.
intros _ Heq.
rewrite <- HeqK in Heq.
subst K'.
clear x' Hd'.
so (cbasic_value_inv _#6 value_clam Hclam) as H; clear Hclam.
so (interp_clam_invert _#7 H) as (K' & L' & f & h & _ & _ & Hact & Heq); clear H.
change (space K' -n> space L') in f.
unfold stdc in Heq; cbn in Heq.
injection Heq.
intros <- <-.
injectionT Heq.
intros ->.
so (Hact i (le_refl _) (transport HeqK spcar x)) as Hbx.
clear Hact.
match type of Hbx with
| cbasic _ _ _ _ (subst1 ?X _) _ => set (xt := X) in Hbx
end.
rewrite -> std_arrow_is.
cbn.
fold (std (S i) L).
fold (std (S i) K).
match type of Hbx with
| cbasic _ _ _ _ _ ?X =>
  replace X with (@expair qkind spcar L (std (S i) L (pi1 f (std (S i) K x)))) in Hbx
end.
2:{
  apply expair_compat_dep.
  apply (eq_impl_eq_dep _#6 HeqL).
  symmetry.
  apply (transport_symm' _ spcar _ _ HeqL).
  rewrite -> proj_near'.
  rewrite -> embed_approx'.
  reflexivity.
  }
assert (forall s, cinterp pg s i xt (expair (approx i K) (proj i K (std (S i) K x)))) as Hxt.
  {
  intro s.
  apply cinterp_eval_refl.
  relquest.
    {
    apply interp_ext.
    cbn.
    rewrite <- HeqK; auto.
    }
  unfold projc, stdc; cbn.
  rewrite <- HeqK.
  so (cbasic_impl_std _#6 Hd) as H.
  unfold stdc in H; cbn in H.
  injectionT H.
  intro H.
  rewrite -> H at 2.
  reflexivity.
  }
assert (rel (con_urel pg K) i xt xt) as Hxt_xt.
  {
  eexists.
  split; eauto.
  }
assert (rel (con_urel pg K) i xt d) as Hxt_d.
  {
  eexists.
  split; auto.
  rewrite -> (cbasic_impl_std _#6 Hd) in Hd.
  unfold stdc in Hd; cbn in Hd.
  force_exact Hd.
  unfold cinterp.
  f_equal.
  apply expair_compat_dep.
  apply (eq_impl_eq_dep _#6 HeqK).
  symmetry.
  apply (transport_symm' _ spcar _ _ HeqK).
  apply proj_near'.
  }
so (Hab i _ _ (le_refl _) Hxt_xt) as Hxta_xtb.
so (Hab i _ _ (le_refl _) Hxt_d) as Hxta_db.
destruct Hxta_xtb as (y & Hxta & Hxtb).
destruct Hxta_db as (y' & Hxta' & Hdb).
so (cbasic_fun _#7 Hxta Hxta') as H.
injectionc H.
intro H.
injectionT H.
intros <-.
clear Hxta Hxta'.
revert y Hxtb Hdb.
rewrite <- HeqL.
intros y Hxtb Hdb.
so (cbasic_fun _#7 Hbx Hxtb) as H.
injectionc H.
intro H.
injectionT H.
intros <-.
exact Hdb.
Qed.


Lemma capp_clam_beta_double :
  forall pg K L i k a b c d,
    L = approx i L
    -> interp_kext pg i k K
    -> (forall j c d,
          j <= i
          -> rel (con_urel pg K) j c d
          -> rel (con_urel pg L) j (subst1 c a) (subst1 d b))
    -> rel (con_urel pg K) i c d
    -> rel (con_urel pg L) i (capp (clam k a) c) (subst1 d b)
       /\ rel (con_urel pg L) i (subst1 c a) (subst1 d b).
Proof.
intros pg K L i k a b c d HeqL Hk Hab Hcd.
split.
  {
  eapply capp_clam_beta; eauto.
  }

  {
  exact (Hab _#3 (le_refl _) Hcd).
  }
Qed.


Lemma clam_capp_eta :
  forall pg K L i k a b,
    L = approx i L
    -> interp_kext pg i k K
    -> rel (con_urel pg (qarrow K L)) i a b
    -> rel (con_urel pg (qarrow K L)) i (clam k (capp (subst sh1 a) (var 0))) b.
Proof.
intros pg K L i k a b HeqL Hk Hab.
so (interp_kext_impl_approx _#4 Hk) as HeqK.
exploit (clam_formation pg K L i k k (capp (subst sh1 a) (var 0)) (capp (subst sh1 b) (var 0))) as Hlam; auto.
  {
  intros j c d Hj Hcd.
  simpsub.
  eapply capp_formation; eauto.
  eapply urel_downward_leq; eauto.
  }
destruct Hab as (f & Ha & Hb).
destruct Hlam as (g & Hlam & _).
cut (f = g).
  {
  intros <-.
  exists f; auto.
  }
clear b Hb.
revert f Ha g Hlam.
cbn [approx].
rewrite <- HeqK, <- HeqL.
intros f Ha g Hlam.
so (interp_clam_invert _#7 (cbasic_value_inv _#6 value_clam Hlam)) as H.
destruct H as (K' & L' & g' & fit & _ & _ & Hact & Heq).
change (spcar (qarrow K' L')) in g'.
injectionc Heq.
intros H <- <-.
injectionT H.
intros ->.
so (cbasic_impl_std _#6 Ha) as H.
unfold stdc in H; cbn in H.
injectionT H.
intro Hstdf.
rewrite -> Hstdf.
rename g' into g.
cbn in f, g.
apply (nearrow_extensionality (space K) (space L)).
intro x.
so (Hact i (le_refl _) (transport HeqK spcar x)) as Hax; clear Hact.
simpsubin Hax.
match type of Hax with
| cbasic _ _ _ _ (capp _ ?X) _ =>
  set (xt := X) in Hax
end.
so (interp_kext_bound _#4 Hk) as HlevK.
assert (cinterp pg true i xt (expair K (std (S i) K x))) as Hxt.
  {
  apply cinterp_eval_refl.
  relquest.
    {
    apply interp_ext.
    cbn.
    eapply le_ord_trans; eauto.
    apply approx_level.
    }
  unfold projc, stdc; cbn.
  rewrite <- HeqK.
  symmetry.
  apply expair_compat_dep.
  apply (eq_impl_eq_dep _#6 HeqK).
  cbn.
  rewrite -> std_idem.
  rewrite -> proj_std; auto.
  rewrite <- std_transport.
  f_equal.
  symmetry.
  apply transport_symm'.
  apply proj_near'.
  }
so (cinterp_eval_refl _#6 (interp_capp _#10 Ha Hxt)) as Hax'.
so (cbasic_fun _#7 Hax Hax') as Heq.
rewrite -> std_arrow_is.
cbn.
fold (std (S i) K).
fold (std (S i) L).
symmetry in Heq.
so (expair_injection_transport _#6 Heq) as (h & H); renameover H into Heq.
so (proof_irrelevance _ h HeqL); subst h.
so (transport_symm _ spcar _ _ HeqL _ _ Heq) as H; renameover H into Heq.
rewrite -> proj_near' in Heq.
rewrite -> embed_approx' in Heq.
etransitivity.
2:{
  exact Heq.
  }
setoid_rewrite -> Hstdf at 2.
rewrite -> std_arrow_is.
cbn.
fold (std (S i) K).
rewrite -> std_idem.
reflexivity.
Qed.


Lemma interp_ctlam_invert :
  forall system pg s i a b k Q,
    cbasicv system pg s i (ctlam a b k) Q
    -> exists K A f (B : urelsp A -n> space K),
         hygiene (permit clo) b
         /\ interp_uext pg i a A
         /\ interp_kext pg i k K
         /\ (forall j m n (Hmn : rel (extend_urel (cin pg) stop A) j m n),
               cbasic system pg s j
                 (subst1 (if s then m else n) b)
                 (expair (approx j K) (f j m n Hmn)))
         /\ (forall j m n (Hmn : rel (extend_urel (cin pg) stop A) j m n),
               pi1 B (urelspinj A j _ _ Hmn)
               =
               embed j K (f j m n Hmn))
         /\ Q = expair (qtarrow (cin pg) A K) B.
Proof.
intros system pg s i a b k Q H.
remember (ctlam a b k) as c eqn:Heq.
revert Heq.
cases H; try (intros; discriminate Heq).
intros pg s i a' b' k' K A f B Hclb Ha Hk Hf HB Heq.
injectionc Heq.
intros -> -> ->.
exists K, A, f, B.
do2 5 split; auto.
Qed.


Lemma ctlam_formation :
  forall pg A K i a a' b c k k',
    interp_uext pg i a A
    -> interp_uext pg i a' A
    -> interp_kext pg i k K
    -> interp_kext pg i k' K
    -> hygiene (permit clo) b
    -> hygiene (permit clo) c
    -> (forall j m p,
          rel (extend_urel (cin pg) stop A) j m p
          -> rel (con_urel pg K) j (subst1 m b) (subst1 p c))
    -> rel (con_urel pg (qtarrow (cin pg) A K)) i (ctlam a b k) (ctlam a' c k').
Proof.
intros pg A K i a a' b c k k' Ha Ha' Hk Hk' Hclb Hclc Hbc.
set (fit := cin_stop pg).
set (As := extend_urel (cin pg) stop A).
assert (forall j m p (Hmp : rel As j m p), exists! (x : spcar (approx j K)),
          cinterp pg true j (subst1 m b) (expair (approx j K) x)
          /\ cinterp pg false j (subst1 p c) (expair (approx j K) x)) as Huniq.
  {
  intros j m p Hmp.
  so (Hbc j m p Hmp) as (x & Hmb & Hpc).
  exists x.
  split; auto.
  intros x' (Hmb' & _).
  so (cbasic_fun _#7 Hmb Hmb') as H.
  injectionT H.
  auto.
  }
set (f := fun j m p Hmp => pi1 (description _ _ (Huniq j m p Hmp))).
assert (forall j m p Hmp,
          cinterp pg true j (subst1 m b) (expair (approx j K) (f j m p Hmp))
          /\ cinterp pg false j (subst1 p c) (expair (approx j K) (f j m p Hmp))) as Hf.
  {
  intros j m p Hmp.
  exact (pi2 (description _ _ (Huniq j m p Hmp))).
  }
clearbody f.
clear Huniq.
assert (forall j m p Hmp,
          f j m p Hmp = std (S j) (approx j K) (f j m p Hmp)) as Hstdf.
  {
  intros j m p Hmp.
  so (cbasic_impl_std _#6 (Hf j m p Hmp andel)) as H.
  unfold stdc in H; cbn in H.
  injectionT H; auto.
  }
assert (forall (C : urelsp_car A), exists! (y : spcar K),
          forall j m p Hmp,
            C = urelspinj _ j _ _ Hmp
            -> y = embed j K (f j m p Hmp)) as Huniq.
  {
  intro C.
  so (urelsp_eta _ _ C) as (j & m & p & Hmp & ->).
  assert (rel As j (map_term (extend _ stop) m) (map_term (extend _ stop) p)) as Hmp'.
    {
    unfold As.
    cbn.
    rewrite -> !extend_term_cancel; auto.
    }
  set (y := embed j K (f j (map_term (extend _ stop) m) (map_term (extend _ stop) p) Hmp')).
  exists y.
  assert (forall j' n q 
            (Hnq : rel A j' (map_term (extend _ _) n) (map_term (extend _ _) q)),
              urelspinj _ j m p Hmp = urelspinj _ j' (map_term (extend _ _) n) (map_term (extend _ _) q) Hnq
              -> y = embed j' K (f j' n q Hnq)) as Hy.
    {
    intros j' n q Hnq Heq.
    so (urelspinj_equal_invert _#10 Heq) as (<- & Hmq).
    unfold y.
    f_equal.
    so (Hf j _ _ Hmp') as (Hmb & _).
    so (Hf j _ _ Hnq) as (_ & Hqc).
    eassert _ as H.
      {
      refine (Hbc j (map_term (extend _ stop) m) q _).
      cbn.
      rewrite -> extend_term_cancel; auto.
      }
    destruct H as (z & Hmb' & Hqc').
    so (cbasic_fun _#7 Hmb Hmb') as H.
    injectionT H.
    intros <-.
    so (cbasic_fun _#7 Hqc Hqc') as H.
    injectionT H.
    auto.
    }
  split; auto.
  intros y' Hy'.
  exploit (Hy j _ _ Hmp') as H.
    {
    apply urelspinj_equal.
    rewrite -> extend_term_cancel; auto.
    }
  rewrite -> H; clear H.
  exploit (Hy' j _ _ Hmp') as H.
    {
    apply urelspinj_equal.
    rewrite -> extend_term_cancel; auto.
    }
  subst y'.
  reflexivity.
  }
so (choice _#3 Huniq) as (g & Hg).
clear Huniq.
assert (forall j m p (Hmp : rel (extend_urel _ stop A) j m p),
          g (urelspinj A j _ _ Hmp) = embed j K (f j m p Hmp)) as Hg'.
  {
  intros j m p Hmp.
  exact (Hg (urelspinj A j _ _ Hmp) j _ _ Hmp (eq_refl _)).
  }
renameover Hg' into Hg.
assert (@nonexpansive (urelsp A) (space K) g) as Hneg.
  {
  intros j C D HCD.
  so (urelsp_eta _ _ C) as (j' & m & p & Hmp & ->).
  so (urelsp_eta _ _ D) as (j'' & n & q & Hnq & ->).
  set (m' := map_term (extend _ stop) m).
  set (p' := map_term (extend _ stop) p).
  set (n' := map_term (extend _ stop) n).
  set (q' := map_term (extend _ stop) q).
  destruct j as [| j].
    {
    apply dist_zero.
    }
  so (urelspinj_dist_invert _#11 HCD) as Hmq.
  assert (rel (extend_urel _ stop A) j' m' p') as Hmp'.
    {
    unfold extend_urel; cbn [rel].
    unfold m', p'.
    rewrite -> !extend_term_cancel; auto.
    }
  assert (rel (extend_urel _ stop A) j'' n' q') as Hnq'.
    {
    unfold extend_urel; cbn [rel].
    unfold n', q'.
    rewrite -> !extend_term_cancel; auto.
    }
  apply (dist_trans _#3 (embed j' K (f j' m' p' Hmp'))).
    {
    apply dist_refl'.
    rewrite <- (Hg j' m' p' Hmp').
    f_equal.
    apply urelspinj_equal.
    unfold p'.
    rewrite -> extend_term_cancel; auto.
    }
  apply (dist_trans _#3 (embed j'' K (f j'' n' q' Hnq'))).
  2:{
    apply dist_refl'.
    rewrite <- (Hg j'' _ _ Hnq').
    f_equal.
    apply urelspinj_equal.
    unfold n'.
    rewrite -> extend_term_cancel; auto.
    }
  so (Hf j' m' p' Hmp') as (Hmb & _).
  so (Hf j'' n' q' Hnq') as (_ & Hqc).
  so (urelspinj_dist_index' _#11 HCD) as [H | H].
    {
    apply dist_refl'.
    destruct H as (<- & H).
    assert (j' <= j) as Hj' by omega; clear H.
    rewrite -> Nat.min_r in Hmq; auto.
    f_equal.
    assert (rel (extend_urel _ stop A) j' m' q') as Hmq'.
      {
      cbn.
      unfold m', q'.
      rewrite -> !extend_term_cancel; auto.
      }
    so (Hbc j' m' q' Hmq') as (z & Hmb' & Hqc').
    so (cbasic_fun _#7 Hmb Hmb') as H.
    injectionT H.
    intros <-.
    so (cbasic_fun _#7 Hqc Hqc') as H.
    injectionT H.
    auto.
    }

    {
    assert (j <= j') as Hj' by omega.
    assert (j <= j'') as Hj'' by omega.
    clear H.
    rewrite -> Nat.min_l in Hmq; auto.
    apply proj_dist_dist.
    rewrite -> (proj_embed_down _#4 Hj').
    rewrite -> (proj_embed_down _#4 Hj'').
    assert (rel (extend_urel _ stop A) j m' q') as Hmq'.
      {
      cbn.
      unfold m', q'.
      rewrite -> !extend_term_cancel; auto.
      }
    so (Hbc j m' q' Hmq') as (z & Hmb' & Hqc').
    so (cbasic_fun _#7 (cbasic_downward _#7 Hj' Hmb) Hmb') as Heq1.
    unfold projc, stdc in Heq1; cbn in Heq1.
    so (cbasic_fun _#7 (cbasic_downward _#7 Hj'' Hqc) Hqc') as Heq2.
    unfold projc, stdc in Heq2; cbn in Heq2.
    so (expair_injection_dep _#6 (eqtrans Heq1 (eqsymm Heq2))) as Heq; clear Heq1 Heq2.
    so (eq_dep_impl_eq _#6 Heq) as (h & Heq'); clear Heq.
    so (proof_irrelevance _ (eqtrans (approx_combine_le _#3 Hj') (eqsymm (approx_combine_le _#3 Hj''))) h); subst h.
    rewrite <- transport_compose in Heq'.
    so (transport_symm' _ spcar _ _ (approx_combine_le _#3 Hj'') _ _ Heq') as Heq.
    refine (dist_trans _#5 _ (dist_trans _#5 (dist_refl' _#4 Heq) _)); clear Heq Heq'.
      {
      apply transport_nonexpansive.
      apply (pi2 (proj_ne j (approx j' K))).
      apply dist_symm.
      setoid_rewrite -> Hstdf at 2.
      apply std_dist; omega.
      }

      {
      apply transport_nonexpansive.
      apply (pi2 (proj_ne j (approx j'' K))).
      setoid_rewrite -> Hstdf at 2.
      apply std_dist; omega.
      }
    }
  }
change (car (urelsp A) -> car (space K)) in g.
cbn.
unfold con_action.
set (X := approx i (qtarrow (cin pg) A K)).
assert (X = qtarrow (cin pg) A K).
  {
  subst X.
  cbn.
  f_equal.
    {
    symmetry.
    eapply interp_uext_impl_ceiling; eauto.
    }
    
    {
    symmetry.
    eapply interp_kext_impl_approx; eauto.
    }
  }
clearbody X.
subst X.
exists (expair g Hneg).
split.
  {
  apply cinterp_eval_refl.
  apply (interp_ctlam _#9 f); auto.
  intros j m p Hmp.
  exact (Hf j m p Hmp andel).
  }

  {
  apply cinterp_eval_refl.
  apply (interp_ctlam _#9 f); auto.
  intros j m p Hmp.
  exact (Hf j m p Hmp ander).
  }
Qed.


Lemma ctapp_formation :
  forall pg A K i a b m p,
    rel (con_urel pg (qtarrow (cin pg) A K)) i a b
    -> rel (extend_urel (cin pg) stop A) i m p
    -> rel (con_urel pg K) i (ctapp a m) (ctapp b p).
Proof.
intros pg A K i a b m p Hab Hmp.
destruct Hab as (B & Ha & Hb).
cbn in B.
set (m' := map_term (extend stop (cin pg)) m).
set (p' := map_term (extend stop (cin pg)) p).
assert (rel (ceiling (S i) A) i m' p') as Hmp'.
  {
  split; auto.
  }
exists (pi1 B (urelspinj _ i _ _ Hmp')).
split.
  {
  apply cinterp_eval_refl.
  apply interp_ctapp; auto.
  }

  {
  apply cinterp_eval_refl.
  apply interp_ctapp; auto.
  }
Qed.


Lemma ctapp_ctlam_beta :
  forall pg A K i a b c k m p,
    interp_uext pg i a A
    -> interp_kext pg i k K
    -> hygiene (permit clo) b
    -> hygiene (permit clo) c
    -> (forall j m p,
          rel (extend_urel (cin pg) stop A) j m p
          -> rel (con_urel pg K) j (subst1 m b) (subst1 p c))
    -> rel (extend_urel (cin pg) stop A) i m p
    -> rel (con_urel pg K) i (ctapp (ctlam a b k) m) (subst1 p c).
Proof.
intros pg A K i a b c k m p Ha Hk Hclb Hclc Hbc Hmp.
so (ctlam_formation _#10 Ha Ha Hk Hk Hclb Hclc Hbc) as Hlam.
so (ctapp_formation _#8 Hlam Hmp) as Happ.
destruct Happ as (y & Hleft & Hright).
exists y.
split; auto.
clear Hlam Hleft.
(* Root around in Hright to get what we need. *)
so (cbasic_value_inv _#6 value_ctapp Hright) as H.
invertc H.
intros w A' n Hnp B Hlam <-.
so (interp_kext_impl_approx _#4 Hk) as HeqK.
clear Hright.
revert B Hlam.
rewrite <- HeqK.
intros B Hlam.
so (cbasic_value_inv _#6 value_ctlam Hlam) as H.
so (interp_ctlam_invert _#8 H) as (K' & A'' & f & B' & _ & Ha' & Hk' & Hf & HB & Heq); clear H.
so (interp_uext_fun _#5 Ha Ha'); subst A''.
so (interp_kext_fun _#5 Hk Hk'); subst K'.
clear Ha' Hk'.
injection Heq.
intros H ->.
injectionT H.
intros ->.
injectionT Heq.
intros <-.
assert (rel (extend_urel _ _ A) i (map_term (extend _ _) n) p) as Hnp'.
  {
  cbn.
  rewrite -> extend_term_cancel; auto using cin_stop.
  }
so (Hf _ _ _ Hnp') as Hpc.
force_exact Hpc.
unfold cinterp.
f_equal.
clear Hpc.
so (HB _ _ _ Hnp') as HBnp.
match type of HBnp with
| pi1 B ?X = _ =>
    replace X with (urelspinj _ _ _ _ Hnp) in HBnp
end.
2:{
  apply urelspinj_equal; auto.
  }
cbn in HBnp.
rewrite -> HBnp.
symmetry.
apply (expair_compat_transport _#6 HeqK).
rewrite -> transport_embed.
rewrite -> embed_approx'.
reflexivity.
Qed.


Lemma ctapp_ctlam_beta_double :
  forall pg A K i a b c k m p,
    interp_uext pg i a A
    -> interp_kext pg i k K
    -> hygiene (permit clo) b
    -> hygiene (permit clo) c
    -> (forall j m p,
          rel (extend_urel (cin pg) stop A) j m p
          -> rel (con_urel pg K) j (subst1 m b) (subst1 p c))
    -> rel (extend_urel (cin pg) stop A) i m p
    -> rel (con_urel pg K) i (ctapp (ctlam a b k) m) (subst1 p c)
       /\ rel (con_urel pg K) i (subst1 m b) (subst1 p c).
Proof.
intros pg A K i a b c k m p Ha Hk Hclb Hclc Hbc Hmp.
split.
  {
  eapply ctapp_ctlam_beta; eauto.
  }

  {
  apply Hbc; auto.
  }
Qed.


Lemma ctlam_ctapp_eta :
  forall pg A K i a b c k,
    interp_kext pg i k K
    -> interp_uext pg i a A
    -> rel (con_urel pg (qtarrow (cin pg) A K)) i b c
    -> rel (con_urel pg (qtarrow (cin pg) A K)) i (ctlam a (ctapp (subst sh1 b) (var 0)) k) c.
Proof.
intros pg A K i a b c k Hk Ha Hbc.
so (urel_closed _#5 Hbc) as (Hclb & Hclc).
so (interp_uext_impl_ceiling _#4 Ha) as HeqA.
so (interp_kext_impl_approx _#4 Hk) as HeqK.
exploit (ctlam_formation pg A K i a a (ctapp (subst sh1 b) (var 0)) (ctapp (subst sh1 c) (var 0)) k k) as Hlam; auto; try prove_hygiene.
  {
  intros j m p Hmp.
  simpsub.
  assert (j <= i) as Hj.
    {
    rewrite -> HeqA in Hmp.
    rewrite <- ceiling_extend_urel in Hmp.
    destruct Hmp; omega.
    }
  eapply ctapp_formation; eauto.
  eapply urel_downward_leq; eauto.
  }
destruct Hlam as (B & Hlam & _).
destruct Hbc as (C & Hb & Hc).
cut (B = C).
  {
  intros <-.
  exists B.
  auto.
  }
clear c Hc Hclc.
revert B Hlam C Hb.
cbn [approx].
rewrite <- HeqK.
rewrite <- HeqA.
intros B Hlam C Hb.
cbn in B, C.
apply (nearrow_extensionality (urelsp A) (space K)).
intros x.
so (urelsp_eta _ _ x) as (j & m & p & Hmp & ->).
assert (j <= i) as Hj.
  {
  rewrite -> HeqA in Hmp.
  destruct Hmp; omega.
  }
so (interp_ctlam_invert _#8 (cbasic_value_inv _#6 value_ctlam Hlam)) as (K' & A' & f & B'' & Hhygiene & Ha' & Hk' & Hf & HB & Heq).
so (interp_uext_fun _#5 Ha Ha'); subst A'.
so (interp_kext_fun _#5 Hk Hk'); subst K'.
injectionT Heq.
intros <-.
clear Ha' Hk'.
assert (rel (extend_urel (cin pg) stop A) j (map_term (extend _ _) m) (map_term (extend _ _) p)) as Hmp'.
  {
  cbn.
  rewrite -> !extend_term_cancel; auto using cin_stop.
  }
so (HB _ _ _ Hmp') as Heq.
rewrite -> (urelspinj_equal _ A j _ _ _ _ Hmp' Hmp) in Heq.
2:{
  rewrite -> extend_term_cancel; auto using cin_stop.
  }
rewrite -> Heq.
clear Heq.
so (Hf _ _ _ Hmp') as Hint.
simpsubin Hint.
assert (rel (ceiling (S j) A) j m p) as Hmp''.
  {
  split; [omega | auto].
  }
assert (j < S j) as Hlt by omega.
exploit (interp_ctapp the_system pg true j b (map_term (extend _ _) m) (cin pg) (ceiling (S j) A) (approx j K) (nearrow_compose2 (embed_ceiling_ne (S j) A) (proj_ne j K) (std (S j) (qtarrow (cin pg) A K) C)) _ _ (conj Hlt Hmp)).
  {
  apply extend_term_cancel; auto using cin_stop.
  }

  {
  exact (cbasic_downward _#7 Hj Hb).
  }
so (cbasic_fun _#7 Hint (cinterp_eval_refl _#6 H)) as Heq; clear Hint H.
injectionT Heq.
intro Heq.
rewrite -> Heq.
cbn.
fold (proj j K).
so (cbasic_impl_std _#6 Hb) as H.
unfold stdc in H; cbn in H.
injectionT H.
intros HstdC.
setoid_rewrite -> HstdC at 2.
rewrite -> std_tarrow_is.
rewrite -> std_tarrow_is.
cbn.
rewrite -> (embed_ceiling_urelspinj _ (S j) A j _ _ Hmp Hlt).
unfold std_tarrow_action.
rewrite -> urelsp_index_inj.
rewrite -> Min.min_idempotent.
rewrite -> Nat.min_r; [| omega].
fold (std (S j) K).
rewrite -> proj_std; auto.
rewrite -> embed_std; auto.
apply std_collapse.
apply embed_proj.
Qed.


Lemma cpair_formation :
  forall pg K L i a b c d,
    rel (con_urel pg K) i a b
    -> rel (con_urel pg L) i c d
    -> rel (con_urel pg (qprod K L)) i (cpair a c) (cpair b d).
Proof.
intros pg K L i a b c d Hab Hcd.
cbn.
destruct Hab as (x & Ha & Hb).
destruct Hcd as (y & Hc & Hd).
exists (x, y).
split.
  {
  apply cinterp_eval_refl.
  cbn.
  apply interp_cpair; auto.
  }

  {
  apply cinterp_eval_refl.
  cbn.
  apply interp_cpair; auto.
  }
Qed.


Lemma cpi1_formation :
  forall pg K L i a b,
    rel (con_urel pg (qprod K L)) i a b
    -> rel (con_urel pg K) i (cpi1 a) (cpi1 b).
Proof.
intros pg K L i a b Hab.
destruct Hab as (x & Ha & Hb).
cbn in x, Ha, Hb.
exists (fst x).
split.
  {
  apply cinterp_eval_refl.
  apply interp_cpi1; auto.
  }

  {
  apply cinterp_eval_refl.
  apply interp_cpi1; auto.
  }
Qed.


Lemma cpi2_formation :
  forall pg K L i a b,
    rel (con_urel pg (qprod K L)) i a b
    -> rel (con_urel pg L) i (cpi2 a) (cpi2 b).
Proof.
intros pg K L i a b Hab.
destruct Hab as (x & Ha & Hb).
cbn in x, Ha, Hb.
exists (snd x).
split.
  {
  apply cinterp_eval_refl.
  apply interp_cpi2; auto.
  }

  {
  apply cinterp_eval_refl.
  apply interp_cpi2; auto.
  }
Qed.


Lemma cpi1_cpair_beta :
  forall pg K L i a b c d,
    rel (con_urel pg K) i a b
    -> rel (con_urel pg L) i c d
    -> rel (con_urel pg K) i (cpi1 (cpair a c)) b.
Proof.
intros pg K L i a b c d Hab Hcd.
destruct Hab as (x & Ha & Hb).
destruct Hcd as (y & Hc & Hd).
exists x.
split; auto.
apply cinterp_eval_refl.
replace x with (fst (x, y)) by reflexivity.
apply interp_cpi1.
apply cinterp_eval_refl.
apply interp_cpair; auto.
Qed.


Lemma cpi2_cpair_beta :
  forall pg K L i a b c d,
    rel (con_urel pg K) i a b
    -> rel (con_urel pg L) i c d
    -> rel (con_urel pg L) i (cpi2 (cpair a c)) d.
Proof.
intros pg K L i a b c d Hab Hcd.
destruct Hab as (x & Ha & Hb).
destruct Hcd as (y & Hc & Hd).
exists y.
split; auto.
apply cinterp_eval_refl.
replace y with (snd (x, y)) by reflexivity.
apply interp_cpi2.
apply cinterp_eval_refl.
apply interp_cpair; auto.
Qed.


Lemma cpair_cpi_eta :
  forall pg K L i a b,
    rel (con_urel pg (qprod K L)) i a b
    -> rel (con_urel pg (qprod K L)) i (cpair (cpi1 a) (cpi2 a)) b.
Proof.
intros pg K L i a b Hab.
destruct Hab as (x & Ha & Hb).
exists x.
split; auto.
replace x with (fst x, snd x).
2:{
  destruct x; auto.
  }
apply cinterp_eval_refl.
cbn.
apply (interp_cpair _#6 (approx i K) (approx i L)).
  {
  apply cinterp_eval_refl.
  apply interp_cpi1; auto.
  }

  {
  apply cinterp_eval_refl.
  apply interp_cpi2; auto.
  }
Qed.


Lemma cnext_formation_zero :
  forall pg K a b,
    hygiene clo a
    -> hygiene clo b
    -> rel (con_urel pg (qfut K)) 0 (cnext a) (cnext b).
Proof.
intros pg K a b.
cbn.
exists tt.
cbn.
split.
  {
  apply cinterp_eval_refl.
  apply interp_cnext_zero; auto.
  }

  {
  apply cinterp_eval_refl.
  apply interp_cnext_zero; auto.
  }
Qed.


Lemma cnext_formation :
  forall pg K i a b,
    rel (con_urel pg K) i a b
    -> rel (con_urel pg (qfut K)) (S i) (cnext a) (cnext b).
Proof.
intros pg K i a b Hab.
destruct Hab as (x & Ha & Hb).
exists x.
split.
  {
  cbn.
  apply cinterp_eval_refl.
  apply interp_cnext; auto.
  }

  {
  cbn.
  apply cinterp_eval_refl.
  apply interp_cnext; auto.
  }
Qed.


Lemma cprev_formation :
  forall pg K i a b,
    rel (con_urel pg (qfut K)) (S i) a b
    -> rel (con_urel pg K) i (cprev a) (cprev b).
Proof.
intros pg K i a b Hab.
destruct Hab as (x & Ha & Hb).
cbn in Ha, Hb.
exists x.
split.
  {
  apply cinterp_eval_refl.
  apply interp_cprev; auto.
  }

  {
  apply cinterp_eval_refl.
  apply interp_cprev; auto.
  }
Qed.


Lemma cprev_cnext_beta :
  forall pg K i a b,
    rel (con_urel pg K) i a b
    -> rel (con_urel pg K) i (cprev (cnext a)) b.
Proof.
intros pg K i a b Hab.
destruct Hab as (x & Ha & Hb).
exists x.
split; auto.
apply cinterp_eval_refl.
apply interp_cprev.
apply cinterp_eval_refl.
apply interp_cnext; auto.
Qed.


Lemma cnext_cprev_eta :
  forall pg K i a b,
    rel (con_urel pg (qfut K)) i a b
    -> rel (con_urel pg (qfut K)) i (cnext (cprev a)) b.
Proof.
intros pg K i a b Hab.
so (urel_closed _#5 Hab) as (Hcla & Hclb).
destruct Hab as (x & Ha & Hb).
destruct i as [| i].
  {
  exists tt.
  cbn in x.
  destruct x.
  split; auto.
  apply cinterp_eval_refl.
  apply interp_cnext_zero.
  apply hygiene_auto; cbn; auto.
  }
exists x.
split; auto.
apply cinterp_eval_refl.
cbn.
apply interp_cnext.
apply cinterp_eval_refl.
apply interp_cprev; auto.
Qed.
