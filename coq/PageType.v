
Require Import Axioms.
Require Import Tactics.
Require Import Sigma.
Require Import Relation.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.
Require Import Dynamic.
Require Import Equivalence.
Require Import MapTerm.
Require Import Hygiene.
Require Import Ofe.
Require Import Uniform.
Require Import Urelsp.
Require Import Intensional.
Require Import Candidate.
Require Import SemanticsSimple.
Require Import SemanticsWtype.
Require Import SemanticsProperty.
Require Import Semantics.
Require Import SemanticsKnot.
Require Import System.
Require Import Defined.
Require Import PageCode.
Require Import Hygiene.
Require Import Equivalences.
Require Import ProperClosed.
Require Import ProperEquiv.
Require Import ProperFun.
Require Import ProperDownward.
Require Import Ordinal.
Require Import Judgement.

Require Import Extend.
Require Import MapTerm.
Require Import Ceiling.
Require Import Truncate.
Require Import SemanticsMu.
Require Import SemanticsSigma.
Require Import ExtendTruncate.
Require Import Equality.
Require Import SemanticsPositive.
Require Import SemanticsGuard.



Local Ltac prove_hygiene :=
  repeat (first [ apply hygiene_shift_permit
                | apply hygiene_sumbool
                | apply natlit_closed
                | apply map_hygiene
                | apply hygiene_auto; cbn; repeat2 split; auto
                ]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1;
  try (apply hygiene_var; cbn; auto; done).


Definition nat_action i : nat -> relation sterm
  :=
  fun j m n =>
    exists k,
    j <= i
    /\ natinterp m k
    /\ natinterp n k.


Lemma nat_uniform :
  forall i, uniform _ (nat_action i).
Proof.
intros i.
do2 3 split.

(* closed *)
{
intros j m n H.
destruct H as (k & _ & Hm & Hn).
split; eauto using natinterp_closed.
}

(* equiv *)
{
intros j m m' n n' Hclm' Hcln' Hequivm Hequivn Hact.
destruct Hact as (k & Hj & Hm & Hn).
exists k.
do2 2 split; eauto using natinterp_equiv.
}

(* zigzag *)
{
intros j m n p q Hmn Hpn Hpq.
destruct Hmn as (k & Hj & Hm & Hn).
destruct Hpn as (k' & _ & Hp & Hn').
so (natinterp_fun _#3 Hn Hn'); subst k'.
destruct Hpq as (k' & _ & Hp' & Hq).
so (natinterp_fun _#3 Hp Hp'); subst k'.
exists k.
auto.
}

(* downward *)
{
intros j m n H.
destruct H as (k & Hj & Hm & Hn).
exists k.
do2 2 split; auto.
omega.
}
Qed.


Definition nat_urel i : surel := mk_urel (nat_action i) (nat_uniform i).


Lemma bool_eval_iff_true :
  forall w i j m p,
    rel (bool_urel w i) j m p
    -> star step m btrue <-> star step p btrue.
Proof.
intros w i j m p Hmp.
destruct Hmp as (_ & _ & _ & [(Hm & Hp) | (Hm & Hp)]).
  {
  split; auto.
  }
  
  {
  split.
    {
    intro Hm'.
    so (determinism_eval _#4 (conj Hm value_bfalse) (conj Hm' value_btrue)) as H.
    discriminate H.
    }

    {
    intro Hp'.
    so (determinism_eval _#4 (conj Hp value_bfalse) (conj Hp' value_btrue)) as H.
    discriminate H.
    }
  }
Qed.


Lemma bool_eval_iff_false :
  forall w i j m p,
    rel (bool_urel w i) j m p
    -> star step m bfalse <-> star step p bfalse.
Proof.
intros w i j m p Hmp.
destruct Hmp as (_ & _ & _ & [(Hm & Hp) | (Hm & Hp)]).
  {
  split.
    {
    intro Hm'.
    so (determinism_eval _#4 (conj Hm' value_bfalse) (conj Hm value_btrue)) as H.
    discriminate H.
    }

    {
    intro Hp'.
    so (determinism_eval _#4 (conj Hp' value_bfalse) (conj Hp value_btrue)) as H.
    discriminate H.
    }
  }

  {
  split; auto.
  }
Qed.


Lemma bool_action_contra :
  forall w i j m,
    bool_action w i j btrue m
    -> bool_action w i j bfalse m
    -> False.
Proof.
intros w i j m Htrue Hfalse.
so (bool_eval_iff_true _#5 Htrue andel (star_refl _)) as H.
so (bool_eval_iff_false _#5 Hfalse andel (star_refl _)) as H'.
so (determinism_eval _#4 (conj H value_btrue) (conj H' value_bfalse)) as HH.
discriminate HH.
Qed.


Lemma bool_urelsp_contra :
  forall w i (C : urelsp_car (bool_urel w i)) j,
    pi1 C j btrue
    -> pi1 C j bfalse
    -> False.
Proof.
intros w i C j Htrue Hfalse.
so (urelsp_eta _#2 C) as (k & m & p & Hmp & ->).
cbn in Htrue, Hfalse.
destruct Htrue as (_ & _ & _ & _ & [(_ & Hsteps) | (Hcontra & _)]).
2:{
  so (determinism_eval _#4 (conj (star_refl _) value_btrue) (conj Hcontra value_bfalse)) as H.
  discriminate H.
  }
destruct Hfalse as (_ & _ & _ & _ & [(Hcontra & _) | (_ & Hsteps')]).
  {
  so (determinism_eval _#4 (conj (star_refl _) value_bfalse) (conj Hcontra value_btrue)) as H.
  discriminate H.
  }
so (determinism_eval _#4 (conj Hsteps value_btrue) (conj Hsteps' value_bfalse)) as H.
discriminate H.
Qed.


Definition sumtp_rhs_action w i (A B : wurel w) (C : urelsp_car (bool_urel w i))
  : nat -> wterm w -> wterm w -> Prop
  :=
  fun j m p =>
    (pi1 C j btrue /\ rel A j m p)
    \/
    (pi1 C j bfalse /\ rel B j m p).


Lemma sumtp_rhs_uniform :
  forall w i A B C,
    uniform _ (sumtp_rhs_action w i A B C).
Proof.
intros w i A B C.
do2 3 split.

(* closed *)
{
intros j m p Hmp.
destruct Hmp as [(Htrue & Hmp) | (Hfalse & Hmp)]; eapply urel_closed; eauto.
}

(* equiv *)
{
intros j m m' p p' Hclm' Hclp' Hequivm Hequivp Hmp.
destruct Hmp as [(Htrue & Hmp) | (Hfalse & Hmp)].
  {
  left.
  eauto using urel_equiv.
  }

  {
  right.
  eauto using urel_equiv.
  }
}

(* zigzag *)
{
intros j m p n q Hmp Hnp Hnq.
destruct Hmp as [(Htrue & Hmp) | (Hfalse & Hmp)].
  {
  destruct Hnp as [(_ & Hnp) | (Hfalse & _)].
  2:{
    destruct (bool_urelsp_contra _#4 Htrue Hfalse).
    }
  destruct Hnq as [(_ & Hnq) | (Hfalse & _)].
  2:{
    destruct (bool_urelsp_contra _#4 Htrue Hfalse).
    }
  left.
  split; auto.
  eapply urel_zigzag; eauto.
  }

  {
  destruct Hnp as [(Htrue & _) | (_ & Hnp)].
    {
    destruct (bool_urelsp_contra _#4 Htrue Hfalse).
    }
  destruct Hnq as [(Htrue & _) | (_ & Hnq)].
    {
    destruct (bool_urelsp_contra _#4 Htrue Hfalse).
    }
  right.
  split; auto.
  eapply urel_zigzag; eauto.
  }
}

(* downward *)
{
intros j m p Hmp.
destruct Hmp as [(Htrue & Hmp) | (Hfalse & Hmp)].
  {
  left; split; auto using urel_downward.
  apply (urelsp_downward _#4 (S j)); auto.
  }

  {
  right; split; auto using urel_downward.
  apply (urelsp_downward _#4 (S j)); auto.
  }
}
Qed.


Definition sumtp_rhs_urel w i (A B : wurel w) (C : car (urelsp (bool_urel w i)))
  : car (wurel_ofe w)
  :=
  mk_urel _ (sumtp_rhs_uniform w i A B C).


Lemma sumtp_rhs_meta_unique :
  forall w i (A B : wiurel w) (C : urelsp_car (bool_urel w i)),
    exists! (x : meta (obj w)), exists y,
      x = meta_truncate (S (urelsp_index _ C)) y
      /\
      ((pi1 C (urelsp_index _ C) btrue /\ y = snd A)
       \/
       (pi1 C (urelsp_index _ C) bfalse /\ y = snd B)).
Proof.
intros w i A B C.
so (urelsp_eta _ _ C) as (j & m & p & Hmp & ->).
rewrite -> urelsp_index_inj.
destruct Hmp as (Hj & Hclm & Hclp & [(Hstepsm & Hstepsp) | (Hstepsm & Hstepsp)]).
  {
  exists (meta_truncate (S j) (snd A)).
  split.
    {
    exists (snd A).
    split; auto.
    left.
    split; auto.
    cbn.
    split; auto.
    do2 3 split; auto.
      {
      apply hygiene_auto; cbn; auto.
      }
    left.
    split; auto.
    apply star_refl.
    }

    {
    intros x Hx.
    destruct Hx as (y & -> & [(Htrue & ->) | (Hfalse & ->)]); auto.
    cbn in Hfalse.
    exfalso.
    destruct Hfalse as (_ & _ & _ & _ & [(Hcontra & _) | (_ & Hstepsp')]).
      {
      so (determinism_eval _#4 (conj (star_refl _) value_bfalse) (conj Hcontra value_btrue)) as H.
      discriminate H.
      }

      {
      so (determinism_eval _#4 (conj Hstepsp' value_bfalse) (conj Hstepsp value_btrue)) as H.
      discriminate H.
      }
    }
  }

  {
  exists (meta_truncate (S j) (snd B)).
  split.
    {
    exists (snd B).
    split; auto.
    right.
    split; auto.
    cbn.
    split; auto.
    do2 3 split; auto.
      {
      apply hygiene_auto; cbn; auto.
      }
    right.
    split; auto.
    apply star_refl.
    }

    {
    intros x Hx.
    destruct Hx as (y & -> & [(Htrue & ->) | (Hfalse & ->)]); auto.
    cbn in Htrue.
    exfalso.
    destruct Htrue as (_ & _ & _ & _ & [(_ & Hstepsp') | (Hcontra & _)]).
      {
      so (determinism_eval _#4 (conj Hstepsp value_bfalse) (conj Hstepsp' value_btrue)) as H.
      discriminate H.
      }

      {
      so (determinism_eval _#4 (conj (star_refl _) value_btrue) (conj Hcontra value_bfalse)) as H.
      discriminate H.
      }
    }
  }
Qed.


Definition sumtp_rhs_meta w i (A B : wiurel w) (C : car (urelsp (bool_urel w i))) 
  : meta (obj w)
  :=
  pi1 (description _ _ (sumtp_rhs_meta_unique w i A B C)).


Definition sumtp_rhs w i (A B : wiurel w) (C : car (urelsp (bool_urel w i)))
  : car (wiurel_ofe w)
  :=
  (sumtp_rhs_urel w i (den A) (den B) C, sumtp_rhs_meta w i A B C).


Lemma sumtp_rhs_nonexpansive :
  forall w i A B, nonexpansive (sumtp_rhs w i A B).
Proof.
intros w i A B.
intros j C D Hdist.
split.
  {
  intros k Hj.
  fextensionality 2.
  intros m p.
  pextensionality.
    {
    intro Hmp.
    destruct Hmp as [(Htrue & Hmp) | (Hfalse & Hmp)].
      {
      left.
      split; auto.
      rewrite <- Hdist; auto.
      }
  
      {
      right.
      split; auto.
      rewrite <- Hdist; auto.
      }
    }
  
    {
    intro Hmp.
    destruct Hmp as [(Htrue & Hmp) | (Hfalse & Hmp)].
      {
      left.
      split; auto.
      rewrite -> Hdist; auto.
      }
  
      {
      right.
      split; auto.
      rewrite -> Hdist; auto.
      }
    }
  }

  {
  destruct j as [| j].
    {
    apply dist_zero.
    }
  unfold sumtp_rhs.
  cbn [snd].
  unfold sumtp_rhs_meta.
  match goal with
  | |- dist _ (pi1 (@description _ _ ?Z)) (pi1 (@description _ _ ?Z')) =>
     set (X := Z); set (Y := Z')
  end.
  destruct X as (xx & Hxx).
  destruct Y as (yy & Hyy).
  rewrite -> !description_beta.
  destruct Hxx as ((x & -> & Hx) & Huniq).
  destruct Hyy as ((y & -> & Hy) & _).
  so (urelsp_eta _ _ C) as (k & m & p & Hmp & ->).
  so (urelsp_eta _ _ D) as (k' & n & q & Hnq & ->).
  rewrite -> !urelsp_index_inj in Hx, Huniq, Hy |- *.
  rewrite -> urelsp_index_inj.
  cut (x = y).
    {
    intros <-.
    so (urelspinj_dist_index' _#11 Hdist) as [(<- & _) | (Hle & Hle')].
      {
      apply dist_refl.
      }

      {
      eapply dist_trans.
        {
        refine (dist_downward_leq _#5 Hle _).
        apply meta_truncate_near.
        }
      eapply dist_trans.
      2:{
        apply dist_symm.
        refine (dist_downward_leq _#5 Hle' _).
        apply meta_truncate_near.
        }
      apply dist_refl.
      }
    }
  so (urelspinj_dist_invert _#11 Hdist) as Hmq.
  destruct Hx as [(Htrue & ->) | (Hfalse & ->)].
    {
    destruct Hy as [(_ & ->) | (Hfalse & ->)]; auto.
    exfalso.
    cbn -[rel] in Htrue, Hfalse.
    destruct Htrue as (_ & Htrue).
    destruct Hfalse as (_ & Hfalse).
    so (bool_eval_iff_true _#5 Htrue andel (star_refl _)) as H.
    rewrite <- (bool_eval_iff_true _#5 Hmp) in H.
    rewrite -> (bool_eval_iff_true _#5 Hmq) in H.
    rewrite <- (bool_eval_iff_true _#5 Hfalse) in H.
    so (determinism_eval _#4 (conj (star_refl _) value_bfalse) (conj H value_btrue)) as H'.
    discriminate H'.
    }

    {
    destruct Hy as [(Htrue & ->) | (_ & ->)]; auto.
    exfalso.
    cbn -[rel] in Htrue, Hfalse.
    destruct Htrue as (_ & Htrue).
    destruct Hfalse as (_ & Hfalse).
    so (bool_eval_iff_true _#5 Htrue andel (star_refl _)) as H.
    rewrite <- (bool_eval_iff_true _#5 Hmq) in H.
    rewrite -> (bool_eval_iff_true _#5 Hmp) in H.
    rewrite <- (bool_eval_iff_true _#5 Hfalse) in H.
    so (determinism_eval _#4 (conj (star_refl _) value_bfalse) (conj H value_btrue)) as H'.
    discriminate H'.
    }
  }
Qed.


Definition sumtp_rhs_ne w i (A B : wiurel w) : urelsp (bool_urel w i) -n> wiurel_ofe w
  :=
  expair (sumtp_rhs w i A B) (sumtp_rhs_nonexpansive w i A B).


Definition sumtp_def w i (A B : wiurel w) : wiurel w
  :=
  iusigma w
    (iubase (bool_urel w i))
    (sumtp_rhs_ne w i A B).


Lemma interp_sumtp :
  forall pg s i a b A B,
    interp pg s i a A
    -> interp pg s i b B
    -> interp pg s i (sumtype a b) (sumtp_def stop i A B).
Proof.
intros pg s i a b A B Hinta Hintb.
so (basic_closed _#6 Hinta) as Hcla.
so (basic_closed _#6 Hintb) as Hclb.
apply interp_eval_refl.
apply interp_sigma.
  {
  apply interp_eval_refl.
  apply interp_bool.
  }
apply functional_i.
  {
  prove_hygiene.
  }

  {
  rewrite -> den_iubase.
  rewrite -> ceiling_bool.
  rewrite -> min_l; auto.
  }
intros j m p Hj Hmp.
simpsub.
cbn.
so Hmp as H.
cbn in H.
destruct H as (_ & Hclm & Hclp & Hsteps).
assert (hygiene clo (if s then m else p)) as Hclmp.
  {
  destruct s; auto.
  }
destruct Hsteps as [(Hstepsm & Hstepsp) | (Hstepsm & Hstepsp)].
  {
  assert (star step (if s then m else p) btrue) as Hsteps.
    {
    destruct s; auto.
    }
  assert (interp pg s j (bite (if s then m else p) a b) (iutruncate (S j) A)) as H.
    {
    refine (basic_equiv _#7 _ _ (basic_downward _#7 Hj Hinta)).
      {
      prove_hygiene.
      }

      {
      apply equiv_symm.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ (fun z => bite z _ _)); eauto using step_bite1.
        }
      apply star_one.
      apply step_bite2.
      }
    }
  force_exact H; clear H.
  unfold interp.
  f_equal.
  unfold iutruncate.
  unfold sumtp_rhs.
  f_equal.
    {
    apply urel_extensionality.
    fextensionality 3.
    intros k n q.
    cbn.
    pextensionality.
      {
      intros (Hk & Hnq).
      left.
      cbn.
      split; auto.
      split; [omega |].
      do2 3 split; [omega | prove_hygiene | auto |].
      left; split; auto.
      apply star_refl.
      }

      {
      intro Hnq.
      destruct Hnq as [(Htrue & Hnq) | (Hfalse & _)].
        {
        cbn in Htrue.
        destruct Htrue as (Hk & Htrue).
        split; auto.
        omega.
        }

        {
        exfalso.
        destruct Hfalse as (Hk & Hfalse).
        destruct Hfalse as (_ & _ & _ & [(Hcontra & _) | (_ & Hfalse)]).
          {
          so (determinism_eval _#4 (conj (star_refl _) value_bfalse) (conj Hcontra value_btrue)) as H.
          discriminate H.
          }

          {
          so (determinism_eval _#4 (conj Hstepsp value_btrue) (conj Hfalse value_bfalse)) as H.
          discriminate H.
          }
        }
      }
    }

    {
    unfold sumtp_rhs_meta.
    match goal with
    | |- _ = pi1 (description _ _ ?Z) =>
       set (X := Z)
    end.
    destruct X as (x & Hx).
    rewrite -> description_beta.
    symmetry.
    apply (Hx ander).
    rewrite -> urelsp_index_inj.
    exists (snd A).
    split; auto.
    left.
    split; auto.
    cbn -[rel].
    split; auto.
    do2 3 split; auto; try prove_hygiene.
    left; auto using star_refl.
    }
  }

  {
  assert (star step (if s then m else p) bfalse) as Hsteps.
    {
    destruct s; auto.
    }
  assert (interp pg s j (bite (if s then m else p) a b) (iutruncate (S j) B)) as H.
    {
    refine (basic_equiv _#7 _ _ (basic_downward _#7 Hj Hintb)).
      {
      prove_hygiene.
      }

      {
      apply equiv_symm.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ (fun z => bite z _ _)); eauto using step_bite1.
        }
      apply star_one.
      apply step_bite3.
      }
    }
  force_exact H; clear H.
  unfold interp.
  f_equal.
  unfold iutruncate.
  unfold sumtp_rhs.
  f_equal.
    {
    apply urel_extensionality.
    fextensionality 3.
    intros k n q.
    cbn.
    pextensionality.
      {
      intros (Hk & Hnq).
      right.
      cbn.
      split; auto.
      split; [omega |].
      do2 3 split; [omega | prove_hygiene | auto |].
      right; split; auto.
      apply star_refl.
      }

      {
      intro Hnq.
      destruct Hnq as [(Htrue & _) | (Hfalse & Hnq)].
        {
        exfalso.
        destruct Htrue as (Hk & Htrue).
        destruct Htrue as (_ & _ & _ & [(_ & Htrue) | (Hcontra & _)]).
          {
          so (determinism_eval _#4 (conj Hstepsp value_bfalse) (conj Htrue value_btrue)) as H.
          discriminate H.
          }

          {
          so (determinism_eval _#4 (conj (star_refl _) value_btrue) (conj Hcontra value_bfalse)) as H.
          discriminate H.
          }
        }

        {
        cbn in Hfalse.
        destruct Hfalse as (Hk & Hfalse).
        split; auto.
        omega.
        }
      }
    }

    {
    unfold sumtp_rhs_meta.
    match goal with
    | |- _ = pi1 (description _ _ ?Z) =>
       set (X := Z)
    end.
    destruct X as (x & Hx).
    rewrite -> description_beta.
    symmetry.
    apply (Hx ander).
    rewrite -> urelsp_index_inj.
    exists (snd B).
    split; auto.
    right.
    split; auto.
    cbn -[rel].
    split; auto.
    do2 3 split; auto; try prove_hygiene.
    right; auto using star_refl.
    }
  }
Qed.


(* Proving extend_sumtp is much harder than it seems like it should be. *)


Lemma extend_iurel_sumtp_rhs :
  forall v w (h : v <<= w) i A B C,
    extend_iurel h (sumtp_rhs v i A B C)
    =
    sumtp_rhs w i (extend_iurel h A) (extend_iurel h B) 
      (transport (extend_bool v w i h) urelsp_car (extend_urelsp h _ C)).
Proof.
intros v w h i A B C.
unfold sumtp_rhs, extend_iurel.
cbn.
f_equal.
  {
  apply urel_extensionality.
  cbn.
  unfold sumtp_rhs_action.
  fextensionality 3.
  intros j m p.
  cbn.
  rewrite -> (pi1_transport_lift _ _ urelsp_car_rhs _ _ (extend_bool v w i h)).
  pextensionality.
    {
    intros H.
    destruct H as [(Htrue & Hmp) | (Hfalse & Hmp)].
      {
      left.
      split; auto.
      }

      {
      right.
      split; auto.
      }
    }

    {
    intros H.
    destruct H as [(Htrue & Hmp) | (Hfalse & Hmp)].
      {
      left.
      split; auto.
      }

      {
      right.
      split; auto.
      }
    }
  }

  {
  unfold sumtp_rhs_meta.
  match goal with
  | |- extend_meta _ (pi1 (description _ _ ?Z1)) = pi1 (description _ _ ?Z2) =>
     set (x := Z1); set (y := Z2)
  end.
  destruct x as (x & Hx).
  destruct y as (y & Hy).
  rewrite -> !description_beta.
  symmetry.
  apply (Hy ander).
  destruct Hx as (Hx & _).
  destruct Hx as (x' & -> & Hx).
  rename x' into x.
  destruct Hy as (Hy & _).
  destruct Hy as (y' & -> & Hy).
  rename y' into y.
  so (urelsp_eta _ _ C) as (j & m & p & Hmp & ->).
  rewrite -> !urelsp_index_inj in Hx |- *.
  exists (extend_meta h x).
  split.
    {
    rewrite -> extend_meta_truncate.
    rewrite -> urelsp_index_transport.
    rewrite -> urelsp_index_extend.
    rewrite -> urelsp_index_inj.
    reflexivity.
    }
  destruct Hy as [(Htrue & ->) | (Hfalse & ->)].
    {
    left.
    split; auto.
    cbn.
    destruct Hx as [(_ & ->) | (Hcontra & _)]; auto.
    exfalso.
    rewrite -> (pi1_transport_lift _ _ urelsp_car_rhs _ _ (extend_bool v w i h)) in Htrue.
    destruct Htrue as (_ & Htrue).
    rewrite -> urelsp_index_transport in Htrue.
    rewrite -> urelsp_index_extend in Htrue.
    rewrite -> urelsp_index_inj in Htrue.
    simpmapin Htrue.
    cbn in Htrue.
    cbn in Hcontra.
    exact (bool_action_contra _#4 Htrue (Hcontra ander)).
    }

    {
    right.
    split; auto.
    cbn.
    destruct Hx as [(Hcontra & _) | (_ & ->)]; auto.
    exfalso.
    rewrite -> (pi1_transport_lift _ _ urelsp_car_rhs _ _ (extend_bool v w i h)) in Hfalse.
    destruct Hfalse as (_ & Hfalse).
    rewrite -> urelsp_index_transport in Hfalse.
    rewrite -> urelsp_index_extend in Hfalse.
    rewrite -> urelsp_index_inj in Hfalse.
    simpmapin Hfalse.
    cbn in Hfalse.
    cbn in Hcontra.
    exact (bool_action_contra _#4 (Hcontra ander) Hfalse).
    }
  }
Qed.


Lemma urelsp_of_extend :
  forall v w (A : wurel v) (C : urelsp_car (extend_urel v w A)),
    v <<= w
    -> pi1 C = (fun i m => pi1 C i (map_term (extend v w) (map_term (extend w v) m))).
Proof.
intros v w A C Hvw.
so (urelsp_eta _ _ C) as (i & m & p & Hmp & ->).
cbn.
fextensionality 2.
intros j n.
pextensionality.
  {
  intros (Hj & Hnp).
  split; auto.
  rewrite -> (extend_term_cancel _ _ Hvw); auto.
  }

  {
  intros (Hj & Hnp).
  split; auto.
  rewrite -> (extend_term_cancel _ _ Hvw) in Hnp; auto.
  }
Qed.


Lemma extend_sumtp :
  forall v w i A B (h : v <<= w),
    extend_iurel h (sumtp_def v i A B)
    =
    sumtp_def w i (extend_iurel h A) (extend_iurel h B).
Proof.
intros v w i A B h.
unfold sumtp_def.
rewrite -> extend_iusigma.
cbn.
match goal with
| |- iusigma _ ?x1 ?x2 = iusigma _ ?y1 ?y2 =>
   set (x := @expair 
               (wiurel w) (fun X => urelsp (den X) -n> wiurel_ofe w)
               x1 x2);
   set (y := @expair
               (wiurel w) (fun X => urelsp (den X) -n> wiurel_ofe w)
               y1 y2)
end.
change (iusigma w (pi1 x) (pi2 x) = iusigma w (pi1 y) (pi2 y)).
cut (x = y).
  {
  clearbody x y.
  intros <-.
  auto.
  }
subst x y.
apply expair_compat_dep.
apply exT_extensionality_prop_eq_dep.
cbn.
apply (eq_dep_prod_fst (wurel w) (meta (obj w)) (fun X => urelsp_car X -> wiurel w)).
  {
  f_equal.
  rewrite -> extend_iubase.
  f_equal.
  apply extend_bool; auto.
  }
cbn.
apply functional_extensionality_eq_dep_dom.
  {
  rewrite -> extend_bool; auto.
  }
intros C D Heq.
change (urelsp_car (extend_urel v w (bool_urel v i))) in C.
change (urelsp_car (bool_urel w i)) in D.
rewrite -> extend_iurel_sumtp_rhs.
f_equal.
so (eq_dep_impl_eq _#6 Heq) as (h' & <-).
so (proof_irrelevance _ (extend_bool v w i h) h'); subst h'.
f_equal.
apply exT_extensionality_prop.
cbn.
fextensionality 2.
intros j m.
so (f_equal (fun z => z j m) (urelsp_of_extend _#3 C h)) as H.
cbn in H.
rewrite -> H.
reflexivity.
Qed.


Definition nattp_body w i (X : car (wurel_ofe w)) : wiurel w
  :=
  sumtp_def w i 
    (iubase (unit_urel w i))
    (iubase (ceiling (S i) X)).


Definition nattp_def w i : siurel :=
  iubase
    (extend_urel w stop (mu_urel w (fun X => den (nattp_body w i X)))).


Lemma nattp_body_mono :
  forall w i,
    monotone (fun X => den (nattp_body w i X)).
Proof.
intros w i.
intros X Y Hincl.
unfold nattp_body.
cbn.
intros j m p Hmp.
cbn in Hmp.
cbn.
decompose Hmp.
intros m1 p1 m2 p2 Hmp1 Hclm Hclp Hstepsm Hstepsp Hmp2.
exists m1, p1, m2, p2, Hmp1.
do2 4 split; auto.
destruct Hmp2 as [(Htrue & Hmp2) | (Hfalse & Hmp2)].
  {
  left.
  split; auto.
  }

  {
  right.
  split; auto.
  destruct Hmp2 as (Hj & Hmp2).
  split; auto.
  }
Qed.


Lemma nattp_body_mono_blur :
  forall v w i,
    monotone (fun X => den (nattp_body w i (extend_urel v w (extend_urel w v X)))).
Proof.
intros v w i.
assert (monotone (fun X => extend_urel v w (extend_urel w v X))) as Hmono.
  {
  intros X Y Hincl.
  intros j m p Hmp.
  cbn.
  cbn in Hmp.
  apply Hincl; auto.
  }
so (Lattice.impl_compose _#8 Hmono (nattp_body_mono w i)) as H.
exact H.
Qed.


Lemma interp_nattp :
  forall pg s i,
    interp pg s i nattp (nattp_def (cin pg) i).
Proof.
intros pg s i.
assert (cin pg <<= stop) as Hstop.
  {
  eapply le_ord_trans; eauto using cin_top.
  apply succ_nodecrease.
  }
apply interp_eval_refl.
apply interp_mu; auto using le_ord_refl.
  {
  intros X h.
  simpsub.
  unfold nattp_body.
  rewrite -> extend_sumtp.
  rewrite -> extend_iubase.
  rewrite <- iutruncate_iubase.
  rewrite -> extend_unit; auto.
  apply interp_sumtp.
    {
    apply interp_eval_refl.
    apply interp_unit.
    }

    {
    apply interp_eval_refl.
    apply interp_extt.
    apply le_ord_refl.
    }
  }

  {
  intros j X Y Hdist.
  destruct j as [| j].
    {
    apply dist_zero.
    }
  eapply dist_trans.
    {
    apply dist_symm.
    apply ceiling_near.
    }
  eapply dist_trans.
  2:{
    apply ceiling_near.
    }
  apply dist_refl'.
  unfold nattp_body.
  cbn.
  rewrite -> !ceiling_sigma.
  f_equal.
  apply nearrow_extensionality.
  intros Z.
  cbn.
  apply ceiling_collapse.
  intros k Hk.
  fextensionality 2.
  intros m p.
  revert X Y Hdist.
  match goal with
  | |- forall (X Y : car (wurel_ofe (cin pg))), _ -> ?Z = ?Z' =>
     cut (forall (X Y : car (wurel_ofe (cin pg))), dist (S j) X Y -> Z -> Z')
  end.
    {
    intro Hprop.
    intros X Y Hdist.
    pextensionality; intro H; eapply Hprop; eauto.
    apply dist_symm; auto.
    }
  intros X Y Hdist Hmp.
  destruct Hmp as [(Htrue & Hmp) | (Hfalse & Hmp)].
    {
    left.
    split; auto.
    }

    {
    right.
    split; auto.
    destruct Hmp as (Hk' & Hmp).
    split; auto.
    eapply rel_from_dist; eauto.
    apply (dist_downward_leq _ _ (S j)); auto.
    }
  }

  {
  apply nattp_body_mono.
  }

  {
  apply robust_sigma.
    {
    replace booltp with (@subst (obj stop) (under 0 sh1) booltp) by (simpsub; auto).
    apply robust_const.
    }
  replace (var 0) with (@subst (obj stop) (under 1 sh1) (var 0)) by (simpsub; auto).
  apply robust_bite.
    {
    simpsub.
    replace unittp with (@subst (obj stop) (under 1 sh1) unittp) by (simpsub; auto).
    apply robust_const.
    }

    {
    simpsub.
    apply robust_var.
    }
  }
Qed.


Lemma map_natinterp_conv :
  forall (f : obj stop -> obj stop) m i,
    natinterp (map_term f m) i
    -> natinterp m i.
Proof.
intros f m i H.
remember (map_term f m) as n eqn:Heq.
revert m Heq.
induct H.

(* 0 *)
{
intros ? n p Hhyg Hstepsm Hstepsn Hstepsp m ->.
so (map_steps_form _#5 Hstepsm) as (np & Heqnp & Hstepsm').
so (map_eq_ppair_invert _#6 (eqsymm Heqnp)) as (n' & p' & -> & <- & <-).
so (map_steps_form _#5 Hstepsn) as (r & Heqr & Hstepsn').
so (map_eq_btrue_invert _#4 (eqsymm Heqr)); subst r.
so (map_steps_form _#5 Hstepsp) as (t & Heqt & Hstepsp').
so (map_eq_triv_invert _#4 (eqsymm Heqt)); subst t.
eapply natinterp_0; eauto using map_hygiene_conv.
}

(* S *)
{
intros ? n p i Hhyg Hstepsm Hstepsn _ IH m ->.
so (map_steps_form _#5 Hstepsm) as (np & Heqnp & Hstepsm').
so (map_eq_ppair_invert _#6 (eqsymm Heqnp)) as (n' & p' & -> & <- & <-).
so (map_steps_form _#5 Hstepsn) as (r & Heqr & Hstepsn').
so (map_eq_bfalse_invert _#4 (eqsymm Heqr)); subst r.
eapply natinterp_S; eauto using map_hygiene_conv.
}
Qed.


Lemma nattp_nat_urel :
  forall w i,
    w <<= stop
    -> den (nattp_def w i) = nat_urel i.
Proof.
intros w i Hw.
apply urel_extensionality.
fextensionality 3.
intros j m p.
pextensionality.
  {
  intros Hmp.
  cut (incl (den (nattp_def w i)) (nat_urel i)).
    {
    intro Hincl.
    unfold nattp_def in Hincl.
    rewrite -> den_iubase in Hincl.
    apply Hincl.
    exact Hmp.
    }
  clear j m p Hmp.
  unfold nattp_def in *.
  rewrite -> den_iubase.
  rewrite -> extend_mu; auto.
  2:{
    apply nattp_body_mono.
    }
  apply mu_least.
  unfold nattp_body.
  rewrite <- (den_extend_iurel _ _ Hw).
  rewrite -> extend_sumtp.
  rewrite -> !extend_iubase.
  rewrite -> extend_unit; auto.
  intros j m p Hmp.
  destruct Hmp as (m1 & p1 & m2 & p2 & Hmp1 & Hclm & Hclp & Hstepsm & Hstepsp & Hmp2).
  cbn in Hmp2.
  destruct Hmp2 as [(Htrue & Hmp2) | (Hfalse & Hmp2)].
    {
    cbn in Htrue.
    destruct Htrue as (_ & _ & _ & _ & [(Htrue & Hstepsp1) | (Hcontra & _)]).
    2:{
      so (determinism_eval _#4 (conj (star_refl _) value_btrue) (conj Hcontra value_bfalse)) as H.
      discriminate H.
      }
    destruct Hmp2 as (_ & Hj & _ & _ & Hstepsm2 & Hstepsp2).
    exists 0.
    do2 2 split; auto.
      {
      eapply natinterp_0; eauto.
      apply (bool_eval_iff_true _#5 Hmp1); auto.
      }

      {
      eapply natinterp_0; eauto.
      }
    }

    {
    cbn in Hfalse.
    destruct Hfalse as (_ & _ & _ & _ & [(Hcontra & _) | (Hfalse & Hstepsp1)]).
      {
      so (determinism_eval _#4 (conj (star_refl _) value_bfalse) (conj Hcontra value_btrue)) as H.
      discriminate H.
      }
    destruct Hmp2 as (_ & Hmp2).
    destruct Hmp2 as (n & Hj & Hm2 & Hp2).
    exists (S n).
    do2 2 split; auto.
      {
      eapply natinterp_S; eauto.
      apply (bool_eval_iff_false _#5 Hmp1); auto.
      rewrite -> map_term_compose in Hm2.
      eapply map_natinterp_conv; eauto.
      }

      {
      eapply natinterp_S; eauto.
      rewrite -> map_term_compose in Hp2.
      eapply map_natinterp_conv; eauto.
      }
    }
  }

  {
  intros Hmp.
  so (nattp_body_mono w i) as Hmono.
  unfold nattp_def.
  rewrite -> den_iubase.
  cbn [rel extend_urel].
  unfold nattp_body.
  destruct Hmp as (k & Hj & Hm & Hp).
  revert p Hp.
  induct Hm.
    (* 0 *)
    {
    intros m m1 m2 Hclm Hstepsm Hstepsm1 Hstepsm2 p Hp.
    invertc Hp.
    intros p1 p2 Hclp Hstepsp Hstepsp1 Hstepsp2.
    rewrite -> mu_fix; auto.
    so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsm Hclm)) as H; cbn in H.
    destruct H as (Hclm1 & Hclm2 & _).
    so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsp Hclp)) as H; cbn in H.
    destruct H as (Hclp1 & Hclp2 & _).
    so (map_steps _ _ (extend stop w) _ _ Hstepsm) as Hstepsm'.
    simpmapin Hstepsm'.
    so (map_steps _ _ (extend stop w) _ _ Hstepsp) as Hstepsp'.
    simpmapin Hstepsp'.
    so (map_steps _ _ (extend stop w) _ _ Hstepsm1) as Hstepsm1'.
    simpmapin Hstepsm1'.
    so (map_steps _ _ (extend stop w) _ _ Hstepsp1) as Hstepsp1'.
    simpmapin Hstepsp1'.
    so (map_steps _ _ (extend stop w) _ _ Hstepsm2) as Hstepsm2'.
    simpmapin Hstepsm2'.
    so (map_steps _ _ (extend stop w) _ _ Hstepsp2) as Hstepsp2'.
    simpmapin Hstepsp2'.
    assert (rel (bool_urel w i) j (map_term (extend stop w) m1) (map_term (extend stop w) p1)) as Hmp1.
      {
      do2 3 split; auto; try prove_hygiene.
      }
    exists (map_term (extend stop w) m1), (map_term (extend stop w) p1), (map_term (extend stop w) m2), (map_term (extend stop w) p2), Hmp1.
    do2 4 split; auto; try prove_hygiene.
    left.
    split.
      {
      cbn.
      split; auto.
      do2 3 split; auto; try prove_hygiene.
      left; split; auto.
      apply star_refl.
      }

      {
      do2 4 split; auto; try prove_hygiene.
      }
    }

    (* S *)
    {
    intros m m1 m2 k Hclm Hstepsm Hstepsm1 _ IH p Hp.
    invertc Hp.
    intros p1 p2 Hclp Hstepsp Hstepsp1 Hstepsp2.
    so (IH _ Hstepsp2) as Hmp2.
    rewrite -> mu_fix; auto.
    so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsm Hclm)) as H; cbn in H.
    destruct H as (Hclm1 & Hclm2 & _).
    so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsp Hclp)) as H; cbn in H.
    destruct H as (Hclp1 & Hclp2 & _).

    so (map_steps _ _ (extend stop w) _ _ Hstepsm) as Hstepsm'.
    simpmapin Hstepsm'.
    so (map_steps _ _ (extend stop w) _ _ Hstepsp) as Hstepsp'.
    simpmapin Hstepsp'.
    so (map_steps _ _ (extend stop w) _ _ Hstepsm1) as Hstepsm1'.
    simpmapin Hstepsm1'.
    so (map_steps _ _ (extend stop w) _ _ Hstepsp1) as Hstepsp1'.
    simpmapin Hstepsp1'.
    assert (rel (bool_urel w i) j (map_term (extend stop w) m1) (map_term (extend stop w) p1)) as Hmp1.
      {
      do2 3 split; auto; try prove_hygiene.
      }
    exists (map_term (extend stop w) m1), (map_term (extend stop w) p1), (map_term (extend stop w) m2), (map_term (extend stop w) p2), Hmp1.
    do2 4 split; auto; try prove_hygiene.
    right.
    split.
      {
      cbn.
      split; auto.
      do2 3 split; auto; try prove_hygiene.
      right; split; auto.
      apply star_refl.
      }

      {
      split; [omega |].
      apply IH; auto.
      }
    }
  }
Qed.


Lemma interp_nattp_invert :
  forall pg s i A j m n,
    interp pg s i nattp A
    -> rel (den A) j m n
    -> exists k,
         natinterp m k
         /\ natinterp n k.
Proof.
intros pg s i A j m n Hint Hmn.
so (basic_fun _#7 Hint (interp_nattp pg s i)); subst A.
rewrite -> nattp_nat_urel in Hmn; auto using cin_stop.
destruct Hmn as (k & _ & Hm & Hn).
eauto.
Qed.


Lemma interp_pagetp_invert :
  forall pg s i A j m n,
    interp pg s i pagetp A
    -> rel (den A) j m n
    -> exists pg',
         pginterp m pg'
         /\ pginterp n pg'.
Proof.
intros pg s i A j m n Hint Hmn.
so (interp_nattp_invert _#7 Hint Hmn) as (k & Hm & Hn).
set (pg' := mk_page (fin k) (fin k) (fin k) (le_ord_trans _#3 (le_fin_omega _ _) omega_top) (le_ord_trans _#3 (le_fin_omega _ _) omega_top) (le_ord_refl _)).
exists pg'.
split.
  {
  exists (fin k).
  do2 3 split; auto.
  exists k; auto.
  }

  {
  exists (fin k).
  do2 3 split; auto.
  exists k; auto.
  }
Qed.


Lemma app_leqtp_equiv :
  forall object (m b p b' n c q c' : @term object),
    star step m (ppair b p)
    -> star step n (ppair c q)
    -> star step b b'
    -> star step c c'
    -> equiv
         (app (app leqtp m) n)
         (bite b' unittp
            (bite c' voidtp
               (app (app leqtp p) q))).
Proof.
intros object m b p b' n c q c' Hm Hn Hb Hc.
eapply equiv_trans.
  {
  apply equiv_app; [| apply equiv_refl].
  eapply equiv_trans.
    {
    eapply equiv_trans.
      {
      apply equiv_app; [| apply equiv_refl].
      eapply equiv_trans.
        {
        apply steps_equiv.
        apply theta_fix.
        }
      fold (@leqtp object).
      apply steps_equiv.
      apply star_one.
      apply step_app2.
      }
    simpsub.
    cbn [Nat.add].
    apply steps_equiv.
    apply star_one.
    apply step_app2.
    }
  simpsub.
  cbn [Nat.add].
  apply equiv_refl.
  }
eapply equiv_trans.
  {
  apply steps_equiv.
  apply star_one.
  apply step_app2.
  }
simpsub.
cbn [Nat.add].
unfold sumcase.
apply equiv_bite.
  {
  eapply equiv_trans.
    {
    apply equiv_ppi1.
    apply steps_equiv; eauto.
    }
  apply steps_equiv.
  eapply star_step.
    {
    apply step_ppi12.
    }
  auto.
  }

  {
  simpsub.
  apply equiv_refl.
  }
simpsub.
apply equiv_bite.
  {
  eapply equiv_trans.
    {
    apply equiv_ppi1.
    apply steps_equiv; eauto.
    }
  apply steps_equiv.
    {
    eapply star_step.
      {
      apply step_ppi12.
      }
    auto.
    }
  }

  {
  apply equiv_refl.
  }
apply equiv_app.
  {
  apply equiv_app.
    {
    apply equiv_refl.
    }

    {
    eapply equiv_trans.
      {
      apply equiv_ppi2.
      apply steps_equiv; eauto.
      }
    apply steps_equiv.
    apply star_one.
    apply step_ppi22.
    }
  }

  {
  eapply equiv_trans.
    {
    apply equiv_ppi2.
    apply steps_equiv; eauto.
    }
  apply steps_equiv.
  apply star_one.
  apply step_ppi22.
  }
Qed.


Lemma leqtp_false_equiv :
  forall m n i j,
    natinterp m i
    -> natinterp n j
    -> j < i
    -> equiv (app (app leqtp m) n) voidtp.
Proof.
intros m n i j Hm Hn Hlt.
revert n j Hn Hlt.
induct Hm.

(* 0 *)
{
intros m _ _ _ _ _ _ n j _ Hlt.
omega.
}

(* S *)
{
intros m b p i Hclm Hstepsm Hstepsb _ IH n jj Hn Hlt.
invertc Hn.
  (* n = 0 *)
  {
  intros c q _ Hstepsn Hstepsc _ <-.
  eapply equiv_trans.
    {
    eapply app_leqtp_equiv; eauto.
    }
  eapply equiv_trans.
    {
    apply steps_equiv.
    apply star_one.
    apply step_bite3.
    }
  eapply equiv_trans.
    {
    apply steps_equiv.
    apply star_one.
    apply step_bite2.
    }
  apply equiv_refl.
  }

  (* n > 0 *)
  {
  intros c q j Hcln Hstepsn Hstepsc Hc <-.
  eapply equiv_trans.
    {
    eapply app_leqtp_equiv; eauto.
    }
  eapply equiv_trans.
    {
    apply steps_equiv.
    apply star_one.
    apply step_bite3.
    }
  eapply equiv_trans.
    {
    apply steps_equiv.
    apply star_one.
    apply step_bite3.
    }
  eapply IH; eauto.
  omega.
  }
}
Qed.


Lemma interp_leqtp_invert :
  forall pg s i m n A j p q k k',
    interp pg s i (app (app leqtp m) n) A
    -> rel (den A) j p q
    -> natinterp m k
    -> natinterp n k'
    -> k <= k'.
Proof.
intros pg s i m n A j p q k k' Hint Hpq Hm Hn.
so (le_lt_dec k k') as [| Hlt]; auto.
exfalso.
so (leqtp_false_equiv _#4 Hm Hn Hlt) as Hequiv.
eassert _ as Hint'; [refine (basic_equiv _#7 _ Hequiv Hint) |].
  {
  apply hygiene_auto; cbn; auto.
  }
so (basic_fun _#7 Hint' (interp_eval_refl _#6 (interp_void _#4))); subst A.
cbn in Hpq.
destruct Hpq.
Qed.


Lemma interp_lttp_invert :
  forall pg s i m n A j p q k k',
    interp pg s i (app (app lttp m) n) A
    -> rel (den A) j p q
    -> natinterp m k
    -> natinterp n k'
    -> k < k'.
Proof.
intros pg s i m n A j p q k k' Hint Hpq Hm Hn.
so (le_lt_dec (S k) k') as [| Hlt]; auto.
exfalso.
so (natinterp_nsucc _ _ Hm) as Hm'.
so (leqtp_false_equiv _#4 Hm' Hn Hlt) as Hequiv.
eassert _ as Hint'; [refine (basic_equiv _#5 voidtp _ _ _ Hint) |].
  {
  apply hygiene_auto; cbn; auto.
  }

  {
  eapply equiv_trans; eauto.
  apply equiv_app; [| apply equiv_refl].
  unfold lttp.
  eapply steps_equiv.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
so (basic_fun _#7 Hint' (interp_eval_refl _#6 (interp_void _#4))); subst A.
cbn in Hpq.
destruct Hpq.
Qed.


Lemma interp_leqpagetp_invert :
  forall pg s i lv1 lv2 A j m n pg1 pg2,
    interp pg s i (leqpagetp lv1 lv2) A
    -> rel (den A) j m n
    -> pginterp lv1 pg1
    -> pginterp lv2 pg2
    -> le_page pg1 pg2.
Proof.
intros pg s i lv1 lv2 A j m n pg1 pg2 Hint Hmn Hlv1 Hlv2.
destruct pg1 as [str1 cex1 cin1].
destruct pg2 as [str2 cex2 cin2].
unfold le_page; cbn.
destruct Hlv1 as (w1 & Hlv1 & H).
cbn in H.
destruct H as (-> & -> & ->).
destruct Hlv2 as (w2 & Hlv2 & H).
cbn in H.
destruct H as (-> & -> & ->).
destruct Hlv1 as (k1 & Hk1 & ->).
destruct Hlv2 as (k2 & Hk2 & ->).
unfold leqpagetp in Hint.
so (interp_leqtp_invert _#11 Hint Hmn Hk1 Hk2) as Hle.
do2 2 split; apply le_fin; auto.
Qed.


Lemma interp_ltpagetp_invert :
  forall pg s i lv1 lv2 A j m n pg1 pg2,
    interp pg s i (ltpagetp lv1 lv2) A
    -> rel (den A) j m n
    -> pginterp lv1 pg1
    -> pginterp lv2 pg2
    -> lt_page pg1 pg2.
Proof.
intros pg s i lv1 lv2 A j m n pg1 pg2 Hint Hmn Hlv1 Hlv2.
destruct pg1 as [str1 cex1 cin1].
destruct pg2 as [str2 cex2 cin2].
unfold lt_page; cbn.
destruct Hlv1 as (w1 & Hlv1 & H).
cbn in H.
destruct H as (-> & -> & ->).
destruct Hlv2 as (w2 & Hlv2 & H).
cbn in H.
destruct H as (-> & -> & ->).
destruct Hlv1 as (k1 & Hk1 & ->).
destruct Hlv2 as (k2 & Hk2 & ->).
unfold ltpagetp in Hint.
so (interp_lttp_invert _#11 Hint Hmn Hk1 Hk2) as Hlt.
split; apply le_fin; auto.
Qed.


Lemma seq_pagetp_invert :
  forall G lv,
    (forall i t t',
       pwctx i t t' G
       -> exists pg R,
            interp pg true i (subst t pagetp) R
            /\ rel (den R) i (subst t lv) (subst t' lv))
    -> forall i s s',
         pwctx i s s' G
         -> exists pg,
              pginterp (subst s lv) pg
              /\ pginterp (subst s' lv) pg.
Proof.
intros G lv Hseq i s s' Hs.
so (Hseq _#3 Hs) as (pg & R & HR & Hlv).
exact (interp_pagetp_invert _#7 HR Hlv).
Qed.


Lemma seq_leqpagetp_invert :
  forall G lv lv' m,
    (forall i t t',
       pwctx i t t' G
       -> exists pg R,
            interp pg true i (subst t (leqpagetp lv lv')) R
            /\ rel (den R) i (subst t m) (subst t' m))
    -> forall i s s' pg pg',
         pwctx i s s' G
         -> pginterp (subst s lv) pg
         -> pginterp (subst s lv') pg'
         -> le_page pg pg'.
Proof.
intros G lv lv' m Hseq i s s' pg pg' Hs Hlv Hlv'.
so (Hseq _#3 Hs) as (pg'' & R & HR & Hm).
exact (interp_leqpagetp_invert _#11 HR Hm Hlv Hlv').
Qed.


Lemma seq_ltpagetp_invert :
  forall G lv lv' m,
    (forall i t t',
       pwctx i t t' G
       -> exists pg R,
            interp pg true i (subst t (ltpagetp lv lv')) R
            /\ rel (den R) i (subst t m) (subst t' m))
    -> forall i s s' pg pg',
         pwctx i s s' G
         -> pginterp (subst s lv) pg
         -> pginterp (subst s lv') pg'
         -> lt_page pg pg'.
Proof.
intros G lv lv' m Hseq i s s' pg pg' Hs Hlv Hlv'.
so (Hseq _#3 Hs) as (pg'' & R & HR & Hm).
exact (interp_ltpagetp_invert _#11 HR Hm Hlv Hlv').
Qed.


Lemma interp_nonsense :
  forall system pg s i,
    basicv system pg s i nonsense
      (iuguard stop i 
         (iubase (void_urel stop))
         (nearrow_const _ (iurel_ofe _) (iubase (void_urel stop)))).
Proof.
intros system pg s i.
apply interp_guard.
  {
  apply interp_eval_refl.
  apply interp_void.
  }

  {
  apply functional_i.
    {
    prove_hygiene.
    }

    {
    rewrite -> ceiling_squash.
    rewrite -> Nat.min_l; auto.
    }

    {
    intros j m p Hj Hmp.
    simpsub.
    cbn.
    apply interp_eval_refl.
    apply interp_void.
    }
  }
Qed.
