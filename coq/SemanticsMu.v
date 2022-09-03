
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
Require Import Standard.
Require Import Equivalences.
Require Import ExtendTruncate.
Require Import Page.
Require Import Lattice.
Require Import Reduction.
Require Import Standardization.


Definition irelation (T : Type) := nat -> T -> T -> Prop.


Definition incl {object} (A B : urel object) : Prop :=
  forall i m p, rel A i m p -> rel B i m p.


Lemma incl_refl :
  forall object (A : urel object),
    incl A A.
Proof.
intros T A.
intros i m p Hmp.
auto.
Qed.


Lemma incl_trans :
  forall object (A B C : urel object),
    incl A B
    -> incl B C
    -> incl A C.
Proof.
intros T A B C HAB HBC.
intros i m p Hmp.
auto.
Qed.


Lemma incl_antisymm :
  forall object (A B : urel object),
    incl A B
    -> incl B A
    -> A = B.
Proof.
intros object A B HAB HBA.
apply urel_extensionality.
fextensionality 3.
intros i m p.
pextensionality; auto.
Qed.


Definition monotone {object} (F : urel object -> urel object)
  : Prop
  :=
  impl incl incl F.


Definition top_action {object} (i : nat) (m p : term object) := hygiene clo m /\ hygiene clo p.


Lemma top_uniform : 
  forall object, uniform object top_action.
Proof.
unfold top_action.
intros object.
do2 3 split; auto.
(* zigzag *)
intros _ m _ _ q (Hclm & _) _ (_ & Hclq).
auto.
Qed.


Definition top_urel {object} : urel object
  :=
  mk_urel _ (top_uniform object).



Definition mu_action (w : ordinal) (F : wurel w -> wurel w)
  : irelation (wterm w)
  :=
  fun i m p =>
    forall R,
      incl (F R) R
      -> rel R i m p.


Lemma mu_uniform :
  forall w F,
    uniform _ (mu_action w F).
Proof.
intros w F.
do2 3 split.

(* closed *)
{
intros i m p Hmp.
exploit (Hmp top_urel) as H.
  {
  intros j n q Hnq.
  exact (urel_closed _#5 Hnq).
  }
exact H.
}

(* equiv *)
{
intros i m m' n n' Hclm' Hcln' Hequivm Hequivn Hmn.
intros R HR.
eapply urel_equiv; eauto.
}

(* zigzag *)
{
intros i m n p q Hmn Hpn Hpq.
intros R HR.
apply (urel_zigzag _ _ _ m n p q); auto.
}

(* downward *)
{
intros i m n Hmn.
intros R HR.
apply urel_downward; auto.
}
Qed.


Definition mu_urel (w : ordinal) (F : wurel w -> wurel w) : wurel w :=
  mk_urel (mu_action w F) (mu_uniform w F).


Lemma mu_least :
  forall w F R,
    incl (F R) R
    -> incl (mu_urel w F) R.
Proof.
intros w F R Huincl.
intros i m p Hmp.
apply Hmp; auto.
Qed.


Lemma mu_prefix :
  forall w F,
    monotone F
    -> incl (F (mu_urel w F)) (mu_urel w F).
Proof.
intros w F Hmono.
intros i m n Hmn.
intros R HR.
so (incl_trans _#4 (Hmono _ _ (mu_least w _ _ HR)) HR) as H.
apply H; auto.
Qed.


Lemma mu_postfix :
  forall w F,
    monotone F
    -> incl (mu_urel w F) (F (mu_urel w F)).
Proof.
intros w F Hmono.
intros i m p Hmp.
apply Hmp.
apply Hmono.
apply mu_prefix; auto.
Qed.


Lemma mu_fix :
  forall w F,
    monotone F
    -> mu_urel w F = F (mu_urel w F).
Proof.
intros w F Hmono.
apply incl_antisymm; auto using mu_prefix, mu_postfix.
Qed.


Lemma mu_action_intro :
  forall w F i m p,
    monotone F
    -> rel (F (mu_urel w F)) i m p
    -> mu_action w F i m p.
Proof.
intros w F i m p Hmono Hmp.
rewrite <- mu_fix in Hmp; auto.
Qed.


Lemma mu_action_ind :
  forall w (F : wurel w -> wurel w) (A : wurel w),
    monotone F
    -> (forall i m p,
          rel (F (mu_urel w F)) i m p
          -> rel (F A) i m p
          -> rel A i m p)
    -> forall i m p, mu_action w F i m p -> rel A i m p.
Proof.
intros w F A Hmono Hind.
set (Bf := fun i m p => rel (mu_urel w F) i m p /\ rel A i m p).
assert (uniform _ Bf) as Huniform.
  {
  do2 3 split.
    {
    intros i m p Hmp.
    exact (urel_closed _#5 (Hmp ander)).
    }

    {
    intros i m m' p p' Hclm' Hclp' Hequivm Hequivp Hmp.
    destruct Hmp.
    split; eauto using urel_equiv.
    }

    {
    intros i m n p q Hmn Hpn Hpq.
    destruct Hmn; destruct Hpn; destruct Hpq.
    split; eauto using urel_zigzag.
    }

    {
    intros i m p Hmp.
    destruct Hmp; split; eauto using urel_downward.
    }
  }
set (B := mk_urel Bf Huniform).
assert (incl B (mu_urel w F)) as HB.
  {
  intros i m p Hmp.
  cbn in Hmp.
  destruct Hmp; auto.
  }
intros i m p Hmp.
cut (Bf i m p).
  {
  intros (_ & H).
  auto.
  }
exploit (Hmp B) as H; auto.
clear i m p Hmp.
intros i m p Hmp.
cbn.
split.
  {
  apply mu_action_intro; auto.
  exact (Hmono _ _ HB _ _ _ Hmp).
  }

  {
  apply Hind.
    {
    exact (Hmono _ _ HB _ _ _ Hmp).
    }

    {
    refine (Hmono _ _ _ _ _ _ Hmp).
    clear i m p Hmp.
    intros i m p Hmp.
    destruct Hmp; auto.
    }
  }
Qed.



(* So far, so good.  Next we need to show that mu_urelf is nonexpansive.  Unfortunately,
   that is not so obvious.  The problem is containment talks about *all* indices,
   so it doesn't give us any leverage on particular indices.  So we define another
   version of mu that does, and then prove they are equivalent.
*)

Definition muc_action (w : ordinal) (F : car (wurel_ofe w) -> car (wurel_ofe w))
  : nat -> relation (wterm w)
  :=
  fun i m m' =>
    (* The ceiling business gives a handle on step indices,  but alas is MUCH messier
       to work with, especially in muc_prefix (which is almost a one-liner for mu).

       Quantifying over j makes the downward property work and doesn't really cause
       any problems.
    *)
    forall j R,
      j <= i
      -> incl (ceiling (S j) (F R)) R
      -> rel R j m m'.


Lemma muc_uniform :
  forall w F,
    uniform _ (muc_action w F).
Proof.
intros w F.
do2 3 split.

(* closed *)
{
intros i m p Hmp.
exploit (Hmp i top_urel) as H; auto.
intros j n q Hnq.
exact (urel_closed _#5 Hnq).
}

(* equiv *)
{
intros i m m' n n' Hclm' Hcln' Hequivm Hequivn Hmn.
intros j R Hj HR.
eapply urel_equiv; eauto.
}

(* zigzag *)
{
intros i m n p q Hmn Hpn Hpq.
intros j R Hj HR.
apply (urel_zigzag _ _ _ m n p q); auto.
}

(* downward *)
{
intros i m n Hmn.
intros j R Hj HR.
apply Hmn; auto.
}
Qed.


Definition muc_urel (w : ordinal) (F : wurel w -> wurel w) : wurel w :=
  mk_urel (muc_action w F) (muc_uniform w F).


Lemma muc_least :
  forall w F R,
    incl (F R) R
    -> incl (muc_urel w F) R.
Proof.
intros w F R Hincl.
intros i m p Hmp.
apply Hmp; auto.
intros k q r Hqr.
destruct Hqr as (_ & Hqr).
apply Hincl; auto.
Qed.


(* Compare to the proof of mu_prefix, which is almost a one-liner. *)
Lemma muc_prefix :
  forall w (F : car (wurel_ofe w) -> car (wurel_ofe w)),
    monotone F
    -> nonexpansive F
    -> incl (F (muc_urel w F)) (muc_urel w F).
Proof.
intros w F Hmono Hne.
intros i m n Hmn.
intros j R Hj HR.
assert (ceiling (S j) (F (ceiling (S j) R)) = ceiling (S j) (F R)) as Heq.
  {
  apply ceiling_collapse.
  apply Hne.
  apply ceiling_near.
  }
assert (incl ((fun A => ceiling (S j) (F A)) (ceiling (S j) R)) (ceiling (S j) R)) as HR'.
  {
  rewrite -> Heq.
  rewrite <- ceiling_idem.
  intros k p q (Hk & Hpq).
  split; auto.
  }
lapply (HR' j m n).
  {
  intro H; destruct H; auto.
  }
split; auto.
so (Hmono _ _ (muc_least _#3 HR')) as H.
apply H; clear H.
cut (@dist (wurel_ofe w) (S j) (F (muc_urel w (fun A => ceiling (S j) (F A)))) (F (muc_urel w F))).
  {
  intro Hdist.
  rewrite -> Hdist; auto.
  eapply urel_downward_leq; eauto.
  }
clear m n Hmn.
apply Hne.
intros k Hk.
fextensionality 2.
intros m n.
pextensionality.
  {
  intros H l Q Hl HQ.
  apply H; auto.
  rewrite -> ceiling_combine_le; auto.
  omega.
  }

  {
  intros H l Q Hl HQ.
  apply H; auto.
  rewrite -> ceiling_combine_le in HQ; auto.
  omega.
  }
Qed.


Lemma mu_is_muc :
  forall w (F : car (wurel_ofe w) -> car (wurel_ofe w)),
    monotone F
    -> nonexpansive F
    -> mu_urel w F = muc_urel w F.
Proof.
intros w F Hmono Hne.
apply urel_extensionality.
fextensionality 3.
intros i m p.
pextensionality.
  {
  intro Hmu.
  refine (mu_least _#3 _ _ _ _ Hmu).
  apply muc_prefix; auto.
  }

  {
  intro Hmuc.
  refine (muc_least _#3 _ _ _ _ Hmuc).
  apply mu_prefix; auto.
  }
Qed.


Lemma mu_nonexpansive :
  forall w (F G : car (wurel_ofe w) -> car (wurel_ofe w)) i,
    nonexpansive F
    -> nonexpansive G
    -> monotone F
    -> monotone G
    -> (forall R, dist i (F R) (G R))
    -> @dist (wurel_ofe w) i (mu_urel w F) (mu_urel w G).
Proof.
intros w F G i HneF HneG HmonoF HmonoG Hdist.
revert F G HneF HneG HmonoF HmonoG Hdist.
cut (forall (F G : car (wurel_ofe w) -> car (wurel_ofe w)) j m p,
       nonexpansive F
       -> nonexpansive G
       -> monotone F
       -> monotone G
       -> (forall R, dist i (F R) (G R))
       -> j < i
       -> rel (mu_urel w F) j m p
       -> rel (mu_urel w G) j m p).
  {
  intros Hprop F G HneF HneG HmonoF HmonoG Hdist.
  cbn.
  intros j Hj.
  fextensionality 2.
  intros m p.
  pextensionality.
    {
    intro H.
    apply (Hprop F G); eauto.
    }

    {
    intro H.
    apply (Hprop G F); eauto.
    intro R.
    apply dist_symm; auto.
    }
  }
intros F G j m p HneF HneG HmonoF HmonoG Hdist Hj Hmp.
rewrite -> mu_is_muc in Hmp |- *; auto.
intros k R Hk HR.
apply Hmp; auto.
clear m p Hmp.
intros l m p Hmp.
apply HR.
force_exact Hmp.
f_equal.
apply ceiling_collapse.
apply (dist_downward_leq _ _ i); auto.
omega.
Qed.


Lemma monotone_ceiling :
  forall w i,
    @monotone (obj w) (ceiling i).
Proof.
intros w i.
intros A B HAB.
intros j m p Hmp.
destruct Hmp as (Hj & Hmp).
split; auto.
Qed.


Lemma ceiling_mu :
  forall n w (F : car (wurel_ofe w) -> car (wurel_ofe w)),
    monotone F
    -> nonexpansive F
    -> ceiling (S n) (mu_urel w F)
       =
       mu_urel w (fun A => ceiling (S n) (F A)).
Proof.
intros n w F Hmono Hne.
so (impl_compose _#8 Hmono (monotone_ceiling _ (S n))) as Hmono'.
setoid_rewrite -> mu_fix at 1 2; auto.
apply ceiling_collapse.
apply Hne.
apply mu_nonexpansive; auto.
  {
  apply compose_ne_ne; auto.
  apply ceiling_nonexpansive.
  }
intro R.
apply dist_symm.
apply ceiling_near.
Qed.


Lemma extend_mu :
  forall v w (h : v <<= w) (F : wurel v -> wurel v),
    monotone F
    -> extend_urel v w (mu_urel v F)
       =
       mu_urel w (fun R => extend_urel v w (F (extend_urel w v R))).
Proof.
intros v w h F Hmono.
assert (monotone (fun R => extend_urel v w (F (extend_urel w v R)))) as Hmono'.
  {
  intros A B HAB.
  intros i m p Hmp.
  cbn in Hmp |- *.
  refine (Hmono (extend_urel w v A) (extend_urel w v B) _ i _ _ Hmp).
  clear i m p Hmp.
  intros i m p Hmp.
  cbn in Hmp |- *.
  apply HAB; auto.
  }
cut (incl
       (extend_urel v w (mu_urel v F))
       (mu_urel w (fun R => extend_urel v w (F (extend_urel w v R))))
     /\
     incl
       (mu_urel w (fun R => extend_urel v w (F (extend_urel w v R))))
       (extend_urel v w (mu_urel v F))).
  {
  intros (H1 & H2).
  apply urel_extensionality.
  fextensionality 3.
  intros i m p.
  pextensionality; auto.
  }
split.
  {
  intros i m p Hmp.
  cbn in Hmp.
  (* we want to replace the m in the conclusion with 
     (map_term (extend v w) (map_term (extend w v) m)) (and likewise for p)
     but those aren't equivalent, so we need to use the fact that the relation
     is extended from v to w.  That, however, involves unrolling the fixpoint,
     fiddling with the terms, and then rerolling the fixpoint.
  *)
  rewrite -> mu_fix; auto.
  cbn.
  rewrite <- (extend_term_cancel _ _ h (map_term (extend w v) m)).
  rewrite <- (extend_term_cancel _ _ h (map_term (extend w v) p)).
  (* reroll it, but Coq can't seem to handle the inference *)
  cut (rel (mu_urel w (fun R => extend_urel v w (F (extend_urel w v R))))
         i
         (map_term (extend v w) (map_term (extend w v) m))
         (map_term (extend v w) (map_term (extend w v) p))).
    {
    intro H.
    rewrite -> mu_fix in H; auto.
    }
  apply (mu_action_ind v F (extend_urel w v (mu_urel w (fun R => extend_urel v w (F (extend_urel w v R)))))); auto.
  clear i m p Hmp.
  intros i m p Hmp IH.
  rewrite -> mu_fix; auto.
  cbn.
  rewrite -> !extend_term_cancel; auto.
  }

  {
  intros i m p Hmp.
  apply (mu_action_ind w (fun R => extend_urel v w (F (extend_urel w v R))) (extend_urel v w (mu_urel v F))); auto.
  clear i m p Hmp.
  intros i m p Hmp IH.
  rewrite <- extend_urel_compose_up in IH; auto.
  rewrite -> extend_urel_id in IH.
  rewrite <- mu_fix in IH; auto.
  }
Qed.


(* Finally we need the blur_vanish lemma, which requires a bunch of development
   and the vanish lemma.
*)


(* If P is a chain, we can compute its join as a union. *)

Definition join_action {object} (P : urel object -> Prop) : irelation (term object)
  :=
  fun i m p =>
    exists R,
      P R
      /\ rel R i m p.


Lemma join_uniform :
  forall object P,
    is_chain incl P
    -> uniform object (join_action P).
Proof.
intros object P Hchain.
do2 3 split.

(* closed *)
{
intros i m p Hmp.
destruct Hmp as (R & _ & Hmp).
eapply urel_closed; eauto.
}

(* equal *)
{
intros i m m' p p' Hclom' Hclop' Hm Hp Hmp.
destruct Hmp as (R & HR & Hmp).
exists R.
split; auto.
eapply urel_equiv; eauto.
}

(* zigzag *)
{
intros i m n p q Hmn Hpn Hpq.
destruct Hmn as (R1 & HR1 & Hmn).
destruct Hpn as (R2 & HR2 & Hpn).
destruct Hpq as (R3 & HR3 & Hpq).
(* Here is the key place where we use the fact that P is a chain. *)
assert (exists R, P R /\ incl R1 R /\ incl R2 R /\ incl R3 R) as (R & HR & Hincl1 & Hincl2 & Hincl3).
  {
  so (Hchain _ _ HR1 HR2) as [H12 | H21].
    {
    so (Hchain _ _ HR2 HR3) as [H23 | H32].
      {
      exists R3.
      eauto using incl_refl, incl_trans.
      }

      {
      exists R2.
      eauto using incl_refl, incl_trans.
      }
    }

    {
    so (Hchain _ _ HR1 HR3) as [H13 | H31].
      {
      exists R3.
      eauto using incl_refl, incl_trans.
      }

      {
      exists R1.
      eauto using incl_refl, incl_trans.
      }
    }
  }
exists R.
split; auto.
apply (urel_zigzag _ _ _ m n p q); eauto.
}

(* downward *)
{
intros i m p Hmp.
destruct Hmp as (R & HR & Hmp).
exists R.
split; auto.
apply urel_downward; auto.
}
Qed.


Definition join_urel {object} (P : urel object -> Prop) (h : is_chain incl P) : urel object
  :=
  mk_urel _ (join_uniform object P h).


Definition wurel_ccp (w : ordinal) : ccp.
Proof.
refine (mk_lat
          (wurel w) 
          incl
          join_urel
          _ _ _ _ _).

(* refl *)
{
intro R.
apply incl_refl.
}

(* trans *)
{
intros A B C HAB HBC.
eapply incl_trans; eauto.
}

(* antisymm *)
{
intros A B HAB HBA.
apply urel_extensionality.
fextensionality 3.
intros i m p.
pextensionality; auto.             
}

(* join_ub *)
{
intros P Hchain R HR.
intros i m p Hmp.
exists R.
auto.
}

(* join_least *)
{
intros P Hchain R HR.
intros i m p Hmp.
destruct Hmp as (Q & HQ & Hmp).
eapply HR; eauto.
}
Defined.


Definition blur (v w : ordinal) (R : wurel w) : wurel w :=
  extend_urel v w (extend_urel w v R).


Lemma blur_monotone :
  forall v w,
    monotone (blur v w).
Proof.
intros v w.
intros Q R HQR.
intros i m p Hmp.
cbn in Hmp |- *.
apply HQR; auto.
Qed.


Lemma blur_vanish :
  forall v w (G : wurel w -> wurel w),
    monotone G
    -> (forall X, blur v w (G (blur v w X)) = G (blur v w X))
    -> mu_urel w (fun X => G (blur v w X)) = mu_urel w G.
Proof.
intros v w G HmonoG Hequation.
apply (vanish' (wurel_ccp w) (blur v w) G); auto.
  {
  exists (blur_monotone v w).
  intros C Hchain.
  apply incl_antisymm.
  2:{
    intros i m p Hmp.
    destruct Hmp as (R & HR & Hmp).
    destruct HR as (R' & -> & HR).
    cbn in Hmp.
    cbn.
    exists R'.
    split; auto.
    }
  intros i m p Hmp.
  cbn in Hmp.
  destruct Hmp as (R & HR & Hmp).
  exists (blur v w R).
  split; auto.
  exists R; auto.
  }

  {
  apply (mu_prefix _ (fun X => G (blur v w X))).
  eapply impl_compose; eauto.
  apply blur_monotone.
  }

  {
  intros R HR.
  apply mu_least; auto.
  }

  {
  apply mu_prefix; auto.
  }

  {
  intros R HR.
  apply mu_least; auto.
  }
Qed.
