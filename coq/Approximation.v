
Require Import Axioms.

Require Import Tactics.
Require Import Equality.
Require Import Relation.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.
Require Import Dynamic.
Require Import Hygiene.
Require Import Reduction.
Require Import Equivalence.
Require Import Standardization.


Section object.


Arguments operator {object}.
Arguments term {object}.
Arguments row {object}.
Arguments rw_cons {object i a}.


Variable object : Type.


(* closed instances *)
Definition ci (R : relation (@term object)) (m m' : term) : Prop :=
  forall s, hygiene clo (subst s m) -> hygiene clo (subst s m') -> R (subst s m) (subst s m').


(* evaluation closure and compatibility *)
Definition ec (R : relation (@term object)) (m m' : term) : Prop :=
  forall v,
    eval m v
    -> exists v',
         eval m' v'
         /\ mc (ci R) v v'.


(* restrict to closed *)
Definition rc (R : relation (@term object)) (m m' : term) : Prop :=
  hygiene clo m
  /\ hygiene clo m'
  /\ R m m'.


Definition approx (m m' : term) : Prop :=
  exists (R : relation term),
    inclusion _ R (rc (ec R))
    /\ R m m'.


Lemma closed_ci :
  forall R m n,
    hygiene clo m
    -> hygiene clo n
    -> ci R m n
    -> R m n.
Proof.
intros R m n Hclm Hcln H.
so (H id) as H; simpsubin H.
exact (H Hclm Hcln).
Qed.


Lemma ci_from_closed :
  forall (R : relation (@term object)) m n,
    hygiene clo m
    -> hygiene clo n
    -> R m n
    -> ci R m n.
Proof.
intros R m n Hclm Hcln Hmn.
intros s _ _.
rewrite -> !subst_into_closed; auto.
Qed.


Lemma subst_ci :
  forall R s m m',
    ci R m m'
    -> ci R (subst s m) (subst s m').
Proof.
intros R s m m' Hci.
intros s' Hcl Hcl'.
simpsubin Hcl.
simpsubin Hcl'.
simpsub.
exact (Hci _ Hcl Hcl').
Qed.


Lemma ci_mono :
  forall (R R' : relation term),
    inclusion _ R R'
    -> inclusion _ (ci R) (ci R').
Proof.
intros R R' Hincl.
intros m m' Hcim.
intros s Hcl Hcl'.
apply Hincl.
apply Hcim; auto.
Qed.


Lemma ec_mono :
  forall (R R' : relation term),
    inclusion _ R R'
    -> inclusion _ (ec R) (ec R').
Proof.
intros R R' Hincl.
intros m m' Hm.
intros v Heval.
so (Hm v Heval) as (v' & Heval' & Hv).
exists v'.
split; auto.
eapply (mc_mono _ (ci R)); eauto.
apply ci_mono; auto.
Qed.


Lemma rc_mono :
  forall (R R' : relation term),
    inclusion _ R R'
    -> inclusion _ (rc R) (rc R').
Proof.
intros R R' Hincl.
intros m n Hmn.
destruct Hmn as (Hclm & Hcln & Hmn).
do2 2 split; auto.
Qed.


Lemma ci_refl :
  forall (R : relation term),
    reflexive _ R
    -> reflexive _ (ci R).
Proof.
intros R Hrefl.
intros m.
intros s Hcl _.
apply Hrefl.
Qed.


Lemma ec_refl :
  forall (R : relation term),
    reflexive _ R
    -> reflexive _ (ec R).
Proof.
intros R Hrefl m.
intros v Heval.
exists v.
split; auto.
apply mc_refl; auto.
apply ci_refl; auto.
Qed.



Lemma rc_refl :
  forall (R : relation term),
    reflexive _ R
    -> forall m, hygiene clo m -> rc R m m.
Proof.
intros R Hrefl m Hclm.
do2 2 split; auto.
Qed.



Lemma free_variables_term_and_row :
  (forall m, exists i, @hygiene object (fun j => j < i) m)
  /\
  (forall a (r : row a), exists i, @hygiene_row object (fun j => j < i) a r).
Proof.
exploit
  (syntax_ind _
     (fun m => exists i, @hygiene object (fun j => j < i) m)
     (fun a r => exists i, @hygiene_row object (fun j => j < i) a r))
  as Hind.

(* var *)
{
intros n.
exists (S n).
apply hygiene_var.
omega.
}

(* oper *)
{
intros a th r (i & IH).
exists i.
apply hygiene_oper; auto.
}

(* nil *)
{
exists 0.
apply hygiene_nil.
}

(* cons *)
{
intros k a m (i1 & IH1) r (i2 & IH2).
exists (i1 + i2).  (* easier than max *)
apply hygiene_cons.
  {
  eapply hygiene_weaken; eauto.  
  intros x Hx.
  omega.
  }

  {
  eapply hygiene_row_weaken; eauto.
  intros x Hx.
  omega.
  }
}

(* wrapup *)
{
destruct Hind.
split; intros; eauto.
}
Qed.



Lemma free_variables :
  forall m, exists i, @hygiene object (fun j => j < i) m.
Proof.
exact (free_variables_term_and_row andel).
Qed.



Lemma closing_substitution :
  forall m, exists s, @hygiene object clo (subst s m).
Proof.
intro m.
so (free_variables m) as (i & Hhyg).
cut (exists s, @closub object (fun j => j < i) s).
  {
  intros (s & Hs).
  exists s.
  eapply subst_closub; eauto.
  }
clear m Hhyg.
induct i.
  {
  exists id.
  intros j H.
  omega.
  }

  {
  intros i (s & IH).
  exists (dot arb s).
  intros j Hj.
  destruct j as [| j].
    {
    simpsub.
    apply hygiene_auto; cbn.
    split.
    }

    {
    simpsub.
    apply IH.
    omega.
    }
  }
Qed.



(* commutes with composition *)
Definition compositional (Q : relation (@term object) -> relation (@term object)) :=
  forall R1 R2,
    inclusion _ (Relation.compose (Q R1) (Q R2)) (Q (Relation.compose R1 R2)).


Lemma compositional_transitive :
  forall (Q : relation (@term object) -> relation (@term object)) R,
    compositional Q
    -> (forall R R', inclusion _ R R' -> inclusion _ (Q R) (Q R'))
    -> transitive _ R
    -> transitive _ (Q R).
Proof.
intros Q R Hcomp Hmono Htrans.
intros x y z Hxy Hyz.
apply (Hmono (Relation.compose R R)).
  {
  clear x y z Hxy Hyz.
  intros x z Hxz.
  destruct Hxz as (y & Hxy & Hyz).
  eapply Htrans; eauto.
  }
apply Hcomp.
exists y.
auto.
Qed.


Lemma mc_compose : compositional mc.
Proof.
intros R R'.
intros m1 m3 H13.
destruct H13 as (m2 & H12 & H23).
revert m3 H23.
induct H12.

(* var *)
{
intros i m3 H23.
invert H23.
intros <-.
apply mc_var.
}

(* oper *)
{
intros a t r1 r2 H12 m3 H23.
invertc H23.
intros r3 H23 <-.
apply mc_oper; [].
clear t.
revert r3 H23.
induct H12.
  (* nil *)
  {
  intros r3 H23.
  invert H23.
  intros <-.
  apply mcr_nil.
  }

  (* cons *)
  {
  intros i a m1 m2 r1 r2 Hm12 _ IH r H23.
  invert H23.
  intros m3 r3 Hm23 Hr23 <-.
  apply mcr_cons; auto.
  eexists; eauto.
  }
}
Qed.


Lemma ci_compose : compositional ci.
Proof.
intros R1 R2 m1 m3 H13.
destruct H13 as (m2 & H12 & H23).
intros s Hcl1 Hcl3.
so (closing_substitution (subst s m2)) as (t & Hcl2).
simpsubin Hcl2.
exists (subst (compose s t) m2).
split.
  {
  rewrite <- (subst_into_closed _ t (subst s m1)); auto.
  rewrite <- (subst_into_closed _ t (subst s m1)) in Hcl1; auto.
  simpsub.
  simpsubin Hcl1.
  apply H12; auto.
  }

  {
  rewrite <- (subst_into_closed _ t (subst s m3)); auto.
  rewrite <- (subst_into_closed _ t (subst s m3)) in Hcl3; auto.
  simpsub.
  simpsubin Hcl3.
  apply H23; auto.
  }
Qed.


Lemma ci_trans :
  forall (R : relation term),
    transitive _ R
    -> transitive _ (ci R).
Proof.
intros R Htrans.
apply compositional_transitive; auto using ci_compose, ci_mono.
Qed.



Lemma approx_fixpoint :
  rc (ec approx) = approx.
Proof.
assert (inclusion _ approx (rc (ec approx))) as Hincl.
  {
  intros m n Hmn.
  destruct Hmn as (R & Hincl & Hmn).
  apply (rc_mono (ec R) (ec approx)).
  2:{
    apply Hincl; auto.
    }
  clear m n Hmn.
  intros m n Hmn.
  apply (ec_mono R approx); auto.
  clear m n Hmn.
  intros m n Hmn.
  exists R.
  auto.
  }
fextensionality 2.
intros m n.
pextensionality.
  {
  intro Hmn.
  exists (rc (ec approx)).
  split; auto.
  clear m n Hmn.
  intros m n Hmn.
  eapply rc_mono; eauto.
  eapply ec_mono; eauto.
  }

  {
  intros Hmn.
  apply Hincl; auto.
  }
Qed.


Lemma approx_action :
  forall (m p v : @term object),
    approx m p
    -> eval m v
    -> exists w,
         eval p w
         /\ mc (ci approx) v w.
Proof.
intros m p v Hmp Hmv.
rewrite <- approx_fixpoint in Hmp.
destruct Hmp as (_ & _ & Hmp).
so (Hmp v Hmv) as (w & Hpw & Hmc).
eauto.
Qed.



Lemma ci_rc_cancel :
  forall R,
    ci (rc R) = ci R.
Proof.
intro R.
fextensionality 2.
intros m n.
pextensionality.
  {
  intro Hmn.
  intros s Hclsm Hclsn.
  so (Hmn s Hclsm Hclsn) as H.
  destruct H as (_ & _ & H).
  exact H.
  }
  
  {
  intro Hmn.
  intros s Hclsm Hclsn.
  do2 2 split; auto.
  }
Qed.


Lemma ec_rc_cancel :
  forall R,
    ec (rc R) = ec R.
Proof.
intro R.
unfold ec.
rewrite -> ci_rc_cancel.
reflexivity.
Qed.


Lemma approx_closed :
  forall (m n : @term object), approx m n -> hygiene clo m /\ hygiene clo n.
Proof.
intros m n H.
rewrite <- approx_fixpoint in H.
destruct H as (? & ? & _).
auto.
Qed.


Lemma ci_approx_from_approx :
  forall (m n : @term object), approx m n -> ci approx m n.
Proof.
intros m n H.
so (approx_closed _ _ H) as (Hclm & Hcln).
apply ci_from_closed; auto.
Qed.


Lemma approx_refl :
  forall m,
    hygiene clo m
    -> approx m m.
Proof.
intros m Hclm.
exists (rc eq).
split.
2:{
  do2 2 split; auto.
  }
clear m Hclm.
intros m n Hmn.
rewrite -> ec_rc_cancel.
eapply rc_mono; eauto.
clear m n Hmn.
intros m n <-.
apply ec_refl.
unfold reflexive; auto.
Qed.


Lemma ci_approx_refl :
  reflexive _ (ci approx).
Proof.
intro m.
intros s Hcl _.
apply approx_refl; auto.
Qed.


Lemma approx_trans :
  forall m1 m2 m3,
    approx m1 m2
    -> approx m2 m3
    -> approx m1 m3.
Proof.
intros m1 m2 m3 H12 H23.
destruct H12 as (R1 & Hincl1 & H12).
destruct H23 as (R2 & Hincl2 & H23).
exists (Relation.compose R1 R2).
split.
  {
  clear m1 m2 m3 H12 H23.
  intros m1 m3 H13.
  destruct H13 as (m2 & H12 & H23).
  do2 2 split.
    {
    exact (Hincl1 _ _ H12 andel).
    }

    {
    exact (Hincl2 _ _ H23 anderl).
    }
  intros v1 Heval1.
  so (Hincl1 _ _ H12 anderr v1 Heval1) as (v2 & Heval2 & Hv12).
  so (Hincl2 _ _ H23 anderr v2 Heval2) as (v3 & Heval3 & Hv23).
  exists v3.
  split; auto.
  apply (mc_mono _ (Relation.compose (ci R1) (ci R2))).
    {
    apply ci_compose.
    }
  apply mc_compose.
  exists v2.
  auto.
  }

  {
  exists m2.
  auto.
  }
Qed.


Lemma ci_approx_trans :
  forall m1 m2 m3,
    ci approx m1 m2
    -> ci approx m2 m3 
    -> ci approx m1 m3.
Proof.
intros m1 m2 m3 H12 H23.
eapply ci_trans; eauto.
exact approx_trans.
Qed.


Lemma step_approx :
  forall m n,
    hygiene clo m
    -> step m n
    -> approx m n.
Proof.
intros m n Hclm Hstep.
so (step_hygiene _#4 Hstep Hclm) as Hcln.
rewrite <- approx_fixpoint.
do2 2 split; auto.
intros v Heval.
exists v.
split.
  {
  eapply eval_first_step; eauto.
  }

  {
  apply mc_refl.
  apply ci_approx_refl.
  }
Qed.



Lemma anti_step_approx :
  forall m n,
    hygiene clo m
    -> step m n
    -> approx n m.
Proof.
intros m n Hclm Hstep.
so (step_hygiene _#4 Hstep Hclm) as Hcln.
rewrite <- approx_fixpoint.
do2 2 split; auto.
intros v Heval.
exists v.
split.
  {
  destruct Heval as (Hsteps & Hval).
  split; auto.
  eapply star_step; eauto.
  }

  {
  apply mc_refl.
  apply ci_approx_refl.
  }
Qed.



Lemma steps_approx :
  forall m n,
    hygiene clo m
    -> star step m n
    -> approx m n.
Proof.
intros m n Hclm Hsteps.
revert Hclm.
induct Hsteps.

(* refl *)
{
intros m Hcl.
apply approx_refl; auto.
}

(* step *)
{
intros m n p Hmn _ IH Hclm.
so (step_hygiene _#4 Hmn Hclm) as Hcln.
apply (approx_trans _ n); auto.
apply step_approx; auto.
}
Qed.


Lemma anti_steps_approx :
  forall m n,
    hygiene clo m
    -> star step m n
    -> approx n m.
Proof.
intros m n Hclm Hsteps.
revert Hclm.
induct Hsteps.

(* refl *)
{
intros m Hcl.
apply approx_refl; auto.
}

(* step *)
{
intros m n p Hmn _ IH Hclm.
so (step_hygiene _#4 Hmn Hclm) as Hcln.
apply (approx_trans _ n); auto.
apply anti_step_approx; auto.
}
Qed.



Inductive approxc : relation term :=
| approxc_var :
    forall i m,
      ci approx (var i) m
      -> approxc (var i) m

| approxc_oper :
    forall a t r r' m,
      mcr approxc a r r'
      -> ci approx (oper a t r') m
      -> approxc (oper a t r) m
.


Lemma approxc_refl :
  forall m, approxc m m.
Proof.
apply
  (term_mut_ind _
     (fun m => approxc m m)
     (fun a r => mcr approxc a r r)).

(* var *)
{
intro i.
apply approxc_var.
apply ci_approx_refl.
}

(* oper *)
{
intros a t r Hr.
apply (approxc_oper _ _ _ r); auto.
apply ci_approx_refl.
}

(* nil *)
{
apply mcr_nil.
}

(* cons *)
{
intros i a m IH1 r IH2.
apply mcr_cons; auto.
}
Qed.


Lemma approxc_compat :
  forall m m',
    mc approxc m m'
    -> approxc m m'.
Proof.
intros m m' Hm.
induct Hm.

(* var *)
{
intro i.
apply approxc_refl.
}

(* oper *)
{
intros a t r r' Hr.
apply (approxc_oper _#3 r'); auto.
apply ci_approx_refl.
}
Qed.



Lemma ci_approx_implies_approxc :
  forall m m', ci approx m m' -> approxc m m'.
Proof.
intros m m' Happrox.
destruct m as [i | a t r].
  {
  apply approxc_var; auto.
  }

  {
  apply (approxc_oper _ _ _ r); auto.
  apply mcr_refl.
  exact approxc_refl.
  }
Qed.


Lemma approxc_ci_approx_trans :
  forall m1 m2 m3,
    approxc m1 m2
    -> ci approx m2 m3
    -> approxc m1 m3.
Proof.
intros m1 m2 m3 H12 H23.
revert m3 H23.
induct H12.

(* var *)
{
intros i m2 H12 m3 H23.
apply approxc_var.
eapply ci_approx_trans; eauto.
}

(* oper *)
{
intros a t r r' m2 Hr H12 m3 H23.
apply (approxc_oper _#3 r'); auto.
eapply ci_approx_trans; eauto.
}
Qed.


Lemma approxc_approx_trans :
  forall m1 m2 m3,
    approxc m1 m2
    -> approx m2 m3
    -> approxc m1 m3.
Proof.
intros m1 m2 m3 H12 H23.
eapply approxc_ci_approx_trans; eauto.
intros s _ _.
so H23 as H.
rewrite <- approx_fixpoint in H.
destruct H as (Hcl2 & Hcl3 & _).
rewrite -> !subst_into_closed; auto.
Qed.


Lemma approxc_shift_under :
  forall i j m m',
    approxc m m'
    -> approxc (subst (under j (sh i)) m) (subst (under j (sh i)) m').
Proof.
intros i j m m' H.
revert m i j m' H.
apply
  (term_mut_ind _
     (fun m =>
        forall i j m',
          approxc m m'
          -> approxc (subst (under j (sh i)) m) (subst (under j (sh i)) m'))
     (fun a r =>
        forall i j r',
          mcr approxc a r r'
          -> mcr approxc a (substr (under j (sh i)) r) (substr (under j (sh i)) r'))).

(* var *)
{
intros k i j m H.
invertc H.
intros Hci.
simpsub.
assert (exists k', @project object (under j (sh i)) k = var k') as (k' & Heq).
  {
  so (lt_dec k j) as [Hlt | Hnlt].
    {
    exists k.
    rewrite -> project_under_lt; auto.
    }

    {
    exists (k + i).
    rewrite -> project_under_geq; [| omega].
    simpsub.
    f_equal.
    omega.
    }
  }
rewrite -> Heq.
apply approxc_var.
intros s Hcl Hcl'.
simpsub.
so (Hci (compose (under j (sh i)) s)) as H.
simpsubin H.
simpsub.
simpsubin Hcl.
simpsubin Hcl'.
rewrite -> Heq in H; [].
simpsubin H.
apply H; auto.
}

(* oper *)
{
intros a t r IH i j m H.
invertc H.
intros r' Hr Hci.
simpsub.
apply (approxc_oper _#3 (substr (under j (sh i)) r')); auto.
intros s Hcl Hcl'.
simpsub.
so (Hci (compose (under j (sh i)) s)) as H.
simpsubin H.
simpsubin Hcl.
simpsubin Hcl'.
apply H; auto.
}

(* nil *)
{
intros i j r H.
invert H.
intros <-.
simpsub.
apply mcr_nil.
}

(* cons *)
{
intros k a m IH r IH2 i j rr H.
invertc H.
intros m' r' Hm Hr <-.
simpsub.
apply mcr_cons; auto.
}
Qed.


Lemma approxc_shift :
  forall i m m',
    approxc m m'
    -> approxc (subst (sh i) m) (subst (sh i) m').
Proof.
intros i m m' H.
so (approxc_shift_under i 0 m m' H) as H'.
simpsubin H'.
exact H'.
Qed.


Lemma approxc_funct_term_and_row :
 (forall s s' m m',
    (forall i, approxc (project s i) (project s' i))
    -> approxc m m'
    -> approxc (subst s m) (subst s' m'))
 /\
 (forall s s' a (r r' : row a),
    (forall i, approxc (project s i) (project s' i))
    -> mcr approxc a r r'
    -> mcr approxc a (substr s r) (substr s' r')).
Proof.
exploit
  (syntax_ind _
     (fun m =>
        forall m' s s',
          (forall i, approxc (project s i) (project s' i))
          -> approxc m m'
          -> approxc (subst s m) (subst s' m'))
     (fun a r =>
        forall r' s s',
          (forall i, approxc (project s i) (project s' i))
          -> mcr approxc a r r'
          -> mcr approxc a (substr s r) (substr s' r'))) as Hind.

(* var *)
{
intros i m' s s' Hs Hm.
apply (approxc_ci_approx_trans _ (subst s' (var i))).
  {
  simpsub.
  apply Hs.
  }

  {
  intros t Hcl Hcl'.
  rewrite <- !subst_compose.
  invert Hm.
  intros Hm'.
  apply (Hm' (compose s' t)).
    {
    simpsub.
    simpsubin Hcl.
    assumption.
    }

    {
    simpsub.
    simpsubin Hcl'.
    assumption.
    }
  }
}

(* oper *)
{
intros a t r IH m' s s' Hs Hm.
simpsub.
invertc Hm.
intros r' Hr Hm.
apply (approxc_oper _ _ _ (substr s' r')); auto; [].
intros u Hcl Hcl'.
simpsub.
apply (Hm (compose s' u)).
  {
  simpsubin Hcl.
  simpsub.
  exact Hcl.
  }

  {
  simpsubin Hcl'.
  exact Hcl'.
  }
}

(* nil *)
{
intros r' s s' _ H.
invert H.
intros <-.
simpsub.
apply mcr_nil.
}

(* cons *)
{
intros i a t IH1 r IH2 r' s s' Hs Hm.
invert Hm.
intros m' r'' Hm' Hr <-.
simpsub.
apply mcr_cons; auto.
apply IH1; auto.
intros j.
destruct (lt_dec j i) as [Ht | Hnlt].
  {
  rewrite -> !project_under_lt; auto.
  apply approxc_refl.
  }

  {
  rewrite -> !project_under_geq; try omega.
  apply approxc_shift.
  apply Hs.
  }
}

(* epilogue *)
{
destruct Hind; split; intros; eauto.
}
Qed.


Lemma approxc_funct :
  forall s s' m m',
    (forall i, approxc (project s i) (project s' i))
    -> approxc m m'
    -> approxc (subst s m) (subst s' m').
Proof.
exact (approxc_funct_term_and_row andel).
Qed.


Lemma approxc_funct_row :
  forall s s' a (r r' : row a),
    (forall i, approxc (project s i) (project s' i))
    -> mcr approxc a r r'
    -> mcr approxc a (substr s r) (substr s' r').
Proof.
exact (approxc_funct_term_and_row ander).
Qed.


Lemma approxc_funct1 :
  forall n n' m m',
    approxc n n'
    -> approxc m m'
    -> approxc (subst1 n m) (subst1 n' m').
Proof.
intros n n' m m' Hn Hm.
apply approxc_funct; auto.
intro i.
destruct i as [| i].
  {
  simpsub.
  auto.
  }

  {
  simpsub.
  apply approxc_refl.
  }
Qed.


Lemma approxc_subst :
  forall s m m',
    approxc m m'
    -> approxc (subst s m) (subst s m').
Proof.
intros s m m' H.
apply approxc_funct; auto.
intro i.
apply approxc_refl.
Qed.


Lemma approxc_subst_row :
  forall s a (r r' : row a),
    mcr approxc a r r'
    -> mcr approxc a (substr s r) (substr s r').
Proof.
intros s a r r' Hr.
apply approxc_funct_row; eauto.
intros i.
apply approxc_refl.
Qed.


Lemma approxc_closed_invert :
  forall m n,
    hygiene clo m
    -> hygiene clo n
    -> approxc m n
    -> exists p,
         mc approxc m p
         /\ approx p n
         /\ hygiene clo p.
Proof.
intros m n Hclm Hcln Hmn.
revert Hclm Hcln.
induct Hmn.

(* var *)
{
intros i m _ Hcl.
exfalso.
invert Hcl.
intro H.
destruct H.
}

(* oper *)
{
intros a t r r' m Hr Happrox Hclm Hcln.
so (closing_substitution (oper a t r')) as (s & Hcl).
exists (subst s (oper a t r')).
do2 2 split; auto.
  {
  rewrite <- (subst_into_closed _ s (oper a t r)); auto.
  simpsub.
  apply mc_oper.
  apply approxc_subst_row; eauto.
  }

  {
  rewrite <- (subst_into_closed _ s m); auto.
  apply Happrox; auto.
  rewrite -> subst_into_closed; auto.
  }
}
Qed.


Lemma approxc_value :
  forall v m,
    hygiene clo v
    -> hygiene clo m
    -> value v
    -> approxc v m
    -> exists v',
         eval m v'
         /\ mc approxc v v'.
Proof.
intros v m Hclv Hclm Hval Hvm.
so (approxc_closed_invert _ _ Hclv Hclm Hvm) as (p & Hvp & Hpm & Hclp).
invert Hval.
intros a t r Hcanon <-.
invertc Hvp; [].
intros r' Hr <-.
rewrite <- approx_fixpoint in Hpm.
so (Hpm anderr (oper a t r') (conj (star_refl _) (value_i _ Hcanon))) as (w & Heval' & Hvw).
exists w.
split; auto.
apply (mc_mono _ (Relation.compose approxc (ci approx))).
  {
  clear_all.
  intros x z H.
  destruct H as (y & Hxy & Hyz).
  eapply approxc_ci_approx_trans; eauto.
  }

  {
  apply mc_compose.
  exists (oper a t r').
  split; auto.
  apply mc_oper.
  exact Hr.
  }
Qed.


Definition converges (m : @term object) := exists v, eval m v.


Lemma approx_converges :
  forall m n,
    approx m n
    -> converges m
    -> converges n.
Proof.
intros m n Happrox (v & Heval).
rewrite <- approx_fixpoint in Happrox.
destruct Happrox as (_ & _ & Happrox).
so (Happrox v Heval) as (v' & Heval' & _).
exists v'.
auto.
Qed.


Lemma approxc_converges :
  forall m n,
    hygiene clo n
    -> approxc m n
    -> value m
    -> converges n.
Proof.
intros m n Hcln Happroxc Hval.
invert Happroxc.
  {
  intros i _ <-.
  invert Hval.
  }
intros a th r r' Hmc Hciapprox <-.
invert Hval.
intro Hcanon.
so (closing_substitution (oper a th r')) as (s & Hcl).
exploit (Hciapprox s) as Happrox; auto.
  {
  rewrite -> subst_into_closed; auto.
  }
simpsubin Happrox.
rewrite -> subst_into_closed in Happrox; auto.
eapply approx_converges; eauto.
exists (oper a th (substr s r')).
split; auto using star_refl.
apply value_i; auto.
Qed.


Lemma extensionality_step :
  forall m n m',
    hygiene clo m
    -> hygiene clo n
    -> step m m'
    -> mc approxc m n
    -> approxc m' n.
Proof.
(* Make the main body of the induction look a bit nicer. *)
set (P :=
       (fun m m' =>
          forall n,
            hygiene clo m
            -> hygiene clo n
            -> mc approxc m n
            -> approxc m' n)).
set (Q :=
       (fun m m' =>
          forall n,
            hygiene clo m
            -> hygiene clo n
            -> approxc m n
            -> approxc m' n)).
assert (forall m m', P m m' -> Q m m') as HPQ.
  {
  unfold P, Q.
  intros m m' HP n Hclm Hcln Hmn.
  so (approxc_closed_invert _ _ Hclm Hcln Hmn) as (p & Hmp & Hpn & Hclp).
  eapply approxc_approx_trans; eauto.
  }
cut (forall m m', step m m' -> P m m').
  {
  unfold P.
  intro Hind.
  intros; eauto.
  }
apply step_ind;
revertnew
  (intros;
   repeat
     (match goal with
      | H : P _ _ |- _ => let H' := fresh in so (HPQ _ _ H) as H'; renameover H' into H
      end));
unfold P, Q;
clear P Q HPQ.

(* app1 *)
{
intros m1 m1' m2 _ IH1 n Hclapp Hcln Hmc.
revert Hcln.
invertc_mc Hmc.
intros n1 H1 n2 H2 <-.
fold (app n1 n2).
intro Hcln.
so (hygiene_invert_auto _#5 Hclapp) as H; cbn in H.
destruct H as (Hclm1 & Hclm2 & _).
so (hygiene_invert_auto _#5 Hcln) as H; cbn in H.
destruct H as (Hcln1 & Hcln2 & _).
apply approxc_compat.
apply mc_oper.
repeat (apply mcr_cons); auto using mcr_nil.
}

(* app2 *)
{
intros m1 m2 n Hclapp Hcln Hmc.
revert Hcln.
invertc_mc Hmc.
intros l Hlam_m1 n2 H2 <-.
fold (app l n2).
intro Hcln.
so (hygiene_invert_auto _#5 Hclapp) as H; cbn in H.
destruct H as (Hcllam & Hclm2 & _).
so (hygiene_invert_auto _#5 Hcln) as H; cbn in H.
destruct H as (Hcll & Hcln2 & _).
so (approxc_closed_invert _ _ Hcllam Hcll Hlam_m1) as (p & Hlam_m1_p & Hpl & Hclp).
invertc_mc Hlam_m1_p.
intros n1 H1.
fold (lam n1).
intros <-.
rewrite <- approx_fixpoint in Hpl.
so (Hpl anderr _ (conj (star_refl _) value_lam)) as (v & Heval & Hlam_n1_v).
revert Heval.
invertc_mc Hlam_n1_v.
intros q Hn1q.
fold (lam q).
intros <- Heval.
so (approxc_ci_approx_trans _#3 H1 Hn1q) as Hm1q.
apply (approxc_approx_trans _ (subst1 n2 q)).
  {
  apply approxc_funct1; auto.
  }

  {
  apply anti_steps_approx.
    {
    apply hygiene_auto; cbn.
    auto.
    }

    {
    destruct Heval as (Hstepsp & _).
    eapply star_trans.
      {
      apply (star_map' _ _ (fun x => app x _)); eauto using step_app1.
      }
    apply star_one.
    apply step_app2.
    }
  }
}

(* prev1 *)
{
intros m1 m1' _ IH n Hclprev Hcln Hmc.
invertc_mc Hmc.
intros n1 H1 Heq.
fold (prev n1) in Heq.
subst n.
so (hygiene_invert_auto _#5 Hclprev) as H; cbn in H.
destruct H as (Hclm1 & _).
so (hygiene_invert_auto _#5 Hcln) as H; cbn in H.
destruct H as (Hcln1 & _).
apply approxc_compat.
apply mc_oper.
repeat (apply mcr_cons); auto using mcr_nil.
}

(* prev2 *)
{
intros m n Hclprevnext Hcln Hmc.
invertc_mc Hmc.
intros l Hnext_l Heq.
fold (prev l) in Heq.
subst n.
so (hygiene_invert_auto _#5 Hclprevnext) as H; cbn in H.
destruct H as (Hclnext & _).
so (hygiene_invert_auto _#5 Hclnext) as H; cbn in H.
destruct H as (Hclm & _).
so (hygiene_invert_auto _#5 Hcln) as H; cbn in H.
destruct H as (Hcll & _).
so (approxc_closed_invert _ _ Hclnext Hcll Hnext_l) as (p & Hnext_p & Hpl & Hclp).
invertc_mc Hnext_p.
intros m' Hm_m' Heq.
fold (next m') in Heq.
subst p.
rewrite <- approx_fixpoint in Hpl.
so (Hpl anderr _ (conj (star_refl _) value_next)) as (v & Heval & Hnext_v).
invertc_mc Hnext_v.
intros q Hm'_q Heq.
fold (next q) in Heq.
subst v.
so (approxc_ci_approx_trans _#3 Hm_m' Hm'_q) as Hmq.
apply (approxc_approx_trans _ q); auto.
apply anti_steps_approx.
  {
  apply hygiene_auto; cbn; auto.
  }
destruct Heval as (Hsteps & _).
eapply star_trans.
  {
  apply (star_map' _ _ prev); eauto using step_prev1.
  }
apply star_one.
apply step_prev2.
}

(* bite1 *)
{
intros m1 m1' m2 m3 _ IH n Hclite Hcln Hmc.
invertc_mc Hmc.
intros n1 Hmn1 n2 Hmn2 n3 Hmn3 Heq.
fold (bite n1 n2 n3) in Heq.
subst n.
so (hygiene_invert_auto _#5 Hclite) as H; cbn in H.
destruct H as (Hclm1 & Hclm2 & Hclm3 & _).
so (hygiene_invert_auto _#5 Hcln) as H; cbn in H.
destruct H as (Hcln1 & Hcln2 & Hcln3 & _).
apply approxc_compat.
apply mc_oper.
repeat (apply mcr_cons); auto using mcr_nil.
}

(* bite2 *)
{
intros m2 m3 n Hclite Hcln Hmc.
invertc_mc Hmc.
intros n1 Hn1 n2 Hmn2 n3 Hmn3 Heq.
fold (bite n1 n2 n3) in Heq.
subst n.
so (hygiene_invert_auto _#5 Hclite) as H; cbn in H.
destruct H as (Hcltrue & Hclm2 & Hclm3 & _).
so (hygiene_invert_auto _#5 Hcln) as H; cbn in H.
destruct H as (Hcln1 & Hcln2 & Hcln3 & _).
so (approxc_closed_invert _ _ Hcltrue Hcln1 Hn1) as (p1 & Htrue_p1 & Hpn1 & Hclp1).
invertc_mc Htrue_p1.
fold (@btrue object).
intros <-.
rewrite <- approx_fixpoint in Hpn1.
so (Hpn1 anderr _ (conj (star_refl _) value_btrue)) as (v & Heval & Htrue_v).
invertc_mc Htrue_v.
fold (@btrue object).
intros <-.
apply (approxc_approx_trans _ n2); auto.
apply anti_steps_approx.
  {
  apply hygiene_auto; cbn; auto.
  }
destruct Heval as (Hsteps & _).
eapply star_trans.
  {
  apply (star_map' _ _ (fun z => bite z _ _)); eauto using step_bite1.
  }
apply star_one.
apply step_bite2.
}

(* bite3 *)
{
intros m2 m3 n Hclite Hcln Hmc.
invertc_mc Hmc.
intros n1 Hn1 n2 Hmn2 n3 Hmn3 Heq.
fold (bite n1 n2 n3) in Heq.
subst n.
so (hygiene_invert_auto _#5 Hclite) as H; cbn in H.
destruct H as (Hcltrue & Hclm2 & Hclm3 & _).
so (hygiene_invert_auto _#5 Hcln) as H; cbn in H.
destruct H as (Hcln1 & Hcln2 & Hcln3 & _).
so (approxc_closed_invert _ _ Hcltrue Hcln1 Hn1) as (p1 & Hfalse_p1 & Hpn1 & Hclp1).
invertc_mc Hfalse_p1.
fold (@bfalse object).
intros <-.
rewrite <- approx_fixpoint in Hpn1.
so (Hpn1 anderr _ (conj (star_refl _) value_bfalse)) as (v & Heval & Hfalse_v).
invertc_mc Hfalse_v.
fold (@bfalse object).
intros <-.
apply (approxc_approx_trans _ n3); auto.
apply anti_steps_approx.
  {
  apply hygiene_auto; cbn; auto.
  }
destruct Heval as (Hsteps & _).
eapply star_trans.
  {
  apply (star_map' _ _ (fun z => bite z _ _)); eauto using step_bite1.
  }
apply star_one.
apply step_bite3.
}

(* ppi11 *)
{
intros m1 m1' _ IH n Hclpi Hcln Hmc.
invertc_mc Hmc.
intros n1 H1 Heq.
fold (ppi1 n1) in Heq.
subst n.
so (hygiene_invert_auto _#5 Hclpi) as H; cbn in H.
destruct H as (Hclm1 & _).
so (hygiene_invert_auto _#5 Hcln) as H; cbn in H.
destruct H as (Hcln1 & _).
apply approxc_compat.
apply mc_oper.
repeat (apply mcr_cons); auto using mcr_nil.
}

(* ppi12 *)
{
intros m1 m2 n Hclpipair Hcln Hmc.
invertc_mc Hmc.
intros l Hpair_l Heq.
fold (ppi1 l) in Heq.
subst n.
so (hygiene_invert_auto _#5 Hclpipair) as H; cbn in H.
destruct H as (Hclpair & _).
so (hygiene_invert_auto _#5 Hclpair) as H; cbn in H.
destruct H as (Hclm1 & Hclm2 & _).
so (hygiene_invert_auto _#5 Hcln) as H; cbn in H.
destruct H as (Hcll & _).
so (approxc_closed_invert _ _ Hclpair Hcll Hpair_l) as (p & Hpair_p & Hpl & Hclp).
invertc_mc Hpair_p.
intros p1 Hmp1 p2 Hmp2 Heq.
fold (ppair p1 p2) in Heq.
subst p.
rewrite <- approx_fixpoint in Hpl.
so (Hpl anderr _ (conj (star_refl _) value_ppair)) as (v & Heval & Hpair_v).
invertc_mc Hpair_v.
intros q1 Hpq1 q2 Hpq2 Heq.
fold (ppair q1 q2) in Heq.
subst v.
so (approxc_ci_approx_trans _#3 Hmp1 Hpq1) as Hmq1.
so (approxc_ci_approx_trans _#3 Hmp2 Hpq2) as Hmq2.
apply (approxc_approx_trans _ q1); auto.
apply anti_steps_approx.
  {
  apply hygiene_auto; cbn; auto.
  }
destruct Heval as (Hsteps & _).
eapply star_trans.
  {
  apply (star_map' _ _ ppi1); eauto using step_ppi11.
  }
apply star_one.
apply step_ppi12.
}

(* ppi21 *)
{
intros m1 m1' _ IH n Hclpi Hcln Hmc.
invertc_mc Hmc.
intros n1 H1 Heq.
fold (ppi2 n1) in Heq.
subst n.
so (hygiene_invert_auto _#5 Hclpi) as H; cbn in H.
destruct H as (Hclm1 & _).
so (hygiene_invert_auto _#5 Hcln) as H; cbn in H.
destruct H as (Hcln1 & _).
apply approxc_compat.
apply mc_oper.
repeat (apply mcr_cons); auto using mcr_nil.
}

(* ppi22 *)
{
intros m1 m2 n Hclpipair Hcln Hmc.
invertc_mc Hmc.
intros l Hpair_l Heq.
fold (ppi2 l) in Heq.
subst n.
so (hygiene_invert_auto _#5 Hclpipair) as H; cbn in H.
destruct H as (Hclpair & _).
so (hygiene_invert_auto _#5 Hclpair) as H; cbn in H.
destruct H as (Hclm1 & Hclm2 & _).
so (hygiene_invert_auto _#5 Hcln) as H; cbn in H.
destruct H as (Hcll & _).
so (approxc_closed_invert _ _ Hclpair Hcll Hpair_l) as (p & Hpair_p & Hpl & Hclp).
invertc_mc Hpair_p.
intros p1 Hmp1 p2 Hmp2 Heq.
fold (ppair p1 p2) in Heq.
subst p.
rewrite <- approx_fixpoint in Hpl.
so (Hpl anderr _ (conj (star_refl _) value_ppair)) as (v & Heval & Hpair_v).
invertc_mc Hpair_v.
intros q1 Hpq1 q2 Hpq2 Heq.
fold (ppair q1 q2) in Heq.
subst v.
so (approxc_ci_approx_trans _#3 Hmp1 Hpq1) as Hmq1.
so (approxc_ci_approx_trans _#3 Hmp2 Hpq2) as Hmq2.
apply (approxc_approx_trans _ q2); auto.
apply anti_steps_approx.
  {
  apply hygiene_auto; cbn; auto.
  }
destruct Heval as (Hsteps & _).
eapply star_trans.
  {
  apply (star_map' _ _ ppi2); eauto using step_ppi21.
  }
apply star_one.
apply step_ppi22.
}

(* seq1 *)
{
intros m1 m1' m2 _ IH n Hclseq Hcln Hmc.
invertc_mc Hmc.
intros n1 H1 n2 H2 <-.
fold (seq n1 n2).
so (hygiene_invert_auto _#5 Hclseq) as H; cbn in H.
destruct H as (Hclm1 & Hclm2 & _).
so (hygiene_invert_auto _#5 Hcln) as H; cbn in H.
destruct H as (Hcln1 & Hcln2 & _).
apply approxc_compat.
apply mc_oper.
repeat (apply mcr_cons); auto using mcr_nil.
}

(* seq2 *)
{
intros m1 m2 Hval n Hclseq Hcln Hmc.
revert Hcln.
invertc_mc Hmc.
intros n1 H1 n2 H2 <-.
fold (seq n1 n2).
intro Hcln.
so (hygiene_invert_auto _#5 Hclseq) as H; cbn in H.
destruct H as (Hclm1 & Hclm2 & _).
so (hygiene_invert_auto _#5 Hcln) as H; cbn in H.
destruct H as (Hcln1 & Hcln2 & _).
eassert _ as H; [refine (approxc_converges _ _ _ H1 _) |]; auto.
destruct H as (v & (Hstepsv & Hvalv)).
apply (approxc_approx_trans _ (subst1 v n2)).
  {
  apply approxc_funct1; auto.
  apply (approxc_approx_trans _ n1); auto.
  apply steps_approx; auto.
  }

  {
  apply anti_steps_approx.
    {
    apply hygiene_auto; cbn; auto.
    }
  eapply star_trans.
    {
    apply (star_map' _ _ (fun z => seq z _)); eauto using step_seq1.
    }
  apply star_one.
  apply step_seq2; auto.
  }
}
Qed.



Lemma approxc_eval :
  forall m n v,
    hygiene clo m
    -> hygiene clo n
    -> star step m v
    -> approxc m n
    -> approxc v n.
Proof.
intros m n v Hclm Hcln Hsteps Hmn.
revert n Hclm Hcln Hmn.
induct Hsteps.

(* refl *)
{
intros m n _ _ Hmn.
exact Hmn.
}

(* step *)
{
intros m1 m2 m3 Hstep Hsteps IH n Hclm1 Hcln Hm1n.
so (approxc_closed_invert _ _ Hclm1 Hcln Hm1n) as (p & Hm1p & Hpm & Hclp).
so (extensionality_step _#3 Hclm1 Hclp Hstep Hm1p) as Hm2p.
so (step_hygiene _#4 Hstep Hclm1) as Hclm2. 
so (IH p Hclm2 Hclp Hm2p) as Hm3p.
eapply approxc_approx_trans; eauto.
}
Qed.


Lemma approxc_implies_approx :
  forall m m',
    hygiene clo m
    -> hygiene clo m'
    -> approxc m m' 
    -> approx m m'.
Proof.
intros m n Hclm Hcln Hmn.
exists (fun m n => hygiene clo m /\ hygiene clo n /\ approxc m n).
split; auto.
clear m n Hclm Hcln Hmn.
intros m n H.
destruct H as (Hclm & Hcln & Hmn).
do2 2 split; auto.
intros v Heval.
so (approxc_eval _ _ _ Hclm Hcln (Heval andel) Hmn) as Hvn.
destruct Heval as (Hsteps & Hval).
so (steps_hygiene _#4 Hsteps Hclm) as Hclv.
so (approxc_value _ _ Hclv Hcln Hval Hvn) as (v' & Heval' & Hv).
exists v'.
split; auto; [].
apply (mc_mono _ approxc); auto; [].
clear_all.
intros x y Hxy.
intros s Hclx Hcly.
do2 2 split; auto.
apply approxc_subst; auto.
Qed.


Lemma approxc_implies_ci_approx :
  forall m m',
    approxc m m' 
    -> ci approx m m'.
Proof.
intros m m' Happrox.
intros s Hcl Hcl'.
so (approxc_subst s _ _ Happrox) as Happrox'.
apply approxc_implies_approx; auto.
Qed.


Lemma approx_compat :
  forall m n,
    hygiene clo m
    -> hygiene clo n
    -> mc (ci approx) m n
    -> approx m n.
Proof.
intros m n Hclm Hcln Hmn.
apply approxc_implies_approx; auto.
apply approxc_compat.
eapply (mc_mono _ (ci approx)); eauto.
intros x y Hxy.
apply ci_approx_implies_approxc; auto.
Qed.


Lemma ci_approx_compat :
  forall m n,
    mc (ci approx) m n
    -> ci approx m n.
Proof.
intros m n Hmc.
intros s Hclm Hcln.
apply approx_compat; auto.
clear Hclm Hcln.
induct Hmc.

(* var *)
{
intros i.
simpsub.
apply mc_refl.
exact ci_approx_refl.
}

(* oper *)
{
intros a t r r' Hr.
simpsub.
apply mc_oper.
clear t.
induct Hr.
  (* nil *)
  {
  simpsub.
  apply mcr_nil.
  }

  (* cons *)
  {
  intros i a m m' r r' Hm _ IH.
  simpsub.
  apply mcr_cons; auto.
  intros s' Hclm Hcln.
  simpsub.
  simpsubin Hclm.
  simpsubin Hcln.
  apply Hm; auto.
  }
}
Qed.


Lemma ci_approx_funct :
  forall s s' m m',
    (forall i, ci approx (project s i) (project s' i))
    -> ci approx m m'
    -> ci approx (subst s m) (subst s' m').
Proof.
intros s s' m m' Happs Happm.
apply approxc_implies_ci_approx.
apply approxc_funct; auto using ci_approx_implies_approxc.
Qed.


Lemma ci_approx_funct1 :
  forall n n' m m',
    ci approx n n'
    -> ci approx m m'
    -> ci approx (subst1 n m) (subst1 n' m').
Proof.
intros n n' m m' Happn Happm.
apply approxc_implies_ci_approx.
apply approxc_funct1;
auto using ci_approx_implies_approxc.
Qed.


Lemma approx_funct1 :
  forall (m n p : @term object),
    approx m n
    -> hygiene (permit clo) p
    -> approx (subst1 m p) (subst1 n p).
Proof.
intros m n p Hmn Hclp.
so (approx_closed _ _ Hmn) as (Hclm & Hcln).
apply approxc_implies_approx.
  {
  apply hygiene_subst1; auto.
  }

  {
  apply hygiene_subst1; auto.
  }
apply approxc_funct1; auto using approxc_refl.
apply ci_approx_implies_approxc.
apply ci_approx_from_approx; auto.
Qed.


Lemma equiv_approx :
  forall (m n : @term object),
    hygiene clo m
    -> hygiene clo n
    -> equiv m n
    -> approx m n.
Proof.
intros m n Hclm Hcln Hequiv.
exists (fun m n => hygiene clo m /\ hygiene clo n /\ equiv m n).
do2 3 split; auto.
clear m n Hclm Hcln Hequiv.
intros m n (Hclm & Hcln & Hequiv).
do2 2 split; auto.
intros v (Hstepsm & Hvalv).
so (church_rosser _ _ _ (equiv_trans _#4 (equiv_symm _#3 Hequiv) (steps_equiv _#3 Hstepsm))) as (w & Hnw & Hvw).
so (standardization _#3 Hvw) as (x & Hstepsv & Hinternal).
invert Hstepsv.
2:{
  intros y Hstep _.
  destruct (determinism_value _#3 Hvalv Hstep).
  }
intros <-.
so (standardization _#3 Hnw) as (u & Hnu & Huw).
assert (mc equiv v u) as Hvu.
  {
  apply star_mc_impl_mc_star.
  apply (star_trans _ _ _ w).
    {
    apply (star_mono _ (mc reduce)); auto.
    intros x y Hxy.
    eapply mc_mono; eauto.
    }

    {
    apply (star_reverse _ (mc reduce)); auto.
    apply (mc_reverse _ reduce); auto.
    }
  }
exists u.
split.
  {
  split; auto.
  invert Hvalv.
  intros a th r Hcanon <-.
  invert Hvu.
  intros r' _ <-.
  apply value_i; auto.
  }
refine (mc_mono _#3 _ _ _ Hvu).
intros q r Hqr.
intros s Hcl Hcl'.
do2 2 split; auto.
apply equiv_subst; auto.
Qed.


End object.


Arguments approx {object}.
Arguments ci {object}.
Arguments ec {object}.
Arguments rc {object}.
Arguments converges {object}.


Require Import MapTerm.


(* "strong approximation"
   Lifts over all mappings to other object types.
*)
Definition sapprox {object} (m p : @term object) : Prop :=
  forall T (f : object -> T),
    approx (map_term f m) (map_term f p).


Lemma sapprox_impl_approx :
  forall object (m p : @term object),
    sapprox m p
    -> approx m p.
Proof.
intros object m p H.
so (H _ (fun x => x)) as H'.
rewrite -> !map_term_id in H'.
exact H'.
Qed.


Lemma sapprox_closed :
  forall object (m p : @term object),
    sapprox m p
    -> hygiene clo m /\ hygiene clo p.
Proof.
intros object m p H.
apply approx_closed.
apply sapprox_impl_approx; auto.
Qed.


Lemma sapprox_refl :
  forall object (m : @term object),
    hygiene clo m
    -> sapprox m m.
Proof.
intros object m Hcl T f.
apply approx_refl.
apply map_hygiene; auto.
Qed.


Lemma sapprox_trans :
  forall object (m n p : @term object),
    sapprox m n
    -> sapprox n p
    -> sapprox m p.
Proof.
intros object m n p Hmn Hnp.
intros T f.
apply (approx_trans _ _ (map_term f n)); auto.
Qed.


Lemma steps_sapprox :
  forall object (m n : @term object),
    hygiene clo m
    -> star step m n
    -> sapprox m n.
Proof.
intros object m n Hclm Hsteps.
intros T f.
apply steps_approx; auto using map_steps, map_hygiene.
Qed.


Lemma anti_steps_sapprox :
  forall object (m n : @term object),
    hygiene clo m
    -> star step m n
    -> sapprox n m.
Proof.
intros object m n Hclm Hsteps.
intros T f.
apply anti_steps_approx; auto using map_steps, map_hygiene.
Qed.


Lemma sapprox_action :
  forall object (m p v : @term object),
    sapprox m p
    -> eval m v
    -> exists w,
         eval p w
         /\ mc (ci sapprox) v w.
Proof.
intros object m p v Hmp Hmv.
so (sapprox_impl_approx _#3 Hmp) as H.
rewrite <- approx_fixpoint in H.
destruct H as (_ & _ & H).
so (H v Hmv) as (w & Hpw & Hmc); clear H.
exists w.
split; auto.
destruct Hmv as (Hstepsm & Hvalv).
destruct Hpw as (Hstepsp & Hvalw).
destruct v as [k | a th r].
  {
  invert Hvalv.
  }
destruct w as [k | a' th' r'].
  {
  invert Hvalw.
  }
invertc Hmc.
intros r'' _ <- Heqth Heqr.
injectionT Heqth.
intros <-.
injectionT Heqr.
intros ->.
apply mc_oper.
assert (forall T (f : object -> T),
          mcr (ci approx) a (map_row f r) (map_row f r')) as Hrow.
  {
  intros T f.
  so (Hmp T f) as H.
  rewrite <- approx_fixpoint in H.
  destruct H as (_ & _ & H).
  exploit (H (map_term f (oper a th r))) as (w' & Hpw' & Hmc); clear H.
    {
    apply map_eval.
    split; auto.
    }
  so (determinism_eval _#4 (map_eval _ _ f _ _ (conj Hstepsp Hvalw)) Hpw').
  subst w'.
  cbn in Hmc.
  invertc Hmc.
  intros Hmcr _.
  exact Hmcr.
  }
clear m p th Hstepsm Hvalv Hstepsp Hvalw Hmp.
revert r r' Hrow.
induct a.
  (* nil *)
  {
  intros r r' _.
  cases r.
  cases r'.
  apply mcr_nil.
  }

  (* cons *)
  {
  intros n a IH r r'.
  cases r.
  intros n' a' m r1 Heq.
  injection Heq.
  intros -> ->.
  substrefl Heq.
  cases r'.
  intros n' a' m' r1' Heq Hrow.
  injection Heq.
  intros -> ->.
  substrefl Heq.
  apply mcr_cons.
    {
    intros s Hcl Hcl'.
    intros T f.
    so (Hrow T f) as H.
    invertc H.
    intros H _.
    simpmap.
    apply H.
      {
      so (map_hygiene _ _ f _ _ Hcl) as H'.
      simpmapin H'.
      exact H'.
      }

      {
      so (map_hygiene _ _ f _ _ Hcl') as H'.
      simpmapin H'.
      exact H'.
      }
    }

    {
    apply IH.
    intros T f.
    so (Hrow T f) as H.
    invert H.
    auto.
    }
  }
Qed.


Lemma sapprox_funct1 :
  forall object (m n p : @term object),
    sapprox m n
    -> hygiene (permit clo) p
    -> sapprox (subst1 m p) (subst1 n p).
Proof.
intros object m n p Hmn Hclp.
intros T f.
simpmap.
apply approx_funct1.
  {
  apply Hmn.
  }

  {
  apply map_hygiene; auto.
  }
Qed.


Lemma equiv_sapprox :
  forall object (m n : @term object),
    hygiene clo m
    -> hygiene clo n
    -> equiv m n
    -> sapprox m n.
Proof.
intros object m n Hclm Hcln Hequiv.
intros T f.
apply equiv_approx; auto using map_hygiene, map_equiv.
Qed.  


Lemma map_sapprox :
  forall A B (f : A -> B) m n,
    sapprox m n
    -> sapprox (map_term f m) (map_term f n).
Proof.
intros A B f m n Happrox.
intros C g.
rewrite -> !map_term_compose.
apply Happrox.
Qed.
