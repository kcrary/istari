
Require Import Coq.Lists.List.

Require Import Axioms.
Require Import Tactics.
Require Import Sequence.
Require Import Ordinal.
Require Import Syntax.
Require Import SimpSub.
Require Import Promote.
Require Import Hygiene.


Fixpoint ctxpred {object} (G : @context object) {struct G} : hpred 
  :=
  match G with
  | nil => clo
  | cons h G' => permit (ctxpred G')
  end.


Lemma promote_ctxpred :
  forall object (G : @context object), hincl (ctxpred G) (ctxpred (promote G)).
Proof.
intros object G.
induct G; cbn; auto using clo_min.
intros h G IH.
apply permit_compat; auto.
Qed.


Lemma ctxpred_length :
  forall object (G : @context object), ctxpred G = (fun i => i < length G).
Proof.
intros object G.
fextensionality 1.
intro i.
apply propositional_extensionality.
revert i.
induct G.

(* nil *)
{
intros.
split; intro H; [destruct H | cbn in H; omega].
}

(* cons *)
{
intros h G IH i.
cbn.
split.
  {
  intro H.
  destruct i as [| i].
    {
    omega.
    }
  cut (i < length G).
    {
    omega.
    }
  apply IH.
  exact H.
  }

  {
  intros H.
  destruct i as [| i].
    {
    cbn; auto.
    }
  apply IH.
  omega.
  }
}
Qed.


Lemma project_closub :
  forall object (G : @context object) s i,
    closub (ctxpred G) s
    -> ctxpred G i
    -> @hygiene object clo (project s i).
Proof.
intros object G s i Hcls H.
replace (project s i) with (subst s (var i)) by (simpsub; reflexivity).
eapply subst_closub; eauto using hygiene_var.
Qed.


Inductive hygieneh {object} P : @hyp object -> Prop :=
| hygieneh_tpl :
    hygieneh P hyp_tpl

| hygieneh_tp :
    hygieneh P hyp_tp

| hygieneh_tml :
    forall a,
      hygiene P a
      -> hygieneh P (hyp_tml a)

| hygieneh_tm :
    forall a,
      hygiene P a
      -> hygieneh P (hyp_tm a)

| hygieneh_emp :
    hygieneh P hyp_emp
.


Inductive cloctx {object} : @context object -> Prop :=
| cloctx_nil :
    cloctx nil

| cloctx_cons :
    forall h G,
      cloctx G
      -> hygieneh (ctxpred G) h
      -> cloctx (cons h G)
.


Lemma hygieneh_promote :
  forall object P (h : @hyp object),
    hygieneh P h <-> hygieneh P (promote_hyp h).
Proof.
intros object P h.
cases h; cbn; try reflexivity; split; eauto using hygieneh_tpl, hygieneh_tp.
  {
  intro H.
  invertc H.
  intro H.
  apply hygieneh_tm; auto.
  }

  {
  intro H.
  invertc H.
  intro H.
  apply hygieneh_tml; auto.
  }
Qed.


Lemma cloctx_promote :
  forall object (G : @context object),
    cloctx G <-> cloctx (promote G).
Proof.
intros object G.
split.
  {
  intro H.
  induct H; eauto using cloctx_nil.
  intros h G _ IH Hcl.
  cbn.
  apply cloctx_cons; auto.
  rewrite <- hygieneh_promote.
  rewrite -> ctxpred_length in Hcl |- *.
  rewrite -> List.map_length.
  exact Hcl.
  }

  {
  induct G; auto.
  (* cons *)
  intros h G IH Hcl.
  cbn in Hcl.
  invertc Hcl.
  intros HclG Hcl.
  apply cloctx_cons; auto.
  rewrite <- hygieneh_promote in Hcl.
  rewrite -> ctxpred_length in Hcl |- *.
  rewrite -> List.map_length in Hcl.
  exact Hcl.
  }
Qed.


Lemma hincl_promote_adjust :
  forall object (G : @context object),
    hincl (ctxpred (promote G)) (ctxpred G).
Proof.
intros object G.
induct G.

(* nil *)
{
cbn.
intros i H; destruct H.
}

(* cons *)
{
intros h G IH i H.
cbn.
destruct i as [| i].
  {
  cbn.
  trivial.
  }

  {
  cbn in H |- *.
  apply IH; auto.
  }
}
Qed.


Lemma closub_promote :
  forall object (G : @context object) (s : @sub object),
    closub (ctxpred G) s 
    -> closub (ctxpred (promote G)) s.
Proof.
intros object G s Hcl.
intros i H.
apply (Hcl i).
eapply hincl_promote_adjust; eauto.
Qed.


Lemma hygiene_promote :
  forall object (G : @context object) (m : @term object),
    hygiene (ctxpred G) m
    -> hygiene (ctxpred (promote G)) m.
Proof.
intros object G m Hhyg.
refine (hygiene_weaken _#4 _ Hhyg).
clear Hhyg m.
induct G.

(* nil *)
{
intros i H.
cbn in H.
destruct H.
}

(* cons *)
{
intros h G IH i Hadj.
destruct i as [| i].
  {
  destruct h; auto.
  }
cbn in Hadj |- *.
apply IH; auto.
}
Qed.


Lemma hygieneh_weaken :
  forall object P Q (h : @hyp object),
    hincl P Q
    -> hygieneh P h
    -> hygieneh Q h.
Proof.
intros object P Q h Hincl Hh.
induct Hh; intros; 
[apply hygieneh_tpl | apply hygieneh_tp | apply hygieneh_tml | apply hygieneh_tm | apply hygieneh_emp];
eapply hygiene_weaken; eauto.
Qed.


Lemma hygieneh_subst :
  forall object P Q (s : @sub object) h,
    hygieneh P h
    -> (forall i, P i -> hygiene Q (project s i))
    -> hygieneh Q (substh s h).
Proof.
intros object P Q s h Hh Hs.
induct Hh; intros; simpsub;
[apply hygieneh_tpl | apply hygieneh_tp | apply hygieneh_tml | apply hygieneh_tm | apply hygieneh_emp];
eapply hygiene_subst; eauto.
Qed.


Lemma substh_closub :
  forall object P s (h : @hyp object),
    closub P s
    -> hygieneh P h
    -> hygieneh clo (substh s h).
Proof.
intros object P s m Hs Hm.
refine (hygieneh_subst _#5 Hm _).
intros i Hie.
apply (hygiene_weaken _ clo); auto using clo_min.
Qed.


Lemma hygieneh_subst_invert :
  forall object P (s : @sub object) h,
    hygieneh P (substh s h)
    -> hygieneh (fun j => hygiene P (project s j)) h.
Proof.
intros object P s h.
cases h; eauto using hygieneh_tpl, hygieneh_tp, hygieneh_emp.

(* tml *)
{
intros a H.
invertc H.
intros Hhyg.
so (hygiene_subst_invert _#4 Hhyg) as Hhyg'.
apply hygieneh_tml; auto.
}

(* tm *)
{
intros a H.
invertc H.
intros Hhyg.
so (hygiene_subst_invert _#4 Hhyg) as Hhyg'.
apply hygieneh_tm; auto.
}
Qed.


Lemma hygieneh_shift' :
  forall object P i (h : @hyp object),
    hygieneh (fun j => P (i + j)) h
    -> hygieneh P (substh (sh i) h).
Proof.
intros object P i h H.
induct H; intros;
[apply hygieneh_tpl | apply hygieneh_tp | apply hygieneh_tml | apply hygieneh_tm | apply hygieneh_emp];
eapply hygiene_shift'; eauto.
Qed.


Lemma cloctx_tail :
  forall object (G1 G2 : @context object),
    cloctx (G2 ++ G1) -> cloctx G1.
Proof.
intros object G1 G2.
induct G2; auto.
(* cons *)
intros h G2 IH H.
cbn in H.
invertc H.
auto.
Qed.


Lemma hygieneh_unshift :
  forall object P i (h : @hyp object),
    hygieneh P (substh (sh i) h)
    -> hygieneh (fun j => P (i + j)) h.
Proof.
intros object P i h Hhyg.
revert Hhyg.
cases h; intros; invertc Hhyg; intros; eauto using hygieneh_tpl, hygieneh_tp, hygieneh_tml, hygieneh_tm, hygieneh_emp, hygiene_unshift.
Qed.


Lemma hygieneh_shift_permit_iff :
  forall object P (h : @hyp object),
    hygieneh P h <-> hygieneh (permit P) (substh sh1 h).
Proof.
intros object P h.
split.
  {
  intro Hhyg.
  apply hygieneh_shift'.
  refine (hygieneh_weaken _#4 _ Hhyg).
  intros j H.
  cbn; auto.
  }

  {
  intro Hhyg.
  so (hygieneh_unshift _#4 Hhyg) as Hhyg'.
  cbn in Hhyg'.
  refine (hygieneh_weaken _#4 _ Hhyg').
  intro; intros; eauto.
  }
Qed.


Inductive hygienectx {object} (P : nat -> Prop) : @context object -> Prop :=
| hygienectx_nil :
    hygienectx P nil

| hygienectx_cons :
    forall h G,
      hygienectx P G
      -> hygieneh (fun i => i < length G \/ (i >= length G /\ P (i - length G))) h
      -> hygienectx P (cons h G)
.


Lemma cloctx_is_hygienectx :
  forall object (G : @context object),
    cloctx G <-> hygienectx clo G.
Proof.
intros object G.
split.
  {
  intro HclG.
  induct HclG; auto using hygienectx_nil.
  (* cons *)
  intros h G _ IH Hclh.
  apply hygienectx_cons; auto.
  eapply hygieneh_weaken; eauto.
  intros i Hi.
  rewrite -> ctxpred_length in Hi.
  left; auto.
  }

  {
  intro HclG.
  induct HclG; auto using cloctx_nil.
  intros h G _ IH Hh.
  apply cloctx_cons; auto.
  eapply hygieneh_weaken; eauto.
  intros i Hi.
  rewrite -> ctxpred_length.
  destruct Hi as [| (_ & H)]; auto.
  destruct H.
  }
Qed.


Lemma hygienectx_app :
  forall object P (G1 G2 : @context object),
    hygienectx P G1
    -> hygienectx (fun i => i < length G1 \/ (i >= length G1 /\ P (i - length G1))) G2
    -> hygienectx P (G2 ++ G1).
Proof.
intros object P G1 G2 HG1 HG2.
induct HG2; auto using hygienectx_nil.
intros h G _ IH Hh.
cbn.
apply hygienectx_cons; auto.
eapply hygieneh_weaken; eauto.
intros i Hi.
rewrite -> app_length.
destruct Hi as [Hi | Hi].
  {
  left.
  omega.
  }
destruct Hi as (Himin & [Hi | Hi]).
  {
  left.
  omega.
  }
destruct Hi as (Himin' & Hi).
right.
split.
  {
  omega.
  }
force_exact Hi.
f_equal.
omega.
Qed.


Lemma hygienectx_app_invert :
  forall object P (G1 G2 : @context object),
    hygienectx P (G2 ++ G1)
    -> hygienectx P G1 
      /\ hygienectx (fun i => i < length G1 \/ (i >= length G1 /\ P (i - length G1))) G2.
Proof.
intros object P G1 G2.
induct G2.

(* nil *)
{
intros H.
split; auto.
apply hygienectx_nil.
}

(* cons *)
{
intros h G2 IH H.
cbn in H.
invertc H.
intros HG12 Hh.
so (IH HG12) as (HG1 & HG2).
split; auto.
apply hygienectx_cons; auto.
eapply hygieneh_weaken; eauto.
intros i Hi.
rewrite -> app_length in Hi.
destruct Hi as [Hi | Hi].
  {
  so (lt_dec i (length G2)) as [Hlt | Hnlt].
    {
    left; auto.
    }
  right.
  split; [omega |].
  left.
  omega.
  }

  {
  destruct Hi as (Himin & Hi).
  right.
  split; [omega |].
  right.
  split; [omega |].
  force_exact Hi.
  f_equal.
  omega.
  }
}
Qed.


Lemma hygienectx_subst :
  forall object (P Q : hpred) s (G : @context object),
    hygienectx P G
    -> (forall i, P i -> hygiene Q (project s i))
    -> hygienectx Q (substctx s G).
Proof.
intros object P Q s G HG HP.
induct HG; cbn; auto using hygienectx_nil.
(* cons *)
intros h G _ IH Hh.
apply hygienectx_cons; auto.
clear IH.
eapply hygieneh_subst; eauto.
clear Hh.
intros i Hi.
cbn in Hi.
destruct Hi as [Hi | (Himin & Hi)].
  {
  rewrite -> project_under_lt; auto.
  apply hygiene_var.
  rewrite -> length_substctx.
  left; auto.
  }
rewrite -> project_under_geq; auto.
apply hygiene_shift'.
so (HP _ Hi) as Hproj.
eapply hygiene_weaken; eauto.
clear i Himin Hi Hproj.
intros j Hj.
rewrite -> length_substctx.
right.
split.
  {
  omega.
  }

  {
  force_exact Hj.
  f_equal.
  omega.
  }
Qed.
