
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Tactics.
Require Import Axioms.
Require Import Sigma.
Require Import Equality.
Require Import Sequence.
Require Import Relation.
Require Import Ordinal.
Require Import Syntax.
Require Import SimpSub.
Require Import Dynamic.
Require Import Ofe.
Require Import Uniform.
Require Import Intensional.
Require Import Candidate.
Require Import System.
Require Import Semantics.
Require Import SemanticsKnot.
Require Import Judgement.
Require Import Hygiene.
Require Import ProperClosed.
Require Import ProperFun.
Require Import Shut.

Require Import Equivalence.
Require Import ProperEquiv.
Require Import Defined.
Require Import PageCode.
Require Import PageType.
Require Import Native.
Require Import SemanticsNative.
Require Unshut.
Require SoundPartialUtil.


Local Ltac prove_hygiene :=
  repeat (first [ apply hygiene_shift_permit
                | apply hygiene_auto; cbn; repeat2 split; auto
                ]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1;
  try (apply hygiene_var; cbn; auto; done).


Require Import Equivalences.


Lemma sound_nativetp_formation :
  forall A f G,
    pseq G (deq (nativetp A f) (nativetp A f) (univ nzero)).
Proof.
intros A f.
refine (seq_pseq 0 0 _ _); cbn.
intro G.
rewrite -> seq_univ.
intros i s s' Hs.
exists SoundSimple.zeropg, (iubase (native_urel A f stop i)).
do2 5 split; auto using SoundSimple.pginterp_nzero; simpsub;
apply interp_eval_refl; apply interp_native.
Qed.


Lemma sound_nativetp_intro_compute_pre :
  forall A f x G m n,
    hygiene clo m
    -> hygiene clo n
    -> star step m (native_elem (f x))
    -> star step n (native_elem (f x))
    -> seq G (deq m n (nativetp A f)).
Proof.
intros A f x G m n Hclm Hcln Hstepsm Hstepsn.
rewrite -> seq_deq.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
exists (iubase (native_urel A f stop i)).
rewrite -> !(subst_into_closed _ _ m); auto.
rewrite -> !(subst_into_closed _ _ n); auto.
simpsub.
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_native.
  }

  {
  apply interp_eval_refl.
  apply interp_native.
  }

  {
  cbn.
  do2 3 split; eauto.
  }

  {
  cbn.
  do2 3 split; eauto.
  }

  {
  cbn.
  do2 3 split; eauto.
  }
Qed.


Lemma sound_nativetp_intro_pre :
  forall A f x G,
    seq G (deq (native_elem (f x)) (native_elem (f x)) (nativetp A f)).
Proof.
intros A f x G.
eapply sound_nativetp_intro_compute_pre; auto using star_refl; prove_hygiene.
Qed.


Lemma sound_nativetp_intro :
  forall A f x G,
    pseq G (deq (native_elem (f x)) (native_elem (f x)) (nativetp A f)).
Proof.
intros A f x.
refine (seq_pseq 0 0 _ _); cbn.
intro G.
apply sound_nativetp_intro_pre.
Qed.


Lemma sound_native_unary :
  forall A1 A2 f1 f2 (g : A1 -> A2) (g' : native -> option native),
    (forall x, g' (f1 x) = Some (f2 (g x)))
    -> forall G m p,
         pseq G (deq m p (nativetp A1 f1))
         -> pseq G (deq (native_unary g' m) (native_unary g' p) (nativetp A2 f2)).
Proof.
intros A1 A2 f1 f2 g g' Hg G m p.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (Hseq _ _ _ Hs) as (R & Hl & _ & Hm & Hp & Hmp).
simpsubin Hl.
invert (basic_value_inv _#6 (value_nativetp _ _) Hl).
intros <-.
cbn in Hm, Hp, Hmp.
decompose Hm.
intros _ Hclml Hclmr x Hml Hmr.
decompose Hp.
intros _ Hclpl Hclpr x' Hpl Hpr.
decompose Hmp.
intros _ _ _ x'' Hml' Hpr'.
so (determinism_eval _#4 (conj Hml value_native_elem) (conj Hml' value_native_elem)) as Heq.
so (determinism_eval _#4 (conj Hpr value_native_elem) (conj Hpr' value_native_elem)) as Heq'.
exists (iubase (native_urel A2 f2 stop i)).
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_native.
  }

  {
  apply interp_eval_refl.
  apply interp_native.
  }

  {
  simpsub.
  cbn.
  do2 3 split; auto; try prove_hygiene.
  exists (g x).
  split.
    {
    apply (star_trans _ _ _ (native_unary g' (native_elem (f1 x)))).
      {
      apply (star_map' _ _ (native_unary g')); auto using step_native_unary1.
      }
    apply star_one.
    apply step_native_unary2; auto.
    }

    {
    apply (star_trans _ _ _ (native_unary g' (native_elem (f1 x)))).
      {
      apply (star_map' _ _ (native_unary g')); auto using step_native_unary1.
      }
    apply star_one.
    apply step_native_unary2; auto.
    }
  }

  {
  simpsub.
  cbn.
  do2 3 split; auto; try prove_hygiene.
  exists (g x).
  split.
    {
    apply (star_trans _ _ _ (native_unary g' (native_elem (f1 x')))).
      {
      apply (star_map' _ _ (native_unary g')); auto using step_native_unary1.
      }
    apply star_one.
    rewrite -> Heq', <- Heq.
    apply step_native_unary2; auto.
    }

    {
    apply (star_trans _ _ _ (native_unary g' (native_elem (f1 x')))).
      {
      apply (star_map' _ _ (native_unary g')); auto using step_native_unary1.
      }
    apply star_one.
    rewrite -> Heq', <- Heq.
    apply step_native_unary2; auto.
    }
  }

  {
  simpsub.
  cbn.
  do2 3 split; auto; try prove_hygiene.
  exists (g x).
  split.
    {
    apply (star_trans _ _ _ (native_unary g' (native_elem (f1 x'')))).
      {
      apply (star_map' _ _ (native_unary g')); auto using step_native_unary1.
      }
    apply star_one.
    rewrite <- Heq.
    apply step_native_unary2; auto.
    }

    {
    apply (star_trans _ _ _ (native_unary g' (native_elem (f1 x'')))).
      {
      apply (star_map' _ _ (native_unary g')); auto using step_native_unary1.
      }
    apply star_one.
    rewrite <- Heq.
    apply step_native_unary2; auto.
    }
  }
Qed.


Lemma sound_native_binary :
  forall A1 A2 A3 f1 f2 f3 (g : A1 -> A2 -> A3) (g' : native -> native -> option native),
    (forall x y, g' (f1 x) (f2 y) = Some (f3 (g x y)))
    -> forall G m n p q,
         pseq G (deq m p (nativetp A1 f1))
         -> pseq G (deq n q (nativetp A2 f2))
         -> pseq G (deq (native_binary g' m n) (native_binary g' p q) (nativetp A3 f3)).
Proof.
intros A1 A2 A3 f1 f2 f3 g g' Hg G m n p q.
revert G.
refine (seq_pseq 0 2 [] _ [] _ _ _); cbn.
intros G Hseqm Hseqn.
rewrite -> seq_deq in Hseqm, Hseqn |- *.
intros i s s' Hs.
so (Hseqm _ _ _ Hs) as (R & Hl1 & _ & Hm & Hp & Hmp).
simpsubin Hl1.
invert (basic_value_inv _#6 (value_nativetp _ _) Hl1).
intros <-.
so (Hseqn _ _ _ Hs) as (R & Hl2 & _ & Hn & Hq & Hnq).
simpsubin Hl2.
invert (basic_value_inv _#6 (value_nativetp _ _) Hl2).
intros <-.
cbn in Hm, Hp, Hmp, Hn, Hq, Hnq.
decompose Hm.
intros _ Hclml Hclmr x Hml Hmr.
decompose Hp.
intros _ Hclpl Hclpr x' Hpl Hpr.
decompose Hmp.
intros _ _ _ x'' Hml' Hpr'.
so (determinism_eval _#4 (conj Hml value_native_elem) (conj Hml' value_native_elem)) as Heq.
injectionc Heq.
intro Heq1.
so (determinism_eval _#4 (conj Hpr value_native_elem) (conj Hpr' value_native_elem)) as Heq.
injectionc Heq.
intro Heq1'.
decompose Hn.
intros _ Hclnl Hclnr y Hnl Hnr.
decompose Hq.
intros _ Hclql Hclqr y' Hql Hqr.
decompose Hnq.
intros _ _ _ y'' Hnl' Hqr'.
so (determinism_eval _#4 (conj Hnl value_native_elem) (conj Hnl' value_native_elem)) as Heq.
injectionc Heq.
intro Heq2.
so (determinism_eval _#4 (conj Hqr value_native_elem) (conj Hqr' value_native_elem)) as Heq.
injectionc Heq.
intros Heq2'.
exists (iubase (native_urel A3 f3 stop i)).
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_native.
  }

  {
  apply interp_eval_refl.
  apply interp_native.
  }

  {
  simpsub.
  cbn.
  do2 3 split; auto; try prove_hygiene.
  exists (g x y).
  split.
    {
    apply (star_trans _ _ _ (native_binary g' (native_elem (f1 x)) (subst s n))).
      {
      apply (star_map' _ _ (fun z => native_binary g' z _)); auto using step_native_binary1.
      }
    eapply star_step.
      {
      apply step_native_binary2.
      }
    apply (star_trans _ _ _ (native_unary (g' (f1 x)) (native_elem (f2 y)))).
      {
      apply (star_map' _ _ (native_unary (g' (f1 x)))); auto using step_native_unary1.
      }
    apply star_one.
    apply step_native_unary2; auto.
    }

    {
    apply (star_trans _ _ _ (native_binary g' (native_elem (f1 x)) (subst s' n))).
      {
      apply (star_map' _ _ (fun z => native_binary g' z _)); auto using step_native_binary1.
      }
    eapply star_step.
      {
      apply step_native_binary2.
      }
    apply (star_trans _ _ _ (native_unary (g' (f1 x)) (native_elem (f2 y)))).
      {
      apply (star_map' _ _ (native_unary (g' (f1 x)))); auto using step_native_unary1.
      }
    apply star_one.
    apply step_native_unary2; auto.
    }
  }

  {
  simpsub.
  cbn.
  do2 3 split; auto; try prove_hygiene.
  exists (g x y).
  split.
    {
    apply (star_trans _ _ _ (native_binary g' (native_elem (f1 x')) (subst s q))).
      {
      apply (star_map' _ _ (fun z => native_binary g' z _)); auto using step_native_binary1.
      }
    eapply star_step.
      {
      apply step_native_binary2.
      }
    apply (star_trans _ _ _ (native_unary (g' (f1 x')) (native_elem (f2 y')))).
      {
      apply (star_map' _ _ (native_unary (g' (f1 x')))); auto using step_native_unary1.
      }
    apply star_one.
    apply step_native_unary2.
    rewrite -> Heq1', <- Heq1.
    rewrite -> Heq2', <- Heq2.
    auto.
    }

    {
    apply (star_trans _ _ _ (native_binary g' (native_elem (f1 x')) (subst s' q))).
      {
      apply (star_map' _ _ (fun z => native_binary g' z _)); auto using step_native_binary1.
      }
    eapply star_step.
      {
      apply step_native_binary2.
      }
    apply (star_trans _ _ _ (native_unary (g' (f1 x')) (native_elem (f2 y')))).
      {
      apply (star_map' _ _ (native_unary (g' (f1 x')))); auto using step_native_unary1.
      }
    apply star_one.
    apply step_native_unary2.
    rewrite -> Heq1', <- Heq1.
    rewrite -> Heq2', <- Heq2.
    auto.
    }
  }

  {
  simpsub.
  cbn.
  do2 3 split; auto; try prove_hygiene.
  exists (g x y).
  split.
    {
    apply (star_trans _ _ _ (native_binary g' (native_elem (f1 x'')) (subst s n))).
      {
      apply (star_map' _ _ (fun z => native_binary g' z _)); auto using step_native_binary1.
      }
    eapply star_step.
      {
      apply step_native_binary2.
      }
    apply (star_trans _ _ _ (native_unary (g' (f1 x'')) (native_elem (f2 y'')))).
      {
      apply (star_map' _ _ (native_unary (g' (f1 x'')))); auto using step_native_unary1.
      }
    apply star_one.
    apply step_native_unary2.
    rewrite <- Heq1.
    rewrite <- Heq2.
    auto.
    }

    {
    apply (star_trans _ _ _ (native_binary g' (native_elem (f1 x'')) (subst s' q))).
      {
      apply (star_map' _ _ (fun z => native_binary g' z _)); auto using step_native_binary1.
      }
    eapply star_step.
      {
      apply step_native_binary2.
      }
    apply (star_trans _ _ _ (native_unary (g' (f1 x'')) (native_elem (f2 y'')))).
      {
      apply (star_map' _ _ (native_unary (g' (f1 x'')))); auto using step_native_unary1.
      }
    apply star_one.
    apply step_native_unary2.
    rewrite <- Heq1.
    rewrite <- Heq2.
    auto.
    }
  }
Qed.


(* Redundant *)
Lemma sound_native_bool_elim_pre :
  forall G m n,
    seq G (deq m n (nativetp bool native_bool))
    -> seq G (deq m n booltp).
Proof.
intros G m p Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
so (Hseq i s s' Hs) as (R & Hl & _ & Hm & Hp & Hmp).
simpsubin Hl.
invert (basic_value_inv _#6 (value_nativetp _ _) Hl).
intros <-.
cbn in Hm, Hp, Hmp.
decompose Hm.
intros _ Hclml Hclmr x Hml Hmr.
decompose Hp.
intros _ Hclpl Hclpr x' Hpl Hpr.
decompose Hmp.
intros _ _ _ x'' Hml' Hpr'.
so (determinism_eval _#4 (conj Hml value_native_elem) (conj Hml' value_native_elem)) as Heq.
injectionc Heq.
intros <-.
so (determinism_eval _#4 (conj Hpr value_native_elem) (conj Hpr' value_native_elem)) as Heq.
injectionc Heq.
intros ->.
exists (iubase (SemanticsSimple.bool_urel stop i)).
simpsub.
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_bool.
  }

  {
  apply interp_eval_refl.
  apply interp_bool.
  }

  {
  do2 3 split; auto.
  destruct x.
    {
    left; auto.
    }

    {
    right; auto.
    }
  }

  {
  do2 3 split; auto.
  destruct x.
    {
    left; auto.
    }

    {
    right; auto.
    }
  }

  {
  do2 3 split; auto.
  destruct x.
    {
    left; auto.
    }

    {
    right; auto.
    }
  }
Qed.


(* Redundant *)
Lemma sound_native_bool_elim :
  forall G m n,
    pseq G (deq m n (nativetp bool native_bool))
    -> pseq G (deq m n booltp).
Proof.
intros G m p.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
apply sound_native_bool_elim_pre; auto.
Qed.


Lemma sound_native_left_pre :
  forall A f G m n c,
    hygiene (permit (ctxpred G)) m
    -> hygiene (permit (ctxpred G)) n
    -> hygiene (permit (ctxpred G)) c
    -> (forall x, seq G (deq (subst1 (native_elem (f x)) m) (subst1 (native_elem (f x)) n) (subst1 (native_elem (f x)) c)))
    -> seq (cons (hyp_tm (nativetp A f)) G) (deq m n c).
Proof.
intros A f G m p c Hclm Hclp Hclc Hseq.
rewrite -> seq_deq.
intros i ss ss' Hss.
invert Hss.
intros n q s s' Hs Hm Hleft Hright <- <-.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
invertc Hm.
intros R Hl _ Hnq.
simpsubin Hl.
invert (basic_value_inv _#6 (value_nativetp _ _) Hl).
intros <-.
cbn in Hnq.
decompose Hnq.
intros _ Hcln Hclq x Hstepsn Hstepsq.
so (Hseq x) as Hseqx.
rewrite -> seq_deq in Hseqx.
so (Hseqx _ _ _ Hs) as (R & Hcl & Hcr & Hm & Hp & Hmp).
exists R.
simpsub.
simpsubin Hcl.
simpsubin Hcr.
simpsubin Hm.
simpsubin Hp.
simpsubin Hmp.
do2 4 split.
  {
  apply (basic_equiv _#4 (subst (dot (native_elem (f x)) s) c)); auto.
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    }

    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm.
    apply steps_equiv; auto.
    }
  }

  {
  apply (basic_equiv _#4 (subst (dot (native_elem (f x)) s') c)); auto.
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    }

    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm.
    apply steps_equiv; auto.
    }
  }

  {
  refine (urel_equiv _#7 _ _ _ _ Hm).
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    }
    
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    }
    
    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm.
    apply steps_equiv; auto.
    }
    
    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm.
    apply steps_equiv; auto.
    }
  }

  {
  refine (urel_equiv _#7 _ _ _ _ Hp).
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    }
    
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    }
    
    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm.
    apply steps_equiv; auto.
    }
    
    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm.
    apply steps_equiv; auto.
    }
  }

  {
  refine (urel_equiv _#7 _ _ _ _ Hmp).
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    }
    
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    }
    
    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm.
    apply steps_equiv; auto.
    }
    
    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm.
    apply steps_equiv; auto.
    }
  }
Qed.


Lemma sound_native_left :
  forall A f G m n c,
    (forall x, pseq G (deq (subst1 (native_elem (f x)) m) (subst1 (native_elem (f x)) n) (subst1 (native_elem (f x)) c)))
    -> pseq (cons (hyp_tm (nativetp A f)) G) (deq m n c).
Proof.
intros A f G m n c Hseqall.
so (can_hygienej (deq m n c)) as (k1 & Hk1).
so (can_hygienectx (hyp_tm (nativetp A f) :: G)) as (k2 & Hk2).
set (k := max k1 k2).
exists k.
intros j Hj.
rewrite <- app_comm_cons.
apply sound_native_left_pre.
  {
  subst k.
  rewrite -> ctxpred_length.
  rewrite -> app_length.
  rewrite -> length_shut.
  invert Hk1.
  intros Hm _ _.
  eapply hygiene_weaken; eauto.
  intros l H.
  destruct l as [| l].
    {
    unfold permit.
    trivial.
    }
  unfold permit.
  so (Nat.le_max_l k1 k2).
  omega.
  }

  {
  subst k.
  rewrite -> ctxpred_length.
  rewrite -> app_length.
  rewrite -> length_shut.
  invert Hk1.
  intros _ Hn _.
  eapply hygiene_weaken; eauto.
  intros l H.
  destruct l as [| l].
    {
    unfold permit.
    trivial.
    }
  unfold permit.
  so (Nat.le_max_l k1 k2).
  omega.
  }

  {
  subst k.
  rewrite -> ctxpred_length.
  rewrite -> app_length.
  rewrite -> length_shut.
  invert Hk1.
  intros _ _ Hc.
  eapply hygiene_weaken; eauto.
  intros l H.
  destruct l as [| l].
    {
    unfold permit.
    trivial.
    }
  unfold permit.
  so (Nat.le_max_l k1 k2).
  omega.
  }
intros x.
so (Hseqall x) as Hseq.
eapply Unshut.pseq_elim_with_hygiene; eauto.
  {
  invert Hk2.
  intros Hk2' _.
  eapply hygienectx_weaken; eauto.
  intros l Hl.
  so (Nat.le_max_r k1 k2).
  omega.
  }

  {
  invert Hk1.
  intros Hm Hn Hc.
  apply hygienej_deq.
    {
    apply hygiene_subst1.
      {
      apply hygiene_auto; cbn; trivial.
      }
    eapply hygiene_weaken; eauto.
    intros l Hl.
    destruct l as [| l].
      {
      unfold permit.
      trivial.
      }
    unfold permit.
    so (Nat.le_max_l k1 k2).
    omega.
    }

    {
    apply hygiene_subst1.
      {
      apply hygiene_auto; cbn; trivial.
      }
    eapply hygiene_weaken; eauto.
    intros l Hl.
    destruct l as [| l].
      {
      unfold permit.
      trivial.
      }
    unfold permit.
    so (Nat.le_max_l k1 k2).
    omega.
    }

    {
    apply hygiene_subst1.
      {
      apply hygiene_auto; cbn; trivial.
      }
    eapply hygiene_weaken; eauto.
    intros l Hl.
    destruct l as [| l].
      {
      unfold permit.
      trivial.
      }
    unfold permit.
    so (Nat.le_max_l k1 k2).
    omega.
    }
  }
Qed.


Lemma sound_nattp_left_pre :
  forall G m n c,
    hygiene (permit (ctxpred G)) m
    -> hygiene (permit (ctxpred G)) n
    -> hygiene (permit (ctxpred G)) c
    -> (forall x, seq G (deq (subst1 (natlit x) m) (subst1 (natlit x) n) (subst1 (natlit x) c)))
    -> seq (cons (hyp_tm nattp) G) (deq m n c).
Proof.
intros G m p c Hclm Hclp Hclc Hseq.
rewrite -> seq_deq.
intros i ss ss' Hss.
invert Hss.
intros n q s s' Hs Hm Hleft Hright <- <-.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
invertc Hm.
intros Rn Hl _ Hnq.
simpsubin Hl.
so (interp_nattp_invert _#7 Hl Hnq) as (x & Hn & Hq).
so (Hseq x) as Hseqx.
rewrite -> seq_deq in Hseqx.
so (Hseqx _ _ _ Hs) as (R & Hcl & Hcr & Hm & Hp & Hmp).
exists R.
simpsub.
simpsubin Hcl.
simpsubin Hcr.
simpsubin Hm.
simpsubin Hp.
simpsubin Hmp.
so (natinterp_closed _ _ Hn) as Hcln.
so (natinterp_closed _ _ Hq) as Hclq.
so (natinterp_invert _ _ Hn) as Hequivn.
so (natinterp_invert _ _ Hq) as Hequivq.
do2 4 split.
  {
  apply (basic_equiv _#4 (subst (dot (natlit x) s) c)); auto.
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    }

    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm; auto.
    }
  }

  {
  apply (basic_equiv _#4 (subst (dot (natlit x) s') c)); auto.
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    }

    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm; auto.
    }
  }

  {
  refine (urel_equiv _#7 _ _ _ _ Hm).
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    }
    
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    }
    
    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm; auto.
    }
    
    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm; auto.
    }
  }

  {
  refine (urel_equiv _#7 _ _ _ _ Hp).
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    }
    
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    }
    
    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm; auto.
    }
    
    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm; auto.
    }
  }

  {
  refine (urel_equiv _#7 _ _ _ _ Hmp).
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    }
    
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    }
    
    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm; auto.
    }
    
    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot; auto using equivsub_refl.
    apply equiv_symm; auto.
    }
  }
Qed.


Lemma sound_nattp_left :
  forall G m n c,
    (forall x, pseq G (deq (subst1 (natlit x) m) (subst1 (natlit x) n) (subst1 (natlit x) c)))
    -> pseq (cons (hyp_tm nattp) G) (deq m n c).
Proof.
intros G m n c Hseqall.
so (can_hygienej (deq m n c)) as (k1 & Hk1).
so (can_hygienectx (hyp_tm nattp :: G)) as (k2 & Hk2).
set (k := max k1 k2).
exists k.
intros j Hj.
rewrite <- app_comm_cons.
apply sound_nattp_left_pre.
  {
  subst k.
  rewrite -> ctxpred_length.
  rewrite -> app_length.
  rewrite -> length_shut.
  invert Hk1.
  intros Hm _ _.
  eapply hygiene_weaken; eauto.
  intros l H.
  destruct l as [| l].
    {
    unfold permit.
    trivial.
    }
  unfold permit.
  so (Nat.le_max_l k1 k2).
  omega.
  }

  {
  subst k.
  rewrite -> ctxpred_length.
  rewrite -> app_length.
  rewrite -> length_shut.
  invert Hk1.
  intros _ Hn _.
  eapply hygiene_weaken; eauto.
  intros l H.
  destruct l as [| l].
    {
    unfold permit.
    trivial.
    }
  unfold permit.
  so (Nat.le_max_l k1 k2).
  omega.
  }

  {
  subst k.
  rewrite -> ctxpred_length.
  rewrite -> app_length.
  rewrite -> length_shut.
  invert Hk1.
  intros _ _ Hc.
  eapply hygiene_weaken; eauto.
  intros l H.
  destruct l as [| l].
    {
    unfold permit.
    trivial.
    }
  unfold permit.
  so (Nat.le_max_l k1 k2).
  omega.
  }
intros x.
so (Hseqall x) as Hseq.
eapply Unshut.pseq_elim_with_hygiene; eauto.
  {
  invert Hk2.
  intros Hk2' _.
  eapply hygienectx_weaken; eauto.
  intros l Hl.
  so (Nat.le_max_r k1 k2).
  omega.
  }

  {
  invert Hk1.
  intros Hm Hn Hc.
  apply hygienej_deq.
    {
    apply hygiene_subst1.
      {
      eapply hygiene_weaken; eauto using natlit_closed.
      intros l Hl.
      destruct Hl.
      }
    eapply hygiene_weaken; eauto.
    intros l Hl.
    destruct l as [| l].
      {
      unfold permit.
      trivial.
      }
    unfold permit.
    so (Nat.le_max_l k1 k2).
    omega.
    }

    {
    apply hygiene_subst1.
      {
      eapply hygiene_weaken; eauto using natlit_closed.
      intros l Hl.
      destruct Hl.
      }
    eapply hygiene_weaken; eauto.
    intros l Hl.
    destruct l as [| l].
      {
      unfold permit.
      trivial.
      }
    unfold permit.
    so (Nat.le_max_l k1 k2).
    omega.
    }

    {
    apply hygiene_subst1.
      {
      eapply hygiene_weaken; eauto using natlit_closed.
      intros l Hl.
      destruct Hl.
      }
    eapply hygiene_weaken; eauto.
    intros l Hl.
    destruct l as [| l].
      {
      unfold permit.
      trivial.
      }
    unfold permit.
    so (Nat.le_max_l k1 k2).
    omega.
    }
  }
Qed.


Lemma sound_native_contradiction :
  forall A f x y G p q c,
    f x <> f y
    -> pseq G (deq (native_elem (f x)) (native_elem (f y)) (nativetp A f))
    -> pseq G (deq p q c).
Proof.
intros A f x y G p q c Hneq.
revert G.
refine (seq_pseq 0 1 [] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
exfalso.
so (Hseq _#3 Hs) as (R & Hl & _ & _ & _ & Hm).
simpsubin Hl.
invert (basic_value_inv _#6 (value_nativetp _ _) Hl).
intros <-.
simpsubin Hm.
cbn in Hm.
decompose Hm.
intros _ _ _ z Hx Hy.
so (equiv_eval _#4 (equiv_trans _#4 (steps_equiv _#3 Hx) (equiv_symm _#3 (steps_equiv _#3 Hy))) (conj (star_refl _) value_native_elem)) as (m & (Hym & _) & Hxm).
so (determinism_normal_value _#3 value_native_elem Hym).
subst m.
invert Hxm.
intros _ H.
injectionc H.
intros Heq.
destruct (Hneq Heq).
Qed.


Lemma sound_nativetp_uptype :
  forall A f G,
    pseq G (deq triv triv (uptype (nativetp A f))).
Proof.
intros A f.
refine (seq_pseq 0 0 _ _); cbn.
intro G.
rewrite -> SoundPartialUtil.seq_uptype.
intros i s s' Hs.
exists (iubase (native_urel A f stop i)).
simpsub.
do2 2 split.
  {
  apply interp_eval_refl.
  apply interp_native.
  }

  {
  apply interp_eval_refl.
  apply interp_native.
  }
intros j m m' p p' Happroxm Happroxp Hmp.
destruct Hmp as (Hj & Hmp).
split; auto.
cbn in Hmp |- *.
decompose Hmp.
intros Hj' Hclm Hclp x Hstepsm Hstepsp.
so (Approximation.sapprox_action _#4 Happroxm (conj Hstepsm value_native_elem)) as (v & (Hstepsm' & _) & Hmc).
invertc_mc Hmc.
fold (@native_elem (Candidate.obj stop) (f x)).
intros <-.
so (Approximation.sapprox_action _#4 Happroxp (conj Hstepsp value_native_elem)) as (v & (Hstepsp' & _) & Hmc).
invertc_mc Hmc.
fold (@native_elem (Candidate.obj stop) (f x)).
intros <-.
so (Approximation.sapprox_closed _#3 Happroxm ander) as Hclm'.
so (Approximation.sapprox_closed _#3 Happroxp ander) as Hclp'.
do2 3 split; eauto.
Qed.
