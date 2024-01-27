
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Tactics.
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

Require Import Axioms.
Require Import Spaces.
Require Import Model.
Require Import Truncate.
Require Import Standard.
Require Import SemanticsAll.
Require Import SemanticsPi.
Require Import SemanticsUniv.
Require Import Constructor.
Require Import Spacify.
Require Import ProperDownward.
Require Import ProperLevel.
Require Import Extend.
Require Import ExtendTruncate.
Require Import Equivalence.
Require Import Ceiling.
Require Import Defined.
Require Import PageType.


Local Ltac prove_hygiene :=
  repeat (first [ apply hygiene_shift_permit
                | apply hygiene_sumbool
                | apply hygiene_auto; cbn [row_rect nat_rect]; repeat2 split; auto
                ]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1;
  try (apply hygiene_var; cbn; auto; done).


Lemma extract_parametric :
  forall pg gpg K A i a b (h : level K <<= top),
    K = approx i K
    -> le_page gpg pg
    -> level K <<= cin gpg
    -> spacification gpg i K A
    -> (forall j c d,
          j <= i
          -> rel (den A) j c d
          -> rel (univ_urel the_system j pg) j (subst1 c a) (subst1 d b))
    -> exists (f : space K -n> wiurel_ofe stop),
         forall j,
           j <= i
           -> forall (x : spcar (approx j K)),
                let xt := 
                  (app
                     (fromsp stop gpg (approx j K))
                     (ext (objin (objsome
                                    (expair (approx j K) (std (S j) (approx j K) x))
                                    (le_ord_succ _ _ (le_ord_trans _#3 (approx_level j K) h))))))
                in
                  interp pg true j (subst1 xt a) 
                    (iutruncate (S j) (pi1 f (std (S j) K (embed j K x))))
                  /\
                  interp pg false j (subst1 xt b)
                    (iutruncate (S j) (pi1 f (std (S j) K (embed j K x)))).
Proof.
intros pg gpg K A i a b fit HeqK Hle Hlev Hspacify Hact.
exploit (nearrow_formation gpg pg K (qtype (cin pg)) i
           (subst (dot (app (fromsp stop gpg K) (var 0)) sh1) (cty a))
           (subst (dot (app (fromsp stop gpg K) (var 0)) sh1) (cty b)) fit) as H; auto.
  {
  intros j c d Hj Hcd.
  simpsub.
  exploit (Hact j (app (fromsp stop gpg K) c) (app (fromsp stop gpg K) d)) as H; auto.
    {
    exact (arrow_action_app _#9 (urel_downward_leq _#6 Hj (spacification_fromsp _#4 Hspacify)) Hcd).
    }
  destruct H as (_ & R & Hl & Hr).
  rewrite -> sint_unroll in Hl, Hr.
  so (interp_level_internal _#5 (cin_stop pg) Hl) as (B & ->).
  cbn.
  unfold con_action.
  cbn [approx].
  exists B.
  split.
    {
    apply cinterp_eval_refl.
    apply interp_cty; auto.
    }

    {
    apply cinterp_eval_refl.
    apply interp_cty; auto.
    }
  }
destruct H as (f & Hstdf & Hf).
set (f' := nearrow_compose (extend_iurel_ne (cin_stop pg)) f).
exists f'.
intros j Hj x xt.
set (xt' := 
       (ext (objin (objsome
                      (expair 
                         (approx j K) (std (S j) (approx j K) x))
                      (le_ord_succ _ _
                         (le_ord_trans _#3 (approx_level _ _) fit)))))) in *.
assert (rel (con_urel gpg K) j xt' xt') as Hxt'.
  {
  clear Hf.
  unfold xt'.
  apply con_urel_raise.
  exists (proj j (approx j K) (std (S j) (approx j K) x)).
  split.
    {
    relquest.
      {
      apply cinterp_eval_refl.
      apply interp_ext.
      cbn.
      eapply le_ord_trans; eauto using approx_level.
      }
    unfold projc, stdc.
    cbn.
    f_equal.
    rewrite -> std_idem; auto.
    }

    {
    relquest.
      {
      apply cinterp_eval_refl.
      apply interp_ext.
      cbn.
      eapply le_ord_trans; eauto using approx_level.
      }
    unfold projc, stdc.
    cbn.
    f_equal.
    rewrite -> std_idem; auto.
    }
  }
split.
  {
  so (Hf (embed j K x) ander j Hj andel) as H; clear Hf.
  simpsubin H.
  invert (cbasic_value_inv _#6 value_cty H); clear H.
  intros R Hint Heq.
  cbn in Heq.
  injectionT Heq.
  intros ->.
  subst xt.
  rewrite -> proj_std in Hint; auto.
  rewrite -> proj_embed in Hint.
  unfold f'.
  cbn.
  rewrite -> iutruncate_extend_iurel.
  exploit (Hact j (app (fromsp stop gpg K) xt') (app (fromsp stop gpg K) xt')) as H1; auto.
    {
    exact (arrow_action_app _#9 (urel_downward_leq _#6 Hj (spacification_fromsp _#4 Hspacify)) Hxt').
    }
  exploit (Hact j (app (fromsp stop gpg (approx j K)) xt') (app (fromsp stop gpg K) xt')) as H2; auto.
    {
    destruct Hspacify as (_ & _ & Hfrom & _).
    so (Hfrom j j i Hj (le_refl _) Hj) as Hfrom'.
    rewrite <- HeqK in Hfrom'.
    exact (arrow_action_app _#9 Hfrom' Hxt').
    }
  destruct H1 as (_ & R & Hint' & Hright).
  rewrite -> sint_unroll in Hint', Hright.
  so (basic_fun _#7 Hint Hint'); subst R; clear Hint Hint'.
  destruct H2 as (_ & R & Hint & Hright').
  rewrite -> sint_unroll in Hint, Hright'.
  so (basic_fun _#7 Hright Hright'); subst R.
  exact Hint.
  }

  {
  so (Hf (embed j K x) ander j Hj ander) as H; clear Hf.
  simpsubin H.
  invert (cbasic_value_inv _#6 value_cty H); clear H.
  intros R Hint Heq.
  cbn in Heq.
  injectionT Heq.
  intros ->.
  subst xt.
  rewrite -> proj_std in Hint; auto.
  rewrite -> proj_embed in Hint.
  unfold f'.
  cbn.
  rewrite -> iutruncate_extend_iurel.
  exploit (Hact j (app (fromsp stop gpg K) xt') (app (fromsp stop gpg K) xt')) as H1; auto.
    {
    exact (arrow_action_app _#9 (urel_downward_leq _#6 Hj (spacification_fromsp _#4 Hspacify)) Hxt').
    }
  exploit (Hact j (app (fromsp stop gpg K) xt') (app (fromsp stop gpg (approx j K)) xt')) as H2; auto.
    {
    destruct Hspacify as (_ & _ & Hfrom & _).
    so (Hfrom j i j Hj Hj (le_refl _)) as Hfrom'.
    rewrite <- HeqK in Hfrom'.
    exact (arrow_action_app _#9 Hfrom' Hxt').
    }
  destruct H1 as (_ & R & Hleft & Hint').
  rewrite -> sint_unroll in Hint', Hleft.
  so (basic_fun _#7 Hint Hint'); subst R; clear Hint Hint'.
  destruct H2 as (_ & R & Hleft' & Hint).
  rewrite -> sint_unroll in Hint, Hleft'.
  so (basic_fun _#7 Hleft Hleft'); subst R.
  exact Hint.
  }
Qed.


Lemma extract_parametric_multi :
  forall pg gpg K A i a a' b b' (h : level K <<= top),
    K = approx i K
    -> le_page gpg pg
    -> level K <<= cin gpg
    -> spacification gpg i K A
    -> (forall j c d,
          j <= i
          -> rel (den A) j c d
          -> exists R,
               interp pg true j (subst1 c a) R
               /\ interp pg false j (subst1 d a') R
               /\ interp pg true j (subst1 c b) R
               /\ interp pg false j (subst1 d b') R)
    -> exists (f : space K -n> wiurel_ofe stop),
         forall j,
           j <= i
           -> forall (x : spcar (approx j K)),
                let xt := 
                  app
                    (fromsp stop gpg (approx j K))
                    (ext (objin (objsome
                                   (expair (approx j K) (std (S j) (approx j K) x))
                                   (le_ord_succ _ _ (le_ord_trans _#3 (approx_level j K) h)))))
                in
                  interp pg true j (subst1 xt a) 
                    (iutruncate (S j) (pi1 f (std (S j) K (embed j K x))))
                  /\
                  interp pg false j (subst1 xt a') 
                    (iutruncate (S j) (pi1 f (std (S j) K (embed j K x))))
                  /\
                  interp pg true j (subst1 xt b)
                    (iutruncate (S j) (pi1 f (std (S j) K (embed j K x))))
                  /\
                  interp pg false j (subst1 xt b')
                    (iutruncate (S j) (pi1 f (std (S j) K (embed j K x)))).
Proof.
intros pg gpg K A i a a' b b' h HeqK Hle Hlev Hspacify Hact.
exploit (extract_parametric pg gpg K A i a a' h) as (fa & Hfa); auto.
  {
  intros j c d Hj Hcd.
  so (Hact j c d Hj Hcd) as (R & Ha & Ha' & _).
  split; auto.
  exists R.
  rewrite -> sint_unroll.
  auto.
  }
exploit (extract_parametric pg gpg K A i b b' h) as (fb & Hfb); auto.
  {
  intros j c d Hj Hcd.
  so (Hact j c d Hj Hcd) as (R & _ & _ & Hb & Hb').
  split; auto.
  exists R.
  rewrite -> sint_unroll.
  auto.
  }
exploit (extract_parametric pg gpg K A i a b' h) as (fab & Hfab); auto.
  {
  intros j c d Hj Hcd.
  so (Hact j c d Hj Hcd) as (R & Ha & _ & _ & Hb').
  split; auto.
  exists R.
  rewrite -> sint_unroll.
  auto.
  }
exists fa.
intros j Hj x xt.
so (Hfa j Hj x) as (Ha & Ha').
so (Hfb j Hj x) as (Hb & Hb').
so (Hfab j Hj x) as (Hal & Hbl).
clear Hfa Hfb Hfab.
fold xt in Ha, Ha', Hb, Hb', Hal, Hbl.
assert (iutruncate (S j) (pi1 fa (std (S j) K (embed j K x)))
        =
        iutruncate (S j) (pi1 fb (std (S j) K (embed j K x)))) as Heq.
  {
  so (basic_fun _#7 Ha Hal) as Heq1.
  so (basic_fun _#7 Hbl Hb') as Heq2.
  etransitivity; eauto.
  }
do2 2 split; auto.
rewrite -> !Heq.
split; auto.
Qed.


Lemma sound_all_formation :
  forall G glv k l a b,
    pseq G (deq k l (kind glv))
    -> pseq (cons (hyp_tm k) G) (deqtype a b)
    -> pseq G (deqtype (all glv k a) (all glv l b)).
Proof.
intros G glv k l a b.
revert G.
refine (seq_pseq 0 2 [] _ [_] _ _ _); cbn.
intros G Hseqkl Hseqab.
rewrite -> seq_eqkind in Hseqkl.
rewrite -> seq_eqtype in Hseqab.
rewrite -> seq_eqtype.
intros i s s' Hs.
so (Hseqkl i s s' Hs) as (gpg & K & R & h & Hglvl & Hglvr & Hkl & Hkr & Hll & Hlr & Hklt & Hkrt & Hllt & Hlrt).
simpsub.
so (kinterp_level_bound _#5 Hkl) as HlevK.
so (le_ord_trans _#3 HlevK (cin_top gpg)) as HlevKt.
exploit (extract_parametric_multi toppg gpg K R i 
           (subst (under 1 s) a) (subst (under 1 s') a) (subst (under 1 s) b) (subst (under 1 s') b)
           HlevKt); auto using toppg_max.
  {
  eapply kbasic_impl_approx; eauto.
  }

  {
  eapply spacify; eauto using interp_increase, toppg_max.
  }

  {
  intros j c d Hj Hcd.
  exploit (Hseqab j (dot c s) (dot d s')) as H.
    {
    apply pwctx_cons_tm_seq; eauto using pwctx_downward, seqhyp_tm_leq, interp_increase, toppg_max.
    intros j' t t' Ht.
    so (Hseqkl _#3 Ht) as (pg' & _ & R' & h' & _ & _ & _ & _ & _ & _ & Hal & Har &_).
    eauto.
    }
  destruct H as (R' & Hal & Har & Hbl & Hbr).
  exists R'; simpsub; auto.
  }
destruct H as (f & Hf).
clear Hseqab.
exists (iuall stop K (std (S i) (qarrow K (qtype stop)) f)).
do2 3 split.
  {
  apply interp_eval_refl.
  apply (interp_all _#7 gpg _ _ HlevKt); auto using toppg_max.
  intros j Hj x.
  exact (Hf j Hj x andel).
  }

  {
  apply interp_eval_refl.
  apply (interp_all _#7 gpg _ _ HlevKt); auto using toppg_max.
  intros j Hj x.
  exact (Hf j Hj x anderl).
  }

  {
  apply interp_eval_refl.
  apply (interp_all _#7 gpg _ _ HlevKt); auto using toppg_max.
  intros j Hj x.
  exact (Hf j Hj x anderrl).
  }

  {
  apply interp_eval_refl.
  apply (interp_all _#7 gpg _ _ HlevKt); auto using toppg_max.
  intros j Hj x.
  exact (Hf j Hj x anderrr).
  }
Qed.


Lemma sound_all_formation_univ :
  forall G glv lv k l a b,
    pseq G (deq k l (kind glv))
    -> pseq (cons (hyp_tm k) G) (deq a b (univ (subst sh1 lv)))
    -> pseq G (deq lv lv pagetp)
    -> pseq G (deq triv triv (leqpagetp glv lv))
    -> pseq G (deq (all glv k a) (all glv l b) (univ lv)).
Proof.
intros G glv lv k l a b.
revert G.
refine (seq_pseq 0 4 [] _ [_] _ [] _ [] _ _ _).
cbn.
intros G Hseqkl Hseqab Hseqlv Hseqleq.
rewrite -> seq_eqkind in Hseqkl.
rewrite -> seq_univ.
rewrite -> seq_univ in Hseqab.
invertc Hseqlv; intro Hseqlv.
invertc Hseqleq; intro Hseqleq.
intros i s s' Hs.
so (Hseqkl i s s' Hs) as (gpg & K & R & h & Hglvl & Hglvr & Hkl & Hkr & Hll & Hlr & Hklt & Hkrt & Hllt & Hlrt).
simpsub.
so (kinterp_level_bound _#5 Hkl) as HlevK.
eassert _ as H; [refine (seq_pagetp_invert G lv _ _#3 Hs) |].
  {
  intros j t t' Ht.
  so (Hseqlv _#3 Ht) as (Q & HQ & _ & Hlv & _).
  eauto.
  }
destruct H as (pg & Hlvl & Hlvr); clear Hseqlv.
eassert _ as Hle; [refine (seq_leqpagetp_invert G glv lv triv _ _#5 Hs Hglvl Hlvl) |].
  {
  intros j t t' Ht.
  so (Hseqleq _#3 Ht) as (Q & HQ & _ & Hlv & _).
  eauto.
  }
clear Hseqleq.
so (le_ord_trans _#3 HlevK (cin_top gpg)) as HlevKt.
exploit (extract_parametric_multi pg gpg K R i 
           (subst (under 1 s) a) (subst (under 1 s') a) (subst (under 1 s) b) (subst (under 1 s') b)
           HlevKt); auto.
  {
  eapply kbasic_impl_approx; eauto.
  }

  {
  eapply spacify; eauto using interp_increase, toppg_max.
  }

  {
  intros j c d Hj Hcd.
  exploit (Hseqab j (dot c s) (dot d s')) as H.
    {
    apply pwctx_cons_tm_seq; eauto using pwctx_downward, seqhyp_tm_leq, interp_increase, toppg_max.
    intros j' t t' Ht.
    so (Hseqkl _#3 Ht) as (pg' & _ & R' & h' & _ & _ & _ & _ & _ & _ & Hal & Har &_).
    eauto.
    }
  destruct H as (pg' & R' & Hlvl' & _ & Hal & Har & Hbl & Hbr).
  simpsubin Hlvl'.
  so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
  exists R'; simpsub; auto.
  }
destruct H as (f & Hf).
clear Hseqab.
exists pg.
exists (iuall stop K (std (S i) (qarrow K (qtype stop)) f)).
do2 5 split; auto.
  {
  apply interp_eval_refl.
  apply (interp_all _#7 gpg _ _ HlevKt); auto.
  intros j Hj x.
  exact (Hf j Hj x andel).
  }

  {
  apply interp_eval_refl.
  apply (interp_all _#7 gpg _ _ HlevKt); auto.
  intros j Hj x.
  exact (Hf j Hj x anderl).
  }

  {
  apply interp_eval_refl.
  apply (interp_all _#7 gpg _ _ HlevKt); auto.
  intros j Hj x.
  exact (Hf j Hj x anderrl).
  }

  {
  apply interp_eval_refl.
  apply (interp_all _#7 gpg _ _ HlevKt); auto.
  intros j Hj x.
  exact (Hf j Hj x anderrr).
  }
Qed.


Lemma sound_all_intro :
  forall G lv k a m n,
    pseq G (deq k k (kind lv))
    -> pseq (cons (hyp_tm k) G) (deq (subst sh1 m) (subst sh1 n) a)
    -> pseq G (deq m n (all lv k a)).
Proof.
intros G lv k a m n.
revert G.
refine (seq_pseq 0 2 [] _ [_] _ _ _); cbn.
intros G Hseqk Hseqmn.
rewrite -> seq_eqkind in Hseqk.
invertc Hseqmn; intro Hseqmn.
apply seq_i.
intros i s s' Hs.
so (Hseqk i s s' Hs) as (pg & K & R & h & Hlvl & Hlvr & Hkl & Hkr & _ & _ & Hklt & Hkrt & _).
so (kinterp_level_bound _#5 Hkl) as HlevK.
so (le_ord_trans _#3 HlevK (cin_top pg)) as HlevKt.
exploit (extract_parametric toppg pg K R i 
           (subst (under 1 s) a) (subst (under 1 s') a) HlevKt); auto using toppg_max.
  {
  eapply kbasic_impl_approx; eauto.
  }

  {
  eapply spacify; eauto using interp_increase, toppg_max.
  }

  {
  intros j c d Hj Hcd.
  exploit (Hseqmn j (dot c s) (dot d s')) as H.
    {
    apply pwctx_cons_tm_seq; eauto using pwctx_downward, seqhyp_tm_leq, interp_increase, toppg_max.
    intros j' t t' Ht.
    so (Hseqk _#3 Ht) as (pg' & _ & R' & h' & _ & _ & _ & _ & _ & _ & Hal & Har &_).
    eauto.
    }
  destruct H as (R' & Hal & Har & _).
  split; auto.
  exists R'.
  rewrite -> sint_unroll.
  simpsub.
  auto.
  }
destruct H as (f & Hf).
exists (iuall stop K (std (S i) (qarrow K (qtype stop)) f)).
unfold iuall.
rewrite -> den_iubase.
simpsub.
so (seqctx_impl_closub _#4 (pwctx_impl_seqctx _#4 Hs)) as (Hcls & Hcls').
set (xt := fun j x =>
       app (fromsp stop pg (approx j K))
         (ext (objin (objsome
                        (expair (approx j K) (std (S j) (approx j K) x))
                        (le_ord_succ _ _ (le_ord_trans _#3 (approx_level j K) HlevKt)))))).
assert (forall j (x : spcar (approx j K)),
          j <= i
          -> pwctx j (dot (xt j x) s) (dot (xt j x) s') (cons (hyp_tm k) G)) as Hss.
  {
  clear Hf.
  intros j x Hj.
  apply pwctx_cons_tm_seq; eauto using pwctx_downward.
  2:{
    intros j' t t' Ht.
    so (Hseqk _#3 Ht) as (pg' & _ & R' & h' & _ & _ & _ & _ & _ & _ & Hal & Har &_).
    eauto.
    }
  apply (seqhyp_tm _#5 (iutruncate (S j) R)).
    {
    apply (basic_downward _#3 i); auto.
    eapply interp_increase; eauto using toppg_max.
    }

    {
    so (Hseqk _#3 Hs) as (pg' & _ & R' & h' & _ & _ & _ & _ & _ & _ & Hklt'' & Hkrt' & _).
    so (interp_fun _#7 Hklt Hklt''); subst R'.
    apply (basic_downward _#3 i); auto.
    eapply interp_increase; eauto using toppg_max.
    }
  rewrite -> den_iutruncate.
  split; [omega |].
  so (spacify _#6 Hkl (interp_increase _#6 (toppg_max _) Hklt)) as (_ & _ & Hfrom & _).
  subst xt.
  cbn.
  refine (arrow_action_app _#9 (Hfrom j j j Hj (le_refl _) (le_refl _)) _).
  apply con_urel_raise.
  exists (proj j (approx j K) (std (S j) (approx j K) x)).
  split.
    {
    apply cinterp_eval_refl.
    relquest.
      {
      apply interp_ext.
      cbn.
      eapply le_ord_trans; eauto using approx_level.
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
      cbn.
      eapply le_ord_trans; eauto using approx_level.
      }
    unfold projc, stdc; cbn.
    rewrite -> std_idem.
    reflexivity.
    }
  }
assert (forall j x,
          xt j x
          =
          app (fromsp stop pg (approx j K))
            (ext (objin (objsome
                           (expair (approx j K) (std (S j) (approx j K) x))
                           (le_lt_ord_trans _#3 (approx_level j K)
                              (le_ord_succ _ _ HlevKt)))))) as Heqxt.
  {
  intros j x.
  subst xt.
  cbn.
  f_equal.
  f_equal.
  f_equal.
  apply objsome_compat; auto.
  }
assert (forall j x A p q,
          j <= i
          -> interp toppg true j (subst (dot (xt j x) s) a) A
          -> rel (den A) j p q
          -> rel (den (pi1 (std (S i) (qarrow K (qtype stop)) f) (embed j K x))) j p q) as Hintro.
  {
  intros j x A p q Hj Hal Hpq.
  match goal with
  | |- rel ?X _ _ _ =>
      cut (dist (S j) X (den A))
  end.
    {
    intro H.
    rewrite -> (H j); auto.
    }
  so (Hf j Hj x) as (Hal' & _).
  simpsubin Hal'.
  so (basic_fun _#7 Hal Hal'); subst A; clear Hal'.
  rewrite -> std_arrow_is.
  cbn -[dist].
  so (std_type_is (S i) stop) as H.
  unfold std in H.
  cbn in H.
  rewrite -> H; clear H.
  rewrite -> den_iutruncate.
  apply dist_symm.
  eapply dist_trans.
    {
    apply (ceiling_dist _ _ (S i)); omega.
    }
  apply ceiling_nonexpansive.
  apply (pi2 f).
  apply std_dist.
  omega.
  }
do2 4 split.
  {
  apply interp_eval_refl.
  apply (interp_all _#7 pg _ _ HlevKt); eauto using toppg_max, pginterp_cin_top.
  intros j Hj x.
  exact (Hf j Hj x andel).
  }

  {
  apply interp_eval_refl.
  apply (interp_all _#7 pg _ _ HlevKt); eauto using toppg_max, pginterp_cin_top.
  intros j Hj x.
  exact (Hf j Hj x ander).
  }

  {
  intros j x Hj.
  so (Hseqmn j _ _ (Hss j x Hj)) as (A & Hal & _ & Hm & _).
  simpsubin Hm.
  eapply Hintro; eauto.
  }

  {
  intros j x Hj.
  so (Hseqmn j _ _ (Hss j x Hj)) as (A & Hal & _ & _ & Hn & _).
  simpsubin Hn.
  eapply Hintro; eauto.
  }

  {
  intros j x Hj.
  so (Hseqmn j _ _ (Hss j x Hj)) as (A & Hal & _ & _ & _ & Hmn).
  simpsubin Hmn.
  eapply Hintro; eauto.
  }
Qed.


Lemma all_action_app :
  forall i pg K (B : space K -n> siurel_ofe) A (C : spcar K) m n p q,
    spacification pg i K A
    -> all_action stop K (fun x => den (pi1 B x)) i m n
    -> rel (den A) i p q
    -> cinterp pg true i (app (tosp stop pg K) p) (expair K C)
    -> rel (den (pi1 B C)) i m n.
Proof.
intros i pg K B A C m n p q Hspacify Hmn Hpq Hintp.
so (urel_closed _#5 Hpq) as (Hclp & Hclq).
so Hspacify as (HeqK & _).
so (Hmn _ (transport HeqK spcar C) (le_refl _)) as Hrel.
rewrite -> embed_approx' in Hrel.
exact Hrel.
Qed.


Lemma sound_all_elim :
  forall G lv k a m n p,
    pseq G (deq m n (all lv k a))
    -> pseq G (deq p p k)
    -> pseq (cons (hyp_tm k) G) (deqtype a a)
    -> pseq G (deq m n (subst1 p a)).
Proof.
intros G lv k a m n p; revert G.
refine (seq_pseq 0 3 [] _ [] _ [_] _ _ _); cbn.
intros G Hseqmn Hseqp Hseqa.
rewrite -> seq_eqtype in Hseqa.
apply seq_i.
invertc Hseqmn; intro Hseqmn.
invertc Hseqp; intro Hseqp.
intros i s s' Hs.
so (Hseqmn i s s' Hs) as (F & _ & Hall & Hm & Hn & Hmn).
so (Hseqp i s s' Hs) as (B & Hklt & Hkrt & Hp & _).
clear Hseqmn.
simpsubin Hall.
invert (basic_value_inv _#6 value_all Hall).
intros pg K A fit Hlv Hkr Hle Hact <-.
so (spacify _#6 Hkr Hkrt) as Hspacify.
so (spacification_tosp _#4 Hspacify) as Hto.
so (arrow_action_app _#9 Hto Hp) as H.
destruct H as (C & Hcl & Hcr).
so (kbasic_impl_approx _#6 Hkr) as HeqK.
so (kinterp_level_bound _#5 Hkr) as HlevK.
revert C Hcl Hcr.
rewrite <- HeqK.
intros C Hcl Hcr.
set (xt := app (fromsp stop pg K)
             (ext (objin (objsome
                            (expair (approx i K) (std (S i) (approx i K) (transport HeqK spcar C)))
                            (le_ord_succ _ _
                               (le_ord_trans _#3 (approx_level i K) fit)))))).
assert (interp toppg false i (subst (dot xt s') a) (pi1 (std (S i) (qarrow K (qtype stop)) A) C)) as Hxta.
  {
  so (Hact i (le_refl _) (transport HeqK spcar C)) as H.
  simpsubin H.
  force_exact H; clear H.
  unfold interp.
  rewrite <- HeqK at 1.
  f_equal.
  rewrite -> embed_approx'.
  reflexivity.
  }
clear Hact.
assert (forall c d,
          rel (den B) i c d
          -> exists R,
               interp toppg true i (subst (dot c s) a) R
               /\ interp toppg false i (subst (dot d s') a) R) as Hsa.
  {
  intros c d Hcd.
  assert (pwctx i (dot c s) (dot d s') (cons (hyp_tm k) G)) as Hss.
    {
    apply pwctx_cons_tm_seq; auto.
      {
      apply (seqhyp_tm _#5 B); auto.
      }

      {
      intros j t t' Ht.
      so (Hseqp _#3 Ht) as (R' & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqa _ _ _ Hss) as (R & Hl & Hr & _).
  eauto.
  }
clear Hseqa.
assert (rel (den B) i (subst s p) xt) as Hsp_xt.
  {
  assert (rel (con_urel pg K) i 
            (app (tosp stop pg K) (subst s p)) 
            (ext (objin (objsome 
                           (expair (approx i K) (std (S i) (approx i K) (transport HeqK spcar C)))
                           (le_ord_succ _ _ (le_ord_trans _#3 (approx_level _ _) fit)))))) as Htsp_txt.
    {
    exists (proj i K (std (S i) K C)).
    split.
      {
      so (cbasic_impl_form _#6 Hcl) as H.
      unfold projc in H.
      cbn in H.
      rewrite -> H in Hcl.
      exact Hcl.
      }

      {
      apply cinterp_eval_refl.
      relquest.
        {
        apply interp_ext.
        cbn.
        rewrite <- HeqK; auto.
        }
      unfold projc, stdc; cbn.
      apply (expair_compat_transport _#6 (approx_idem _ _)).
      rewrite -> (proj_idem' i K).
      f_equal.
      f_equal.
      rewrite -> std_idem.
      rewrite -> proj_std; auto.
      f_equal.
      symmetry.
      apply transport_symm'.
      apply proj_near'.
      }
    }
  so (arrow_action_app _#9 (spacification_fromsp _#4 Hspacify) Htsp_txt) as Hftsp_xt.
  clear Htsp_txt.
  fold xt in Hftsp_xt.
  so Hspacify as (_ & _ & _ & Hbeta & _).
  so (Hbeta i _ _ (le_refl _) Hp) as Hftsp_sp'; clear Hbeta.
  exact (urel_zigzag _#7 Hp Hftsp_sp' Hftsp_xt).
  }
so (Hsa _ _ Hsp_xt) as Hspa_xta; clear Hsp_xt.
exists (pi1 (std (S i) (qarrow K (qtype stop)) A) C).
simpsub.
do2 4 split.
  {
  destruct Hspa_xta as (R & Hl & Hr).
  so (basic_fun _#7 Hxta (interp_increase _#6 (toppg_max _) Hr)); subst R.
  exact (interp_increase _#6 (toppg_max _) Hl).
  }

  {
  destruct Hspa_xta as (R & Hl & Hr).
  so (basic_fun _#7 Hxta (interp_increase _#6 (toppg_max _) Hr)); subst R.
  so (Hsa _ _  Hp) as (R & Hl' & Hr').
  so (basic_fun _#7 Hl Hl'); subst R.
  exact (interp_increase _#6 (toppg_max _) Hr').
  }

  {
  refine (all_action_app _#10 _ Hm _ _); eauto.
  }

  {
  refine (all_action_app _#10 _ Hn _ _); eauto.
  }

  {
  refine (all_action_app _#10 _ Hmn _ _); eauto.
  }
Qed.


Lemma extract_parametric_tp :
  forall i a b,
    (forall j c d C,
       j <= i
       -> interp toppg true j c C
       -> interp toppg false j d C
       -> exists A,
            interp toppg true j (subst1 c a) A
            /\ interp toppg false j (subst1 d b) A)
    -> exists (f : wiurel_ofe top -n> wiurel_ofe stop),
         f = nearrow_compose (iutruncate_ne (S i)) f
         /\
         forall j,
           j <= i
           -> forall (X : wiurel top),
                interp toppg true j
                  (subst1
                     (extt (objin (objsome (expair (qtype top) X) (succ_increase top))))
                     a)
                  (iutruncate (S j) (pi1 f X))
                /\
                interp toppg false j
                  (subst1
                     (extt (objin (objsome (expair (qtype top) X) (succ_increase top))))
                     b)
                  (iutruncate (S j) (pi1 f X)).
Proof.
intros i a b Hact.
exploit (choice
           (car (wiurel_ofe top)) (car (wiurel_ofe stop))
           (fun X A =>
              A = iutruncate (S i) A
              /\
              forall j,
                j <= i
                -> interp toppg true j
                     (subst1
                        (extt (objin (objsome (expair (qtype top) X) (succ_increase top))))
                        a)
                     (iutruncate (S j) A)
                   /\
                   interp toppg false j
                     (subst1
                        (extt (objin (objsome (expair (qtype top) X) (succ_increase top))))
                        b)
                     (iutruncate (S j) A))) as (f & Hf).
  {
  intros X.
  set (xt := extt (objin (objsome (expair (qtype top) X) (succ_increase top)))).
  set (C := extend_iurel (lt_ord_impl_le_ord _ _ (succ_increase top)) (iutruncate (S i) X)).
  exploit (Hact i xt xt C (le_refl _)) as H.
    {
    apply interp_eval_refl.
    apply interp_extt.
    apply le_ord_refl.
    }

    {
    apply interp_eval_refl.
    apply interp_extt.
    apply le_ord_refl.
    }
  destruct H as (A & Ha & Hb).
  exists A.
  split.
    {
    split.
      {
      eapply basic_impl_iutruncate; eauto.
      }
    intros j Hj.
    split; eapply basic_downward; eauto.
    }

    {
    intros B.
    intros HB.
    destruct HB as (Htrunc & HB).
    rewrite -> Htrunc.
    exact (interp_fun _#7 Ha (HB i (le_refl _) andel)).
    }
  }
assert (nonexpansive f) as Hne.
  {
  intros n X Y Hdist.
  destruct n as [| j].
    {
    apply dist_zero.
    }
  assert (forall j X, j <= i -> iutruncate (S j) (f X) = iutruncate (S j) (f (iutruncate (S j) X))) as Heq.
    {
    clear X Y Hdist j.
    intros j X Hj.
    so (Hf X ander i (le_refl _)) as (Hli & Hri).
    so (Hf (iutruncate (S j) X) ander j Hj) as (Hlj & Hrj).
    set (xt := extt (objin (objsome (expair (qtype top) X) (succ_increase top)))).
    set (yt := extt (objin (objsome (expair (qtype top) (iutruncate (S j) X)) (succ_increase top)))).
    set (C := extend_iurel (lt_ord_impl_le_ord _ _ (succ_increase top)) (iutruncate (S j) X)).
    exploit (Hact j xt yt C Hj) as H.
      {
      apply interp_eval_refl.
      apply interp_extt.
      apply le_ord_refl.
      }
  
      {
      apply interp_eval_refl.
      unfold yt, C.
      rewrite <- (iutruncate_combine_le _#4 (le_refl _)) at 2.
      apply interp_extt.
      apply le_ord_refl.
      }
    destruct H as (A & Ha & Hb).
    so (interp_fun _#7 (basic_downward _#7 Hj Hli) Ha) as H.
    rewrite -> iutruncate_combine_le in H; [| omega].
    subst A.
    so (interp_fun _#7 Hrj Hb) as Heq.
    symmetry; auto.
    }
  so (le_lt_dec j i) as [Hj | Hnji].
    {
    eapply dist_trans.
      {
      apply dist_symm.
      apply iutruncate_near.
      }
    eapply dist_trans.
    2:{
      apply iutruncate_near.
      }
    apply dist_refl'.
    setoid_rewrite -> Heq at 1 2; auto.
    f_equal.
    f_equal.
    apply iutruncate_collapse; auto.
    }
    
    {
    apply dist_refl'.
    rewrite -> (Hf X andel).
    rewrite -> (Hf Y andel).
    rewrite -> (Heq i X); auto.
    rewrite -> (Heq i Y); auto.
    f_equal.
    f_equal.
    apply iutruncate_collapse.
    apply (dist_downward_leq _ _ (S j)); auto.
    }
  }
exists (expair f Hne).
split.
  {
  apply nearrow_extensionality.
  intro X.
  cbn.
  apply Hf.
  }
intros j Hj X.
cbn.
apply Hf; auto.
Qed.


Lemma extract_parametric_tp_multi :
  forall i a a' b b',
    (forall j c d C,
       j <= i
       -> interp toppg true j c C
       -> interp toppg false j d C
       -> exists A,
            interp toppg true j (subst1 c a) A
            /\ interp toppg false j (subst1 d a') A
            /\ interp toppg true j (subst1 c b) A
            /\ interp toppg false j (subst1 d b') A)
    -> exists (f : wiurel_ofe top -n> wiurel_ofe stop),
         f = nearrow_compose (iutruncate_ne (S i)) f
         /\
         forall j,
           j <= i
           -> forall (X : wiurel top),
                interp toppg true j
                  (subst1
                     (extt (objin (objsome (expair (qtype top) X) (succ_increase top))))
                     a)
                  (iutruncate (S j) (pi1 f X))
                /\
                interp toppg false j
                  (subst1
                     (extt (objin (objsome (expair (qtype top) X) (succ_increase top))))
                     a')
                  (iutruncate (S j) (pi1 f X))
                /\
                interp toppg true j
                  (subst1
                     (extt (objin (objsome (expair (qtype top) X) (succ_increase top))))
                     b)
                  (iutruncate (S j) (pi1 f X))
                /\
                interp toppg false j
                  (subst1
                     (extt (objin (objsome (expair (qtype top) X) (succ_increase top))))
                     b')
                  (iutruncate (S j) (pi1 f X)).
Proof.
intros i a a' b b' Hact.
exploit (extract_parametric_tp i a a') as (fa & Htrunc & Hfa).
  {
  intros j c d C Hj Hc Hd.
  so (Hact j c d C Hj Hc Hd) as (A & Hal & Har & _).
  eauto.
  }
exploit (extract_parametric_tp i b b') as (fb & _ & Hfb).
  {
  intros j c d C Hj Hc Hd.
  so (Hact j c d C Hj Hc Hd) as (A & _ & _ & Hal & Har).
  eauto.
  }
exploit (extract_parametric_tp i a b') as (fab & _ & Hfab).
  {
  intros j c d C Hj Hc Hd.
  so (Hact j c d C Hj Hc Hd) as (A & Hal & _ & _ & Har).
  eauto.
  }
exists fa.
split; auto.
intros j Hj X.
so (Hfa j Hj X) as (Hal & Har).
so (Hfb j Hj X) as (Hbl & Hbr).
so (Hfab j Hj X) as (Hal' & Hbr').
so (interp_fun _#7 Hal Hal') as Heq1.
so (interp_fun _#7 Hbr Hbr') as Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq1 Heq2.
do2 3 split; auto.
  {
  rewrite -> Heq.
  auto.
  }

  {
  rewrite -> Heq.
  auto.
  }
Qed.


Lemma sound_alltp_formation :
  forall G a b,
    pseq (cons hyp_tp G) (deqtype a b)
    -> pseq G (deqtype (alltp a) (alltp b)).
Proof.
intros G a b.
revert G.
refine (seq_pseq 0 1 [_] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_eqtype in Hseq |- *.
intros i s s' Hs.
exploit (extract_parametric_tp_multi i (subst (under 1 s) a) (subst (under 1 s') a) (subst (under 1 s) b) (subst (under 1 s') b)) as H.
  {
  intros j c d C Hj Hc Hd.
  assert (pwctx j (dot c s) (dot d s') (hyp_tp :: G)) as Hss.
    {
    apply pwctx_cons_tp; eauto using pwctx_downward.
    apply (seqhyp_tp _#3 C); auto.
    }
  so (Hseq _#3 Hss) as (R & Hal & Har & Hbl & Hbr).
  exists R.
  simpsub.
  auto.
  }
destruct H as (A & HtruncA & HA).
exists (iualltp stop A).
simpsub.
do2 3 split.
  {
  apply interp_eval_refl.
  rewrite -> HtruncA.
  apply interp_alltp.
  intros j Hj X.
  simpsub.
  so (HA j Hj X andel) as H.
  simpsubin H.
  exact H.
  }

  {
  apply interp_eval_refl.
  rewrite -> HtruncA.
  apply interp_alltp.
  intros j Hj X.
  simpsub.
  so (HA j Hj X anderl) as H.
  simpsubin H.
  exact H.
  }

  {
  apply interp_eval_refl.
  rewrite -> HtruncA.
  apply interp_alltp.
  intros j Hj X.
  simpsub.
  so (HA j Hj X anderrl) as H.
  simpsubin H.
  exact H.
  }

  {
  apply interp_eval_refl.
  rewrite -> HtruncA.
  apply interp_alltp.
  intros j Hj X.
  simpsub.
  so (HA j Hj X anderrr) as H.
  simpsubin H.
  exact H.
  }
Qed.


Lemma sound_alltp_intro :
  forall G a m n,
    pseq (cons hyp_tp G) (deq (subst sh1 m) (subst sh1 n) a)
    -> pseq G (deq m n (alltp a)).
Proof.
intros G a m n.
revert G.
refine (seq_pseq 0 1 [_] _ _ _); cbn.
intros G Hseq.
rewrite -> seq_deq in Hseq |- *.
intros i s s' Hs.
exploit (extract_parametric_tp i (subst (under 1 s) a) (subst (under 1 s') a)) as H.
  {
  intros j c d C Hj Hc Hd.
  assert (pwctx j (dot c s) (dot d s') (hyp_tp :: G)) as Hss.
    {
    apply pwctx_cons_tp; eauto using pwctx_downward.
    apply (seqhyp_tp _#3 C); auto.
    }
  so (Hseq _#3 Hss) as (R & Hal & Har & _).
  exists R.
  simpsub.
  auto.
  }
destruct H as (A & HtruncA & HA).
exists (iualltp stop A).
simpsub.
assert (forall (X : wiurel top),
          pwctx i 
            (dot (extt (objin (objsome (expair (qtype top) X) (succ_increase top)))) s)
            (dot (extt (objin (objsome (expair (qtype top) X) (succ_increase top)))) s')
            (hyp_tp :: G)) as Hallss.
  {
  intro X.
  apply pwctx_cons_tp; auto.
  apply (seqhyp_tp _#3 (extend_iurel (lt_ord_impl_le_ord _ _ (succ_increase top)) (iutruncate (S i) X))).
    {
    apply interp_eval_refl.
    apply interp_extt.
    apply le_ord_refl.
    }

    {
    apply interp_eval_refl.
    apply interp_extt.
    apply le_ord_refl.
    }
  }
do2 4 split.
  {
  rewrite -> HtruncA.
  apply interp_eval_refl.
  apply interp_alltp.
  intros j Hj X.
  simpsub.
  so (HA j Hj X andel) as H.
  simpsubin H.
  exact H.
  }

  {
  rewrite -> HtruncA.
  apply interp_eval_refl.
  apply interp_alltp.
  intros j Hj X.
  simpsub.
  so (HA j Hj X ander) as H.
  simpsubin H.
  exact H.
  }

  {
  intros j X Hj.
  so (Hseq _#3 (Hallss X)) as (R & Hal & _ & Hl & _).
  so (HA j Hj X) as (Hal' & _).
  simpsubin Hal'.
  so (interp_fun _#7 (basic_downward _#7 Hj Hal) Hal') as Heq.
  simpsubin Hl.
  cut (rel (den (iutruncate (S j) (pi1 A X))) j (subst s m) (subst s' m)).
    {
    intro Hprop.
    destruct Hprop; auto.
    }
  rewrite <- Heq.
  split; auto.
  apply (urel_downward_leq _ _ _ i); auto.
  }

  {
  intros j X Hj.
  so (Hseq _#3 (Hallss X)) as (R & Hal & _ & _ & Hr & _).
  so (HA j Hj X) as (Hal' & _).
  simpsubin Hal'.
  so (interp_fun _#7 (basic_downward _#7 Hj Hal) Hal') as Heq.
  simpsubin Hr.
  cut (rel (den (iutruncate (S j) (pi1 A X))) j (subst s n) (subst s' n)).
    {
    intro Hprop.
    destruct Hprop; auto.
    }
  rewrite <- Heq.
  split; auto.
  apply (urel_downward_leq _ _ _ i); auto.
  }

  {
  intros j X Hj.
  so (Hseq _#3 (Hallss X)) as (R & Hal & _ & _ & _ & Hlr).
  so (HA j Hj X) as (Hal' & _).
  simpsubin Hal'.
  so (interp_fun _#7 (basic_downward _#7 Hj Hal) Hal') as Heq.
  simpsubin Hlr.
  cut (rel (den (iutruncate (S j) (pi1 A X))) j (subst s m) (subst s' n)).
    {
    intro Hprop.
    destruct Hprop; auto.
    }
  rewrite <- Heq.
  split; auto.
  apply (urel_downward_leq _ _ _ i); auto.
  }
Qed.


Lemma sound_alltp_elim :
  forall G a b m n,
    pseq G (deq m n (alltp a))
    -> pseq G (deqtype b b)
    -> pseq (cons hyp_tp G) (deqtype a a)
    -> pseq G (deq m n (subst1 b a)).
Proof.
intros G a b m n.
revert G.
refine (seq_pseq 0 3 [] _ [] _ [_] _ _ _); cbn.
intros G Hseqmn Hseqb Hseqa.
rewrite -> seq_deq in Hseqmn |- *.
rewrite -> seq_eqtype in Hseqb, Hseqa.
intros i s s' Hs.
exploit (extract_parametric_tp i (subst (under 1 s) a) (subst (under 1 s') a)) as H.
  {
  intros j c d C Hj Hc Hd.
  assert (pwctx j (dot c s) (dot d s') (hyp_tp :: G)) as Hss.
    {
    apply pwctx_cons_tp; eauto using pwctx_downward.
    apply (seqhyp_tp _#3 C); auto.
    }
  so (Hseqa _#3 Hss) as (R & Hal & Har & _).
  exists R.
  simpsub.
  auto.
  }
destruct H as (A & Htrunc & HA).
so (Hseqb _#3 Hs) as (BB & Hbl & Hbr & _).
set (h := (lt_ord_impl_le_ord _ _ (succ_increase top))).
so (interp_level_internal toppg _#4 h Hbl) as (B & ->).
cbn in B.
so (Hseqmn _#3 Hs) as (R & Hl & _ & Hm & Hn & Hmn).
simpsubin Hl.
invert (basic_value_inv _#6 value_alltp Hl).
intros A' HA' <-.
so (HA i (le_refl _) B) as (Hal & Har).
simpsubin Hal.
simpsubin Har.
so (HA' i (le_refl _) B) as Hal'.
simpsubin Hal'.
so (interp_fun _#7 Hal Hal') as Heq.
set (xt := extt (objin (objsome (expair (qtype top) B) (succ_increase top)))) in Hal, Hal'.
exists (iutruncate (S i) (pi1 A' B)).
do2 4 split; auto.
  {
  simpsub.
  rewrite <- Heq.
  assert (pwctx i (dot (subst s b) s) (dot xt s') (hyp_tp :: G)) as Hss.
    {
    apply pwctx_cons_tp; auto.
    apply (seqhyp_tp _#3 (extend_iurel h (iutruncate (S i) B))).
      {
      so (basic_downward _#7 (le_refl _) Hbl) as H.
      rewrite -> iutruncate_extend_iurel in H.
      exact H.
      }

      {
      apply interp_eval_refl.
      apply interp_extt.
      apply le_ord_refl.
      }
    }
  so (Hseqa _#3 Hss) as (R & H & Har' & _).
  so (basic_fun _#7 Har Har'); subst R.
  exact H.
  }

  {
  simpsub.
  rewrite <- Heq.
  assert (pwctx i (dot xt s) (dot (subst s' b) s') (hyp_tp :: G)) as Hss.
    {
    apply pwctx_cons_tp; auto.
    apply (seqhyp_tp _#3 (extend_iurel h (iutruncate (S i) B))).
      {
      apply interp_eval_refl.
      apply interp_extt.
      apply le_ord_refl.
      }

      {
      so (basic_downward _#7 (le_refl _) Hbr) as H.
      rewrite -> iutruncate_extend_iurel in H.
      exact H.
      }
    }
  so (Hseqa _#3 Hss) as (R & Hal'' & H & _).
  so (basic_fun _#7 Hal Hal''); subst R.
  exact H.
  }

  {
  apply Hm; auto.
  }

  {
  apply Hn; auto.
  }

  {
  apply Hmn; auto.
  }
Qed.
