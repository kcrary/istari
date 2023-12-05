
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Axioms.
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

Require Import Spaces.
Require Import Model.
Require Import Truncate.
Require Import Standard.
Require Import SemanticsExist.
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
Require Import MapTerm.
Require Import SoundAll.
Require Import SoundUtil.
Require Import Urelsp.


Local Ltac prove_hygiene :=
  repeat (first [ apply hygiene_shift_permit
                | apply hygiene_auto; cbn [row_rect nat_rect]; repeat2 split; auto
                ]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1;
  try (apply hygiene_var; cbn; auto; done).


Lemma sound_exist_formation :
  forall G glv k l a b,
    pseq G (deq k l (kuniv glv))
    -> pseq (cons (hyp_tm k) G) (deqtype a b)
    -> pseq G (deqtype (exist glv k a) (exist glv l b)).
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
exists (iuexist stop K (std (S i) (qarrow K (qtype stop)) f)).
do2 3 split.
  {
  apply interp_eval_refl.
  apply (interp_exist _#7 gpg _ _ HlevKt); auto using toppg_max.
  intros j Hj x.
  exact (Hf j Hj x andel).
  }

  {
  apply interp_eval_refl.
  apply (interp_exist _#7 gpg _ _ HlevKt); auto using toppg_max.
  intros j Hj x.
  exact (Hf j Hj x anderl).
  }

  {
  apply interp_eval_refl.
  apply (interp_exist _#7 gpg _ _ HlevKt); auto using toppg_max.
  intros j Hj x.
  exact (Hf j Hj x anderrl).
  }

  {
  apply interp_eval_refl.
  apply (interp_exist _#7 gpg _ _ HlevKt); auto using toppg_max.
  intros j Hj x.
  exact (Hf j Hj x anderrr).
  }
Qed.


Lemma sound_exist_formation_univ :
  forall G glv lv k l a b,
    pseq G (deq k l (kuniv glv))
    -> pseq (cons (hyp_tm k) G) (deq a b (univ (subst sh1 lv)))
    -> pseq G (deq lv lv pagetp)
    -> pseq G (deq triv triv (leqpagetp glv lv))
    -> pseq G (deq (exist glv k a) (exist glv l b) (univ lv)).
Proof.
intros G glv lv k l a b.
revert G.
refine (seq_pseq 0 4 [] _ [_] _ [] _ [] _ _ _); cbn.
intros G Hseqkl Hseqab Hseqlv Hseqleq.
rewrite -> seq_eqkind in Hseqkl.
rewrite -> seq_univ in Hseqab |- *.
rewrite -> seq_deq in Hseqlv, Hseqleq.
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
exists (iuexist stop K (std (S i) (qarrow K (qtype stop)) f)).
do2 5 split; auto.
  {
  apply interp_eval_refl.
  apply (interp_exist _#7 gpg _ _ HlevKt); auto.
  intros j Hj x.
  exact (Hf j Hj x andel).
  }

  {
  apply interp_eval_refl.
  apply (interp_exist _#7 gpg _ _ HlevKt); auto.
  intros j Hj x.
  exact (Hf j Hj x anderl).
  }

  {
  apply interp_eval_refl.
  apply (interp_exist _#7 gpg _ _ HlevKt); auto.
  intros j Hj x.
  exact (Hf j Hj x anderrl).
  }

  {
  apply interp_eval_refl.
  apply (interp_exist _#7 gpg _ _ HlevKt); auto.
  intros j Hj x.
  exact (Hf j Hj x anderrr).
  }
Qed.


Lemma sound_exist_intro :
  forall G lv k a b m n,
    pseq G (deq k k (kuniv lv))
    -> pseq G (deq b b k)
    -> pseq G (deq m n (subst1 b a))
    -> pseq (cons (hyp_tm k) G) (deqtype a a)
    -> pseq G (deq m n (exist lv k a)).
Proof.
intros G lv k a b m n.
revert G.
refine (seq_pseq 2 [] m [] n 4 [] _ [] _ [] _ [_] _ _ _); cbn.
intros G Hclm Hcln Hseqk Hseqb Hseqmn Hseqa.
rewrite -> seq_eqkind in Hseqk.
rewrite -> seq_eqtype in Hseqa.
rewrite -> seq_deq in Hseqb, Hseqmn |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqk i s s' Hs) as (pg & K & R & hh & Hlvl & Hlvr & Hkl & Hkr & _ & _ & Hklt & Hkrt & _).
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
  intros j d e Hj Hcd.
  exploit (Hseqa j (dot d s) (dot e s')) as H.
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
so (Hseqb _#3 Hs) as (R' & Hklt' & _ & Hb & _).
clear Hseqb.
so (interp_fun _#7 Hklt Hklt'); subst R'.
clear Hklt'.
so (Hseqmn _#3 Hs) as (A & Hal & Har & Hm & Hn & Hmn).
clear Hseqmn.
so (spacify _#6 Hkl (interp_increase _#6 (toppg_max _) Hklt)) as (_ & Hto & Hfrom & Hbeta & _).
so (Hto i i i (le_refl _) (le_refl _) (le_refl _)) as H; clear Hto.
so (arrow_action_app _#9 H Hb) as Htospb; clear H.
destruct Htospb as (x & Hxl & Hxr).
revert x Hxl Hxr.
rewrite <- (kbasic_impl_approx _#6 Hkl).
intros x Hxl Hxr.
assert (A = iutruncate (S i) (pi1 f (std (S i) K (embed i K (proj i K x))))).
  {
  so (Hbeta _#3 (le_refl _) Hb) as Hftb.
  exploit (Hseqa i (dot (app (fromsp stop pg K) (app (tosp stop pg K) (subst s b))) s) (dot (subst s' b) s')) as H.
    {
    apply pwctx_cons_tm_seq; auto.
      {
      apply (seqhyp_tm _#5 R); eauto using interp_increase, toppg_max.
      }
  
      {
      intros j t t' Ht.
      so (Hseqk _#3 Ht) as (pg' & _ & Q & h' & _ & _ & _ & _ & _ & _ & Hl & Hr & _).
      exists toppg.
      eauto using interp_increase, toppg_max.
      }
    }
  destruct H as (A' & Hal' & Har' & _).
  simpsubin Hal.
  simpsubin Har.
  so (interp_fun _#7 Har Har'); subst A'.
  so (Hf i (le_refl _) (proj i K x)) as (_ & Har'').
  simpsubin Har''.
  set (X := @expair _ spcar (approx i K) (proj i K x)).
  set (h := le_ord_succ _ _ (le_ord_trans _ _ _ (approx_level _ _ ) HlevKt) : level (pi1 X) << stop) in Har''.
  clearbody h.
  change (interp toppg false i
            (subst (dot (app (fromsp stop pg (pi1 X)) (ext (objin (objsome (expair (pi1 X) (std (S i) (pi1 X) (pi2 X))) h)))) s') a)
            (iutruncate (S i) (pi1 f (std (S i) K (embed i K (proj i K x)))))) in Har''.
  assert (X = expair K x) as Heq.
    {
    clear Har''.
    so (kbasic_impl_approx _#6 Hkl) as Heq.
    symmetry in Heq.
    subst X.
    apply (exT_extensionality _ _ (expair (approx i K) (proj i K x)) (expair K x) Heq).
    cbn.
    apply proj_near'.
    }
  clearbody X.
  subst X.
  cbn [pi1 pi2] in Har''.
  match type of Har'' with
  | interp _ _ _ (subst (dot (app _ ?X) _) _) _ =>
      set (xt := X) in Har''
  end.
  assert (rel (con_urel pg K) i (app (tosp stop pg K) (subst s b)) xt) as Hrel.
    {
    exists (proj i K (std (S i) K x)).
    split.
      {
      so (cbasic_downward _#7 (le_refl _) Hxl) as H.
      unfold projc, stdc in H.
      cbn in H.
      exact H.
      }

      {
      apply cinterp_eval_refl.
      relquest.
        {
        apply interp_ext; auto.
        }
      unfold projc, stdc; cbn.
      f_equal.
      f_equal.
      apply std_idem.
      }
    }
  so (Hfrom i i i (le_refl _) (le_refl _) (le_refl _)) as H.
  rewrite <- (kbasic_impl_approx _#6 Hkl) in H.
  so (arrow_action_app _#9 H Hrel) as Hrel'; clear Hrel H.
  exploit (Hseqa i (dot (app (fromsp stop pg K) (app (tosp stop pg K) (subst s b))) s) (dot (app (fromsp stop pg K) xt) s')) as H.
    {
    apply pwctx_cons_tm_seq; auto.
      {
      apply (seqhyp_tm _#5 R); eauto using interp_increase, toppg_max.
      }
  
      {
      intros j t t' Ht.
      so (Hseqk _#3 Ht) as (pg' & _ & Q & h' & _ & _ & _ & _ & _ & _ & Hl & Hr & _).
      exists toppg.
      eauto using interp_increase, toppg_max.
      }
    }
  destruct H as (A' & Hal''' & _ & _ & Har''').
  so (interp_fun _#7 Hal' Hal'''); subst A'.
  so (interp_fun _#7 Har'' Har''').
  symmetry; auto.
  }
clear Hseqa Hseqk.
subst A.
so (Hf i (le_refl _) (proj i K x)) as (_ & Har').
simpsubin Har'.
clear Har'.
rewrite -> den_iutruncate in Hm, Hn, Hmn.
assert (forall j,
          j <= i
          -> @dist (wurel_ofe stop) (S j)
               (ceiling (S i) (den (pi1 f (std (S i) K (embed i K (proj i K x))))))
               (ceiling (S i) (den (pi1 f (std (S i) K (embed j K (proj j K x))))))) as Hdist.
  {
  intros j Hj.
  apply ceiling_nonexpansive.
  apply den_nonexpansive.
  apply (pi2 f).
  apply std_nonexpansive.
  apply (dist_trans _ _ _ x).
    {
    apply (dist_downward_leq _ _ (S i)); [omega |].
    apply embed_proj.
    }
   
    {
    apply dist_symm.
    apply embed_proj.
    }
  }
exists (iuexist stop K (std (S i) (qarrow K (qtype stop)) f)).
simpsub.
do2 4 split.
  {
  apply interp_eval_refl.
  apply (interp_exist _#7 pg _ _ HlevKt); eauto using toppg_max, pginterp_cin_top.
  intros j Hj y.
  exact (Hf j Hj y andel).
  }

  {
  apply interp_eval_refl.
  apply (interp_exist _#7 pg _ _ HlevKt); eauto using toppg_max, pginterp_cin_top.
  intros j Hj y.
  exact (Hf j Hj y ander).
  }

  {
  do2 4 split; auto.
    {
    eapply subst_closub; eauto.
    }

    {
    eapply subst_closub; eauto.
    }

    {
    exists x, (subst s' m).
    rewrite -> std_arrow_is.
    cbn.
    change (rel (den (std (S i) (qtype stop) (pi1 f (std (S i) K x)))) i (subst s m) (subst s' m)).
    rewrite -> std_type_is.
    rewrite -> den_iutruncate.
    replace (std (S i) K x) with (std (S i) K (embed i K (proj i K x))); auto.
    apply std_collapse.
    apply embed_proj.
    }

    {
    exists x, (subst s m).
    rewrite -> std_arrow_is.
    cbn.
    change (rel (den (std (S i) (qtype stop) (pi1 f (std (S i) K x)))) i (subst s m) (subst s' m)).
    rewrite -> std_type_is.
    rewrite -> den_iutruncate.
    replace (std (S i) K x) with (std (S i) K (embed i K (proj i K x))); auto.
    apply std_collapse.
    apply embed_proj.
    }
  intros j p q C Hj Hpq.
  so (Hpq (proj j K x)) as H; renameover H into Hpq.
  refine (arrow_action_app _#9 Hpq _); clear Hpq.
  cbn.
  rewrite -> !extend_term_id.
  rewrite -> std_arrow_is.
  change (rel (den (std (S i) (qtype stop) (pi1 f (std (S i) K (embed j K (proj j K x)))))) j
            (subst s m) (subst s' m)).
  rewrite -> std_type_is.
  rewrite -> den_iutruncate.
  refine (rel_from_dist _#6 (Hdist _ Hj) _).
  apply (urel_downward_leq _#3 i); auto.
  }

  {
  do2 4 split; auto.
    {
    eapply subst_closub; eauto.
    }

    {
    eapply subst_closub; eauto.
    }

    {
    exists x, (subst s' n).
    rewrite -> std_arrow_is.
    cbn.
    change (rel (den (std (S i) (qtype stop) (pi1 f (std (S i) K x)))) i (subst s n) (subst s' n)).
    rewrite -> std_type_is.
    rewrite -> den_iutruncate.
    replace (std (S i) K x) with (std (S i) K (embed i K (proj i K x))); auto.
    apply std_collapse.
    apply embed_proj.
    }

    {
    exists x, (subst s n).
    rewrite -> std_arrow_is.
    cbn.
    change (rel (den (std (S i) (qtype stop) (pi1 f (std (S i) K x)))) i (subst s n) (subst s' n)).
    rewrite -> std_type_is.
    rewrite -> den_iutruncate.
    replace (std (S i) K x) with (std (S i) K (embed i K (proj i K x))); auto.
    apply std_collapse.
    apply embed_proj.
    }
  intros j p q C Hj Hpq.
  so (Hpq (proj j K x)) as H; renameover H into Hpq.
  refine (arrow_action_app _#9 Hpq _); clear Hpq.
  cbn.
  rewrite -> !extend_term_id.
  rewrite -> std_arrow_is.
  change (rel (den (std (S i) (qtype stop) (pi1 f (std (S i) K (embed j K (proj j K x)))))) j
            (subst s n) (subst s' n)).
  rewrite -> std_type_is.
  rewrite -> den_iutruncate.
  refine (rel_from_dist _#6 (Hdist _ Hj) _).
  apply (urel_downward_leq _#3 i); auto.
  }

  {
  do2 4 split; auto.
    {
    eapply subst_closub; eauto.
    }

    {
    eapply subst_closub; eauto.
    }

    {
    exists x, (subst s' m).
    rewrite -> std_arrow_is.
    cbn.
    change (rel (den (std (S i) (qtype stop) (pi1 f (std (S i) K x)))) i (subst s m) (subst s' m)).
    rewrite -> std_type_is.
    rewrite -> den_iutruncate.
    replace (std (S i) K x) with (std (S i) K (embed i K (proj i K x))); auto.
    apply std_collapse.
    apply embed_proj.
    }

    {
    exists x, (subst s m).
    rewrite -> std_arrow_is.
    cbn.
    change (rel (den (std (S i) (qtype stop) (pi1 f (std (S i) K x)))) i (subst s m) (subst s' n)).
    rewrite -> std_type_is.
    rewrite -> den_iutruncate.
    replace (std (S i) K x) with (std (S i) K (embed i K (proj i K x))); auto.
    apply std_collapse.
    apply embed_proj.
    }
  intros j p q C Hj Hpq.
  so (Hpq (proj j K x)) as H; renameover H into Hpq.
  refine (arrow_action_app _#9 Hpq _); clear Hpq.
  cbn.
  rewrite -> !extend_term_id.
  rewrite -> std_arrow_is.
  change (rel (den (std (S i) (qtype stop) (pi1 f (std (S i) K (embed j K (proj j K x)))))) j
            (subst s m) (subst s' n)).
  rewrite -> std_type_is.
  rewrite -> den_iutruncate.
  refine (rel_from_dist _#6 (Hdist _ Hj) _).
  apply (urel_downward_leq _#3 i); auto.
  }
Qed.


Lemma sound_exist_elim :
  forall G lv k a b m n p q,
    pseq G (deq m n (exist lv k a))
    -> pseq G (deqtype k k)
    -> pseq (cons (hyp_tm k) G) (deqtype a a)
    -> pseq (cons (hyp_tm a) (cons (hyp_tm k) G)) (deq (subst (dot (var 0) (sh 2)) p) (subst (dot (var 0) (sh 2)) q) (subst (sh 2) b))
    -> pseq G (deq (subst1 m p) (subst1 n q) b).
Proof.
intros G lv k a b m n p q.
revert G.
refine (seq_pseq 2 [hyp_emp] p [hyp_emp] q 4 [] _ [] _ [_] _ [_; _] _ _ _); cbn.
intros G Hclp Hclq Hseqmn Hseqk Hseqa Hseqpq.
rewrite -> seq_eqtype in Hseqa, Hseqk.
rewrite -> seq_deq in Hseqmn, Hseqpq |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmn _#3 Hs) as (R & Hexl & Hexr & Hm & Hn & Hmn); clear Hseqmn.
simpsubin Hexl.
simpsubin Hexr.
invert (basic_value_inv _#6 value_exist Hexl).
intros pg K A h Hlvl Hkl _ Hactl <-.
assert (forall (x : spcar K) j r t,
          j <= i
          -> rel (den (pi1 A (std (S j) K x))) j r t
          -> pwctx j 
               (dot r (dot (app 
                              (fromsp stop pg (approx j K))
                              (ext (objin (objsome 
                                             (expair (approx j K) (std (S j) (approx j K) (proj j K x)))
                                             (le_ord_succ _ _ 
                                                (le_ord_trans _#3 (approx_level j K) h)))))) s))
               (dot t (dot (app 
                              (fromsp stop pg (approx j K))
                              (ext (objin (objsome 
                                             (expair (approx j K) (std (S j) (approx j K) (proj j K x)))
                                             (le_ord_succ _ _ 
                                                (le_ord_trans _#3 (approx_level j K) h)))))) s'))
               (cons (hyp_tm a) (cons (hyp_tm k) G))) as Hs'.
  {
  intros x j r t Hj Hrt.
  assert (pwctx j 
          (dot (app 
                  (fromsp stop pg (approx j K))
                  (ext (objin (objsome 
                                 (expair (approx j K) (std (S j) (approx j K) (proj j K x)))
                                 (le_ord_succ _ _ 
                                    (le_ord_trans _#3 (approx_level j K) h)))))) s)
          (dot (app 
                  (fromsp stop pg (approx j K))
                  (ext (objin (objsome 
                                 (expair (approx j K) (std (S j) (approx j K) (proj j K x)))
                                 (le_ord_succ _ _ 
                                    (le_ord_trans _#3 (approx_level j K) h)))))) s')
          (cons (hyp_tm k) G)) as Hs'.
    {
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      so (Hseqk _#3 Hs) as (Kt & Hklt & Hkrt & _).
      apply (seqhyp_tm _#5 (iutruncate (S j) Kt)).
        {
        eapply basic_downward; eauto.
        }

        {
        eapply basic_downward; eauto.
        }
      so (spacify _#6 Hkl Hklt) as (_ & _ & H & _).
      so (H j j j Hj (le_refl _) (le_refl _)) as Hfrom; clear H.
      split; [omega |].
      refine (arrow_action_app _#9 Hfrom _).
      exists (std (S j) (approx j K) (proj j K x)).
      split.
        {
        apply cinterp_eval_refl.
        relquest.
          {
          apply interp_ext.
          cbn.
          eapply le_ord_trans; eauto using approx_level.
          eapply kinterp_level_bound; eauto.
          }
        change (projc j (stdc (S j) (stdc (S j) (projc j (expair K x)))) = stdc (S j) (projc j (expair K x))).
        rewrite -> stdc_idem.
        rewrite -> projc_stdc; auto.
        rewrite -> projc_idem; auto.
        }

        {
        apply cinterp_eval_refl.
        relquest.
          {
          apply interp_ext.
          cbn.
          eapply le_ord_trans; eauto using approx_level.
          eapply kinterp_level_bound; eauto.
          }
        change (projc j (stdc (S j) (stdc (S j) (projc j (expair K x)))) = stdc (S j) (projc j (expair K x))).
        rewrite -> stdc_idem.
        rewrite -> projc_stdc; auto.
        rewrite -> projc_idem; auto.
        }
      }

      {
      intros j' u u' Hu.
      so (Hseqk _#3 Hu) as (Q & Hl & Hr & _).
      eauto.
      }
    }
  apply pwctx_cons_tm_seq; auto.
    {
    apply (seqhyp_tm _#5 (iutruncate (S j) (pi1 A (std (S j) K (embed j K (proj j K x)))))).
      {
      so (Hactl j Hj (proj j K x)) as H.
      simpsubin H.
      exact H.
      }

      {
      so (Hactl j Hj (proj j K x)) as Hl.
      simpsubin Hl.
      so (Hseqa _#3 Hs') as (Q & Hl' & Hr & _).
      so (basic_fun _#7 Hl Hl'); subst Q.
      exact Hr.
      }

      {
      split; auto.
      refine (rel_from_dist _#6 _ Hrt).
      apply den_nonexpansive.
      apply (pi2 A).
      apply std_nonexpansive.
      apply dist_symm.
      apply embed_proj.
      }
    }

    {
    intros j' u u' Hu.
    so (Hseqa _#3 Hu) as H.
    destruct H as (Q & Hl & Hr & _).
    eauto.
    }
  }
assert (exists B,
          interp toppg true i (subst s b) B
          /\ interp toppg false i (subst s' b) B) as (B & Hbl & Hbr).
  {
  cbn in Hm.
  destruct Hm as (_ & _ & H & _).
  destruct H as (x & r & H).
  rewrite -> std_arrow_is in H.
  cbn in H.
  fold (std (S i) (qtype stop)) in H.
  change (rel (den (std (S i) (qtype stop) (pi1 A (std (S i) K x)))) i (subst s m) r) in H.
  rewrite -> std_type_is in H.
  destruct H as (_ & H).
  so (Hs' _#4 (le_refl _) H) as H'; clear H.
  so (Hseqpq _#3 H') as (B & Hbl & Hbr & _).
  simpsubin Hbl.
  simpsubin Hbr.
  eauto.
  }
exists B.
do2 2 split; auto.
simpsub.
revert m n p q Hclp Hclq Hseqpq Hm Hn Hmn.
cut (forall m n p q,
        hygiene (permit (ctxpred G)) p
        -> hygiene (permit (ctxpred G)) q
        -> (forall j s s',
              pwctx j s s' (cons (hyp_tm a) (cons (hyp_tm k) G))
              -> exists R,
                   interp toppg true j (subst s (subst (sh 2) b)) R
                   /\ interp toppg false j (subst s' (subst (sh 2) b)) R
                   /\ rel (den R) j (subst s (subst (dot (var 0) (sh 2)) p)) (subst s' (subst (dot (var 0) (sh 2)) q)))
        -> rel (den (iuexist stop K (std (S i) (qarrow K (qtype stop)) A))) i m n
        -> rel (den B) i (subst (dot m s) p) (subst (dot n s') q)).
  {
  intro Hcond.
  intros m n p q Hclp Hclq Hseq Hm Hn Hmn.
  do2 2 split.
    {
    apply Hcond; auto.
    intros j u u' Hu.
    so (Hseq _#3 Hu) as (R & Hl & Hr & Hp & _).
    eauto.
    }

    {
    apply Hcond; auto.
    intros j u u' Hu.
    so (Hseq _#3 Hu) as (R & Hl & Hr & _ & Hq & _).
    eauto.
    }

    {
    apply Hcond; auto.
    intros j u u' Hu.
    so (Hseq _#3 Hu) as (R & Hl & Hr & _ & _ & Hpq).
    eauto.
    }
  }
intros m n p q Hclp Hclq Hseqpq Hmn.
assert (forall (x : spcar K),
          rel (arrow_urel stop i (ceiling (S i) (den (pi1 A (std (S i) K x)))) (den B)) i (subst s (lam p)) (subst s' (lam q))) as Hp.
  {
  intros x.
  exists (subst (under 1 s) p), (subst (under 1 s') q).
  do2 5 split; auto.
    {
    eapply subst_closub; eauto.
    apply hygiene_auto; cbn; auto.
    }

    {
    eapply subst_closub; eauto.
    apply hygiene_auto; cbn; auto.
    }

    {
    simpsub; apply star_refl.
    }

    {
    simpsub; apply star_refl.
    }
  intros j r t Hj Hrt.
  destruct Hrt as (_ & Hrt).
  simpsub.
  eassert _ as H; [refine (Hseqpq _#3 (Hs' x j r t Hj _)) |].
    {
    refine (rel_from_dist _#6 _ Hrt).
    apply den_nonexpansive.
    apply (pi2 A).
    apply dist_symm.
    apply std_dist.
    omega.
    }
  simpsubin H.
  destruct H as (B' & Hbl' & _ & Hp).
  so (basic_fun _#7 (basic_downward _#7 Hj Hbl) Hbl'); subst B'.
  destruct Hp; auto.
  }
destruct Hmn as (Hclm & Hcln & _ & _ & Hact).
so (Hact i (subst s (lam p)) (subst s' (lam q)) (den B) (le_refl _)) as H.
lapply H; clear H.
2:{
  intro x.
  rewrite -> extend_urel_id.
  simpsub.
  rewrite -> std_arrow_is.
  change (rel (arrow_urel stop i (den (std (S i) (qtype stop) (pi1 A (std (S i) K (embed i K x))))) (den B)) i (lam (subst (under 1 s) p)) (lam (subst (under 1 s') q))).
  rewrite -> std_type_is.
  rewrite -> den_iutruncate.
  so (Hp (embed i K x)) as H.
  simpsubin H.
  exact H.
  }
intros H.
rewrite -> !extend_term_id in H.
simpsubin H.
refine (urel_equiv _#7 _ _ _ _ H); clear H.
  {
  eapply hygiene_subst; eauto.
  intros j Hj.
  destruct j as [| j]; simpsub; auto.
  }

  {
  eapply hygiene_subst; eauto.
  intros j Hj.
  destruct j as [| j]; simpsub; auto.
  }

  {
  apply steps_equiv.
  eapply star_step; [apply step_app2 |].
  simpsub.
  apply star_refl.
  }

  {
  apply steps_equiv.
  eapply star_step; [apply step_app2 |].
  simpsub.
  apply star_refl.
  }
Qed.


Lemma sound_exist_elim_eqtype :
  forall G lv k a m n p q,
    pseq G (deq m n (exist lv k a))
    -> pseq G (deqtype k k)
    -> pseq (cons (hyp_tm k) G) (deqtype a a)
    -> pseq (cons (hyp_tm a) (cons (hyp_tm k) G)) (deqtype (subst (dot (var 0) (sh 2)) p) (subst (dot (var 0) (sh 2)) q))
    -> pseq G (deqtype (subst1 m p) (subst1 n q)).
Proof.
intros G lv k a m n p q.
revert G.
refine (seq_pseq 2 [hyp_emp] p [hyp_emp] q 4 [] _ [] _ [_] _ [_; _] _ _ _); cbn.
intros G Hclp Hclq Hseqmn Hseqk Hseqa Hseqpq.
rewrite -> seq_eqtype in Hseqpq, Hseqa, Hseqk |- *.
rewrite -> seq_deq in Hseqmn.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmn _#3 Hs) as (R & Hexl & Hexr & Hm & Hn & Hmn); clear Hseqmn.
simpsubin Hexl.
simpsubin Hexr.
invert (basic_value_inv _#6 value_exist Hexl).
intros pg K A h Hlvl Hkl _ Hactl <-.
simpsub.
assert (forall (x : spcar K) j r t,
          j <= i
          -> rel (den (pi1 A (std (S j) K x))) j r t
          -> pwctx j 
               (dot r (dot (app 
                              (fromsp stop pg (approx j K))
                              (ext (objin (objsome 
                                             (expair (approx j K) (std (S j) (approx j K) (proj j K x)))
                                             (le_ord_succ _ _ 
                                                (le_ord_trans _#3 (approx_level j K) h)))))) s))
               (dot t (dot (app 
                              (fromsp stop pg (approx j K))
                              (ext (objin (objsome 
                                             (expair (approx j K) (std (S j) (approx j K) (proj j K x)))
                                             (le_ord_succ _ _ 
                                                (le_ord_trans _#3 (approx_level j K) h)))))) s'))
               (cons (hyp_tm a) (cons (hyp_tm k) G))) as Hs'.
  {
  intros x j r t Hj Hrt.
  assert (pwctx j 
          (dot (app 
                  (fromsp stop pg (approx j K))
                  (ext (objin (objsome 
                                 (expair (approx j K) (std (S j) (approx j K) (proj j K x)))
                                 (le_ord_succ _ _ 
                                    (le_ord_trans _#3 (approx_level j K) h)))))) s)
          (dot (app 
                  (fromsp stop pg (approx j K))
                  (ext (objin (objsome 
                                 (expair (approx j K) (std (S j) (approx j K) (proj j K x)))
                                 (le_ord_succ _ _ 
                                    (le_ord_trans _#3 (approx_level j K) h)))))) s')
          (cons (hyp_tm k) G)) as Hs'.
    {
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      so (Hseqk _#3 Hs) as (Kt & Hklt & Hkrt & _).
      apply (seqhyp_tm _#5 (iutruncate (S j) Kt)).
        {
        eapply basic_downward; eauto.
        }

        {
        eapply basic_downward; eauto.
        }
      so (spacify _#6 Hkl Hklt) as (_ & _ & H & _).
      so (H j j j Hj (le_refl _) (le_refl _)) as Hfrom; clear H.
      split; [omega |].
      refine (arrow_action_app _#9 Hfrom _).
      exists (std (S j) (approx j K) (proj j K x)).
      split.
        {
        apply cinterp_eval_refl.
        relquest.
          {
          apply interp_ext.
          cbn.
          eapply le_ord_trans; eauto using approx_level.
          eapply kinterp_level_bound; eauto.
          }
        change (projc j (stdc (S j) (stdc (S j) (projc j (expair K x)))) = stdc (S j) (projc j (expair K x))).
        rewrite -> stdc_idem.
        rewrite -> projc_stdc; auto.
        rewrite -> projc_idem; auto.
        }

        {
        apply cinterp_eval_refl.
        relquest.
          {
          apply interp_ext.
          cbn.
          eapply le_ord_trans; eauto using approx_level.
          eapply kinterp_level_bound; eauto.
          }
        change (projc j (stdc (S j) (stdc (S j) (projc j (expair K x)))) = stdc (S j) (projc j (expair K x))).
        rewrite -> stdc_idem.
        rewrite -> projc_stdc; auto.
        rewrite -> projc_idem; auto.
        }
      }

      {
      intros j' u u' Hu.
      so (Hseqk _#3 Hu) as (Q & Hl & Hr & _).
      eauto.
      }
    }
  apply pwctx_cons_tm_seq; auto.
    {
    apply (seqhyp_tm _#5 (iutruncate (S j) (pi1 A (std (S j) K (embed j K (proj j K x)))))).
      {
      so (Hactl j Hj (proj j K x)) as H.
      simpsubin H.
      exact H.
      }

      {
      so (Hactl j Hj (proj j K x)) as Hl.
      simpsubin Hl.
      so (Hseqa _#3 Hs') as (Q & Hl' & Hr & _).
      so (basic_fun _#7 Hl Hl'); subst Q.
      exact Hr.
      }

      {
      split; auto.
      refine (rel_from_dist _#6 _ Hrt).
      apply den_nonexpansive.
      apply (pi2 A).
      apply std_nonexpansive.
      apply dist_symm.
      apply embed_proj.
      }
    }

    {
    intros j' u u' Hu.
    so (Hseqa _#3 Hu) as H.
    destruct H as (Q & Hl & Hr & _).
    eauto.
    }
  }
revert m n p q Hclp Hclq Hseqpq Hm Hn Hmn.
cut (forall m n p q,
        hygiene (permit (ctxpred G)) p
        -> hygiene (permit (ctxpred G)) q
        -> (forall j s s',
              pwctx j s s' (cons (hyp_tm a) (cons (hyp_tm k) G))
              -> rel (tp_urel toppg) j 
                   (subst s (subst (dot (var 0) (sh 2)) p))
                   (subst s' (subst (dot (var 0) (sh 2)) q)))
        -> rel (den (iuexist stop K (std (S i) (qarrow K (qtype stop)) A))) i m n
        -> rel (tp_urel toppg) i (subst (dot m s) p) (subst (dot n s') q)).
  {
  intro Hcond.
  intros m n p q Hclp Hclq Hseq Hm Hn Hmn.
  exploit (Hcond (subst s m) (subst s' m) p p) as H; auto.
    {
    intros j u u' Hu.
    so (Hseq _#3 Hu) as (? & ? & ? & _).
    eexists; eauto.
    }
  destruct H as (R & Hpl & Hpr).
  exists R.
  do2 2 split; auto.
  exploit (Hcond (subst s m) (subst s' n) p q) as H; auto.
    {
    intros j u u' Hu.
    so (Hseq _#3 Hu) as (? & ? & _ & _ & ?).
    eexists; eauto.
    }
  destruct H as (R' & Hpl' & Hqr).
  so (basic_fun _#7 Hpl Hpl'); subst R'.
  exploit (Hcond (subst s n) (subst s' n) q q) as H; auto.
    {
    intros j u u' Hu.
    so (Hseq _#3 Hu) as (? & _ & _ & ? & ?).
    eexists; eauto.
    }
  destruct H as (R' & Hql & Hqr').
  so (basic_fun _#7 Hqr Hqr'); subst R'.
  auto.
  }
intros m n p q Hclp Hclq Hseqpq Hmn.
assert (forall (x : spcar K),
          rel (arrow_urel stop i (ceiling (S i) (den (pi1 A (std (S i) K x)))) (tp_urel toppg)) i (subst s (lam p)) (subst s' (lam q))) as Hp.
  {
  intros x.
  exists (subst (under 1 s) p), (subst (under 1 s') q).
  do2 5 split; auto.
    {
    eapply subst_closub; eauto.
    apply hygiene_auto; cbn; auto.
    }

    {
    eapply subst_closub; eauto.
    apply hygiene_auto; cbn; auto.
    }

    {
    simpsub; apply star_refl.
    }

    {
    simpsub; apply star_refl.
    }
  intros j r t Hj Hrt.
  destruct Hrt as (_ & Hrt).
  simpsub.
  eassert _ as H; [refine (Hseqpq _#3 (Hs' x j r t Hj _)) |].
    {
    refine (rel_from_dist _#6 _ Hrt).
    apply den_nonexpansive.
    apply (pi2 A).
    apply dist_symm.
    apply std_dist.
    omega.
    }
  simpsubin H.
  exact H.
  }
destruct Hmn as (Hclm & Hcln & _ & _ & Hact).
so (Hact i (subst s (lam p)) (subst s' (lam q)) (tp_urel toppg) (le_refl _)) as H.
lapply H; clear H.
2:{
  intro x.
  rewrite -> extend_urel_id.
  simpsub.
  rewrite -> std_arrow_is.
  change (rel (arrow_urel stop i (den (std (S i) (qtype stop) (pi1 A (std (S i) K (embed i K x))))) (tp_urel toppg)) i (lam (subst (under 1 s) p)) (lam (subst (under 1 s') q))).
  rewrite -> std_type_is.
  rewrite -> den_iutruncate.
  so (Hp (embed i K x)) as H.
  simpsubin H.
  exact H.
  }
intros H.
rewrite -> !extend_term_id in H.
simpsubin H.
refine (urel_equiv _#7 _ _ _ _ H); clear H.
  {
  eapply hygiene_subst; eauto.
  intros j Hj.
  destruct j as [| j]; simpsub; auto.
  }

  {
  eapply hygiene_subst; eauto.
  intros j Hj.
  destruct j as [| j]; simpsub; auto.
  }

  {
  apply steps_equiv.
  eapply star_step; [apply step_app2 |].
  simpsub.
  apply star_refl.
  }

  {
  apply steps_equiv.
  eapply star_step; [apply step_app2 |].
  simpsub.
  apply star_refl.
  }
Qed.


Lemma sound_union_formation :
  forall G a a' b b',
    pseq G (deqtype a a')
    -> pseq (cons (hyp_tm a) G) (deqtype b b')
    -> pseq G (deqtype (union a b) (union a' b')).
Proof.
intros G a b c d.
revert G.
refine (seq_pseq 4 [] a [] b [hyp_emp] c [hyp_emp] d 2 [] _ [_] _ _ _); cbn.
intros G Hcla Hclb Hclc Hcld Hseqab Hseqcd.
rewrite -> seq_eqtype in Hseqab, Hseqcd |- *.
intros i s s' Hs.
so (seqctx_impl_closub _#4 (pwctx_impl_seqctx _#4 Hs)) as (Hcls & Hcls').
so (Hseqab _#3 Hs) as (A & Hal & Har & Hbl & Hbr).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional_multi toppg i (den A) (subst (under 1 s) c) (subst (under 1 s') c) (subst (under 1 s) d) (subst (under 1 s') d)) as (C & Hcl & Hcr & Hdl & Hdr); eauto using subst_closub_under_permit.
  {
  intros j m p Hmp.
  assert (pwctx j (dot m s) (dot p s') (cons (hyp_tm a) G)) as Hss.
    {
    assert (j <= i) as Hj.
      {
      rewrite -> HeqA in Hmp.
      destruct Hmp.
      omega.
      }
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
      }

      {
      intros j' t t' Ht.
      so (Hseqab _#3 Ht) as (R & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqcd _#3 Hss) as (R & Hcl & Hcr & Hdl & Hdr).
  exists R.
  simpsub.
  auto.
  }
exists (iuunion stop A C).
simpsub.
do2 3 split; auto;
apply interp_eval_refl;
apply interp_union; auto.
Qed.


Lemma sound_union_formation_univ :
  forall G lv a a' b b',
    pseq G (deq a a' (univ lv))
    -> pseq (cons (hyp_tm a) G) (deq b b' (univ (subst sh1 lv)))
    -> pseq G (deq (union a b) (union a' b') (univ lv)).
Proof.
intros G lv a b c d.
revert G.
refine (seq_pseq 5 [] a [] b [hyp_emp] c [hyp_emp] d [] lv 2 [] _ [_] _ _ _); cbn.
intros G Hcla Hclb Hclc Hcld Hcllv Hseqab Hseqcd.
rewrite -> seq_univ in Hseqab, Hseqcd |- *.
intros i s s' Hs.
so (seqctx_impl_closub _#4 (pwctx_impl_seqctx _#4 Hs)) as (Hcls & Hcls').
so (Hseqab _#3 Hs) as (pg & A & Hlvl & Hlvr & Hal & Har & Hbl & Hbr).
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
exploit (extract_functional_multi pg i (den A) (subst (under 1 s) c) (subst (under 1 s') c) (subst (under 1 s) d) (subst (under 1 s') d)) as (C & Hcl & Hcr & Hdl & Hdr); eauto using subst_closub_under_permit.
  {
  intros j m p Hmp.
  assert (pwctx j (dot m s) (dot p s') (cons (hyp_tm a) G)) as Hss.
    {
    assert (j <= i) as Hj.
      {
      rewrite -> HeqA in Hmp.
      destruct Hmp.
      omega.
      }
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
      }

      {
      intros j' t t' Ht.
      so (Hseqab _#3 Ht) as (pg' & R & _ & _ & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqcd _#3 Hss) as (pg' & R & Hlvl' & _ & Hcl & Hcr & Hdl & Hdr).
  simpsubin Hlvl'.
  so (pginterp_fun _#3 Hlvl Hlvl'); subst pg'.
  exists R.
  simpsub.
  auto.
  }
exists pg, (iuunion stop A C).
simpsub.
do2 5 split; auto;
apply interp_eval_refl;
apply interp_union; auto.
Qed.


Lemma sound_union_intro :
  forall G a b p m n,
    pseq G (deq p p a)
    -> pseq G (deq m n (subst1 p b))
    -> pseq (cons (hyp_tm a) G) (deqtype b b)
    -> pseq G (deq m n (union a b)).
Proof.
intros G a b p m n.
revert G.
refine (seq_pseq 3 [hyp_emp] b [] m [] n 3 [] _ [] _ [_] _ _ _); cbn.
intros G Hclb Hclm Hcln Hseqp Hseqmn Hseqb.
rewrite -> seq_eqtype in Hseqb.
rewrite -> seq_deq in Hseqp, Hseqmn |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqp i s s' Hs) as (A & Hal & Har & Hp & _).
so (Hseqmn i s s' Hs) as (Bp & Hbpl & Hbpr & Hm & Hn & Hmn).
exploit (extract_functional toppg i (den A) (subst (under 1 s) b) (subst (under 1 s') b)) as H; eauto using subst_closub_under_permit.
  { 
  exact (f_equal den (basic_impl_iutruncate _#6 Hal)).
  }

  {
  intros j r t Hrt.
  so (basic_member_index _#9 Hal Hrt) as Hj.
  assert (pwctx j (dot r s) (dot t s') (cons (hyp_tm a) G)) as Hs'.
    {
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      apply (seqhyp_tm _#5 (iutruncate (S j) A)).
        {
        eapply basic_downward; eauto.
        }

        {
        eapply basic_downward; eauto.
        }

        {
        split; auto.
        }
      }

      {
      intros j' u u' Hu.
      so (Hseqp _#3 Hu) as (Q & Hl & Hr & _).
      eauto.
      }
    }
  so (Hseqb _#3 Hs') as (Q & Hl & Hr & _).
  exists Q.
  simpsub.
  auto.
  }
destruct H as (B & Hbl & Hbr).
exists (iuunion stop A B).
simpsub.
invert Hbl.
intros _ _ Hact.
so (Hact _#3 (le_refl _) Hp) as H.
simpsubin H.
simpsubin Hbpl.
so (basic_fun _#7 H Hbpl); clear H; subst Bp.
do2 4 split.
  {
  apply interp_eval_refl.
  apply interp_union; auto.
  }

  {
  apply interp_eval_refl.
  apply interp_union; auto.
  }

  {
  cbn.
  do2 2 split.
    {
    exists (subst s p), (subst s' p), Hp, (subst s' m).
    auto.
    }

    {
    exists (subst s p), (subst s' p), Hp, (subst s m).
    auto.
    }
  intros j q r C Hj Hqr.
  rewrite -> !extend_term_id.
  so (Hqr _ _ (urel_downward_leq _#6 Hj Hp)) as Hqr'.
  cbn in Hqr'.
  rewrite -> extend_urel_id in Hqr'.
  eapply arrow_action_app; eauto.
  refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hm)).
  apply den_nonexpansive.
  apply (pi2 B).
  apply dist_symm.
  apply urelspinj_dist; auto.
  }

  {
  cbn.
  do2 2 split.
    {
    exists (subst s p), (subst s' p), Hp, (subst s' n).
    auto.
    }

    {
    exists (subst s p), (subst s' p), Hp, (subst s n).
    auto.
    }
  intros j q r C Hj Hqr.
  rewrite -> !extend_term_id.
  so (Hqr _ _ (urel_downward_leq _#6 Hj Hp)) as Hqr'.
  cbn in Hqr'.
  rewrite -> extend_urel_id in Hqr'.
  eapply arrow_action_app; eauto.
  refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hn)).
  apply den_nonexpansive.
  apply (pi2 B).
  apply dist_symm.
  apply urelspinj_dist; auto.
  }

  {
  cbn.
  do2 2 split.
    {
    exists (subst s p), (subst s' p), Hp, (subst s' n).
    auto.
    }

    {
    exists (subst s p), (subst s' p), Hp, (subst s m).
    auto.
    }
  intros j q r C Hj Hqr.
  rewrite -> !extend_term_id.
  so (Hqr _ _ (urel_downward_leq _#6 Hj Hp)) as Hqr'.
  cbn in Hqr'.
  rewrite -> extend_urel_id in Hqr'.
  eapply arrow_action_app; eauto.
  refine (rel_from_dist _#6 _ (urel_downward_leq _#6 Hj Hmn)).
  apply den_nonexpansive.
  apply (pi2 B).
  apply dist_symm.
  apply urelspinj_dist; auto.
  }
Qed.


Lemma sound_union_elim :
  forall G a b c m n p q,
    pseq G (deq m n (union a b))
    -> pseq (cons (hyp_tm b) (cons (hyp_tm a) G)) (deq (subst (dot (var 0) (sh 2)) p) (subst (dot (var 0) (sh 2)) q) (subst (sh 2) c))
    -> pseq G (deq (subst1 m p) (subst1 n q) c).
Proof.
intros G a b c m n p q.
revert G.
refine (seq_pseq 5 [hyp_emp] b [hyp_emp] p [hyp_emp] q [] m [] n 2 [] _ [_; _] _ _ _); cbn.
intros G Hclb Hclp Hclq Hclm Hcln Hseqmn Hseqpq.
rewrite -> seq_deq in Hseqmn, Hseqpq |- *.
intros i s s' Hs.
so (Hseqmn i s s' Hs) as (R & Hl & Hr & Hm & Hn & Hmn).
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_union Hl).
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_union Hr).
intros A' B' Har Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iuunion_inj _#5 Heq) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
clear Heq Hl Hr.
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
assert (forall j r t u v (Hrt : rel (den A) j r t),
          rel (den (pi1 B (urelspinj (den A) j r t Hrt))) j u v
          -> pwctx j (dot u (dot r s)) (dot v (dot t s')) (cons (hyp_tm b) (cons (hyp_tm a) G))) as Hss.
  {
  intros j r t u v Hrt Huv.
  assert (j <= i) as Hj.
    {
    so Hrt as H.
    rewrite -> HeqA in H.
    destruct H.
    omega.
    }
  apply pwctx_cons_tm_seq.
    {
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
      }
  
      {
      intros j' w w' Hw.
      so (Hseqmn _#3 Hw) as (R & Hl & Hr & _).
      simpsubin Hl.
      simpsubin Hr.
      invert (basic_value_inv _#6 value_union Hl).
      intros A' B' Hal' _ Heq1.
      invert (basic_value_inv _#6 value_union Hr).
      intros A'' B'' Har' _ Heq2.
      so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
      so (iuunion_inj _#5 Heq) as H.
      injectionT H.
      intros <-.
      exists toppg, A'.
      auto.
      }
    }

    {
    eapply seqhyp_tm; eauto.
      {
      invert Hbl.
      intros _ _ Hact.
      so (Hact _ _ _ Hj Hrt) as H.
      simpsubin H.
      exact H.
      }

      {
      invert Hbr.
      intros _ _ Hact.
      so (Hact _ _ _ Hj Hrt) as H.
      simpsubin H.
      exact H.
      }
    }

    {
    intros j' w w' Hw.
    invert Hw.
    intros x x' y y' Hy Hx _ _ <- <-.
    so (Hseqmn _#3 Hy) as (R & Hl & Hr & _).
    simpsubin Hl.
    simpsubin Hr.
    invert (basic_value_inv _#6 value_union Hl).
    intros A' B' Hal' Hbl' Heq1.
    invert (basic_value_inv _#6 value_union Hr).
    intros A'' B'' _ Hbr' Heq2.
    so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
    clear Heq2.
    subst R.
    so (iuunion_inj _#5 Heq) as H.
    injectionT H.
    intros <-.
    injectionT H.
    intros <-.
    invertc Hx.
    intros A'' Hal'' _ Hx.
    so (basic_fun _#7 Hal' Hal'').
    subst A''.
    exists toppg, (pi1 B' (urelspinj _ _ _ _ Hx)).
    split.
      {
      invert Hbl'.
      intros _ _ Hact.
      so (Hact _ _ _ (le_refl _) Hx) as H.
      simpsubin H.
      exact H.
      }

      {
      invert Hbr'.
      intros _ _ Hact.
      so (Hact _ _ _ (le_refl _) Hx) as H.
      simpsubin H.
      exact H.
      }
    }
  }
assert (exists C,
          interp toppg true i (subst s c) C
          /\ interp toppg false i (subst s' c) C) as (C & Hcl & Hcr).
  {
  cbn in Hmn.
  destruct Hmn as (H & _).
  destruct H as (r & t & Hrt & u & Hmu).
  so (Hseqpq _ _ _ (Hss i r t (subst s m) u Hrt Hmu)) as (C & Hcl & Hcr & _).
  simpsubin Hcl.
  simpsubin Hcr.
  exists C.
  auto.
  }
exists C.
do2 4 split; auto.
  {
  simpsub.
  destruct Hm as (_ & _ & Hact).
  exploit (Hact i (subst s (lam p)) (subst s' (lam p)) (den C) (le_refl _)) as H.
    {
    intros r t Hrt.
    simpsub.
    apply arrow_action_lam; auto.
      {
      apply hygiene_auto; cbn.
      split; auto.
      eapply subst_closub_under_permit; eauto.
      }

      {
      apply hygiene_auto; cbn.
      split; auto.
      eapply subst_closub_under_permit; eauto.
      }
    intros j u v Hj Huv.
    simpsub.
    exploit (Hss j r t u v (urel_downward_leq _#6 Hj Hrt)) as Hss'.
      {
      rewrite -> extend_urel_id in Huv.
      refine (rel_from_dist _#6 _ Huv).
      cbn -[dist].
      apply den_nonexpansive.
      apply (pi2 B).
      apply dist_symm.
      apply urelspinj_dist.
      auto.
      }
    so (Hseqpq _#3 Hss') as (C' & Hcl' & _ & H & _).
    simpsubin Hcl'.
    simpsubin H.
    so (basic_fun _#7 (basic_downward _#7 Hj Hcl) Hcl').
    subst C'.
    destruct H as (_ & H).
    exact H.
    }
  simpsubin H.
  cbn [Nat.add] in H.
  rewrite -> !extend_term_id in H.
  refine (urel_equiv _#7 _ _ _ _ H).
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    eapply subst_closub; eauto.
    }

    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    eapply subst_closub; eauto.
    }

    {
    apply steps_equiv.
    eapply star_step.
      {
      apply step_app2.
      }
    simpsub.
    apply star_refl.
    }

    {
    apply steps_equiv.
    eapply star_step.
      {
      apply step_app2.
      }
    simpsub.
    apply star_refl.
    }
  }

  {
  simpsub.
  destruct Hn as (_ & _ & Hact).
  exploit (Hact i (subst s (lam q)) (subst s' (lam q)) (den C) (le_refl _)) as H.
    {
    intros r t Hrt.
    simpsub.
    apply arrow_action_lam; auto.
      {
      apply hygiene_auto; cbn.
      split; auto.
      eapply subst_closub_under_permit; eauto.
      }

      {
      apply hygiene_auto; cbn.
      split; auto.
      eapply subst_closub_under_permit; eauto.
      }
    intros j u v Hj Huv.
    simpsub.
    exploit (Hss j r t u v (urel_downward_leq _#6 Hj Hrt)) as Hss'.
      {
      rewrite -> extend_urel_id in Huv.
      refine (rel_from_dist _#6 _ Huv).
      cbn -[dist].
      apply den_nonexpansive.
      apply (pi2 B).
      apply dist_symm.
      apply urelspinj_dist.
      auto.
      }
    so (Hseqpq _#3 Hss') as (C' & Hcl' & _ & _ & H & _).
    simpsubin Hcl'.
    simpsubin H.
    so (basic_fun _#7 (basic_downward _#7 Hj Hcl) Hcl').
    subst C'.
    destruct H as (_ & H).
    exact H.
    }
  simpsubin H.
  cbn [Nat.add] in H.
  rewrite -> !extend_term_id in H.
  refine (urel_equiv _#7 _ _ _ _ H).
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    eapply subst_closub; eauto.
    }

    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    eapply subst_closub; eauto.
    }

    {
    apply steps_equiv.
    eapply star_step.
      {
      apply step_app2.
      }
    simpsub.
    apply star_refl.
    }

    {
    apply steps_equiv.
    eapply star_step.
      {
      apply step_app2.
      }
    simpsub.
    apply star_refl.
    }
  }

  {
  simpsub.
  destruct Hmn as (_ & _ & Hact).
  exploit (Hact i (subst s (lam p)) (subst s' (lam q)) (den C) (le_refl _)) as H.
    {
    intros r t Hrt.
    simpsub.
    apply arrow_action_lam; auto.
      {
      apply hygiene_auto; cbn.
      split; auto.
      eapply subst_closub_under_permit; eauto.
      }

      {
      apply hygiene_auto; cbn.
      split; auto.
      eapply subst_closub_under_permit; eauto.
      }
    intros j u v Hj Huv.
    simpsub.
    exploit (Hss j r t u v (urel_downward_leq _#6 Hj Hrt)) as Hss'.
      {
      rewrite -> extend_urel_id in Huv.
      refine (rel_from_dist _#6 _ Huv).
      cbn -[dist].
      apply den_nonexpansive.
      apply (pi2 B).
      apply dist_symm.
      apply urelspinj_dist.
      auto.
      }
    so (Hseqpq _#3 Hss') as (C' & Hcl' & _ & _ & _ & H).
    simpsubin Hcl'.
    simpsubin H.
    so (basic_fun _#7 (basic_downward _#7 Hj Hcl) Hcl').
    subst C'.
    destruct H as (_ & H).
    exact H.
    }
  simpsubin H.
  cbn [Nat.add] in H.
  rewrite -> !extend_term_id in H.
  refine (urel_equiv _#7 _ _ _ _ H).
    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    eapply subst_closub; eauto.
    }

    {
    eapply subst_closub; eauto.
    apply closub_dot; auto.
    eapply subst_closub; eauto.
    }

    {
    apply steps_equiv.
    eapply star_step.
      {
      apply step_app2.
      }
    simpsub.
    apply star_refl.
    }

    {
    apply steps_equiv.
    eapply star_step.
      {
      apply step_app2.
      }
    simpsub.
    apply star_refl.
    }
  }
Qed.


Lemma sound_union_elim_eqtype :
  forall G a b m n p q,
    pseq G (deq m n (union a b))
    -> pseq (cons (hyp_tm b) (cons (hyp_tm a) G)) (deqtype (subst (dot (var 0) (sh 2)) p) (subst (dot (var 0) (sh 2)) q))
    -> pseq G (deqtype (subst1 m p) (subst1 n q)).
Proof.
intros G a b m n p q.
revert G.
refine (seq_pseq 5 [hyp_emp] b [hyp_emp] p [hyp_emp] q [] m [] n 2 [] _ [_; _] _ _ _); cbn.
intros G Hclb Hclp Hclq Hclm Hcln Hseqmn Hseqpq.
rewrite -> seq_deq in Hseqmn.
rewrite -> seq_eqtype in Hseqpq |- *.
intros i s s' Hs.
so (Hseqmn i s s' Hs) as (R & Hl & Hr & Hm & Hn & Hmn).
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
simpsubin Hl.
simpsubin Hr.
invert (basic_value_inv _#6 value_union Hl).
intros A B Hal Hbl Heq1.
invert (basic_value_inv _#6 value_union Hr).
intros A' B' Har Hbr Heq2.
so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
clear Heq2.
subst R.
so (iuunion_inj _#5 Heq) as H.
injectionT H.
intros <-.
injectionT H.
intros <-.
clear Heq Hl Hr.
assert (den A = ceiling (S i) (den A)) as HeqA.
  {
  so (basic_impl_iutruncate _#6 Hal) as Heq.
  exact (f_equal den Heq).
  }
assert (forall j r t u v (Hrt : rel (den A) j r t),
          rel (den (pi1 B (urelspinj (den A) j r t Hrt))) j u v
          -> pwctx j (dot u (dot r s)) (dot v (dot t s')) (cons (hyp_tm b) (cons (hyp_tm a) G))) as Hss.
  {
  intros j r t u v Hrt Huv.
  assert (j <= i) as Hj.
    {
    so Hrt as H.
    rewrite -> HeqA in H.
    destruct H.
    omega.
    }
  apply pwctx_cons_tm_seq.
    {
    apply pwctx_cons_tm_seq; eauto using pwctx_downward.
      {
      eapply seqhyp_tm_leq; eauto using interp_increase, toppg_max.
      }
  
      {
      intros j' w w' Hw.
      so (Hseqmn _#3 Hw) as (R & Hl & Hr & _).
      simpsubin Hl.
      simpsubin Hr.
      invert (basic_value_inv _#6 value_union Hl).
      intros A' B' Hal' _ Heq1.
      invert (basic_value_inv _#6 value_union Hr).
      intros A'' B'' Har' _ Heq2.
      so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
      so (iuunion_inj _#5 Heq) as H.
      injectionT H.
      intros <-.
      exists toppg, A'.
      auto.
      }
    }

    {
    eapply seqhyp_tm; eauto.
      {
      invert Hbl.
      intros _ _ Hact.
      so (Hact _ _ _ Hj Hrt) as H.
      simpsubin H.
      exact H.
      }

      {
      invert Hbr.
      intros _ _ Hact.
      so (Hact _ _ _ Hj Hrt) as H.
      simpsubin H.
      exact H.
      }
    }

    {
    intros j' w w' Hw.
    invert Hw.
    intros x x' y y' Hy Hx _ _ <- <-.
    so (Hseqmn _#3 Hy) as (R & Hl & Hr & _).
    simpsubin Hl.
    simpsubin Hr.
    invert (basic_value_inv _#6 value_union Hl).
    intros A' B' Hal' Hbl' Heq1.
    invert (basic_value_inv _#6 value_union Hr).
    intros A'' B'' _ Hbr' Heq2.
    so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
    clear Heq2.
    subst R.
    so (iuunion_inj _#5 Heq) as H.
    injectionT H.
    intros <-.
    injectionT H.
    intros <-.
    invertc Hx.
    intros A'' Hal'' _ Hx.
    so (basic_fun _#7 Hal' Hal'').
    subst A''.
    exists toppg, (pi1 B' (urelspinj _ _ _ _ Hx)).
    split.
      {
      invert Hbl'.
      intros _ _ Hact.
      so (Hact _ _ _ (le_refl _) Hx) as H.
      simpsubin H.
      exact H.
      }

      {
      invert Hbr'.
      intros _ _ Hact.
      so (Hact _ _ _ (le_refl _) Hx) as H.
      simpsubin H.
      exact H.
      }
    }
  }
clear Hseqmn.
revert m n p q Hclp Hclq Hclm Hcln Hseqpq Hm Hn Hmn.
cut (forall m n p q,
        hygiene clo m
        -> hygiene clo n
        -> hygiene (permit (ctxpred G)) p
        -> hygiene (permit (ctxpred G)) q
        -> (forall j s s',
              pwctx j s s' (cons (hyp_tm b) (cons (hyp_tm a) G))
              -> rel (tp_urel toppg) j 
                   (subst s (subst (dot (var 0) (sh 2)) p))
                   (subst s' (subst (dot (var 0) (sh 2)) q)))
        -> rel (den (iuunion stop A B)) i m n
        -> rel (tp_urel toppg) i (subst (dot m s) p) (subst (dot n s') q)).
  {
  intro Hcond.
  intros m n p q Hclp Hclq Hclm Hcln Hseq Hm Hn Hmn.
  exploit (Hcond (subst s m) (subst s' m) p p) as H; eauto using subst_closub.
    {
    intros j u u' Hu.
    so (Hseq _#3 Hu) as (? & ? & ? & _).
    eexists; eauto.
    }
  destruct H as (R & Hpl & Hpr).
  exists R.
  do2 2 split.
    {
    simpsub; auto.
    }

    {
    simpsub; auto.
    }
  exploit (Hcond (subst s m) (subst s' n) p q) as H; eauto using subst_closub.
    {
    intros j u u' Hu.
    so (Hseq _#3 Hu) as (? & ? & _ & _ & ?).
    eexists; eauto.
    }
  destruct H as (R' & Hpl' & Hqr).
  so (basic_fun _#7 Hpl Hpl'); subst R'.
  exploit (Hcond (subst s n) (subst s' n) q q) as H; eauto using subst_closub.
    {
    intros j u u' Hu.
    so (Hseq _#3 Hu) as (? & ? & _ & ?).
    eexists; eauto.
    }
  destruct H as (R' & Hql & Hqr').
  so (basic_fun _#7 Hqr Hqr'); subst R'.
  simpsub.
  auto.
  }
intros m n p q Hclm Hcln Hclp Hclq Hpq Hmn.
destruct Hmn as (_ & _ & Hact).
exploit (Hact i (subst s (lam p)) (subst s' (lam q)) (tp_urel toppg) (le_refl _)) as H.
  {
  intros r t Hrt.
  simpsub.
  apply arrow_action_lam; auto.
    {
    apply hygiene_auto; cbn.
    split; auto.
    eapply subst_closub_under_permit; eauto.
    }

    {
    apply hygiene_auto; cbn.
    split; auto.
    eapply subst_closub_under_permit; eauto.
    }
  intros j u v Hj Huv.
  simpsub.
  exploit (Hss j r t u v (urel_downward_leq _#6 Hj Hrt)) as Hss'.
    {
    rewrite -> extend_urel_id in Huv.
    refine (rel_from_dist _#6 _ Huv).
    cbn -[dist].
    apply den_nonexpansive.
    apply (pi2 B).
    apply dist_symm.
    apply urelspinj_dist.
    auto.
    }
  so (Hpq _#3 Hss') as H.
  simpsubin H.
  exact H.
  }
simpsubin H.
rewrite -> !extend_term_id in H.
refine (urel_equiv _#7 _ _ _ _ H).
  {
  eapply subst_closub; eauto.
  apply closub_dot; auto.
  }

  {
  eapply subst_closub; eauto.
  apply closub_dot; auto.
  }

  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }

  {
  apply steps_equiv.
  eapply star_step.
    {
    apply step_app2.
    }
  simpsub.
  apply star_refl.
  }
Qed.
