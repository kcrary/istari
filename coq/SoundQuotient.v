
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

Require Import Urelsp.
Require Import Equivalence.
Require Import Ceiling.
Require Import Truncate.
Require Import ProperEquiv.
Require Import ProperDownward.
Require Import ProperLevel.
Require Import SemanticsSigma.
Require Import SemanticsQuotient.
Require Import SoundUtil.
Require Import SoundStructural.


Local Ltac prove_hygiene :=
  repeat (first [ eapply subst_closub; eauto
                | apply closub_dot
                | apply hygiene_auto; cbn; repeat2 split; auto
                ]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1;
  try (apply hygiene_var; cbn; auto; done).


Lemma ex_intro_2 :
  forall (A B : Type) (P : A -> B -> Prop) x y,
    P x y
    -> exists x y, P x y.
Proof.
intros A B P x y H.
exists x, y; auto.
Qed.


Lemma sound_quotient_formation_main :
  forall lvo G a b c d mr ml ms mt,
    hygiene (ctxpred G) a
    -> hygiene (ctxpred G) b
    -> hygiene (permit (permit (ctxpred G))) c
    -> hygiene (permit (permit (ctxpred G))) d
    -> (forall i s s',
          pwctx i s s' G
          -> exists pg R,
               pgointerp s lvo pg
               /\ interp pg true i (subst s a) R
               /\ interp pg false i (subst s' a) R
               /\ interp pg true i (subst s b) R
               /\ interp pg false i (subst s' b) R)
    -> (forall i s s',
          pwctx i s s' (hyp_tm (subst sh1 a) :: hyp_tm a :: G)
          -> exists pg R,
               pgointerp (compose (sh 2) s) lvo pg
               /\ interp pg true i (subst s c) R
               /\ interp pg false i (subst s' c) R)
    -> (forall i s s',
          pwctx i s s' (hyp_tm (subst sh1 a) :: hyp_tm a :: G)
          -> exists pg R,
               pgointerp (compose (sh 2) s) lvo pg
               /\ interp pg true i (subst s d) R
               /\ interp pg false i (subst s' d) R)
    -> (forall i s s',
          pwctx i s s' (hyp_tm c :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)
          -> exists R,
               interp toppg true i (subst s (subst sh1 d)) R
               /\ interp toppg false i (subst s' (subst sh1 d)) R
               /\ rel (den R) i (subst s mr) (subst s' mr))
    -> (forall i s s',
          pwctx i s s' (hyp_tm d :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)
          -> exists R,
               interp toppg true i (subst s (subst sh1 c)) R
               /\ interp toppg false i (subst s' (subst sh1 c)) R
               /\ rel (den R) i (subst s ml) (subst s' ml))
    -> (forall i s s',
          pwctx i s s' (hyp_tm c :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)
          -> exists R,
               interp toppg true i (subst s (subst (dot (var 2) (dot (var 1) (sh 3))) c)) R
               /\ interp toppg false i (subst s' (subst (dot (var 2) (dot (var 1) (sh 3))) c)) R
               /\ rel (den R) i (subst s ms) (subst s' ms))
    -> (forall i s s',
          pwctx i s s' (hyp_tm (subst (dot (var 1) (dot (var 2) (sh 4))) c)
                        :: hyp_tm (subst sh1 c)
                        :: hyp_tm (subst (sh 2) a) :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)
          -> exists R,
               interp toppg true i (subst s (subst (dot (var 2) (dot (var 4) (sh 5))) c)) R
               /\ interp toppg false i (subst s' (subst (dot (var 2) (dot (var 4) (sh 5))) c)) R
               /\ rel (den R) i (subst s mt) (subst s' mt))
    -> forall i s s',
         pwctx i s s' G
         -> exists pg R,
              pgointerp s lvo pg
              /\ interp pg true i (subst s (quotient a c)) R
              /\ interp pg false i (subst s' (quotient a c)) R
              /\ interp pg true i (subst s (quotient b d)) R
              /\ interp pg false i (subst s' (quotient b d)) R.
Proof.
intros lvo G a b c d mr ml ms mt Hcla Hclb Hclc Hcld Hseqab Hseqc Hseqd Hseqcd Hseqdc Hseqsymm Hseqtrans.
assert (forall i s s' R m1 m2 p1 p2,
          pwctx i s s' G
          -> interp toppg true i (subst s a) R
          -> interp toppg false i (subst s' a) R
          -> rel (den R) i m1 p1
          -> rel (den R) i m2 p2
          -> pwctx i (dot m2 (dot m1 s)) (dot p2 (dot p1 s')) (hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hsextgen.
  {
  intros i s s' R m1 m2 p1 p2 Hs Hal Har Hmp1 Hmp2.
  apply pwctx_cons_tm_seq.
    {
    apply pwctx_cons_tm_seq; auto.
      {
      apply (seqhyp_tm _#5 R); eauto.
      }

      {
      intros j' u u' Hu.
      so (Hseqab _#3 Hu) as (pg & R' & _ & Hl & Hr & _).
      eauto.
      }
    }

    {
    simpsub.
    apply (seqhyp_tm _#5 R); eauto.
    }

    {
    intros j' uu uu' Huu.
    invertc Huu.
    intros n q u u' Hu _ _ _ <- <-.
    simpsub.
    so (Hseqab _#3 Hu) as (pg & R' & _ & Hl & Hr & _).
    eauto.
    }
  }
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
simpsub.
so (Hseqab _#3 Hs) as (pg & A & Hlv & Hal & Har & Hbl & Hbr).
assert (forall j m1 m2 p1 p2,
          rel (den A) j m1 p1
          -> rel (den A) j m2 p2
          -> pwctx j (dot m2 (dot m1 s)) (dot p2 (dot p1 s')) (hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hsext.
  {
  intros j m1 m2 p1 p2 Hmp1 Hmp2.
  so (basic_member_index _#9 Hal Hmp1) as Hj.  
  eapply (Hsextgen _#3 (iutruncate (S j) A)); eauto using pwctx_downward.
    {
    apply (interp_increase pg); auto using toppg_max.
    eapply basic_downward; eauto.
    }

    {
    apply (interp_increase pg); auto using toppg_max.
    eapply basic_downward; eauto.
    }

    {
    split; auto.
    }

    {
    split; auto.
    }
  }
assert (forall e,
          hygiene (permit (permit (ctxpred G))) e
          -> (forall i s s',
                pwctx i s s' (hyp_tm (subst sh1 a) :: hyp_tm a :: G)
                -> exists pg R,
                     pgointerp (compose (sh 2) s) lvo pg
                     /\ interp pg true i (subst s e) R
                     /\ interp pg false i (subst s' e) R)
          -> exists (E : urelsp (prod_urel stop (den A) (den A)) -n> siurel_ofe),
               functional the_system pg true i (prod_urel stop (den A) (den A)) (subst (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) (compose s sh1))) e) E
               /\ functional the_system pg false i (prod_urel stop (den A) (den A)) (subst (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) (compose s' sh1))) e) E) as Hextract.
  {
  intros e Hcle Hseqe.
  exploit (extract_functional pg i (prod_urel stop (den A) (den A)) (subst (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) (compose s sh1))) e) (subst (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) (compose s' sh1))) e)) as H; auto.
    {
    so (f_equal den (basic_impl_iutruncate _#6 Hal)) as HeqA.
    cbn in HeqA.
    rewrite -> HeqA at 1 2.
    symmetry.
    apply ceiling_prod.
    }
  
    {
    eapply hygiene_subst; eauto.
    intros j Hj.
    destruct j as [|[|j]]; simpsub; prove_hygiene.
    }
  
    {
    eapply hygiene_subst; eauto.
    intros j Hj.
    destruct j as [|[|j]]; simpsub; prove_hygiene.
    }
  intros j m p Hmp.
  simpsub.
  cbn in Hmp.
  decompose Hmp.
  intros m1 p1 m2 p2 Hclm Hclp Hstepsm Hstepsp Hmp1 Hmp2.
  so (Hseqe _#3 (Hsext _#5 Hmp1 Hmp2)) as (pg' & R & Hlv' & Hl & Hr).
  simpsubin Hlv'.
  so (pgointerp_fun _#4 Hlv Hlv'); subst pg'.
  exists R.
  split; eapply basic_equiv; eauto; try prove_hygiene.
    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot.
      {
      apply equiv_symm.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi2); auto using step_ppi21.
        eauto.
        }
      apply star_one; apply step_ppi22.
      }

      {
      apply equivsub_dot; auto using equivsub_refl.
      apply equiv_symm.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1); auto using step_ppi11.
        eauto.
        }
      apply star_one; apply step_ppi12.
      }
    }

    {
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot.
      {
      apply equiv_symm.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi2); auto using step_ppi21.
        eauto.
        }
      apply star_one; apply step_ppi22.
      }

      {
      apply equivsub_dot; auto using equivsub_refl.
      apply equiv_symm.
      apply steps_equiv.
      eapply star_trans.
        {
        apply (star_map' _ _ ppi1); auto using step_ppi11.
        eauto.
        }
      apply star_one; apply step_ppi12.
      }
    }
  }
so (Hextract c Hclc Hseqc) as (C & Hcl & Hcr).
so (Hextract d Hcld Hseqd) as (D & Hdl & Hdr).
clear Hextract.  
assert (forall e (E : urelsp (prod_urel stop (den A) (den A)) -n> siurel_ofe) j m p n q u u' (Hmn : rel (den A) j m n) (Hpq : rel (den A) j p q),
          hygiene (permit (permit (ctxpred G))) e
          -> functional the_system pg true i (prod_urel stop (den A) (den A))
               (subst (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) (compose s sh1))) e) E
          -> functional the_system pg false i (prod_urel stop (den A) (den A))
               (subst (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) (compose s' sh1))) e) E
          -> (rel
                (den
                   (pi1 E
                      (urelspinj (prod_urel stop (den A) (den A)) _#3
                         (prod_action_ppair _#8 Hmn Hpq)))) j u u')
          -> seqhyp j u u' (hyp_tm (subst (dot p (dot m s)) e)) (hyp_tm (subst (dot q (dot n s')) e))) as Hhypu.
  {
  intros e E j m p n q u u' Hmn Hpq Hcle Hel Her Hu.
  so (urel_closed _#5 Hmn) as (Hclm & Hcln).
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  so (basic_member_index _#9 Hal Hmn) as Hj.
  eapply seqhyp_tm; eauto.
    {
    invert Hel.
    intros _ _ Hact.
    so (Hact _#3 Hj (prod_action_ppair _#8 Hmn Hpq)) as H.
    simpsubin H.
    apply (interp_increase pg); auto using toppg_max. 
    eapply basic_equiv; eauto; clear H; try prove_hygiene.
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot.
      {
      apply steps_equiv.
      apply star_one; apply step_ppi22.
      }

      {
      apply equivsub_dot; auto using equivsub_refl.
      apply steps_equiv.
      apply star_one; apply step_ppi12.
      }
    }

    {
    invert Her.
    intros _ _ Hact.
    so (Hact _#3 Hj (prod_action_ppair _#8 Hmn Hpq)) as H.
    simpsubin H.
    apply (interp_increase pg); auto using toppg_max.
    eapply basic_equiv; eauto; clear H; try prove_hygiene.
    apply equiv_funct; auto using equiv_refl.
    apply equivsub_dot.
      {
      apply steps_equiv.
      apply star_one; apply step_ppi22.
      }

      {
      apply equivsub_dot; auto using equivsub_refl.
      apply steps_equiv.
      apply star_one; apply step_ppi12.
      }
    }
  }
assert (symmish stop (den A) (fun x => den (pi1 C x))) as hs.
  {
  intros j m n p q u u' Hmn Hpq Hu.
  so (urel_closed _#5 Hmn) as (Hclm & Hcln).
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  so (basic_member_index _#9 Hal Hmn) as Hj.
  assert (pwctx j (dot u (dot p (dot m s))) (dot u' (dot q (dot n s'))) (hyp_tm c :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hs'.
    {
    apply pwctx_cons_tm_seq; auto.
      {
      eapply Hhypu; eauto.
      }

      {
      intros j' w w' Hw.
      so (Hseqc _#3 Hw) as (pg' & R & _ & Hl & Hr).
      eauto.
      }
    }
  so (Hseqsymm _#3 Hs') as (R & Hl & _ & Hinh).
  simpsubin Hl.
  exists (subst (dot u (dot p (dot m s))) ms), (subst (dot u' (dot q (dot n s'))) ms).
  force_exact Hinh.
  f_equal.
  clear Hinh.
  f_equal.
  invert Hcl.
  intros _ _ Hact.
  so (Hact _#3 Hj (prod_action_ppair _#8 Hpq Hmn)) as H; clear Hact.
  simpsubin H.
  refine (interp_fun _#7 Hl (basic_equiv _#7 _ _ H)); try prove_hygiene.
  apply equiv_funct; auto using equiv_refl.
  apply equivsub_dot.
    {
    apply steps_equiv.
    apply star_one; apply step_ppi22.
    }

    {
    apply equivsub_dot; auto using equivsub_refl.
    apply steps_equiv.
    apply star_one; apply step_ppi12.
    }
  }
assert (transish stop (den A) (fun x => den (pi1 C x))) as ht.
  {
  intros j m n p q r t u1 u1' u2 u2' Hmn Hpq Hrt Hu1 Hu2.
  so (basic_member_index _#9 Hal Hmn) as Hj.
  assert (pwctx j 
            (dot u2 (dot u1 (dot r (dot p (dot m s)))))
            (dot u2' (dot u1' (dot t (dot q (dot n s')))))
            (hyp_tm (subst (dot (var 1) (dot (var 2) (sh 4))) c)
             :: hyp_tm (subst sh1 c)
             :: hyp_tm (subst (sh 2) a) :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hs'.
    {
    apply pwctx_cons_tm_seq.
      {
      apply pwctx_cons_tm_seq.
        {
        apply pwctx_cons_tm_seq.
          {
          apply Hsext; auto.
          }

          {
          simpsub.
          apply (seqhyp_tm _#5 (iutruncate (S j) A)).
            {
            apply (interp_increase pg); auto using toppg_max.
            eapply basic_downward; eauto.
            }
    
            {
            apply (interp_increase pg); auto using toppg_max.
            eapply basic_downward; eauto.
            }
    
            {
            split; auto.
            }
          }

          {
          intros j' uu uu' Huu.
          invertc Huu.
          intros x y uu1 uu1' Huu _ _ _ <- <-.
          invertc Huu.
          intros x' y' u u' Hu _ _ _ <- <-.
          simpsub.
          so (Hseqab _#3 Hu) as (pg' & R & _ & Hl & Hr & _).
          eauto.
          }
        }

        {
        simpsub.
        eapply Hhypu; eauto.
        }
      
        {
        intros j' ww ww' Hww.
        invertc Hww.
        intros x1 y1 w w' Hw _ _ _ <- <-.
        simpsub.
        so (Hseqc _#3 Hw) as (pg' & R & _ & Hl & Hr).
        eauto.
        }
      }

      {
      simpsub.
      eapply Hhypu; eauto.
      }

      {
      intros j' ww ww' Hww.
      invertc Hww.
      intros x1 y1 ww1 ww1' Hww _ _ _ <- <-.
      invertc Hww.
      intros x2 y2 ww2 ww2' Hww Hxy2 _ _ <- <-.
      invertc Hww.
      intros x3 y3 ww3 ww3' Hww Hxy3 _ _ <- <-.
      invertc Hww.
      intros x4 y4 w w' Hw _ _ _ <- <-.
      simpsub.
      invertc Hxy2.
      intros A' Hal' Har' Hxy2.
      simpsubin Hal'.
      simpsubin Har'.
      invertc Hxy3.
      intros A'' Hal'' _ Hxy3.
      simpsubin Hal''.
      so (basic_fun _#7 Hal' Hal''); subst A''.
      so (Hseqc _#3 (Hsextgen j' w w' A' x3 x2 y3 y2 Hw Hal' Har' Hxy3 Hxy2)) as (pg' & R & _ & Hl & Hr).
      eauto.
      }
    }
  so (Hseqtrans _#3 Hs') as (R & Hl & _ & Hinh).
  simpsubin Hl.
  exists (subst (dot u2 (dot u1 (dot r (dot p (dot m s))))) mt), (subst (dot u2' (dot u1' (dot t (dot q (dot n s'))))) mt).
  force_exact Hinh.
  f_equal.
  clear Hinh.
  f_equal.
  invert Hcl.
  intros _ _ Hact.
  so (Hact _#3 Hj (prod_action_ppair _#8 Hmn Hrt)) as H; clear Hact.
  simpsubin H.
  so (urel_closed _#5 Hmn) as (Hclm & _).
  so (urel_closed _#5 Hrt) as (Hclr & _).
  refine (interp_fun _#7 Hl (basic_equiv _#7 _ _ H)); try prove_hygiene.
  apply equiv_funct; auto using equiv_refl.
  apply equivsub_dot.
    {
    apply steps_equiv.
    apply star_one; apply step_ppi22.
    }

    {
    apply equivsub_dot; auto using equivsub_refl.
    apply steps_equiv.
    apply star_one; apply step_ppi12.
    }
  }
assert (forall j m n p q (Hmn : rel (den A) j m n) (Hpq : rel (den A) j p q),
          (exists u u',
             rel (den (pi1 C 
                         (urelspinj (prod_urel stop (den A) (den A)) _#3
                            (prod_action_ppair _#8 Hmn Hpq))))
             j u u')
          <->
          (exists u u',
             rel (den (pi1 D
                         (urelspinj (prod_urel stop (den A) (den A)) _#3
                          (prod_action_ppair _#8 Hmn Hpq))))
             j u u')) as Hciffd.
  {
  intros j m n p q Hmn Hpq.
  so (basic_member_index _#9 Hal Hmn) as Hj.
  so (urel_closed _#5 Hmn) as (Hclm & Hcln).
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  split.
    {
    intros (u & u' & Hu).
    assert (pwctx j (dot u (dot p (dot m s))) (dot u' (dot q (dot n s'))) (hyp_tm c :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hs'.
      {
      apply pwctx_cons_tm_seq.
        {
        simpsub.
        apply Hsext; auto.
        }
  
        {
        eapply Hhypu; eauto.
        }
  
        {
        intros j' w w' Hw.
        so (Hseqc _#3 Hw) as (pg' & R & _ & Hl & Hr).
        eauto.
        }
      }
    so (Hseqcd _#3 Hs') as (R & Hl & _ & Hinh).
    clear Hu.
    simpsubin Hl.
    invert Hdl.
    intros _ _ Hact.
    so (Hact _#3 Hj (prod_action_ppair _#8 Hmn Hpq)) as H; clear Hact.
    simpsubin H.
    eassert _ as Heq; [refine (interp_fun _#7 Hl (basic_equiv _#7 _ _ H)) |]; clear H Hl; try prove_hygiene.
      {
      apply equiv_funct; auto using equiv_refl.
      apply equivsub_dot.
        {
        apply steps_equiv; apply star_one; apply step_ppi22.
        }
  
        {
        apply equivsub_dot; auto using equivsub_refl.
        apply steps_equiv; apply star_one; apply step_ppi12.
        }
      }
    subst R.
    eauto.
    }

    {
    intros (u & u' & Hu).
    assert (pwctx j (dot u (dot p (dot m s))) (dot u' (dot q (dot n s'))) (hyp_tm d :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hs'.
      {
      apply pwctx_cons_tm_seq.
        {
        simpsub.
        apply Hsext; auto.
        }
  
        {
        eapply Hhypu; eauto.
        }
  
        {
        intros j' w w' Hw.
        so (Hseqd _#3 Hw) as (pg' & R & _ & Hl & Hr).
        eauto.
        }
      }
    so (Hseqdc _#3 Hs') as (R & Hl & _ & Hinh).
    clear Hu.
    simpsubin Hl.
    invert Hcl.
    intros _ _ Hact.
    so (Hact _#3 Hj (prod_action_ppair _#8 Hmn Hpq)) as H; clear Hact.
    simpsubin H.
    eassert _ as Heq; [refine (interp_fun _#7 Hl (basic_equiv _#7 _ _ H)) |]; clear H Hl; try prove_hygiene.
      {
      apply equiv_funct; auto using equiv_refl.
      apply equivsub_dot.
        {
        apply steps_equiv; apply star_one; apply step_ppi22.
        }
  
        {
        apply equivsub_dot; auto using equivsub_refl.
        apply steps_equiv; apply star_one; apply step_ppi12.
        }
      }
    subst R.
    eauto.
    }
  }
assert (symmish stop (den A) (fun x => den (pi1 D x))) as hs'.
  {
  intros j m n p q u u' Hmn Hpq Hu.
  so (basic_member_index _#9 Hal Hmn) as Hj.
  so (urel_closed _#5 Hmn) as (Hclm & Hcln).
  so (urel_closed _#5 Hpq) as (Hclp & Hclq).
  apply Hciffd.
  so (Hciffd _#7 ander (ex_intro_2 _#5 Hu)) as H.
  clear u u' Hu.
  destruct H as (u & u' & Hu).
  so (hs _#9 Hu) as (v & v' & Hv).
  exists v, v'.
  exact Hv.
  }
assert (transish stop (den A) (fun x => den (pi1 D x))) as ht'.
  {
  intros j m n p q r t u1 u1' u2 u2' Hmn Hpq Hrt Hu1 Hu2.
  apply Hciffd.
  so (Hciffd _#7 ander (ex_intro_2 _#5 Hu1)) as H.
  clear u1 u1' Hu1.
  destruct H as (u1 & u1' & Hu1).
  so (Hciffd _#7 ander (ex_intro_2 _#5 Hu2)) as H.
  clear u2 u2' Hu2.
  destruct H as (u2 & u2' & Hu2).
  so (ht _#14 Hu1 Hu2) as (u3 & u3' & Hu3).
  eauto.
  }
assert (iuquotient stop A C hs ht = iuquotient stop A D hs' ht') as Heq.
  {
  unfold iuquotient, iubase.
  f_equal.
  apply urel_extensionality.
  fextensionality 3.
  intros j m p.
  cbn.
  pextensionality.
    {
    intro H.
    decompose H.
    intros n q u u' Hmq Hnp Hu.
    so (Hciffd _#7 andel (ex_intro_2 _#5 Hu)) as H.
    clear u u' Hu.
    destruct H as (u & u' & Hu).
    exists n, q, u, u', Hmq, Hnp.
    exact Hu.
    }

    {
    intro H.
    decompose H.
    intros n q u u' Hmq Hnp Hu.
    so (Hciffd _#7 ander (ex_intro_2 _#5 Hu)) as H.
    clear u u' Hu.
    destruct H as (u & u' & Hu).
    exists n, q, u, u', Hmq, Hnp.
    exact Hu.
    }
  }
exists pg, (iuquotient stop A C hs ht).
replace (1 + 0) with 1 by omega.
replace (1 + 1) with 2 by omega.
do2 4 split; auto.
  {
  apply interp_eval_refl.
  apply interp_quotient; auto.
  simpsub.
  exact Hcl.
  }

  {
  apply interp_eval_refl.
  apply interp_quotient; auto.
  simpsub.
  exact Hcr.
  }

  {
  rewrite -> Heq.
  apply interp_eval_refl.
  apply interp_quotient; auto.
  simpsub.
  exact Hdl.
  }

  {
  rewrite -> Heq.
  apply interp_eval_refl.
  apply interp_quotient; auto.
  simpsub.
  exact Hdr.
  }
Qed.


Lemma sound_quotient_formation :
  forall G a a' b b' mr ml ms mt,
    pseq G (deqtype a a')
    -> pseq (hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deqtype b b)
    -> pseq (hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deqtype b' b')
    (* b implies b' *)
    -> pseq (hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)
         (deq mr mr (subst sh1 b'))
    (* b' implies b *)
    -> pseq (hyp_tm b' :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)
         (deq ml ml (subst sh1 b))
    (* symmetry *)
    -> pseq (hyp_tm b ::
            hyp_tm (subst sh1 a) ::
            hyp_tm a :: 
            G) 
         (deq ms ms (subst (dot (var 2) (dot (var 1) (sh 3))) b))
    (* transitivity *)
    -> pseq (hyp_tm (subst (dot (var 1) (dot (var 2) (sh 4))) b) :: 
            hyp_tm (subst sh1 b) ::
            hyp_tm (subst (sh 2) a) :: 
            hyp_tm (subst sh1 a) :: 
            hyp_tm a :: 
            G)
         (deq mt mt (subst (dot (var 2) (dot (var 4) (sh 5))) b))
    -> pseq G (deqtype (quotient a b) (quotient a' b')).
Proof.
intros G a b c d mr ml ms mt.
revert G.
refine (seq_pseq 4 [] a [] b [hyp_emp; hyp_emp] c [hyp_emp; hyp_emp] d 7 [] _ [_; _] _ [_; _] _ [_; _; _] _ [_; _; _] _ [_; _; _] _ [_; _; _; _; _] _ _ _); cbn.
intros G Hcla Hclb Hclc Hcld Hseqab Hseqc Hseqd Hseqcd Hseqdc Hseqsymm Hseqtrans.
rewrite -> seq_eqtype in Hseqab, Hseqc, Hseqd |- *.
rewrite -> seq_deq in Hseqcd, Hseqdc, Hseqsymm, Hseqtrans.
exploit (sound_quotient_formation_main None G a b c d mr ml ms mt) as H; auto.
  {
  intros i s s' Hs.
  so (Hseqab _#3 Hs) as (R & Hal & Har & Hbl & Hbr).
  exists toppg, R.
  do2 4 split; auto.
  reflexivity.
  }

  {
  intros i s s' Hs.
  so (Hseqc _#3 Hs) as (R & Hl & Hr & _).
  exists toppg, R.
  do2 2 split; auto.
  reflexivity.
  }

  {
  intros i s s' Hs.
  so (Hseqd _#3 Hs) as (R & Hl & Hr & _).
  exists toppg, R.
  do2 2 split; auto.
  reflexivity.
  }

  {
  intros i s s' Hs.
  so (Hseqcd _#3 Hs) as (R & Hl & Hr & H & _).
  eauto.
  }

  {
  intros i s s' Hs.
  so (Hseqdc _#3 Hs) as (R & Hl & Hr & H & _).
  eauto.
  }

  {
  intros i s s' Hs.
  so (Hseqsymm _#3 Hs) as (R & Hl & Hr & H & _).
  eauto.
  }

  {
  intros i s s' Hs.
  so (Hseqtrans _#3 Hs) as (R & Hl & Hr & H & _).
  eauto.
  }
intros i s s' Hs.
so (H _#3 Hs) as (pg & R & Hlv & Hacl & Hacr & Hbdl & Hbdr).
cbn in Hlv.
subst pg.
eauto.
Qed.


Lemma sound_quotient_formation_univ :
  forall G lv a a' b b' mr ml ms mt,
    pseq G (deq a a' (univ lv))
    -> pseq (hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deq b b (univ (subst (sh 2) lv)))
    -> pseq (hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deq b' b' (univ (subst (sh 2) lv)))
    (* b implies b' *)
    -> pseq (hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)
         (deq mr mr (subst sh1 b'))
    (* b' implies b *)
    -> pseq (hyp_tm b' :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)
         (deq ml ml (subst sh1 b))
    (* symmetry *)
    -> pseq (hyp_tm b ::
            hyp_tm (subst sh1 a) ::
            hyp_tm a :: 
            G) 
         (deq ms ms (subst (dot (var 2) (dot (var 1) (sh 3))) b))
    (* transitivity *)
    -> pseq (hyp_tm (subst (dot (var 1) (dot (var 2) (sh 4))) b) :: 
            hyp_tm (subst sh1 b) ::
            hyp_tm (subst (sh 2) a) :: 
            hyp_tm (subst sh1 a) :: 
            hyp_tm a :: 
            G)
         (deq mt mt (subst (dot (var 2) (dot (var 4) (sh 5))) b))
    -> pseq G (deq (quotient a b) (quotient a' b') (univ lv)).
Proof.
intros G lv a b c d mr ml ms mt.
revert G.
refine (seq_pseq 4 [] a [] b [hyp_emp; hyp_emp] c [hyp_emp; hyp_emp] d 7 [] _ [_; _] _ [_; _] _ [_; _; _] _ [_; _; _] _ [_; _; _] _ [_; _; _; _; _] _ _ _); cbn.
intros G Hcla Hclb Hclc Hcld Hseqab Hseqc Hseqd Hseqcd Hseqdc Hseqsymm Hseqtrans.
rewrite -> seq_univ in Hseqab, Hseqc, Hseqd |- *.
rewrite -> seq_deq in Hseqcd, Hseqdc, Hseqsymm, Hseqtrans.
exploit (sound_quotient_formation_main (Some lv) G a b c d mr ml ms mt) as H; auto.
  {
  intros i s s' Hs.
  so (Hseqab _#3 Hs) as (pg & R & Hlv & _ & Hal & Har & Hbl & Hbr).
  exists pg, R.
  do2 3 split; eauto.
  }

  {
  intros i s s' Hs.
  so (Hseqc _#3 Hs) as (pg & R & Hlv & _ & Hl & Hr & _).
  simpsubin Hlv.
  exists pg, R.
  do2 2 split; eauto.
  }

  {
  intros i s s' Hs.
  so (Hseqd _#3 Hs) as (pg & R & Hlv & _ & Hl & Hr & _).
  simpsubin Hlv.
  exists pg, R.
  do2 2 split; eauto.
  }

  {
  intros i s s' Hs.
  so (Hseqcd _#3 Hs) as (R & Hl & Hr & H & _).
  eauto.
  }

  {
  intros i s s' Hs.
  so (Hseqdc _#3 Hs) as (R & Hl & Hr & H & _).
  eauto.
  }

  {
  intros i s s' Hs.
  so (Hseqsymm _#3 Hs) as (R & Hl & Hr & H & _).
  eauto.
  }

  {
  intros i s s' Hs.
  so (Hseqtrans _#3 Hs) as (R & Hl & Hr & H & _).
  eauto.
  }
intros i s s' Hs.
so (H _#3 Hs) as (pg & R & Hlv & Hacl & Hacr & Hbdl & Hbdr); clear H.
so (Hseqab _#3 Hs) as (pg' & A & Hlvl & Hlvr & Hal & Har & Hbl & Hbr).
unfold pgointerp in Hlv.
so (pginterp_fun _#3 Hlv Hlvl); subst pg'.
exists pg, R.
do2 4 split; auto.
Qed.


Lemma sound_quotient_intro :
  forall G a b m n p,
    pseq G (deqtype (quotient a b) (quotient a b))
    -> pseq G (deq m m a)
    -> pseq G (deq n n a)
    -> pseq G (deq p p (subst (dot n (dot m id)) b))
    -> pseq G (deq m n (quotient a b)).
Proof.
intros G a b m n p.
revert G.
refine (seq_pseq 5 [] a [hyp_emp; hyp_emp] b [] m [] n [] p 4 [] _ [] _ [] _ [] _ _ _); cbn.
intros G Hcla Hclb Hclm Hcln Hclp Hseqab Hseqm Hseqn Hseqp.
rewrite -> seq_eqtype in Hseqab.
rewrite -> seq_deq in Hseqm, Hseqn, Hseqp |- *.
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqab _#3 Hs) as (R & Habl & Habr & _).
exists R.
do2 2 split; auto.
simpsubin Habl.
invert (basic_value_inv _#6 value_quotient Habl).
intros A B hs ht Hal Hbl <-.
so (Hseqm _#3 Hs) as (A' & Hal' & _ & Hm & _).
so (basic_fun _#7 Hal Hal'); subst A'.
clear Hal'.
so (Hseqn _#3 Hs) as (A' & Hal' & _ & Hn & _).
so (basic_fun _#7 Hal Hal'); subst A'.
clear Hal'.
so (Hseqp _#3 Hs) as (Bmn & Hbmn & _ & Hp & _).
invert Hbl.
intros _ _ Hact.
so (Hact _#3 (le_refl _) (prod_action_ppair _#8 Hm Hn)) as Hbmn'; clear Hact.
simpsubin Hbmn.
simpsubin Hbmn'.
eassert _ as H; [refine (basic_fun _#7 Hbmn (basic_equiv _#7 _ _ Hbmn')) |]; try prove_hygiene.
  {
  apply equiv_funct; auto using equiv_refl.
  apply equivsub_dot.
    {
    apply steps_equiv; apply star_one; apply step_ppi22.
    }

    {
    apply equivsub_dot; auto using equivsub_refl.
    apply steps_equiv; apply star_one; apply step_ppi12.
    }
  }
subst Bmn.
clear Hbmn Hbmn'.
do2 2 split.
  {
  so (hs _#7 Hm Hn Hp) as (x & x' & Hx).
  so (ht _#11 Hm Hn Hm Hp Hx) as (q & q' & Hq).
  clear x x' Hx.
  exists (subst s m), (subst s' m), q, q', Hm, Hm.
  exact Hq.
  }

  {
  so (hs _#7 Hm Hn Hp) as (x & x' & Hx).
  so (ht _#11 Hn Hm Hn Hx Hp) as (q & q' & Hq).
  clear x x' Hx.
  exists (subst s n), (subst s' n), q, q', Hn, Hn.
  exact Hq.
  }

  {
  exists (subst s n), (subst s' m), (subst s p), (subst s' p), Hm, Hn.
  exact Hp.
  }
Qed.


Lemma sound_quotient_elim :
  forall G a b c m n p q,
    pseq G (deq m n (quotient a b))
    -> pseq (hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deqtype b b)
    -> pseq (hyp_tm (quotient a b) :: G) (deqtype c c)
    -> pseq (hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deq (subst (sh 2) p) (subst (dot (var 1) (sh 3)) q) (subst (sh 2) c))
    -> pseq G (deq (subst1 m p) (subst1 n q) (subst1 m c)).
Proof.
intros G a b c m n p q.
revert G.
refine (seq_pseq 2 [] a [hyp_emp; hyp_emp] b 4 [] _ [_; _] _ [_] _ [_; _; _] _ _ _); cbn.
intros G Hcla Hclb Hseqmn Hseqb Hseqc Hseqpq.
rewrite -> seq_eqtype in Hseqb, Hseqc.
rewrite -> seq_deq in Hseqmn, Hseqpq |- *.
assert (forall i s s',
          pwctx i s s' G
          -> exists A,
               interp toppg true i (subst s a) A
               /\ interp toppg false i (subst s' a) A) as Hseqa.
  {
  intros i s s' Hs.
  so (Hseqmn _#3 Hs) as (R & Habl & Habr & _).
  simpsubin Habl.
  simpsubin Habr.
  invert (basic_value_inv _#6 value_quotient Habl).
  intros A B hs ht Hal Hbl Heq1.
  clear Habl.
  invert (basic_value_inv _#6 value_quotient Habr).
  intros A' B' hs' ht' Har _ Heq2.
  so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
  clear Heq1 Heq2.
  so (iuquotient_inj _#9 Heq); subst A'.
  eauto.
  }
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqmn _#3 Hs) as (R & Habl & Habr & Hm & Hn & Hmn).
simpsubin Habl.
simpsubin Habr.
invert (basic_value_inv _#6 value_quotient Habl).
intros A B hs ht Hal Hbl <-.
so (Hseqa _#3 Hs) as (A' & Hal' & Har).
so (basic_fun _#7 Hal Hal'); subst A'.
clear Hal'.
assert (forall r t,
          rel (quotient_urel stop (den A) (nearrow_compose den_ne B) hs ht) i r t
          -> pwctx i (dot r s) (dot t s') (hyp_tm (quotient a b) :: G)) as Hsm.
  {
  intros r t Hrt.
  apply pwctx_cons_tm_seq; auto.
    {
    simpsub.
    eapply seqhyp_tm; eauto.
    }

    {
    intros j w w' Hw.
    exists toppg.
    so (Hseqmn _#3 Hw) as (R & Hl & Hr & _).
    eauto.
    }
  }
so (Hseqc _#3 (Hsm _ _ Hm)) as (C & Hcl & Hcr & _).
clear Hseqmn.
exists C.
simpsub.
do2 2 split; auto.
assert (forall r t r' t' u u' (Hrt : rel (den A) i r t') (Hrt' : rel (den A) i r' t),
          rel (den (pi1 B (urelspinj (prod_urel stop (den A) (den A)) _#3
                             (prod_action_ppair _#8 Hrt Hrt')))) i u u'
          -> pwctx i (dot u (dot r' (dot r s))) (dot u' (dot t (dot t' s'))) (hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hsext.
  {
  intros r t r' t' u u' Hrt Hrt' Hu.
  so (urel_closed _#5 Hrt) as (Hclr & Hclt').
  so (urel_closed _#5 Hrt') as (Hclr' & Hclt).
  assert (pwctx i (dot r' (dot r s)) (dot t (dot t' s')) (hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hs'.
    {
    apply pwctx_cons_tm_seq.
      {
      apply pwctx_cons_tm_seq; auto.
        {
        eapply seqhyp_tm; eauto.
        }

        {
        intros j w w' Hw.
        exists toppg.
        apply Hseqa; auto.
        }
      }

      {
      simpsub.
      eapply seqhyp_tm; eauto.
      }

      {
      intros j ww ww' Hww.
      invertc Hww.
      intros x y w w' Hw _ _ _ <- <-.
      simpsub.
      exists toppg.
      apply Hseqa; auto.
      }
    }
  apply pwctx_cons_tm_seq; auto.
    {
    so (Hseqb _#3 Hs') as (Brt & Hbrtl & Hbrtr & _).
    invert Hbl.
    intros _ _ Hact.
    so (Hact _#3 (le_refl _) (prod_action_ppair _#8 Hrt Hrt')) as Hbrtl'; clear Hact.
    simpsubin Hbrtl'.
    eassert _ as H; [refine (basic_fun _#7 Hbrtl (basic_equiv _#7 _ _ Hbrtl')) |]; try prove_hygiene.
      {
      apply equiv_funct; auto using equiv_refl.
      apply equivsub_dot.
        {
        apply steps_equiv; apply star_one; apply step_ppi22.
        }
    
        {
        apply equivsub_dot; auto using equivsub_refl.
        apply steps_equiv; apply star_one; apply step_ppi12.
        }
      }
    subst Brt.
    clear Hbrtl'.
    eapply seqhyp_tm; eauto.
    }

    {
    intros j w w' Hw.
    so (Hseqb _#3 Hw) as (R & Hl & Hr & _).
    eauto.
    }
  }
do2 2 split.
  {
  cbn in Hm.
  decompose Hm.
  intros r t u u' Hmt Hrm Hu.
  so (hs _#7 Hmt Hrm Hu) as (x & x' & Hx).
  so (ht _#11 Hrm Hmt Hrm Hx Hu) as (v & v' & Hv).
  clear x x' Hx.
  so (Hsext _#6 Hmt Hrm Hu) as Hs'.
  so (Hsext _#6 Hrm Hrm Hv) as Hs''.
  so (Hseqpq _#3 Hs') as (C' & Hcl' & _ & _ & _ & Hpq).
  so (Hseqpq _#3 Hs'') as (C'' & _ & Hcr' & Hp' & _ & Hpq').
  simpsubin Hcl'.
  simpsubin Hcr'.
  so (basic_fun _#7 Hcl Hcl'); subst C'.
  so (basic_fun _#7 Hcr Hcr'); subst C''.
  simpsubin Hpq.
  simpsubin Hp'.
  simpsubin Hpq'.
  eapply urel_zigzag; eauto.
  }

  {
  so Hn as H.
  cbn in H.
  decompose H.
  intros r t u u' Hnt Hrn Hu.
  so (hs _#7 Hnt Hrn Hu) as (x & x' & Hx).
  so (ht _#11 Hnt Hrn Hnt Hu Hx) as (v & v' & Hv).
  clear x x' Hx.
  so (Hsext _#6 Hnt Hrn Hu) as Hs'.
  so (Hsext _#6 Hnt Hnt Hv) as Hs''.
  so (Hseqpq _#3 Hs') as (C' & Hcl' & _ & _ & _ & Hpq).
  so (Hseqpq _#3 Hs'') as (C'' & Hcl'' & _ & _ & Hq' & Hpq').
  simpsubin Hcl'.
  simpsubin Hcl''.
  so (basic_fun _#7 Hcl' Hcl''); subst C''.
  clear Hcl''.
  assert (C = C').
    {
    so (Hseqc _#3 (Hsm _ _ Hmn)) as (R & Hcml & _ & _ & Hcnr).
    so (Hseqc _#3 (Hsm _ _ Hn)) as (R' & Hcnl & _ & _ & Hcnr').
    so (basic_fun _#7 Hcl Hcml); subst R.
    so (basic_fun _#7 Hcnr Hcnr'); subst R'.
    so (basic_fun _#7 Hcl' Hcnl); subst C'.
    reflexivity.
    }
  subst C'.
  simpsubin Hpq.
  simpsubin Hq'.
  simpsubin Hpq'.
  apply (urel_zigzag _#4 (subst (dot t s') q) (subst (dot (subst s n) s) p)); auto.
  }

  {
  cbn in Hmn.
  decompose Hmn.
  intros r t u u' Hmt Hrn Hu.
  so (Hsext _#6 Hmt Hrn Hu) as Hs'.
  so (Hseqpq _#3 Hs') as (C' & Hcl' & _ & _ & _ & Hpq).
  simpsubin Hcl'.
  so (basic_fun _#7 Hcl Hcl'); subst C'.
  simpsubin Hpq.
  exact Hpq.
  }
Qed.


(* Ought to factor out the commonality between this and sound_quotient_elim. *)

Lemma sound_quotient_elim_eqtype :
  forall G a b m n c d,
    pseq G (deq m n (quotient a b))
    -> pseq (hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deqtype b b)
    -> pseq (hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deqtype (subst (sh 2) c) (subst (dot (var 1) (sh 3)) d))
    -> pseq G (deqtype (subst1 m c) (subst1 n d)).
Proof.
intros G a b m n c d.
revert G.
refine (seq_pseq 2 [] a [hyp_emp; hyp_emp] b 3 [] _ [_; _] _ [_; _; _] _ _ _); cbn.
intros G Hcla Hclb Hseqmn Hseqb Hseqcd.
rewrite -> seq_deq in Hseqmn.
rewrite -> seq_eqtype in Hseqb, Hseqcd |- *.
assert (forall i s s',
          pwctx i s s' G
          -> exists A,
               interp toppg true i (subst s a) A
               /\ interp toppg false i (subst s' a) A) as Hseqa.
  {
  intros i s s' Hs.
  so (Hseqmn _#3 Hs) as (R & Habl & Habr & _).
  simpsubin Habl.
  simpsubin Habr.
  invert (basic_value_inv _#6 value_quotient Habl).
  intros A B hs ht Hal Hbl Heq1.
  clear Habl.
  invert (basic_value_inv _#6 value_quotient Habr).
  intros A' B' hs' ht' Har _ Heq2.
  so (eqtrans Heq1 (eqsymm Heq2)) as Heq.
  clear Heq1 Heq2.
  so (iuquotient_inj _#9 Heq); subst A'.
  eauto.
  }
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
simpsub.
so (Hseqmn _#3 Hs) as (R & Habl & _ & Hm & Hn & Hmn).
clear Hseqmn.
simpsubin Habl.
replace (1 + 0) with 1 in Habl by omega.
replace (1 + 1) with 2 in Habl by omega.
invert (basic_value_inv _#6 value_quotient Habl).
intros A B hs ht Hal Hbl <-.
clear Habl.
so (Hseqa _#3 Hs) as (A' & Hal' & Har).
so (basic_fun _#7 Hal Hal'); subst A'.
clear Hal'.
assert (forall r t r' t' u u' (Hrt : rel (den A) i r t') (Hrt' : rel (den A) i r' t),
          rel (den (pi1 B (urelspinj (prod_urel stop (den A) (den A)) _#3
                             (prod_action_ppair _#8 Hrt Hrt')))) i u u'
          -> pwctx i (dot u (dot r' (dot r s))) (dot u' (dot t (dot t' s'))) (hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hsext.
  {
  intros r t r' t' u u' Hrt Hrt' Hu.
  so (urel_closed _#5 Hrt) as (Hclr & Hclt').
  so (urel_closed _#5 Hrt') as (Hclr' & Hclt).
  assert (pwctx i (dot r' (dot r s)) (dot t (dot t' s')) (hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hs'.
    {
    apply pwctx_cons_tm_seq.
      {
      apply pwctx_cons_tm_seq; auto.
        {
        eapply seqhyp_tm; eauto.
        }

        {
        intros j w w' Hw.
        exists toppg.
        apply Hseqa; auto.
        }
      }

      {
      simpsub.
      eapply seqhyp_tm; eauto.
      }

      {
      intros j ww ww' Hww.
      invertc Hww.
      intros x y w w' Hw _ _ _ <- <-.
      simpsub.
      exists toppg.
      apply Hseqa; auto.
      }
    }
  apply pwctx_cons_tm_seq; auto.
    {
    so (Hseqb _#3 Hs') as (Brt & Hbrtl & Hbrtr & _).
    invert Hbl.
    intros _ _ Hact.
    so (Hact _#3 (le_refl _) (prod_action_ppair _#8 Hrt Hrt')) as Hbrtl'; clear Hact.
    simpsubin Hbrtl'.
    eassert _ as H; [refine (basic_fun _#7 Hbrtl (basic_equiv _#7 _ _ Hbrtl')) |]; try prove_hygiene.
      {
      apply equiv_funct; auto using equiv_refl.
      apply equivsub_dot.
        {
        apply steps_equiv; apply star_one; apply step_ppi22.
        }
    
        {
        apply equivsub_dot; auto using equivsub_refl.
        apply steps_equiv; apply star_one; apply step_ppi12.
        }
      }
    subst Brt.
    clear Hbrtl'.
    eapply seqhyp_tm; eauto.
    }

    {
    intros j w w' Hw.
    so (Hseqb _#3 Hw) as (R & Hl & Hr & _).
    eauto.
    }
  }
assert (exists R,
          interp toppg true i (subst (dot (subst s m) s) c) R
          /\ interp toppg false i (subst (dot (subst s' m) s') c) R) as Hmc.
  {
  cbn in Hm.
  decompose Hm.
  intros r t u u' Hmt Hrm Hu.
  so (hs _#7 Hmt Hrm Hu) as (x & x' & Hx).
  so (ht _#11 Hrm Hmt Hrm Hx Hu) as (v & v' & Hv).
  clear x x' Hx.
  so (Hsext _#6 Hmt Hrm Hu) as Hs'.
  so (Hsext _#6 Hrm Hrm Hv) as Hs''.
  so (Hseqcd _#3 Hs') as (R & Hcl & _ & Hdl & _).
  so (Hseqcd _#3 Hs'') as (R' & _ & Hcr' & Hdl' & _).
  exists R.
  simpsubin Hcl.
  simpsubin Hcr'.
  simpsubin Hdl.
  simpsubin Hdl'.
  so (basic_fun _#7 Hdl Hdl'); subst R'.
  split; auto.
  }
assert (exists R,
          interp toppg true i (subst (dot (subst s n) s) d) R
          /\ interp toppg false i (subst (dot (subst s' n) s') d) R) as Hnd.
  {
  cbn in Hn.
  decompose Hn.
  intros r t u u' Hnt Hrn Hu.
  so (hs _#7 Hnt Hrn Hu) as (x & x' & Hx).
  so (ht _#11 Hnt Hrn Hnt Hu Hx) as (v & v' & Hv).
  clear x x' Hx.
  so (Hsext _#6 Hnt Hrn Hu) as Hs'.
  so (Hsext _#6 Hnt Hnt Hv) as Hs''.
  so (Hseqcd _#3 Hs') as (R & _ & Hcr & _ & Hdr).
  so (Hseqcd _#3 Hs'') as (R' & _ & Hcr' & Hdl' & _).
  exists R.
  simpsubin Hcr.
  simpsubin Hcr'.
  simpsubin Hdl'.
  simpsubin Hdr.
  so (basic_fun _#7 Hcr Hcr'); subst R'.
  split; auto.
  }
assert (exists R,
          interp toppg true i (subst (dot (subst s m) s) c) R
          /\ interp toppg false i (subst (dot (subst s' n) s') d) R) as Hmcnd.
  {
  cbn in Hmn.
  decompose Hmn.
  intros r t u u' Hmt Hrn Hu.
  so (Hsext _#6 Hmt Hrn Hu) as Hs'.
  so (Hseqcd _#3 Hs') as (R & Hcl & _ & _ & Hdr).
  simpsubin Hcl.
  simpsubin Hdr.
  eauto.
  }
destruct Hmc as (R & Hmcl & Hmcr).
destruct Hnd as (R' & Hndl & Hndr).
destruct Hmcnd as (R'' & Hmcl' & Hndr').
so (basic_fun _#7 Hmcl Hmcl'); subst R''.
so (basic_fun _#7 Hndr Hndr'); subst R'.
eauto.
Qed.


Lemma sound_descent :
  forall G a b c m n p,
    pseq G (deq m m a)
    -> pseq G (deq n n a)
    -> pseq G (deq m n (quotient a b))
    -> pseq (hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deqtype b b)
    -> pseq G (deqtype c c)
    -> pseq (hyp_tm (subst (dot n (dot m id)) b) :: G) (deq (subst sh1 p) (subst sh1 p) (subst sh1 c))
    -> pseq G (deq p p c).
Proof.
intros G a b c m n p.
revert G.
refine (seq_pseq 2 [] a [hyp_emp; hyp_emp] b 6 [] _ [] _ [] _ [_; _] _ [] _ [_] _ _ _); cbn.
intros G Hcla Hclb Hseqm Hseqn Hseqmn Hseqb Hseqc Hseqp.
rewrite -> seq_eqtype in Hseqb, Hseqc.
rewrite -> seq_deq in Hseqm, Hseqn, Hseqmn, Hseqp |- *.
assert (forall i s s',
          pwctx i s s' G
          -> exists R,
               interp toppg true i (subst s a) R
               /\ interp toppg false i (subst s' a) R) as Hseqa.
  {
  intros i s s' Hs.
  so (Hseqm i s s' Hs) as (R & Hal & Har & _).
  eauto.
  }
assert (forall i s s',
          pwctx i s s' G
          -> pwctx i (dot (subst s n) (dot (subst s m) s)) (dot (subst s' n) (dot (subst s' m) s')) (hyp_tm (subst sh1 a) :: hyp_tm a :: G)) as Hsmn.
  {
  intros i s s' Hs.
  so (Hseqm _#3 Hs) as (A & Hal & Har & Hm & _).
  so (Hseqn _#3 Hs) as (A' & Hal' & _ & Hn & _).
  so (interp_fun _#7 Hal Hal'); subst A'; clear Hal'.
  apply pwctx_cons_tm_seq.
    {
    apply pwctx_cons_tm_seq; auto.
      {
      eapply seqhyp_tm; eauto.
      }
      
      {
      intros j t t' Ht.
      exists toppg.
      apply Hseqa; auto.
      }
    }

    {
    simpsub.
    eapply seqhyp_tm; eauto.
    }

    {
    intros j tt tt' Htt.
    invertc Htt.
    intros u v t t' Ht Huv _ _ <- <-.
    exists toppg.
    simpsub.
    apply Hseqa; auto.
    }
  }
intros i s s' Hs.
so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
so (Hseqm _#3 Hs) as (A & Hal & Har & Hm & _).
so (Hseqn _#3 Hs) as (A' & Hal' & _ & Hn & _).
so (interp_fun _#7 Hal Hal'); subst A'; clear Hal'.
so (Hseqmn _#3 Hs) as (Q & Habl & Habr & Hmq & Hnq & Hmnq).
so (Hseqc _#3 Hs) as (C & Hcl & Hcr & _).
clear Hseqm Hseqn Hseqmn Hseqc.
exists C.
do2 2 split; auto.
cut (rel (den C) i (subst s p) (subst s' p)).
  {
  intro; auto.
  }
cut (exists u v R,
       interp toppg true i (subst (dot (subst s n) (dot (subst s m) s)) b) R
       /\ interp toppg false i (subst (dot (subst s' n) (dot (subst s' m) s')) b) R
       /\ rel (den R) i u v).
  {
  intros (u & v & Bmn & Hbl & Hbr & Huv).
  exploit (Hseqp i (dot u s) (dot v s')) as H.
    {
    apply pwctx_cons_tm_seq; auto.
      {
      simpsub.
      eapply seqhyp_tm; eauto.
      }

      {
      intros j t t' Ht.
      exists toppg.
      exploit (Hseqb j (dot (subst t n) (dot (subst t m) t)) (dot (subst t' n) (dot (subst t' m) t'))) as H; auto.
      destruct H as (R & Hl & Hr & _).
      simpsub.
      eauto.
      }
    }
  destruct H as (C' & Hcl' & _ & _ & _ & Hp).
  simpsubin Hcl'.
  so (interp_fun _#7 Hcl Hcl'); subst C'.
  simpsubin Hp.
  exact Hp.
  }
clear C Hcl Hcr p Hseqp.
simpsubin Habl.
simpsubin Habr.
replace (dot (var 0) (dot (var (1 + 0)) (compose s (sh (1 + 1))))) with (under 2 s) in Habl.
2:{
  rewrite -> !under_succ.
  simpsub.
  reflexivity.
  }
replace (dot (var 0) (dot (var (1 + 0)) (compose s' (sh (1 + 1))))) with (under 2 s') in Habr.
2:{
  rewrite -> !under_succ.
  simpsub.
  reflexivity.
  }
exploit (Hseqb i (dot (subst s n) (dot (subst s m) s)) (dot (subst s' n) (dot (subst s' m) s'))) as H; auto.
destruct H as (Bmn & Hbmnl & Hbmnr & _).    
invert (basic_value_inv _#6 value_quotient Habl).
intros A' B hs ht Hal' Hbl Heq.
so (interp_fun _#7 Hal Hal'); subst A'; clear Hal'.
invert (basic_value_inv _#6 value_quotient Habr).
intros A' B' hs' ht' Har' Hbr Heq'.
so (interp_fun _#7 Har Har'); subst A'; clear Har'.
revert Heq'.
subst Q.
intro Heq.
cbn in Hmnq.
decompose Hmnq.
intros r r' t u Hmr Hrn Htu.
invert Hbl.
intros _ _ Hfunct.
match type of Htu with
| rel (den (pi1  _ (urelspinj _ _ _ _ ?X))) _ _ _ => set (Hmrrn := X) in Htu
end.
so (Hfunct i (ppair (subst s m) r) (ppair r' (subst s' n)) (le_refl _) Hmrrn) as Hbmrrn; clear Hfunct.
simpsubin Hbmrrn.
exists t, u.
eexists.
cut (interp toppg false i (subst (dot (subst s' n) (dot (subst s' m) s')) b) (pi1 B (urelspinj (prod_urel stop (den A) (den A)) i (ppair (subst s m) r) (ppair r' (subst s' n)) Hmrrn))).
  {
  intro Hr.
  do2 2 split; [| exact Hr | exact Htu].
  so (Hseqb _ _ _ (Hsmn _#3 Hs)) as (R & Hl & Hr' & _).
  so (interp_fun _#7 Hr Hr'); subst R.
  exact Hl.
  }
exploit (Hseqb i (dot r (dot (subst s m) s)) (dot (subst s' n) (dot (subst s' m) s'))) as H.
  {
  apply pwctx_cons_tm_seq.
    {
    apply pwctx_cons_tm_seq; auto.
      {
      eapply seqhyp_tm; eauto.
      }

      {
      intros j v v' Hv.
      exists toppg.
      apply Hseqa; auto.
      }
    }

    {
    simpsub.
    eapply seqhyp_tm; eauto.
    }

    {
    intros j vv vv' Hvv.
    exists toppg.
    invertc Hvv.
    intros w x v v' Hv _ _ _ <- <-.
    simpsub.
    apply Hseqa; auto.
    }
  }
destruct H as (R & Hl & Hr & _).
eassert _ as Hbmrrn'; [refine (basic_equiv _#5 (subst (dot r (dot (subst s m) s)) b) _ _ _ Hbmrrn) |].
  {
  eapply hygiene_subst; eauto.
  intros j Hj.
  destruct j as [|[|j]].
    {
    simpsub.
    exact (urel_closed_1 _#5 Hrn).
    }

    {
    simpsub.
    exact (urel_closed_1 _#5 Hmr).
    }
  simpsub.
  eapply project_closub; eauto.
  }

  {
  apply equiv_funct; auto using equiv_refl.
  apply equivsub_dot.
    {
    apply steps_equiv.
    apply star_one.
    apply step_ppi22.
    }
  apply equivsub_dot; auto using equivsub_refl.
  apply steps_equiv.
  apply star_one.
  apply step_ppi12.
  }
so (basic_fun _#7 Hl Hbmrrn'); subst R.
exact Hr.
Qed.


Lemma quotient_strengthen_left :
  forall w A B hs ht i m n q,
    rel (quotient_urel w A B hs ht) i m n
    -> rel A i m q
    -> rel (quotient_urel w A B hs ht) i m q.
Proof.
intros w A B hs ht i m n q Hmn Hmq.
destruct Hmn as (p & r & x & y & Hmr & Hpn & Hmr_pn).
so (hs _#9 Hmr_pn) as (x' & y' & Hpn_mr).
so (ht _#14 Hmr_pn Hpn_mr) as (x'' & y'' & Hmr_mr).
exists m, r, x'', y'', Hmr, Hmq.
eapply rel_from_dist; eauto.
apply (pi2 B).
apply urelspinj_dist_diff; auto.
exists m, r, m, q.
so (urel_closed _#5 Hmr) as (Hclm & Hclr).
so (urel_closed _#5 Hmq) as (_ & Hclq).
do2 4 split; auto using star_refl; apply hygiene_auto; cbn; auto.
Qed.


Lemma quotient_strengthen_right :
  forall w A B hs ht i m n p,
    rel (quotient_urel w A B hs ht) i m n
    -> rel A i p n
    -> rel (quotient_urel w A B hs ht) i p n.
Proof.
intros w A B hs ht i m n p Hmn Hpn.
destruct Hmn as (r & q & x & y & Hmq & Hrn & Hmq_rn).
so (hs _#9 Hmq_rn) as (x' & y' & Hrn_mq).
so (ht _#14 Hrn_mq Hmq_rn) as (x'' & y'' & Hrm_rn).
exists r, n, x'', y'', Hpn, Hrn.
eapply rel_from_dist; eauto.
apply (pi2 B).
apply urelspinj_dist_diff; auto.
exists r, n, r, n.
so (urel_closed _#5 Hrn) as (Hclr & Hcln).
do2 4 split; auto using star_refl; apply hygiene_auto; cbn; auto.
Qed.


Lemma quotient_context_strengthen_left :
  forall G1 G2 a b i s s' s'',
    pwctx i s s' (G2 ++ hyp_tm (quotient a b) :: G1)
    -> seqctx i s s'' (G2 ++ hyp_tm a :: G1)
    -> seqctx i s s'' (G2 ++ hyp_tm (quotient a b) :: G1).
Proof.
intros G1 G2 a b.
induct G2.

(* nil *)
{
cbn.
intros i ss ss' ss'' Hs Hs'.
invertc Hs.
intros m n s s' Hs Hmn Hleft Hright <- <-.
invertc Hs'.
intros q s'' Hs' Hmq <-.
apply seqctx_cons; auto.
simpsubin Hmn.
simpsubin Hmq.
simpsub.
invertc Hmn.
intros R Hl Hrr Hmn.
invertc Hmq.
intros A Hal Har Hpq.
apply (seqhyp_tm _#5 R); auto.
  {
  exploit (Hleft i false s'') as H; auto using smaller_refl.
  rewrite -> qpromote_hyp_tm in H.
  simpsubin H.
  invertc H.
  intros R' Hrr' Hr.
  so (interp_fun _#7 Hrr Hrr'); subst R'.
  exact Hr.
  }
invert (basic_value_inv _#6 value_quotient Hl).
intros A' B hs ht Hal' Hb <-.
so (basic_fun _#7 Hal Hal'); subst A'; clear Hal'.
clear Hl Hrr.
eapply quotient_strengthen_left; eauto.
}

(* cons *)
{
intros h G2 IH i ss ss' ss'' Hss Hss'.
invertc Hss.
intros m n s s' Hs Hmn Hleft Hright <- <-.
invertc Hss'.
intros q s'' Hs' Hmq <-.
cbn [List.app].
apply seqctx_cons; auto.
eapply IH; eauto.
}
Qed.


Lemma quotient_context_strengthen_right :
  forall G1 G2 a b i s s' s'',
    pwctx i s s' (G2 ++ hyp_tm (quotient a b) :: G1)
    -> seqctx i s'' s' (G2 ++ hyp_tm a :: G1)
    -> seqctx i s'' s' (G2 ++ hyp_tm (quotient a b) :: G1).
Proof.
intros G1 G2 a b.
induct G2.

(* nil *)
{
cbn.
intros i ss ss' ss'' Hs Hs'.
invertc Hs.
intros m n s s' Hs Hmn Hleft Hright <- <-.
invertc Hs'.
intros p s'' Hs' Hpn <-.
apply seqctx_cons; auto.
simpsubin Hmn.
simpsubin Hpn.
simpsub.
invertc Hmn.
intros R Hll Hr Hmn.
invertc Hpn.
intros A Hal Har Hpn.
apply (seqhyp_tm _#5 R); auto.
  {
  exploit (Hright i false s'') as H; auto using smaller_refl.
  rewrite -> qpromote_hyp_tm in H.
  simpsubin H.
  invertc H.
  intros R' Hll' Hl.
  so (interp_fun _#7 Hll Hll'); subst R'.
  exact Hl.
  }
invert (basic_value_inv _#6 value_quotient Hr).
intros A' B hs ht Har' Hb <-.
so (basic_fun _#7 Har Har'); subst A'; clear Har'.
clear Hr Hll.
eapply quotient_strengthen_right; eauto.
}

(* cons *)
{
intros h G2 IH i ss ss' ss'' Hss Hss'.
invertc Hss.
intros m n s s' Hs Hmn Hleft Hright <- <-.
invertc Hss'.
intros q s'' Hs' Hmq <-.
cbn [List.app].
apply seqctx_cons; auto.
eapply IH; eauto.
}
Qed.


Lemma dequotient_context :
  forall G1 G2 a b i s s',
    pwctx i s s' (G2 ++ hyp_tm (quotient a b) :: G1)
    -> exists A (B B' : urelsp (prod_urel stop (den A) (den A)) -n> wiurel_ofe stop)
         m p n q u u' s'' (Hmq : rel (den A) i m q) (Hnp : rel (den A) i n p),
           project s (length G2) = m
           /\ project s' (length G2) = p
           /\ project s'' (length G2) = q
           /\ compose (under (length G2) (dot q sh1)) s' = s''
           /\ pwctx i s s'' (G2 ++ hyp_tm a :: G1)
           /\ interp toppg true i (subst (compose (sh (S (length G2))) s) a) A
           /\ interp toppg false i (subst (compose (sh (S (length G2))) s') a) A
           /\ functional the_system toppg true i (prod_urel stop (den A) (den A)) (subst (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) (compose (compose (sh (S (length G2))) s) sh1))) b) B
           /\ functional the_system toppg false i (prod_urel stop (den A) (den A)) (subst (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) (compose (compose (sh (S (length G2))) s') sh1))) b) B'
           /\ rel (den (pi1 B (urelspinj (prod_urel stop (den A) (den A)) i (ppair m n) (ppair q p) (prod_action_ppair _#8 Hmq Hnp)))) i u u'
           /\ symmish _ (den A) (fun x => den (pi1 B x))
           /\ symmish _ (den A) (fun x => den (pi1 B' x))
           /\ transish _ (den A) (fun x => den (pi1 B x))
           /\ transish _ (den A) (fun x => den (pi1 B' x)).
Proof.
intros G1 G2 a b i.
induct G2.

(* nil *)
{
intros ss ss' Hss.
cbn in Hss.
invertc Hss.
intros m p s s' Hs Hmp Hleft Hright <- <-.
simpsubin Hmp.
invertc Hmp.
intros R Hl Hr Hmp.
invert (basic_value_inv _#6 value_quotient Hl).
intros A B hs ht Hal Hbl Heq.
invert (basic_value_inv _#6 value_quotient Hr).
intros A' B' hs' ht' Har Hbr Heq'.
clear Hl Hr.
so (iuquotient_inj _#9 (eqtrans Heq (eqsymm Heq'))); subst A'.
clear Heq'.
subst R.
destruct Hmp as (n & q & u & u' & Hmq & Hnp & Hu).
cbn in Hu.
so (urel_closed _#5 Hmq) as (_ & Hclq).
exists A, B, B', m, p, n, q, u, u', (dot q s'), Hmq, Hnp.
simpsub.
simpsubin Hbl.
simpsubin Hbr.
do2 13 split; auto.
  {
  f_equal.
  apply subst_into_closed; auto.
  }
cbn.
apply pwctx_cons; auto.
  {
  simpsub.
  apply (seqhyp_tm _#5 A); auto.
  }

  {
  clear B hs ht Hbl B' hs' ht' Hbr Hu.
  intros j pr s3 Hsmaller Hs3.
  exploit (Hleft j pr s3) as H; auto.
  rewrite -> qpromote_hyp_tm in H |- *.
  simpsubin H.
  simpsub.
  invertc H.
  intros R Hquot Hquot'.
  so (basic_value_inv _#6 value_quotient Hquot) as H.
  invertc H.
  intros A' B hs ht Har' _ Heq.
  so (interp_fun _#7 (basic_downward _#7 (smaller_impl_le _#3 Hsmaller) Har) Har').
  subst A'.
  so (basic_value_inv _#6 value_quotient Hquot') as H.
  invertc H.
  intros A' B' hs' ht' Har'' _ Heq'.
  so (iuquotient_inj _#9 (eqtrans Heq (eqsymm Heq'))).
  subst A'.
  eapply relhyp_tm; eauto.
  }

  {
  clear B hs ht Hbl B' hs' ht' Hbr Hu.
  intros j pr s3 Hsmaller Hs3.
  exploit (Hright j pr s3) as H; auto.
  rewrite -> qpromote_hyp_tm in H |- *.
  simpsubin H.
  simpsub.
  invertc H.
  intros R Hquot Hquot'.
  so (basic_value_inv _#6 value_quotient Hquot) as H.
  invertc H.
  intros A' B hs ht Hal' _ Heq.
  so (interp_fun _#7 (basic_downward _#7 (smaller_impl_le _#3 Hsmaller) Hal) Hal').
  subst A'.
  so (basic_value_inv _#6 value_quotient Hquot') as H.
  invertc H.
  intros A' B' hs' ht' Hal'' _ Heq'.
  so (iuquotient_inj _#9 (eqtrans Heq (eqsymm Heq'))).
  subst A'.
  eapply relhyp_tm; eauto.
  }
}

(* cons *)
{
intros h G2 IH ss ss' Hss.
cbn [List.app] in Hss.
invertc Hss.
intros x y s s' Hs Hpq Hleft Hright <- <-.
so (IH s s' Hs) as (A & B & B' & m & p & n & q & u & u' & s'' & Hmq & Hnp & Heqm & Heqp & Heqq & Heqs'' & Hs'' & Hal & Har & Hbl & Hbr & Hu & Hsymm & Hsymm' & Htrans & Htrans'); clear IH.
exists A, B, B', m, p, n, q, u, u', (dot y s''), Hmq, Hnp.
do2 13 split; auto.
  {
  cbn [length].
  simpsub.
  f_equal; auto.
  }
clear A B B' m p n q u u' Hmq Hnp Heqm Heqp Heqq Heqs'' Hal Har Hbl Hbr Hu Hsymm Hsymm' Htrans Htrans'.
so (quotient_context_strengthen_left _#8 Hs (pwctx_impl_seqctx _#4 Hs'')) as Hqs''.
apply pwctx_cons; auto.
  {
  eapply seqhyp_relhyp_2; eauto.
  exploit (Hleft i false s'') as H; auto using smaller_refl.
  }
  
  {
  intros j pr s3 Hsmaller Hs3.
  exploit (Hleft j pr s'') as H1; eauto using seqctx_smaller.
  exploit (Hleft j pr s3) as H2; auto.
    {
    so (pwctx_smaller _#6 Hsmaller Hs) as Hs_j.
    rewrite -> qpromote_app, qpromote_cons, qpromote_hyp_tm in Hs_j, Hs3 |- *.
    eapply quotient_context_strengthen_left; eauto.
    }
  exact (relhyp_trans _#5 (relhyp_symm _#4 H1) H2).
  }

  {
  intros j pr s3 Hsmaller Hs3.
  exploit (Hright j pr s3); auto.
  so (pwctx_smaller _#6 Hsmaller Hs) as Hs_j.
  so (seqctx_smaller _#6 Hsmaller Hqs'') as Hs''_j.
  so (seqctx_pwctx_left _#5 Hs_j Hs''_j) as Hs''_jpw.
  rewrite -> qpromote_app, qpromote_cons, qpromote_hyp_tm in Hs_j, Hs''_j, Hs''_jpw, Hs3 |- *.
  so (quotient_context_strengthen_right _#8 Hs''_jpw Hs3) as Hs3_st.
  exact (seqctx_zigzag _#6 Hs3_st Hs''_j (pwctx_impl_seqctx _#4 Hs_j)).
  }
}
Qed.


Lemma sound_quotient_hyp :
  forall G1 G2 a b m n c,
    pseq (G2 ++ hyp_tm (quotient a b) :: G1) (deqtype c c)
    -> pseq (G2 ++ hyp_tm a :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) c)
    -> pseq (G2 ++ hyp_tm (quotient a b) :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) c).
Proof.
intros G1 G2 a b m n c.
revert G1.
refine (seq_pseq_hyp 0 2 _ [_] _ _ [_] _ _ [_] _ _); cbn.
intros G1 Hseqc Hseqmn _.
rewrite -> seq_eqtype in Hseqc.
rewrite -> seq_deq in Hseqmn |- *.
intros i s s' Hs.
so (dequotient_context _#7 Hs) as (_ & _ & _ & _ & _ & _ & q & _ & _ & s'' & _ & _ & _ & _ & _ & Heqs'' & Hs'' & _).
assert (compose (under (length (G2)) sh1) s' = compose (under (length (G2)) sh1) s'') as Heq.
  {
  rewrite <- Heqs''.
  rewrite <- compose_assoc.
  rewrite <- compose_under.
  simpsub.
  reflexivity.
  }
clear Heqs''.
so (Hseqc _#3 Hs) as (C & Hcl & Hcr & _).
exists C.
do2 2 split; auto.
clear Hseqc.
so (Hseqmn _#3 Hs'') as H.
simpsubin H.
destruct H as (C' & Hcl' & Hcrr & Hm & Hn & Hmn).
so (interp_fun _#7 Hcl Hcl'); subst C'; clear Hcl'.
simpsub.
rewrite <- Heq in Hm, Hn, Hmn.
do2 2 split; auto.
Qed.


Lemma reflexiveish :
  forall w (A : wurel w) (B : urelsp_car (prod_urel w A A) -> wurel w)
    i m n p q u u' (Hmn : rel A i m n) (Hpq : rel A i p q),
      symmish w A B
      -> transish w A B
      -> rel (B (urelspinj (prod_urel w A A) _#3 (prod_action_ppair _#8 Hmn Hpq))) i u u'
      -> exists v v',
           rel (B (urelspinj (prod_urel w A A) _#3 (prod_action_ppair _#8 Hmn Hmn))) i v v'.
Proof.
intros w A B i m n p q u u' Hmn Hpq Hsymm Htrans Hu.
so (Hsymm _#7 Hmn Hpq Hu) as (v & v' & Hv).
exact (Htrans _#11 Hmn Hpq Hmn Hu Hv).
Qed.


Lemma sound_quotient_hyp_with_refl_ugly :
  forall G1 G2 a b m n c,
    pseq (hyp_tm (subst sh1 a) :: hyp_tm a :: G1) (deqtype b b)
    -> pseq (G2 ++ hyp_tm (quotient a b) :: G1) (deqtype c c)
    -> pseq 
         (hyp_tm (subst (dot (var (length G2)) (dot (var (length G2)) (sh (S (length G2))))) b)
          :: G2 ++ hyp_tm a :: G1)
         (deq (subst (compose (under (length G2) sh1) sh1) m) (subst (compose (under (length G2) sh1) sh1) n) (subst sh1 c))
    -> pseq (G2 ++ hyp_tm (quotient a b) :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) c).
Proof.
intros G1 G2 a b m n c.
revert G1.
refine (seq_pseq_hyp 2 [] a [hyp_emp; hyp_emp] b 3 [] [_; _] _ _ [_] _ (_ :: _) [_] _ _ [_] _ _); cbn.
intros G1 Hcla Hclb Hseqb Hseqc Hseqmn _.
rewrite -> seq_eqtype in Hseqb, Hseqc.
rewrite -> seq_deq in Hseqmn |- *.
intros i s s' Hs.
so (dequotient_context _#7 Hs) as (A & B & B' & p & q & r & t & u & u' & s'' & Hpt & Hrq & Heqp & Heqq & Heqt & Heqs'' & Hs'' & Hal & Har & Hbl & _ & Hu & Hsymm & _ & Htrans & _).
assert (compose (under (length G2) sh1) s' = compose (under (length G2) sh1) s'') as Heq.
  {
  rewrite <- Heqs''.
  rewrite <- compose_assoc.
  rewrite <- compose_under.
  simpsub.
  reflexivity.
  }
clear Heqs''.
so (Hseqc _#3 Hs) as (C & Hcl & Hcr & _).
exists C.
do2 2 split; auto.
clear Hseqc.
so (reflexiveish _#12 Hsymm Htrans Hu) as (v & v' & Hv).
exploit (Hseqmn i (dot v s) (dot v' s'')) as H.
  {
  assert (forall i sa sa',
            pwctx i sa sa' (G2 ++ hyp_tm a :: G1)
            -> pwctx i 
                 (dot (project sa (length G2)) (dot (project sa (length G2)) (compose (sh (S (length G2))) sa)))
                 (dot (project sa' (length G2)) (dot (project sa' (length G2)) (compose (sh (S (length G2))) sa')))
                 (hyp_tm (subst sh1 a) :: hyp_tm a :: G1)) as Hdouble.
    {
    clear i s s' Hs s'' Hs'' Heqp Heqq Heqt Hal Har Hbl Heq Hcl Hcr Hpt Hrq Hu Hv m n p q r t Hseqmn A B B' Hsymm Htrans.
    intros i sa sa' Hsa.
    so (pwctx_tail _#5 Hsa) as Hsmn.
    invert Hsmn.
    intros m n s s' _ Hmn Hleft Hright Heqs Heqs'.
    rewrite trunc_is_compose_sh in Heqs, Heqs'.
    rewrite <- Heqs, <- Heqs' in Hsmn.
    replace (project sa (length G2)) with (subst (compose (sh (length G2)) sa) (var 0)).
    2:{
      simpsub.
      f_equal.
      omega.
      }
    replace (project sa' (length G2)) with (subst (compose (sh (length G2)) sa') (var 0)).
    2:{
      simpsub.
      f_equal.
      omega.
      }
    rewrite <- (compose_sh_sh _ 1 (length G2)).
    rewrite -> !compose_assoc.
    rewrite <- Heqs, <- Heqs'.
    simpsub.
    apply pwctx_cons; auto.
      {
      simpsub; auto.
      }

      {
      intros j pr ss'' Hsmall Hss''.
      invertc Hss''.
      intros p s'' h G Hs'' Hmp <- H.
      rewrite -> qpromote_cons in H.
      rewrite -> qpromote_hyp_tm in H.
      injectionc H.
      intros -> ->.
      rewrite -> !substh_qpromote_hyp.
      simpsub.
      so (Hleft _#3 Hsmall Hs'') as H.
      rewrite -> !substh_qpromote_hyp in H.
      simpsubin H.
      auto.
      }

      {
      intros j pr ss'' Hsmall Hss''.
      invertc Hss''.
      intros p s'' h G Hs'' Hmp <- H.
      rewrite -> qpromote_cons in H.
      rewrite -> qpromote_hyp_tm in H.
      injectionc H.
      intros -> ->.
      rewrite -> !substh_qpromote_hyp.
      simpsub.
      so (Hright _#3 Hsmall Hs'') as H.
      rewrite -> !substh_qpromote_hyp in H.
      simpsubin H.
      auto.
      }
    }
  apply pwctx_cons_tm_seq; auto.
    {
    simpsub.
    rewrite -> Heqp.
    rewrite -> Heqt.
    so (Hseqb _#3 (Hdouble _#3 Hs'')) as (Ba & Hbal & Hbar & _).
    clear Hdouble Hu Hseqb.
    rewrite -> Heqp in Hbal.
    rewrite -> Heqt in Hbar.
    invertc Hbl.
    intros _ _ Hact.
    so (Hact _#3 (le_refl _) (prod_action_ppair _ (den A) (den A) _#5 Hpt Hpt)) as Hbal'.
    simpsubin Hbal'.
    eassert _ as HeqBa; [refine (basic_fun _#7 Hbal (basic_equiv _#7 _ _ Hbal')) |].
      {
      so (pwctx_impl_closub _#4 Hs) as (Hcls & _).
      so (urel_closed _#5 Hpt) as (Hclp & _).
      eapply hygiene_subst; eauto.
      intros j Hj.
      destruct j as [| [| j]]; simpsub; auto.
      eapply project_closub; eauto.
      cbn in Hj.
      rewrite -> ctxpred_length in Hj |- *.
      rewrite -> app_length.
      cbn.
      omega.
      }

      {
      apply equiv_funct; auto using equiv_refl.
      apply equivsub_dot.
        {
        apply steps_equiv; apply star_one.
        apply step_ppi22.
        }
      apply equivsub_dot.
        {
        apply steps_equiv; apply star_one.
        apply step_ppi12.
        }
      apply equivsub_refl.
      }
    apply (seqhyp_tm _#5 Ba); subst Ba; auto.
    }

    {
    intros j sa sa' Hsa.
    so (Hseqb _#3 (Hdouble _#3 Hsa)) as (R & Hl & Hr & _).
    exists toppg, R.
    simpsub.
    auto.
    }
  }
simpsubin H.
destruct H as (C' & Hcl' & Hcrr & Hm & Hn & Hmn).
so (interp_fun _#7 Hcl Hcl'); subst C'; clear Hcl'.
simpsub.
rewrite <- Heq in Hm, Hn, Hmn.
do2 2 split; auto.
Qed.


Lemma sound_quotient_hyp_with_refl :
  forall G1 G2 a b m n c,
    pseq (hyp_tm (subst sh1 a) :: hyp_tm a :: G1) (deqtype b b)
    -> pseq (G2 ++ hyp_tm (quotient a b) :: G1) (deqtype c c)
    -> pseq 
         (substctx sh1 G2 ++ hyp_tm (subst (dot (var 0) (dot (var 0) sh1)) b) :: hyp_tm a :: G1)
         (deq
            (subst (under (length G2) (sh 2)) m)
            (subst (under (length G2) (sh 2)) n)
            (subst (under (length G2) sh1) c))
    -> pseq (G2 ++ hyp_tm (quotient a b) :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) c).
Proof.
intros G1 G2 a b m n c Hseqb Hseqc Hseq.
apply sound_quotient_hyp_with_refl_ugly; auto.
clear Hseqb Hseqc.
replace (hyp_tm (subst (dot (var (length G2)) (dot (var (length G2)) (sh (S (length G2))))) b))
  with  (substh (sh (length G2)) (hyp_tm (subst (dot (var 0) (dot (var 0) sh1)) b))).
2:{
  simpsub.
  rewrite -> Nat.add_0_r.
  reflexivity.
  }
apply (sound_exchange_multi _ _ _ nil).
cbn [length substctx List.app].
rewrite -> under_zero.
simpsub.
rewrite <- !compose_under.
simpsub.
exact Hseq.
Qed.


Lemma quotient_context_shorten :
 forall G1 G2 a b i s s' so so',
   pwctx i so so' (G2 ++ hyp_tm (quotient a b) :: G1)
   -> (compose (sh (3 + length G2)) s = compose (sh (S (length G2))) so \/ compose (sh (3 + length G2)) s' = compose (sh (S (length G2))) so')
   -> seqctx i s s' (substctx (sh 2) G2 ++ hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G1)
   -> seqctx i (compose (under (length G2) (sh 2)) s) (compose (under (length G2) (sh 2)) s') (G2 ++ hyp_tm (quotient a b) :: G1).
Proof.
intros G1 G2 a b i.
induct G2.

(* nil *)
{
intros ss ss' sso sso' Hsso Heq Hseq.
cbn [List.app length].
simpsub.
cbn [substctx List.app] in Hseq.
invertc Hseq.
intros x y ss1 ss1' Hss1 Hxy <- <-.
invertc Hss1.
intros m n ss2 ss2' Hss2 Hmn <- <-.
invertc Hss2.
intros p q s s' Hs Hpq <- <-.
simpsub.
cbn [List.app] in Hsso.
invertc Hsso.
intros mo no so so' _ Hmno Hleft Hright <- <-.
cbn [length] in Heq.
rewrite -> Nat.add_0_r in Heq.
simpsubin Heq.
apply seqctx_cons; auto.
simpsub.
simpsubin Hmno.
invertc Hmno.
intros R Hl Hr _.
clear mo no.
apply (seqhyp_tm _#5 R); auto.
  {
  destruct Heq as [<- | <-]; auto.
  so (Hright i false _ (smaller_refl _) Hs) as H.
  cbn [qpromote_hyp] in H.
  simpsubin H.
  invertc H.
  intros R' Hl' H.
  so (interp_fun _#7 Hl Hl'); subst R'.
  auto.
  }

  {
  destruct Heq as [<- | <-]; auto.
  so (Hleft i false _ (smaller_refl _) Hs) as H.
  cbn [qpromote_hyp] in H.
  simpsubin H.
  invertc H.
  intros R' Hr' H.
  so (interp_fun _#7 Hr Hr'); subst R'.
  auto.
  }
invertc Hpq.
intros A Hal Har Hpq.
invertc Hmn.
intros A' Hal' _ Hmn.
simpsubin Hal'.
so (basic_fun _#7 Hal Hal'); subst A'; clear Hal'.
invertc Hxy.
intros Bpm Hbpm Hbqn Hxy.
invert (basic_value_inv _#6 value_quotient Hl).
intros Ao Bl hsl htl Halo Hbl HeqR.
invert (basic_value_inv _#6 value_quotient Hr).
intros Ao' Br hsr htr Haro Hbr HeqR'.
clear Hl Hr.
so (iuquotient_inj _#9 (eqtrans HeqR (eqsymm HeqR'))); subst Ao'.
assert (A = Ao).
  {
  destruct Heq as [<- | <-].
    {
    exact (basic_fun _#7 Hal Halo).
    }

    {
    exact (basic_fun _#7 Har Haro).
    }
  }
subst Ao.
clear Halo Haro.
assert (exists B hs ht, 
          ((B = Bl /\ s = so) \/ (B = Br /\ s' = so'))
          /\ (R = iuquotient stop A B hs ht)) as (B & hs & ht & HeqB & ->).
  {
  destruct Heq as [<- | <-].
    {
    exists Bl, hsl, htl.
    split; auto.
    }

    {
    exists Br, hsr, htr.
    split; auto.
    }
  }
clear HeqR HeqR'.
simpsubin Hbl.
simpsubin Hbr.
cbn.
set (Hpair := prod_action_ppair _ (den A) (den A) _#5 Hpq Hpq).
assert (exists v w,
          rel (den (pi1 B (urelspinj (prod_urel _ (den A) (den A)) i (ppair p p) (ppair q q) Hpair))) i v w) as (v & w & Hvw).
  {
  assert (Bpm = pi1 B (urelspinj (prod_urel _ (den A) (den A)) _#3 (prod_action_ppair _#8 Hpq Hmn))).
    {
    destruct HeqB as [(<- & <-) | (<- & <-)].
      {
      invert Hbl.
      intros _ _ Hact.
      so (Hact _#3 (le_refl _) (prod_action_ppair _ (den A) (den A) _#5 Hpq Hmn)) as H.
      simpsubin H.
      refine (basic_fun _#7 Hbpm _).
      refine (basic_equiv _#7 _ _ H).
        {
        exact (basic_closed _#6 Hbpm).
        }

        {
        apply equiv_funct; auto using equiv_refl.
        apply equivsub_dot.
          {
          apply steps_equiv.
          apply star_one.
          apply step_ppi22.
          }
        apply equivsub_dot.
          {
          apply steps_equiv.
          apply star_one.
          apply step_ppi12.
          }
        apply equivsub_refl.
        }
      }

      {
      invert Hbr.
      intros _ _ Hact.
      so (Hact _#3 (le_refl _) (prod_action_ppair _ (den A) (den A) _#5 Hpq Hmn)) as H.
      simpsubin H.
      refine (basic_fun _#7 Hbqn _).
      refine (basic_equiv _#7 _ _ H).
        {
        exact (basic_closed _#6 Hbqn).
        }

        {
        apply equiv_funct; auto using equiv_refl.
        apply equivsub_dot.
          {
          apply steps_equiv.
          apply star_one.
          apply step_ppi22.
          }
        apply equivsub_dot.
          {
          apply steps_equiv.
          apply star_one.
          apply step_ppi12.
          }
        apply equivsub_refl.
        }
      }
    }
  subst Bpm.
  so (reflexiveish _ _ (fun C => den (pi1 B C)) _#7 Hpq Hmn hs ht Hxy) as (v & w & Hvw).
  exists v, w.
  auto.
  }
exists p, q, v, w, Hpq, Hpq.
auto.
}

(* cons *)
{
intros h G2 IH ss ss' sso sso' Hsso Heq Hseq.
cbn [substctx List.app] in Hseq, Hsso.
invertc Hseq.
intros m n s s' Hs Hmn <- <-.
invertc Hsso.
intros mo no so so' Hso _ _ _ <- <-.
exploit (IH s s' so so') as Hs'; auto.
cbn [List.app length].
simpsub.
apply seqctx_cons; auto.
simpsubin Hmn.
auto.
}
Qed.


(* We might be able to write a nicer proof by using dequotient_context, adding the two extra
   bindings to the bottom, and then exchanging them upward (in a similar fashion to 
   sound_quotient_hyp_with_refl).  But this is already done, so we'll leave it alone.
*)
Lemma sound_quotient_hyp_eqtype :
  forall G1 G2 a b c,
    pseq (hyp_tm (subst sh1 a) :: hyp_tm a :: G1) (deqtype b b)
    -> pseq (substctx (sh 2) G2 ++ hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G1) (deqtype (subst (under (length G2) (sh 2)) c) (subst (under (length G2) (dot (var 1) (sh 3))) c))
    -> pseq (G2 ++ hyp_tm (quotient a b) :: G1) (deqtype c c).
Proof.
intros G1 G2 a b c.
revert G1.
refine (seq_pseq_hyp 2 [] a [hyp_emp; hyp_emp] b 2 [] [_; _] _ _ [_; _; _] _ _ [_] _ _); cbn.
intros G1 Hlca Hclb Hseqb Hseq _.
rewrite -> seq_eqtype in Hseqb, Hseq |- *.
intros i s s' Hs.
assert (exists sr sr',
          pwctx i sr sr' (substctx (sh 2) G2 ++ hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G1)
          /\ compose (under (length G2) (sh 2)) sr = s
          /\ compose (under (length G2) (dot (var 1) (sh 3))) sr' = s') as (sr & sr' & Hsr & Heq & Heq').
  {
  clear Hseq c.
  revert i s s' Hs.
  induct G2.
    (* nil *)
    {
    intros i ss ss' Hss.
    cbn in Hss.
    invertc Hss.
    intros m n s s' Hs Hmn Hleft Hright <- <-.
    so (pwctx_impl_closub _#4 Hs) as (Hcls & Hcls').
    simpsubin Hmn.
    invertc Hmn.
    intros R Hl Hr Hmn.
    invert (basic_value_inv _#6 value_quotient Hl).
    intros A B hs ht Hal Hbl Heq.
    invert (basic_value_inv _#6 value_quotient Hr).
    intros A' B' hs' ht' Har Hbr Heq'.
    so (iuquotient_inj _#9 (eqtrans Heq (eqsymm Heq'))); subst A'.
    clear Heq'; subst R.
    destruct Hmn as (p & q & x & y & Hmq & Hpn & Hxy).
    so (urel_closed _#5 Hmq) as (Hclm & Hclq).
    so (urel_closed _#5 Hpn) as (Hclp & Hcln).
    exists (dot x (dot p (dot m s))).
    exists (dot y (dot n (dot q s'))).
    cbn [substctx length List.app].
    rewrite -> !under_zero.
    simpsub.
    do2 2 split; auto.
    assert (pwctx i (dot p (dot m s)) (dot n (dot q s')) (hyp_tm (subst sh1 a) :: hyp_tm a :: G1)) as Hsext.
      {
      apply pwctx_cons_tm.
        {
        apply pwctx_cons_tm; auto.
          {
          simpsub.
          eapply seqhyp_tm; eauto.
          }

          {
          intros j s'' Hj Hs''.
          exploit (Hleft j false s'') as H; auto using smaller_le, pwctx_impl_seqctx.
          rewrite -> qpromote_hyp_tm in H.
          simpsubin H.
          invertc H.
          intros R Hr' Ho.
          invert (basic_value_inv _#6 value_quotient Hr').
          intros A' B'' hs'' ht'' Har' _ Heq.
          invert (basic_value_inv _#6 value_quotient Ho).
          intros A'' B''' hs''' ht''' Hao _ Heq'.
          so (iuquotient_inj _#9 (eqtrans Heq (eqsymm Heq'))); subst A''.
          apply (relhyp_tm _#4 A'); auto.
          }

          {
          intros j s'' Hj Hs''.
          exploit (Hright j false s'') as H; auto using smaller_le, pwctx_impl_seqctx.
          rewrite -> qpromote_hyp_tm in H.
          simpsubin H.
          invertc H.
          intros R Hl' Ho.
          invert (basic_value_inv _#6 value_quotient Hl').
          intros A' B'' hs'' ht'' Hal' _ Heq.
          invert (basic_value_inv _#6 value_quotient Ho).
          intros A'' B''' hs''' ht''' Hao _ Heq'.
          so (iuquotient_inj _#9 (eqtrans Heq (eqsymm Heq'))); subst A''.
          apply (relhyp_tm _#4 A'); auto.
          }
        }

        {
        simpsub.
        eapply seqhyp_tm; eauto.
        }

        {
        intros j ss'' Hj Hss''.
        invertc Hss''.
        intros r s'' Hs'' _ _ _ <-.
        simpsub.
        exploit (Hleft j false s'') as H; auto using smaller_le, pwctx_impl_seqctx.
        rewrite -> qpromote_hyp_tm in H.
        simpsubin H.
        invertc H.
        intros R Hr' Ho.
        invert (basic_value_inv _#6 value_quotient Hr').
        intros A' B'' hs'' ht'' Har' _ Heq.
        invert (basic_value_inv _#6 value_quotient Ho).
        intros A'' B''' hs''' ht''' Hao _ Heq'.
        so (iuquotient_inj _#9 (eqtrans Heq (eqsymm Heq'))); subst A''.
        apply (relhyp_tm _#4 A'); auto.
        }

        {
        intros j ss'' Hj Hss''.
        invertc Hss''.
        intros r s'' Hs'' _ _ _ <-.
        simpsub.
        exploit (Hright j false s'') as H; auto using smaller_le, pwctx_impl_seqctx.
        rewrite -> qpromote_hyp_tm in H.
        simpsubin H.
        invertc H.
        intros R Hl' Ho.
        invert (basic_value_inv _#6 value_quotient Hl').
        intros A' B'' hs'' ht'' Hal' _ Heq.
        invert (basic_value_inv _#6 value_quotient Ho).
        intros A'' B''' hs''' ht''' Hao _ Heq'.
        so (iuquotient_inj _#9 (eqtrans Heq (eqsymm Heq'))); subst A''.
        apply (relhyp_tm _#4 A'); auto.
        }
      }
    apply pwctx_cons_tm_seq; auto.
    2:{
      intros j t t' Ht.
      so (Hseqb _#3 Ht) as (R & Hlf & Hrt & _).
      eauto.
      }
    set (Hpair := ((prod_action_ppair stop (den A) (den A) i m p q n Hmq Hpn)
                   : (rel (prod_urel stop (den A) (den A)) i (ppair m p) (ppair q n)))) in Hxy.
    assert (interp toppg true i (subst (dot p (dot m s)) b) 
              (pi1 B (urelspinj (prod_urel _ (den A) (den A)) i (ppair m p) (ppair q n) Hpair))) as Hbpairl.
      {
      invertc Hbl.
      intros _ _ Hbl.
      so (Hbl _ _ _ (le_refl _) Hpair) as H.
      simpsubin H.
      eapply basic_equiv; eauto.
        {
        apply (subst_closub _ (permit (permit (ctxpred G1)))); auto using closub_dot.
        }
      apply equiv_funct; [| apply equiv_refl].
      apply equivsub_dot.
        {
        apply steps_equiv.
        apply star_one.
        apply step_ppi22.
        }
      apply equivsub_dot.
        {
        apply steps_equiv.
        apply star_one.
        apply step_ppi12.
        }
      apply equivsub_refl.
      }
    so (Hseqb _#3 Hsext) as (R & Hbpairl' & Hbpairr & _).
    so (interp_fun _#7 Hbpairl Hbpairl'); subst R.
    apply (seqhyp_tm _#5 (pi1 B (urelspinj _#4 Hpair))); auto.
    }

    (* cons *)
    {
    intros h G2 IH i ss ss' Hss.
    cbn [List.app] in Hss.
    invertc Hss.
    intros m n s s' Hs Hmn Hleft Hright <- <-.
    so (IH _#3 Hs) as (sr & sr' & Hsr & Heq & Heq'); clear IH.
    eassert _ as Hsr'; [refine (quotient_context_shorten _#9 Hs _ (pwctx_impl_seqctx _#4 Hsr)) |]; eauto.
      {
      left.
      rewrite <- Heq.
      rewrite <- compose_assoc.
      rewrite -> compose_sh_under_geq; [| omega].
      replace (S (length G2) - length G2) with 1 by omega.
      simpsub.
      auto.
      }
    exists (dot m sr), (dot n sr').
    do2 2 split.
      {
      cbn [substctx List.app].
      apply pwctx_cons; auto.
        {
        simpsub.
        rewrite -> Heq.
        rewrite -> Heq in Hsr'.
        so (Hleft i false _ (smaller_refl _) Hsr') as Hrelhyp.
        eapply seqhyp_relhyp_2; eauto.
        }

        {
        intros j pr sr'' Hsmaller Hs''.
        rewrite <- !substh_qpromote_hyp.
        simpsub.
        so (pwctx_smaller _#6 Hsmaller Hs) as Hs_small.
        rewrite -> qpromote_app in Hs'', Hs_small.
        rewrite -> !qpromote_cons in Hs''.
        rewrite -> !qpromote_cons in Hs_small.
        rewrite -> !qpromote_hyp_tm in Hs''.
        rewrite -> !qpromote_hyp_tm in Hs_small.
        rewrite -> qpromote_substctx in Hs''.
        eassert _ as Hs''_short; [refine (quotient_context_shorten _#9 Hs_small _ Hs'') |].
          {
          left.
          rewrite -> length_qpromote.
          rewrite <- Heq.
          rewrite <- compose_assoc.
          rewrite -> compose_sh_under_geq; [| omega].
          replace (S (length G2) - length G2) with 1 by omega.
          simpsub.
          auto.
          }
        so (seqctx_smaller _#6 Hsmaller Hsr') as Hsr'_small.
        rewrite -> qpromote_app in Hsr'_small.
        rewrite -> qpromote_cons in Hsr'_small.
        rewrite -> qpromote_hyp_tm in Hsr'_small.
        rewrite -> length_qpromote in Hs''_short.
        rewrite -> Heq in Hs''_short, Hsr'_small.
        exploit (Hleft j pr (compose (under (length G2) (sh 2)) sr')) as Hrel; auto.
          {
          rewrite -> qpromote_app.
          rewrite -> !qpromote_cons.
          rewrite -> !qpromote_hyp_tm.
          auto.
          }
        exploit (Hleft j pr (compose (under (length G2) (sh 2)) sr'')) as Hrel'; auto.
          {
          rewrite -> qpromote_app.
          rewrite -> !qpromote_cons.
          rewrite -> !qpromote_hyp_tm.
          auto.
          }
        exact (relhyp_trans _#5 (relhyp_symm _#4 Hrel) Hrel').
        }
        
        {
        intros j pr sr'' Hsmaller Hs''.
        rewrite -> !substh_qpromote_hyp.
        simpsub.
        rewrite -> Heq.
        rewrite <- !substh_qpromote_hyp.
        apply Hright; auto.
        so (pwctx_smaller _#6 Hsmaller Hs) as Hs_small.
        rewrite -> qpromote_app in Hs'', Hs_small.
        rewrite -> !qpromote_cons in Hs''.
        rewrite -> !qpromote_cons in Hs_small.
        rewrite -> !qpromote_hyp_tm in Hs''.
        rewrite -> !qpromote_hyp_tm in Hs_small.
        rewrite -> qpromote_substctx in Hs''.
        eassert _ as Hs''_short; [refine (quotient_context_shorten _#9 Hs_small _ Hs'') |].
          {
          right.
          rewrite -> length_qpromote.
          rewrite <- Heq'.
          rewrite <- compose_assoc.
          rewrite -> compose_sh_under_geq; [| omega].
          replace (S (length G2) - length G2) with 1 by omega.
          simpsub.
          auto.
          }
        rewrite -> length_qpromote in Hs''_short.
        so (seqctx_smaller _#6 Hsmaller Hsr') as Hsr'_small.
        rewrite -> Heq in Hsr'_small.
        rewrite -> qpromote_app in Hsr'_small |- *.
        rewrite -> !qpromote_cons in Hsr'_small |- *.
        rewrite -> !qpromote_hyp_tm in Hsr'_small |- *.
        so (pwctx_impl_seqctx _#4 Hs_small).
        eapply seqctx_zigzag; eauto.
        }
      }

      {
      cbn [length].
      simpsub.
      f_equal; auto.
      }
      
      {
      cbn [length].
      simpsub.
      f_equal; auto.
      }
    }
  }
so (Hseq _#3 Hsr) as (C & Hl & _ & _ & Hr).
exists C.
simpsubin Hl.
simpsubin Hr.
rewrite -> Heq in Hl.
rewrite -> Heq' in Hr.
auto.
Qed.
