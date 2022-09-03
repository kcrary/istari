
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
Require Import SemanticsSigma.


Definition quotient_action
  (w : ordinal) (A : wurel w) (B : urelsp_car (prod_urel w A A) -> wurel w)
  : nat -> relation (wterm w)
  :=
  fun i m m' =>
    exists n n' p q (Hm : rel A i m n') (Hm' : rel A i n m'),
      rel (B (urelspinj (prod_urel w A A) i (ppair m n) (ppair n' m') (prod_action_ppair _#8 Hm Hm'))) i p q.


Definition symmish w (A : wurel w) (B : urelsp_car (prod_urel w A A) -> wurel w) : Prop
  :=
  forall i m n p q u u' (Hmn : rel A i m n) (Hpq : rel A i p q),
    rel (B (urelspinj (prod_urel w A A) _#3 (prod_action_ppair _#8 Hmn Hpq))) i u u'
    -> exists v v',
         rel (B (urelspinj (prod_urel w A A) _#3 (prod_action_ppair _#8 Hpq Hmn))) i v v'.


Definition transish w (A : wurel w) (B : urelsp_car (prod_urel w A A) -> wurel w) : Prop
  :=
  forall i m n p q r t u1 u1' u2 u2' (Hmn : rel A i m n) (Hpq : rel A i p q) (Hrt : rel A i r t),
    rel (B (urelspinj (prod_urel w A A) _#3 (prod_action_ppair _#8 Hmn Hpq))) i u1 u1'
    -> rel (B (urelspinj (prod_urel w A A) _#3 (prod_action_ppair _#8 Hpq Hrt))) i u2 u2'
    -> exists u3 u3',
         rel (B (urelspinj (prod_urel w A A) _#3 (prod_action_ppair _#8 Hmn Hrt))) i u3 u3'.


Lemma quotient_uniform :
  forall w A (B : urelsp (prod_urel w A A) -n> wurel_ofe w),
    symmish w A (pi1 B)
    -> transish w A (pi1 B)
    -> uniform _ (quotient_action w A (pi1 B)).
Proof.
intros w A B Hsymm Htrans.
do2 3 split.

(* closed *)
{
intros i m n H.
destruct H as (p & q & _ & _ & Hmq & Hpn & _).
so (urel_closed _#5 Hmq) as (Hclm & _).
so (urel_closed _#5 Hpn) as (_ & Hcln).
auto.
}

(* equiv *)
{
intros i m m' n n' Hclm' Hcln' Hequivm Hequivn Hmn.
decompose Hmn.
intros na ma p q Hm Hn Hpq.
assert (rel A i m' ma) as Hm'.
  {
  eapply urel_equiv_1; eauto.
  }
assert (rel A i na n') as Hn'.
  {
  eapply urel_equiv_2; eauto.
  }
exists na, ma, p, q, Hm', Hn'.
force_exact Hpq.
f_equal.
f_equal.
apply urelspinj_equal.
apply prod_action_ppair; auto.
}

(* zigzag *)
{
intros i m n p q Hmn Hpn Hpq.
destruct Hmn as (m1 & n1 & mn & mn' & Hmn1 & Hm1n & Hmn).
destruct Hpn as (p1 & n1' & pn & pn' & Hpn1 & Hp1n & Hpn).
destruct Hpq as (p1' & q1 & pq & pq' & Hpq1 & Hp1q & Hpq).
replace (urelspinj (prod_urel w A A) _#3 (prod_action_ppair _#8 Hpn1 Hp1n)) with (urelspinj (prod_urel w A A) _#3 (prod_action_ppair _#8 Hpn1 Hm1n)) in Hpn.
2:{
  apply urelspinj_equal.
  apply prod_action_ppair; auto.
  }
so (Hsymm _#9 Hpn) as (np & np' & Hnp).
so (Htrans _#14 Hmn Hnp) as (mp & mp' & Hmp).
replace (urelspinj (prod_urel w A A) _#3 (prod_action_ppair _#8 Hmn1 Hpn1)) with (urelspinj (prod_urel w A A) _#3 (prod_action_ppair _#8 Hmn1 Hpq1)) in Hmp.
2:{
  apply urelspinj_equal.
  apply prod_action_ppair; auto.
  }
so (Htrans _#14 Hmp Hpq) as (mq & mq' & Hmq).
exists p1', n1, mq, mq', Hmn1, Hp1q.
exact Hmq.
}

(* downward *)
{
intros i m n H.
decompose H.
intros n' m' p q Hm Hn Hpq.
exists n', m', p, q, (urel_downward _#5 Hm), (urel_downward _#5 Hn).
refine (rel_from_dist _#6 _ (urel_downward _#5 Hpq)).
apply (pi2 B).
apply urelspinj_dist_diff; auto.
apply prod_action_ppair; auto using urel_downward.
}
Qed.


Definition quotient_urel w (A : wurel w) (B : urelsp (prod_urel w A A) -n> wurel_ofe w) (Hsymm : symmish w A (pi1 B)) (Htrans : transish w A (pi1 B)) : wurel w
  :=
  mk_urel (quotient_action w A (pi1 B)) (quotient_uniform w A B Hsymm Htrans).


Lemma quotient_urel_compat :
  forall w A A' B B' hs hs' ht ht',
    eq_dep _ (fun A => urelsp (prod_urel w A A) -n> wurel_ofe w) A B A' B'
    -> quotient_urel w A B hs ht = quotient_urel w A' B' hs' ht'.
Proof.
intros w A A' B B' hs hs' ht ht' Heq.
injectionT Heq.
intros <-.
injectionT Heq.
intros <-.
f_equal; apply proof_irrelevance.
Qed.


Lemma ceiling_symmish :
  forall n w A (B : urelsp_car (prod_urel w A A) -> wurel w),
    symmish w A B
    -> symmish w (ceiling (S n) A) (fun x => ceiling (S n) (B (embed_ceiling (S n) (prod_urel w A A) (transport (eqsymm (ceiling_prod n w A A)) urelsp_car x)))).
Proof.
intros k w A B Hsymm.
intros i m n p q u u' Hmn Hpq Hu.
destruct Hmn as (Hi & Hmn).
destruct Hpq as (Hi' & Hpq).
so (proof_irrelevance _ Hi Hi'); subst Hi'.
destruct Hu as (_ & Hu).
rewrite -> embed_ceiling_urelspinj_prod in Hu.
so (Hsymm _#9 Hu) as (v & v' & Hv).
exists v, v'.
split; auto.
rewrite -> embed_ceiling_urelspinj_prod.
auto.
Qed.


Lemma ceiling_transish :
  forall n w A (B : urelsp_car (prod_urel w A A) -> wurel w),
    transish w A B
    -> transish w (ceiling (S n) A) (fun x => ceiling (S n) (B (embed_ceiling (S n) (prod_urel w A A) (transport (eqsymm (ceiling_prod n w A A)) urelsp_car x)))).
Proof.
intros k w A B Htrans.
intros i m n p q r t u1 u1' u2 u2' Hmn Hpq Hrt Hu1 Hu2.
destruct Hmn as (Hi & Hmn).
destruct Hpq as (Hi' & Hpq).
so (proof_irrelevance _ Hi Hi'); subst Hi'.
destruct Hrt as (Hi' & Hrt).
so (proof_irrelevance _ Hi Hi'); subst Hi'.
rewrite -> embed_ceiling_urelspinj_prod in Hu1, Hu2.
destruct Hu1 as (_ & Hu1).
destruct Hu2 as (_ & Hu2).
so (Htrans _#14 Hu1 Hu2) as (u3 & u3' & Hu3).
exists u3, u3'.
split; auto.
rewrite -> embed_ceiling_urelspinj_prod; auto.
Qed.


Lemma ceiling_quotient :
  forall n w A (B : urelsp (prod_urel w A A) -n> wurel_ofe w) hs ht,
    ceiling (S n) (quotient_urel w A B hs ht)
    =
    quotient_urel w
      (ceiling (S n) A)
      (nearrow_compose2 (nearrow_compose (embed_ceiling_ne (S n) (prod_urel w A A)) (transport_ne (eqsymm (ceiling_prod n w A A)) urelsp)) (ceiling_ne (S n)) B)
      (ceiling_symmish _#4 hs)
      (ceiling_transish _#4 ht).
Proof.
intros n w A B hs ht.
apply urel_extensionality.
fextensionality 3.
intros i m p.
cbn.
pextensionality.
  {
  intros (Hi, Hact).
  decompose Hact.
  intros n' m' u u' Hm Hn Hu.
  exists n', m', u, u', (conj Hi Hm), (conj Hi Hn).
  cbn.
  split; auto.
  rewrite -> embed_ceiling_urelspinj_prod.
  exact Hu.
  }

  {
  intros Hact.
  decompose Hact.
  intros n' m' u u' Hm Hn Hu.
  destruct Hm as (Hi & Hm).
  destruct Hn as (Hi' & Hn).
  so (proof_irrelevance _ Hi Hi'); subst Hi'.
  cbn in Hu.
  destruct Hu as (_ & Hu).
  rewrite -> embed_ceiling_urelspinj_prod in Hu.
  split; auto.
  exists n', m', u, u', Hm, Hn.
  exact Hu.
  }
Qed.


Lemma extend_symmish :
  forall v w (h : v <<= w) (A : wurel v) (B : urelsp_car (prod_urel v A A) -> wurel v),
    symmish v A B
    -> symmish w (extend_urel v w A) (fun x => extend_urel v w (B (deextend_urelsp h (prod_urel v A A) (transport (eqsymm (extend_prod v w h A A)) urelsp_car x)))).
Proof.
intros v w h A B Hsymm.
intros i m n p q u u' Hmn Hpq Hu.
cbn in Hu |- *.
rewrite -> deextend_urelsp_urelspinj_prod in Hu |- *.
so (Hsymm _#9 Hu) as (t & t' & Ht).
exists (map_term (extend v w) t), (map_term (extend v w) t').
rewrite -> !extend_term_cancel; auto.
Qed.


Lemma extend_transish :
  forall v w (h : v <<= w) (A : wurel v) (B : urelsp_car (prod_urel v A A) -> wurel v),
    transish v A B
    -> transish w (extend_urel v w A) (fun x => extend_urel v w (B (deextend_urelsp h (prod_urel v A A) (transport (eqsymm (extend_prod v w h A A)) urelsp_car x)))).
Proof.
intros v w h A B Htrans.
intros i m n p q r t u1 u1' u2 u2' Hmn Hpq Hrt Hu1 Hu2.
cbn in Hu1, Hu2 |- *.
rewrite -> !deextend_urelsp_urelspinj_prod in Hu1, Hu2 |- *.
so (Htrans _#14 Hu1 Hu2) as (u3 & u3' & Hu3).
exists (map_term (extend v w) u3), (map_term (extend v w) u3').
rewrite -> !extend_term_cancel; auto.
Qed.


Lemma extend_quotient :
  forall v w (h : v <<= w) A B hs ht,
    extend_urel v w (quotient_urel v A B hs ht)
    =
    quotient_urel w 
      (extend_urel v w A)
      (nearrow_compose2 (nearrow_compose (deextend_urelsp_ne h (prod_urel v A A)) (transport_ne (eqsymm (extend_prod v w h A A)) urelsp)) (extend_urel_ne v w) B)
      (extend_symmish _#5 hs)
      (extend_transish _#5 ht).
Proof.
intros v w h A B hs ht.
apply urel_extensionality.
fextensionality 3.
intros i m n.
cbn.
pextensionality.
  {
  intro H.
  decompose H.
  intros n' m' u u' Hm Hn Hu.
  assert (rel (extend_urel v w A) i m (map_term (extend v w) m')) as Hm'.
    {
    cbn.
    rewrite -> extend_term_cancel; auto.
    }
  assert (rel (extend_urel v w A) i (map_term (extend v w) n') n) as Hn'.
    {
    cbn.
    rewrite -> extend_term_cancel; auto.
    }
  exists (map_term (extend v w) n'), (map_term (extend v w) m'), (map_term (extend v w) u), (map_term (extend v w) u'), Hm', Hn'.
  cbn.
  rewrite -> deextend_urelsp_urelspinj_prod.
  rewrite -> (extend_term_cancel v w h u).
  rewrite -> (extend_term_cancel v w h u').
  force_exact Hu.
  do 2 f_equal.
  apply urelspinj_equal.
  simpmap.
  rewrite -> extend_term_cancel; auto.
  apply prod_action_ppair; auto.
  }

  {
  intro H.
  decompose H.
  intros n' m' u u' Hm Hn Hu.
  cbn in Hm, Hn.
  exists (map_term (extend w v) n'), (map_term (extend w v) m'), (map_term (extend w v) u), (map_term (extend w v) u'), Hm, Hn.
  cbn in Hu.
  rewrite -> deextend_urelsp_urelspinj_prod in Hu; auto.
  }
Qed.      


Definition iuquotient (w : ordinal) (A : wiurel w) (B : urelsp (prod_urel w (den A) (den A)) -n> wiurel_ofe w)
  (hs : symmish w (den A) (fun x => den (pi1 B x)))
  (ht : transish w (den A) (fun x => den (pi1 B x)))
  :=
  (quotient_urel w (den A) (nearrow_compose den_ne B) hs ht,
   meta_iurel A).


Lemma iuquotient_inj :
  forall w A A' B B' hs hs' ht ht',
    iuquotient w A B hs ht = iuquotient w A' B' hs' ht'
    -> A = A'.
Proof.
intros w A A' B B' hs hs' ht ht' Heq.
unfold iuquotient in Heq.
so (f_equal (fun z => snd z) Heq) as Heq'.
cbn in Heq'.
exact (meta_iurel_inj _#3 Heq').
Qed.


Lemma iuquotient_compat :
  forall w A A' B B' hs hs' ht ht',
    eq_dep _ (fun A => urelsp (prod_urel w (den A) (den A)) -n> wiurel_ofe w) A B A' B'
    -> iuquotient w A B hs ht = iuquotient w A' B' hs' ht'.
Proof.
intros w A A' B B' hs hs' ht ht' Heq.
injectionT Heq.
intros <-.
injectionT Heq.
intros <-.
f_equal; apply proof_irrelevance.
Qed.


Lemma iutruncate_iuquotient :
  forall n w A B hs ht,
    iutruncate (S n) (iuquotient w A B hs ht)
    =
    iuquotient w 
      (iutruncate (S n) A)
      (nearrow_compose2 
         (nearrow_compose (embed_ceiling_ne (S n) (prod_urel w (den A) (den A))) (transport_ne (eqsymm (ceiling_prod n w (den A) (den A))) urelsp))
         (iutruncate_ne (S n))
         B)
      (ceiling_symmish _#4 hs)
      (ceiling_transish _#4 ht).
Proof.
intros n w A B hs ht.
assert (S n > 0) as Hpos by omega.
unfold iuquotient, iubase.
unfold iutruncate.
unfold den.
cbn [fst snd].
f_equal; auto.
  {
  rewrite -> ceiling_quotient.
  cbn.
  apply quotient_urel_compat.
  apply eq_impl_eq_dep_snd.
  apply nearrow_extensionality.
  auto.
  }

  {
  apply meta_truncate_iurel; auto.
  }
Qed.


Lemma extend_iuquotient :
  forall v w (h : v <<= w) A B hs ht,
    extend_iurel h (iuquotient v A B hs ht)
    =
    iuquotient w 
      (extend_iurel h A)
      (nearrow_compose2
         (nearrow_compose (deextend_urelsp_ne h (prod_urel v (den A) (den A))) (transport_ne (eqsymm (extend_prod v w h (den A) (den A))) urelsp))
         (extend_iurel_ne h)
         B)
      (extend_symmish _#5 hs)
      (extend_transish _#5 ht).
Proof.
intros v w h A B hs ht.
unfold iuquotient, iubase, extend_iurel.
cbn.
rewrite -> extend_meta_iurel.
apply f_equal_dep.
eapply eq_impl_eq_dep.
Unshelve.
2:{
  rewrite -> (extend_quotient _ _ h).
  apply quotient_urel_compat.
  apply eq_impl_eq_dep_snd.
  apply nearrow_extensionality; auto.
  }
rewrite -> transport_const.
clear hs ht.
reflexivity.
Qed.


Lemma deextend_symmish :
  forall v w (h : v <<= w) A (B : urelsp_car (prod_urel v A A) -> wurel v),
    symmish w (extend_urel v w A) (fun x => extend_urel v w (B (deextend_urelsp h (prod_urel v A A) (transport (eqsymm (extend_prod v w h A A)) urelsp_car x))))
    -> symmish v A B.
Proof.
intros v w h A B Hsymm.
intros i m n p q u u' Hmn Hpq Hu.
assert (rel (extend_urel v w A) i (map_term (extend v w) m) (map_term (extend v w) n)) as Hmn'.
  {
  cbn.
  rewrite -> !extend_term_cancel; auto.
  }
assert (rel (extend_urel v w A) i (map_term (extend v w) p) (map_term (extend v w) q)) as Hpq'.
  {
  cbn.
  rewrite -> !extend_term_cancel; auto.
  }
exploit (Hsymm i (map_term (extend v w) m) (map_term (extend v w) n) (map_term (extend v w) p) (map_term (extend v w) q) (map_term (extend v w) u) (map_term (extend v w) u') Hmn' Hpq') as H.
  {
  cbn.  
  rewrite -> deextend_urelsp_urelspinj_prod.
  rewrite -> !(extend_term_cancel v w); auto.
  rewrite -> (extend_term_cancel v w h u).
  force_exact Hu.
  do 2 f_equal.
  apply urelspinj_equal.
  simpmap.
  rewrite -> !extend_term_cancel; auto.
  apply prod_action_ppair; auto.
  }
destruct H as (u2 & u2' & Hu2).
cbn in Hu2.
rewrite -> deextend_urelsp_urelspinj_prod in Hu2.
exists (map_term (extend w v) u2), (map_term (extend w v) u2').
force_exact Hu2.
do 2 f_equal.
apply urelspinj_equal.
simpmap.
rewrite -> !extend_term_cancel; auto.
apply prod_action_ppair; auto.
Qed.


Lemma deextend_transish :
  forall v w (h : v <<= w) A (B : urelsp_car (prod_urel v A A) -> wurel v),
    transish w (extend_urel v w A) (fun x => extend_urel v w (B (deextend_urelsp h (prod_urel v A A) (transport (eqsymm (extend_prod v w h A A)) urelsp_car x))))
    -> transish v A B.
Proof.
intros v w h A B Htrans.
intros i m n p q r t u1 u1' u2 u2' Hmn Hpq Hrt Hu1 Hu2.
assert (rel (extend_urel v w A) i (map_term (extend v w) m) (map_term (extend v w) n)) as Hmn'.
  {
  cbn.
  rewrite -> !extend_term_cancel; auto.
  }
assert (rel (extend_urel v w A) i (map_term (extend v w) p) (map_term (extend v w) q)) as Hpq'.
  {
  cbn.
  rewrite -> !extend_term_cancel; auto.
  }
assert (rel (extend_urel v w A) i (map_term (extend v w) r) (map_term (extend v w) t)) as Hrt'.
  {
  cbn.
  rewrite -> !extend_term_cancel; auto.
  }
exploit (Htrans i (map_term (extend v w) m) (map_term (extend v w) n) (map_term (extend v w) p) (map_term (extend v w) q) (map_term (extend v w) r) (map_term (extend v w) t) (map_term (extend v w) u1) (map_term (extend v w) u1') (map_term (extend v w) u2) (map_term (extend v w) u2') Hmn' Hpq' Hrt') as H.
  {
  cbn.  
  rewrite -> deextend_urelsp_urelspinj_prod.
  rewrite -> !(extend_term_cancel v w); auto.
  rewrite -> (extend_term_cancel v w h u1).
  force_exact Hu1.
  do 2 f_equal.
  apply urelspinj_equal.
  simpmap.
  rewrite -> !extend_term_cancel; auto.
  apply prod_action_ppair; auto.
  }

  {
  cbn.  
  rewrite -> deextend_urelsp_urelspinj_prod.
  rewrite -> !(extend_term_cancel v w); auto.
  rewrite -> (extend_term_cancel v w h u2).
  force_exact Hu2.
  do 2 f_equal.
  apply urelspinj_equal.
  simpmap.
  rewrite -> !extend_term_cancel; auto.
  apply prod_action_ppair; auto.
  }
destruct H as (u3 & u3' & Hu3).
cbn in Hu3.
rewrite -> deextend_urelsp_urelspinj_prod in Hu3.
exists (map_term (extend w v) u3), (map_term (extend w v) u3').
force_exact Hu3.
do 2 f_equal.
apply urelspinj_equal.
simpmap.
rewrite -> !extend_term_cancel; auto.
apply prod_action_ppair; auto.
Qed.
