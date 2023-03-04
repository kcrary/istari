
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Tactics.
Require Import Sequence.
Require Import Relation.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.
Require Import Dynamic.
Require Import Promote.
Require Import Hygiene.
Require Import Rules.
Require Import DerivedRules.
Require Import Dots.
Require Defs.
Require Import Equivalence.
Require Import Equivalences.
Require Import Morphism.

Require Import Defined.
Require Import SumLemmas.
Require Import NatLemmas.



Lemma subst_intersect2 :
  forall object (s : @sub object) a b,
    subst s (intersect2 a b) = intersect2 (subst s a) (subst s b).
Proof.
intros object s a b.
unfold intersect2.
simpsub.
reflexivity.
Qed.


Hint Rewrite subst_intersect2 : subst.  


Lemma tr_intersect2_formation :
  forall G a a' b b',
    tr G (deqtype a a')
    -> tr G (deqtype b b')
    -> tr G (deqtype (intersect2 a b) (intersect2 a' b')).
Proof.
intros G a a' b b' Ha Hb.
apply tr_intersect_formation; auto using tr_booltp_istype.
apply tr_booltp_elim_eqtype.
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  apply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  auto.
  }

  {
  apply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  auto.
  }
Qed.


Lemma tr_intersect2_formation_univ :
  forall G lv a a' b b',
    tr G (deq a a' (univ lv))
    -> tr G (deq b b' (univ lv))
    -> tr G (deq (intersect2 a b) (intersect2 a' b') (univ lv)).
Proof.
intros G lv a a' b b' Ha Hb.
apply tr_intersect_formation_univ.
  {
  apply tr_booltp_formation_univ_gen.
  apply tr_univ_formation_invert.
  eapply tr_inhabitation_formation; eauto.
  }
replace (univ (subst sh1 lv)) with (subst1 (var 0) (univ (subst (sh 2) lv))) by (simpsub; auto).
apply tr_booltp_elim.
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  apply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  auto.
  }

  {
  apply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  auto.
  }
Qed.


Lemma tr_intersect2_intro :
  forall G a b m n,
    tr G (deq m n a)
    -> tr G (deq m n b)
    -> tr G (deq m n (intersect2 a b)).
Proof.
intros G a b m n Ha Hb.
apply tr_intersect_intro; auto using tr_booltp_istype.
apply tr_equal_elim.
apply (tr_equal_eta2 _#4 (bite (var 0) triv triv) (bite (var 0) triv triv)).
replace (equal (bite (var 0) (subst sh1 a) (subst sh1 b)) (subst sh1 m) (subst sh1 n)) with
 (subst1 (var 0) (equal (bite (var 0) (subst (sh 2) a) (subst (sh 2) b)) (subst (sh 2) m) (subst (sh 2) n))) by (simpsub; auto).
apply tr_booltp_elim.
  {
  eapply hypothesis; eauto using index_0.
  }

  {
  simpsub.
  apply tr_equal_intro.
  rewrite -> equiv_bite_l.
  apply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  auto.
  }

  {
  simpsub.
  apply tr_equal_intro.
  rewrite -> equiv_bite_r.
  apply (weakening _ [_] []).
    {
    cbn [length unlift].
    simpsub.
    auto.
    }

    {
    cbn [length unlift].
    simpsub.
    auto.
    }
  cbn [length unlift].
  simpsub.
  cbn [List.app].
  auto.
  }
Qed.


Lemma tr_intersect2_elim1 :
  forall G a b m n,
    tr G (deq m n (intersect2 a b))
    -> tr G (deq m n a).
Proof.
intros G a b m n Hmn.
so (tr_intersect_elim _#7 Hmn (tr_booltp_intro_btrue _)) as H.
simpsubin H.
rewrite -> equiv_bite_l in H.
exact H.
Qed.


Lemma tr_intersect2_elim2 :
  forall G a b m n,
    tr G (deq m n (intersect2 a b))
    -> tr G (deq m n b).
Proof.
intros G a b m n Hmn.
so (tr_intersect_elim _#7 Hmn (tr_booltp_intro_bfalse _)) as H.
simpsubin H.
rewrite -> equiv_bite_r in H.
exact H.
Qed.


Lemma def_lleq :
  forall m n,
    equiv 
      (app (app Defs.lleq m) n)
      (intersect2
         (app (app leqtp m) n)
         (intersect2
            (equal nattp m m)
            (equal nattp n n))).
Proof.
intros m n.
unfold Defs.lleq.
rewrite -> equiv_beta.
simpsub.
rewrite -> equiv_beta.
simpsub.
apply equiv_refl.
Qed.


Lemma lleq_explode :
  forall G m n p q,
    tr G (deq p q (app (app Defs.lleq m) n))
    -> tr G (deq triv triv (app (app leqtp m) n))
       /\ tr G (deq m m nattp)
       /\ tr G (deq n n nattp).
Proof.
intros G m n p q H.
rewrite -> def_lleq in H.
assert (tr G (deq m m nattp)) as Hm.
  {
  apply tr_equal_elim.
  eapply (tr_equal_eta2 _#4 p q).
  eapply tr_intersect2_elim1.
  eapply tr_intersect2_elim2; eauto.
  }
assert (tr G (deq n n nattp)) as Hn.
  {
  apply tr_equal_elim.
  eapply (tr_equal_eta2 _#4 p q).
  eapply tr_intersect2_elim2.
  eapply tr_intersect2_elim2; eauto.
  }
do2 2 split; auto.
eapply (tr_leqtp_eta2 _#3 p q); eauto.
eapply tr_intersect2_elim1; eauto.
Qed.


Lemma lleq_implode :
  forall G m n,
    tr G (deq triv triv (app (app leqtp m) n))
    -> tr G (deq m m nattp)
    -> tr G (deq n n nattp)
    -> tr G (deq triv triv (app (app Defs.lleq m) n)).
Proof.
intros G m n Hleq Hm Hn.
rewrite -> def_lleq.
apply tr_intersect2_intro; auto.
apply tr_intersect2_intro; auto using tr_equal_intro.
Qed.
