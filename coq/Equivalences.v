
Require Import Tactics.
Require Import Relation.
Require Import Syntax.
Require Import Subst.
Require Import Dynamic.
Require Import Reduction.
Require Import Equivalence.


Section object.


Variable object : Type.


Local Ltac prove_equiv_compat :=
  intros;
  apply equiv_compat;
  apply mc_oper; repeat2 (apply mcr_cons); [.. | apply mcr_nil]; auto.


Lemma equiv_beta :
  forall (m n : @term object),
    equiv (app (lam m) n) (subst1 n m).
Proof.
intros m n.
apply steps_equiv.
apply star_one.
apply step_app2.
Qed.


Lemma equiv_beta1 :
  forall (m n : @term object),
    equiv (ppi1 (ppair m n)) m.
Proof.
intros m n.
apply steps_equiv.
apply star_one.
apply step_ppi12.
Qed.


Lemma equiv_beta2 :
  forall (m n : @term object),
    equiv (ppi2 (ppair m n)) n.
Proof.
intros m n.
apply steps_equiv.
apply star_one.
apply step_ppi22.
Qed.


Lemma equiv_bite_l :
  forall (m n : @term object),
    equiv (bite btrue m n) m.
Proof.
intros m n.
apply steps_equiv.
apply star_one.
apply step_bite2.
Qed.


Lemma equiv_bite_r :
  forall (m n : @term object),
    equiv (bite bfalse m n) n.
Proof.
intros m n.
apply steps_equiv.
apply star_one.
apply step_bite3.
Qed.



Lemma equiv_all :
  forall (a a' b b' c c' : term object),
    equiv a a'
    -> equiv b b'
    -> equiv c c'
    -> equiv (all a b c) (all a' b' c').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_alltp :
  forall (a a' : term object),
    equiv a a'
    -> equiv (alltp a) (alltp a').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_app :
  forall (m m' n n' : term object),
    equiv m m'
    -> equiv n n'
    -> equiv (app m n) (app m' n').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_clam :
  forall (k k' c c' : term object),
    equiv k k'
    -> equiv c c'
    -> equiv (clam k c) (clam k' c').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_capp :
  forall (a a' b b' : term object),
    equiv a a'
    -> equiv b b'
    -> equiv (capp a b) (capp a' b').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_ctlam :
  forall (a a' b b' k k' : @term object),
    equiv a a'
    -> equiv b b'
    -> equiv k k'
    -> equiv (ctlam a b k) (ctlam a' b' k').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_ctapp :
  forall (a a' m m' : @term object),
    equiv a a'
    -> equiv m m'
    -> equiv (ctapp a m) (ctapp a' m').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_cpair :
  forall (a a' b b' : term object),
    equiv a a'
    -> equiv b b'
    -> equiv (cpair a b) (cpair a' b').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_cpi1 :
  forall (a a' : term object),
    equiv a a'
    -> equiv (cpi1 a) (cpi1 a').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_cpi2 :
  forall (a a' : term object),
    equiv a a'
    -> equiv (cpi2 a) (cpi2 a').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_cnext :
  forall (m m' : @term object),
    equiv m m'
    -> equiv (cnext m) (cnext m').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_cprev :
  forall (m m' : @term object),
    equiv m m'
    -> equiv (cprev m) (cprev m').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_cty :
  forall (a a' : term object),
    equiv a a'
    -> equiv (cty a) (cty a').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_con :
  forall (m1 m1' m2 m2' : term object),
    equiv m1 m1'
    -> equiv m2 m2'
    -> equiv (con m1 m2) (con m1' m2').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_exist :
  forall (a a' b b' c c' : term object),
    equiv a a'
    -> equiv b b'
    -> equiv c c'
    -> equiv (exist a b c) (exist a' b' c').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_fut :
  forall (k k' : term object),
    equiv k k'
    -> equiv (fut k) (fut k').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_intersect :
  forall (a a' b b' : term object),
    equiv a a'
    -> equiv b b'
    -> equiv (intersect a b) (intersect a' b').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_union :
  forall (a a' b b' : term object),
    equiv a a'
    -> equiv b b'
    -> equiv (union a b) (union a' b').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_ispositive :
  forall (m m' : term object),
    equiv m m'
    -> equiv (ispositive m) (ispositive m').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_isnegative :
  forall (m m' : term object),
    equiv m m'
    -> equiv (isnegative m) (isnegative m').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_pi :
  forall (a a' b b' : term object),
    equiv a a'
    -> equiv b b'
    -> equiv (pi a b) (pi a' b').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_set :
  forall (a a' b b' : term object),
    equiv a a'
    -> equiv b b'
    -> equiv (set a b) (set a' b').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_iset :
  forall (a a' b b' : term object),
    equiv a a'
    -> equiv b b'
    -> equiv (iset a b) (iset a' b').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_quotient :
  forall (a a' b b' : term object),
    equiv a a'
    -> equiv b b'
    -> equiv (quotient a b) (quotient a' b').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_sigma :
  forall (a a' b b' : term object),
    equiv a a'
    -> equiv b b'
    -> equiv (sigma a b) (sigma a' b').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_lam :
  forall (m m' : term object),
    equiv m m'
    -> equiv (lam m) (lam m').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_mu :
  forall (a a' : term object),
    equiv a a'
    -> equiv (mu a) (mu a').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_next :
  forall (m m' : @term object),
    equiv m m'
    -> equiv (next m) (next m').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_prev :
  forall (m m' : @term object),
    equiv m m'
    -> equiv (prev m) (prev m').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_bite :
  forall object (m1 m1' m2 m2' m3 m3' : @term object),
    equiv m1 m1'
    -> equiv m2 m2'
    -> equiv m3 m3'
    -> equiv (bite m1 m2 m3) (bite m1' m2' m3').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_ppair :
  forall (m m' n n' : term object),
    equiv m m'
    -> equiv n n'
    -> equiv (ppair m n) (ppair m' n').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_ppi1 :
  forall object (m m' : @term object),
    equiv m m'
    -> equiv (ppi1 m) (ppi1 m').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_ppi2 :
  forall object (m m' : @term object),
    equiv m m'
    -> equiv (ppi2 m) (ppi2 m').
Proof.
prove_equiv_compat.
Qed.


Lemma equiv_rec :
  forall (k k' : term object),
    equiv k k'
    -> equiv (rec k) (rec k').
Proof.
prove_equiv_compat.
Qed.



End object.


Hint Resolve equiv_fut equiv_rec equiv_clam equiv_capp equiv_cty equiv_con equiv_pi equiv_app equiv_bite equiv_ppair equiv_ppi1 equiv_ppi2 : equiv_compat.
