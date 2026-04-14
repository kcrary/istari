
Require Import Tactics.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.


Definition letnext {object} m n : term object :=
  subst1 (prev m) n.


Lemma subst_letnext :
  forall object (s : @sub object) m n, subst s (letnext m n) = letnext (subst s m) (subst (under 1 s) n).
Proof.
intros.
unfold letnext.
simpsub.
reflexivity.
Qed.
Hint Rewrite subst_letnext : subst.


Definition sumtype {object} a b : term object :=
  sigma booltp (bite (var 0) (subst sh1 a) (subst sh1 b)).


Lemma subst_sumtype :
  forall object (s : @sub object) a b, subst s (sumtype a b) = sumtype (subst s a) (subst s b).
Proof.
intros.
unfold sumtype.
simpsub.
reflexivity.
Qed.
Hint Rewrite subst_sumtype : subst.


Definition sumleft {object} m : term object :=
  ppair btrue m.


Lemma subst_sumleft :
  forall object (s : @sub object) m, subst s (sumleft m) = sumleft (subst s m).
Proof.
prove_subst.
Qed.
Hint Rewrite subst_sumleft : subst.


Definition sumright {object} m : term object :=
  ppair bfalse m.


Lemma subst_sumright :
  forall object (s : @sub object) m, subst s (sumright m) = sumright (subst s m).
Proof.
prove_subst.
Qed.
Hint Rewrite subst_sumright : subst.


Definition sumcase {object} m n p : term object :=
  bite (ppi1 m) (subst1 (ppi2 m) n) (subst1 (ppi2 m) p).


Lemma subst_sumcase :
  forall object (s : @sub object) m n p, subst s (sumcase m n p) = sumcase (subst s m) (subst (under 1 s) n) (subst (under 1 s) p).
Proof.
intros.
unfold sumcase.
simpsub.
reflexivity.
Qed.
Hint Rewrite subst_sumcase : subst.


Definition nattp {object} : term object :=
  mu (sumtype unittp (var 0)).


Lemma subst_nattp :
  forall object (s : @sub object), subst s nattp = nattp.
Proof.
prove_subst.
Qed.
Hint Rewrite subst_nattp : subst.


Definition nzero {object} : term object :=
  sumleft triv.


Lemma subst_nzero :
  forall object (s : @sub object), subst s nzero = nzero.
Proof.
prove_subst.
Qed.
Hint Rewrite subst_nzero : subst.


Definition nsucc {object} m : term object :=
  sumright m.


Lemma subst_nsucc :
  forall object (s : @sub object) a, subst s (nsucc a) = nsucc (subst s a).
Proof.
intros.
unfold nsucc.
simpsub.
reflexivity.
Qed.
Hint Rewrite subst_nsucc : subst.


Definition theta {object} : term object :=
  app 
    (lam (lam (app (var 0) (app (app (var 1) (var 1)) (var 0)))))
    (lam (lam (app (var 0) (app (app (var 1) (var 1)) (var 0))))).


Definition wind {object} f : term object :=
  app theta
    (lam (lam (app
                 (app
                    (app
                       (subst (sh 2) f)
                       (ppi1 (var 0)))
                    (ppi2 (var 0)))
                 (lam (app (var 2) (app (ppi2 (var 1)) (var 0))))))).

Definition bottom {object} : term object := app theta (lam (var 0)).

Definition leqtp {object} : term object :=
  app theta
    (lam (lam (lam (sumcase 
                      (var 1)
                      unittp
                      (sumcase
                         (var 1)
                         voidtp
                         (app (app (var 4) (var 1)) (var 0))))))).

Definition lttp {object} : term object :=
  lam (app (subst sh1 leqtp) (nsucc (var 0))).


Definition pagetp {object} := @nattp object.


Definition leqpagetp {object} m n : term object :=
  app (app leqtp m) n.


Definition ltpagetp {object} m n : term object :=
  app (app lttp m) n.


Definition squash {object} m : term object :=
  set unittp (subst sh1 m).


Lemma subst_squash :
  forall object (s : @sub object) a, subst s (squash a) = squash (subst s a).
Proof.
intros object s a.
unfold squash.
simpsub.
reflexivity.
Qed.
Hint Rewrite subst_squash : subst.


Definition isquash {object} m : term object :=
  iset unittp (subst sh1 m).


Lemma subst_isquash :
  forall object (s : @sub object) a, subst s (isquash a) = isquash (subst s a).
Proof.
intros object s a.
unfold isquash.
simpsub.
reflexivity.
Qed.
Hint Rewrite subst_isquash : subst.


Definition intersect2 {object} (a b : @term object) :=
  intersect booltp (bite (var 0) (subst sh1 a) (subst sh1 b)).


Definition nonsense {object} : term object :=
  guard voidtp voidtp.


Lemma subst_nonsense :
  forall object (s : @sub object), subst s nonsense = nonsense.
Proof.
prove_subst.
Qed.
Hint Rewrite subst_nonsense : subst.

Definition conjoin {object} a b : @term object :=
  intersect booltp (bite (var 0) (subst sh1 a) (subst sh1 b)).


Lemma subst_conjoin :
  forall object (s : @sub object) m1 m2, subst s (conjoin m1 m2) = conjoin (subst s m1) (subst s m2).
Proof.
unfold conjoin.
intros object s m1 m2.
simpsub.
reflexivity.
Qed.
Hint Rewrite subst_conjoin : subst.
