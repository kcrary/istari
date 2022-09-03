
Require Import Tactics.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.


Definition letnext {object} m n : term object :=
  subst1 (prev m) n.


Definition sumtype {object} a b : term object :=
  sigma booltp (bite (var 0) (subst sh1 a) (subst sh1 b)).


Definition sumleft {object} m : term object :=
  ppair btrue m.


Definition sumright {object} m : term object :=
  ppair bfalse m.


Definition sumcase {object} m n p : term object :=
  bite (ppi1 m) (subst1 (ppi2 m) n) (subst1 (ppi2 m) p).


Definition nattp {object} : term object :=
  mu (sumtype unittp (var 0)).


Definition nzero {object} : term object :=
  sumleft triv.


Definition nsucc {object} m : term object :=
  sumright m.


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
