
Require Export Coq.Lists.List.
Require Export Tactics.
Require Export Syntax.
Require Export Subst.
Require Export SimpSub.
Require Export Promote.
Require Import Defined.
Require Export Rules.
Require Export Hygiene.

Definition fterm := @term Rules.obj.

Definition dof (m a : fterm) : judgement := deq m m a.

Fixpoint dots (i : nat) (n : nat) (s : sub) : @sub Rules.obj :=
  match n with
  | 0 => s
  | S n' =>
      dots i n' (dot (var (i + n')) s)
  end.

Definition inl : fterm := lam (ppair btrue (var 0)).
Definition inr : fterm := lam (ppair bfalse (var 0)).

Definition abort : fterm := lam (var 0).

Definition acc : fterm :=
  lam 
    (lam
       (lam
          (sigma
             (mu (sigma (var 3)
                    (pi (var 4)
                       (pi
                          (app (app (var 4) (var 0)) (var 1))
                          (var 3)))))
             (app
                (app
                   (app
                      theta
                      (lam
                         (lam
                            (lam
                               (sigma 
                                  (equal (var 6) (var 0) (ppi1 (var 1)))
                                  (pi (var 7)
                                     (pi 
                                        (app (app (var 7) (var 0)) (var 2))
                                        (app
                                           (app 
                                              (var 5)
                                              (app (app (ppi2 (var 4)) (var 1)) (var 0)))
                                           (var 1)))))))))
                   (var 0))
                (var 1))))).

Definition bool : fterm := booltp.
Definition eeqtp : fterm := lam (lam (prod (subtype (var 1) (var 0)) (subtype (var 0) (var 1)))).
Definition eq : fterm := lam (lam (lam (equal (var 2) (var 1) (var 0)))).
Definition eqtp : fterm := lam (lam (eqtype (var 1) (var 0))).
Definition false : fterm := bfalse.
Definition foralltp : fterm := lam (alltp (app (var 1) (var 0))).
Definition future : fterm := lam (fut (var 0)).
Definition guard : fterm := lam (lam (guard (var 1) (var 0))).
Definition iexists : fterm := lam (lam (lam (exist (var 2) (var 1) (app (var 1) (var 0))))).
Definition iforall : fterm := lam (lam (lam (all (var 2) (var 1) (app (var 1) (var 0))))).
Definition intersect : fterm := lam (lam (intersect (var 1) (app (var 1) (var 0)))).
Definition istp : fterm := lam (eqtype (var 0) (var 0)).
Definition ite : fterm := lam (lam (lam (bite (var 2) (var 1) (var 0)))).
Definition karrow : fterm := lam (lam (karrow (var 1) (var 0))).
Definition kind : fterm := lam (kuniv (var 0)).
Definition letnext : fterm := lam (lam (app (var 0) (prev (var 1)))).
Definition level : fterm := nattp.
Definition lleq : fterm := leqtp.
Definition lmax : fterm :=
  app theta
    (lam (lam (lam (sumcase
                      (var 1)
                      (var 1)
                      (sumcase
                         (var 1)
                         (var 3)
                         (app inr (app (app (var 4) (var 1)) (var 0)))))))).
Definition lsucc : fterm := lam (app inr (var 0)).
Definition lzero : fterm := app inl triv.
Definition monotone : fterm := lam (alltp (alltp (pi (subtype (var 1) (var 0)) (subst sh1 (subtype (app (var 2) (var 1)) (app (var 2) (var 0))))))).
Definition mu : fterm := lam (mu (app (var 1) (var 0))).
Definition nat : fterm := nattp.
Definition negative : fterm := lam (isnegative (app (var 1) (var 0))).
Definition of : fterm := lam (lam (equal (var 1) (var 0) (var 0))).
Definition prod : fterm := lam (lam (prod (var 1) (var 0))).
Definition quotient : fterm := lam (lam (quotient (var 1) (app (app (var 2) (var 1)) (var 0)))).
Definition rec : fterm := lam (rec (app (var 1) (var 0))).
Definition positive : fterm := lam (ispositive (app (var 1) (var 0))).
Definition squash : fterm := lam (set unittp (var 1)).
Definition subtype : fterm := lam (lam (subtype (var 1) (var 0))).
Definition succ : fterm := lam (app inr (var 0)).
Definition sum : fterm := lam (lam (sigma booltp (bite (var 0) (var 2) (var 1)))).
Definition tarrow : fterm := lam (lam (arrow (var 1) (var 0))).
Definition true : fterm := btrue.
Definition unit : fterm := unittp.
Definition univ : fterm := lam (univ (var 0)).
Definition void : fterm := voidtp.
Definition wtype : fterm := lam (lam (wt (var 1) (app (var 1) (var 0)))).
Definition zero : fterm := app inl triv.

Definition sumcase : fterm := 
  lam (lam (lam (bite 
                   (ppi1 (var 2))
                   (app (var 1) (ppi2 (var 2)))
                   (app (var 0) (ppi2 (var 2)))))).

Definition natcase : fterm :=
  lam (lam (lam (app
                   (app
                      (app sumcase (var 2))
                      (lam (var 2)))
                   (lam (app (var 1) (var 0)))))).

Definition max : fterm :=
  app theta (lam (lam (lam (app (app (app natcase
                                        (var 1))
                                   (var 0))
                              (lam
                                 (app (app (app natcase
                                              (var 1))
                                         (var 2))
                                    (lam
                                       (app succ
                                          (app (app (var 4) (var 1)) (var 0)))))))))).

Definition set : fterm := lam (lam (set (var 1) (app (var 1) (var 0)))).
Definition sigma : fterm := lam (lam (sigma (var 1) (app (var 1) (var 0)))).
Definition theta : fterm := theta.
Definition triv : fterm := triv.
Definition wind : fterm := lam (wind (var 0)).

Definition arrow : fterm := lam (lam (pi (var 1) (var 1))).
Definition pi : fterm := lam (lam (pi (var 1) (app (var 1) (var 0)))).
