
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
Require Defs.
Require Import Obligations.
Require Import Morphism.
Require Import DefsEquiv.
Require Import Equivalence.
Require Import Dots.

Require Import ValidationUtil.
Require Import Defined.
Require Import ValidationSum.
Require Import PageType.
Require MuIndExtract.
Require Import NatLemmas.



Lemma def_nat : eq Defs.nat nattp.
Proof.
auto.
Qed.


Hint Rewrite def_nat : prepare.


Definition natcase {object} m n p : term object :=
  sumcase m (subst sh1 n) p.


Definition natmax {object} m n : term object :=
  app (app (app theta
              (lam (lam (lam (natcase (var 1) 
                                (var 0)
                                (natcase (var 1)
                                   (var 2)
                                   (nsucc
                                      (app (app (var 4) (var 1)) (var 0)))))))))
         m)
    n.
