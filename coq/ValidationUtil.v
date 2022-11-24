
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Tactics.
Require Import Sequence.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.
Require Import Promote.
Require Import Hygiene.
Require Import Rules.
Require Import DerivedRules.
Require Defs.
Require Import Obligations.
Require Import Morphism.
Require Import DefsEquiv.
Require Import Equivalence.
Require Import Defined.
Require Import Dots.


Definition ctx := @context Rules.obj.


Lemma deq_intro :
  forall G a m n p q,
    tr G (deq p q (equal a m n))
    -> tr G (deq m n a).
Proof.
intros G a m n p q H.
apply tr_equal_elim.
apply (tr_transitivity _ _ p).
  {
  apply tr_symmetry.
  apply tr_equal_eta.
  apply (tr_transitivity _ _ q); auto.
  apply tr_symmetry; auto.
  }

  {
  apply tr_equal_eta.
  apply (tr_transitivity _ _ q); auto.
  apply tr_symmetry; auto.
  }
Qed.



Hint Rewrite def_istp def_of def_eqtp def_eq def_level def_subtype def_univ def_kind : prepare.


Ltac prepare :=
  try unfoldtop;
  unfold Defs.dof;
  intros;
  autorewrite with prepare in * |- *;
  unfold Defs.triv;
  repeat
    (match goal with
     | |- tr _ (deq triv triv (eqtype ?X ?Y)) => fold (deqtype X Y)

     | H : tr _ (deq _ _ (eqtype ?X ?Y)) |- _ => let H' := fresh in so (tr_eqtype_eta2 _#5 H) as H'; fold (deqtype X Y) in H'; move H' before H; clear H

     | |- tr _ (deq triv triv (subtype ?X ?Y)) => fold (dsubtype X Y)

     | H : tr _ (deq _ _ (subtype ?X ?Y)) |- _ => let H' := fresh in so (tr_subtype_eta2 _#5 H) as H'; fold (dsubtype X Y) in H'; move H' before H; clear H

     | |- tr _ (deq triv triv (equal _ _ _)) => apply tr_equal_intro

     | H : tr _ (deq _ _ (equal _ _ _)) |- _ => let H' := fresh in so (tr_equal_elim _#4 (tr_equal_eta2 _#6 H)) as H'; move H' before H; clear H

     end);
  revert_all.



(* This is from before we worked out the current system.  Now deprecated. *)

Hint Unfold Defs.dof Defs.triv Defs.level Defs.void Defs.bool
  Defs.false Defs.true Defs.unit Defs.zero Defs.nat: valid_hint.


Ltac valid_rewrite := repeat (try rewrite -> def_of in * |- *;
                                try rewrite -> def_arrow in * |- *;
                                try rewrite -> def_kind in * |- *;
                                try rewrite -> def_univ in * |- *;
                                try rewrite -> def_kind in * |- *;
                                try rewrite -> def_pi in * |- *;
                                try rewrite -> def_eq in * |- *;
                                try rewrite -> def_eqtp in * |- *;
                                try rewrite -> def_istp in * |- *;
                                try rewrite -> def_sigma in * |- *;
                                try rewrite -> def_prod in * |- *;
                                try rewrite -> def_fut in * |- *;
                                try rewrite -> def_rec in * |- *;
                                try rewrite -> def_ite in * |- *;
                                try rewrite -> def_tarrow in * |- *
                               ).

