
Require Import Axioms.
Require Import Tactics.
Require Import Sigma.
Require Import Equality.
Require Import Syntax.
Require Import Ofe.
Require Import Spaces.
Require Import Uniform.
Require Import Urelsp.
Require Import Ordinal.
Require Import Equivalence.
Require Import Hygiene.
Require Import Intensional.
Require Import Candidate.
Require Import MapTerm.
Require Import Extend.
Require Export Promote.
Require Import Truncate.
Require Import Page.
Require Import Model.


Definition sterm := wterm stop.
Definition shyp := @hyp (obj stop).
Definition scontext := @context (obj stop).
Definition sjudgement := @judgement (obj stop).
Definition ssub := @sub (obj stop).
Definition surel := wurel stop.
Definition siurel := wiurel stop.
Definition siurel_ofe := wiurel_ofe stop.


Record System : Type :=
mk_system
  { valid : ordinal -> Prop ;

    sint : page -> bool -> nat -> sterm -> siurel -> Prop ;
    sintk : page -> bool -> nat -> sterm -> qkind -> Prop ;

    valid_downward :
      forall v w,
        v <<= w
        -> valid w
        -> valid v ;

    sint_closed :
      forall pg s i c R,
        sint pg s i c R
        -> hygiene clo c ;

    sintk_closed :
      forall pg s i c K,
        sintk pg s i c K
        -> hygiene clo c ;

    sint_equiv :
      forall pg s i c c' R,
        hygiene clo c'
        -> equiv c c'
        -> sint pg s i c R
        -> sint pg s i c' R ;

    sintk_equiv :
      forall pg s i c c' K,
        hygiene clo c'
        -> equiv c c'
        -> sintk pg s i c K
        -> sintk pg s i c' K ;

    sint_fun :
      forall pg s i c R R',
        sint pg s i c R
        -> sint pg s i c R'
        -> R = R' ;

    sintk_fun :
      forall pg s i c K K',
        sintk pg s i c K
        -> sintk pg s i c K'
        -> K = K' ;

    sint_downward :
      forall pg s i j c R,
        j <= i
        -> sint pg s i c R
        -> sint pg s j c (iutruncate (S j) R) ;

    sintk_downward :
      forall pg s i j c K,
        j <= i
        -> sintk pg s i c K
        -> sintk pg s j c (approx j K) ;

  }.
