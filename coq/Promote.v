
Require Import Coq.Lists.List.

Require Import Syntax.
Require Import Sequence.
Require Import Subst.
Require Import Equivalence.


Definition promote_hyp {object} (h : @hyp object) : hyp :=
  match h with
  | hyp_tpl => hyp_tp
  | hyp_tml a => hyp_tm a
  | _ => h
  end.
   

Definition promote {object} (G : @context object) : context :=
  map promote_hyp G.


Inductive hpositive {object} (P N : list (term object)) : nat -> term object -> Prop :=
| hpositive_goal :
    forall i a,
      In a P
      -> hpositive P N i (subst (sh i) a)

| hpositive_var :
    forall i,
      hpositive P N i (var i)

| hpositive_const :
    forall i a,
      hpositive P N i (subst (under i sh1) a)

| hpositive_prod :
    forall i a b,
      hpositive P N i a
      -> hpositive P N i b
      -> hpositive P N i (prod a b)

| hpositive_pi :
    forall i a b,
      hnegative P N i a
      -> hpositive P N (S i) b
      -> hpositive P N i (pi a b)

| hpositive_sigma :
    forall i a b,
      hpositive P N i a
      -> hpositive P N (S i) b
      -> hpositive P N i (sigma a b)

| hpositive_fut :
    forall i a,
      hpositive P N i a
      -> hpositive P N i (fut a)

| hpositive_mu :
    forall i a,
      hpositive P N (S i) a
      -> hpositive P N i (mu a)

| hpositive_bite :
    forall i m a b,
      hpositive P N i a
      -> hpositive P N i b
      -> hpositive P N i (bite (subst (under i sh1) m) a b)

| hpositive_equiv :
    forall i a b,
      equiv a b
      -> hpositive P N i b
      -> hpositive P N i a

with hnegative {object} (P N : list (term object)) : nat -> term object -> Prop :=
| hnegative_goal :
    forall i a,
      In a N
      -> hnegative P N i (subst (sh i) a)

| hnegative_const :
    forall i a,
      hnegative P N i (subst (under i sh1) a)

| hnegative_prod :
    forall i a b,
      hnegative P N i a
      -> hnegative P N i b
      -> hnegative P N i (prod a b)

| hnegative_pi :
    forall i a b,
      hpositive P N i a
      -> hnegative P N (S i) b
      -> hnegative P N i (pi a b)

| hnegative_sigma :
    forall i a b,
      hnegative P N i a
      -> hnegative P N (S i) b
      -> hnegative P N i (sigma a b)

| hnegative_fut :
    forall i a,
      hnegative P N i a
      -> hnegative P N i (fut a)

| hnegative_mu :
    forall i a,
      hnegative P N (S i) a
      -> hnegative P N i (mu a)

| hnegative_bite :
    forall i m a b,
      hnegative P N i a
      -> hnegative P N i b
      -> hnegative P N i (bite (subst (under i sh1) m) a b)

| hnegative_equiv :
    forall i a b,
      equiv a b
      -> hnegative P N i b
      -> hnegative P N i a
.


Scheme hpositive_mut_ind := Minimality for hpositive Sort Prop
with   hnegative_mut_ind := Minimality for hnegative Sort Prop.
Combined Scheme hpositive_hnegative_ind from hpositive_mut_ind, hnegative_mut_ind.


Inductive active {object} : @term object -> Prop :=
| active_var :
    active (var 0)

| active_app :
    forall m n,
      active m
      -> active (app m n)

| active_prev :
    forall m,
      active m
      -> active (prev m)

| active_ppi1 :
    forall m,
      active m
      -> active (ppi1 m)

| active_ppi2 :
    forall m,
      active m
      -> active (ppi2 m)

| active_bite :
    forall m n p,
      active m
      -> active (bite m n p)

| active_seq :
    forall m n,
      active m
      -> active (seq m n)
.
