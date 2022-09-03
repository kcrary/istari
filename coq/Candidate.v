
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
Require Import MapTerm.
Require Import Hygiene.
Require Import Intensional.


Inductive pre_qkind (w : ordinal) (Ob : forall v, v << w -> Type) : Type :=
| pqone : fin 0 << w -> pre_qkind w Ob

| pqtype : forall v, v << w -> pre_qkind w Ob

| pqarrow : pre_qkind w Ob -> pre_qkind w Ob -> pre_qkind w Ob

| pqtarrow : forall v (h : v << w), car (urel_ofe (Ob v h)) -> pre_qkind w Ob -> pre_qkind w Ob

| pqprod : pre_qkind w Ob -> pre_qkind w Ob -> pre_qkind w Ob

| pqfut : pre_qkind w Ob -> pre_qkind w Ob
.


Fixpoint pre_space (w : ordinal) 
  (Ob : forall v, v << w -> Type)
  (k : pre_qkind w Ob)
  : ofe :=
  match k with
  | pqone _ _ _ => unit_ofe

  | pqtype _ _  v h => iurel_ofe (Ob v h)

  | pqarrow _ _ k1 k2 => nearrow_ofe (pre_space w Ob k1) (pre_space w Ob k2)

  | pqtarrow _ _ v h A k2 => nearrow_ofe (urelsp A) (pre_space w Ob k2)

  | pqprod _ _ k1 k2 => prod_ofe (pre_space w Ob k1) (pre_space w Ob k2)

  | pqfut _ _ k1 => half (pre_space w Ob k1)
  end.


Fixpoint pre_obj (w : ordinal) (acc : Acc lt_ord w) {struct acc}
  : Type :=
  option
    (existsT (k : pre_qkind w (fun u h => pre_obj u (Acc_inv acc u h))),
       car (pre_space _ _ k)).


Definition obj (w : ordinal) : Type :=
  pre_obj w (lt_ord_wf w).


Definition wterm (w : ordinal) : Type := term (obj w).
Definition wurel (w : ordinal) : Type := urel (obj w).
Definition wurel_ofe (w : ordinal) : ofe := urel_ofe (obj w).
Definition wiurel (w : ordinal) : Type := iurel (obj w).
Definition wiurel_ofe (w : ordinal) : ofe := iurel_ofe (obj w).


Inductive qkind : Type :=
| qone : qkind

| qtype : ordinal -> qkind

| qarrow : qkind -> qkind -> qkind

| qtarrow : forall w, car (wurel_ofe w) -> qkind -> qkind

| qprod : qkind -> qkind -> qkind

| qfut : qkind -> qkind
.


Fixpoint level (k : qkind) : ordinal :=
  match k with
  | qone => fin 0

  | qtype w => w

  | qarrow k1 k2 => max_ord (level k1) (level k2)

  | qtarrow w _ k2 => max_ord w (level k2)

  | qprod k1 k2 => max_ord (level k1) (level k2)

  | qfut k1 => level k1
  end.


Fixpoint space (k : qkind) : ofe :=
  match k with
  | qone => unit_ofe

  | qtype w => wiurel_ofe w

  | qarrow k1 k2 => nearrow_ofe (space k1) (space k2)

  | qtarrow i A k2 => nearrow_ofe (urelsp A) (space k2)

  | qprod k1 k2 => prod_ofe (space k1) (space k2)

  | qfut k1 => half (space k1)
  end.


Definition spcar (k : qkind) := car (space k).


Definition candidate : Type :=
  existsT (k : qkind), car (space k).


Inductive xobj w : Type :=
| objsome : forall (Q : candidate), level (pi1 Q) << w -> xobj w
| objnone : xobj w.


Arguments objsome {w}.
Arguments objnone {w}.


Lemma objsome_compat :
  forall w Q Q' h h',
    Q = Q'
    -> @objsome w Q h = objsome Q' h'.
Proof.
intros w Q Q' h h' H.
subst Q'.
so (proof_irrelevance _ h h'); subst h'.
reflexivity.
Qed.    


Local Definition Ob {w} (v : ordinal) (h : v << w) : Type := obj v.


Lemma obj_unroll :
  forall w,
    obj w
    =
    option (existsT (k : pre_qkind w Ob),
              car (pre_space _ _ k)).
Proof.
intros w.
unfold Ob.
unfold obj.
set (acc := lt_ord_wf w).
destruct acc as [IH].
cbn.
f_equal.
apply (exT_equal
         (forall u, u << w -> Type)
         (pre_qkind w)
         (fun Ob k => car (pre_space _ _ k))
         (fun Ob k => car (pre_space _ _ k))).
apply (eq_impl_eq_dep_fst
         (forall u, u << w -> Type)         
         (fun Ob => pre_qkind w Ob -> Type)
         _ _
         (fun Ob k => car (pre_space _ _ k))).
fextensionality 2.
intros u H.
f_equal.
apply proof_irrelevance.
Qed.


Fixpoint pre_qkind_to_qkind {w : ordinal} (k : pre_qkind w Ob) {struct k}
  : qkind
  :=
  match k with
  | pqone _ _ _ => qone

  | pqtype _ _ v _ => qtype v

  | pqarrow _ _ k1 k2 => qarrow (pre_qkind_to_qkind k1) (pre_qkind_to_qkind k2)

  | pqtarrow _ _ v _ A k2 => qtarrow v A (pre_qkind_to_qkind k2)

  | pqprod _ _ k1 k2 => qprod (pre_qkind_to_qkind k1) (pre_qkind_to_qkind k2)

  | pqfut _ _ k1 => qfut (pre_qkind_to_qkind k1)
  end.


Fixpoint qkind_to_pre_qkind {w : ordinal} (k : qkind) {struct k}
  : level k << w -> pre_qkind w Ob
  :=
  match k
    as k
    return level k << w -> pre_qkind w Ob
  with
  | qone => (fun h => pqone _ _ h)

  | qtype v => (fun h => pqtype _ _ v h)

  | qarrow k1 k2 => 
      (fun h => 
         pqarrow _ _ 
           (qkind_to_pre_qkind k1 (max_ord_lub_strict_l _#3 h))
           (qkind_to_pre_qkind k2 (max_ord_lub_strict_r _#3 h)))

  | qtarrow v A k2 =>
      (fun h =>
         pqtarrow _ _ 
           v (max_ord_lub_strict_l _#3 h) A
           (qkind_to_pre_qkind k2 (max_ord_lub_strict_r _#3 h)))

  | qprod k1 k2 => 
      (fun h => 
         pqprod _ _ 
           (qkind_to_pre_qkind k1 (max_ord_lub_strict_l _#3 h))
           (qkind_to_pre_qkind k2 (max_ord_lub_strict_r _#3 h)))

  | qfut k1 =>
      (fun h =>
         pqfut _ _ (qkind_to_pre_qkind k1 h))
  end.


Lemma pre_qkind_level :
  forall w (k : pre_qkind w Ob),
    level (pre_qkind_to_qkind k) << w.
Proof.
intros w k.
induct k; cbn; auto using max_ord_lub_strict.
Qed.


Lemma qkind_to_pre_qkind_and_back :
  forall w (k : qkind) (h : level k << w),
    pre_qkind_to_qkind (qkind_to_pre_qkind k h) = k.
Proof.
intros w k.
induct k; intros; cbn; f_equal; auto.
Qed.


Lemma pre_qkind_to_qkind_and_back :
  forall w (k : pre_qkind w Ob) h,
    qkind_to_pre_qkind (pre_qkind_to_qkind k) h = k.
Proof.
intros w k.
induct k; try (intros; cbn; f_equal; auto using proof_irrelevance; done).
Qed.


Lemma pre_space_to_space :
  forall w (k : pre_qkind w Ob),
    pre_space w Ob k = space (pre_qkind_to_qkind k).
Proof.
intros w k.
induct k; intros; cbn; f_equal; auto.
Qed.


Lemma space_to_pre_space :
  forall w (k : qkind) (h : level k << w),
    space k = pre_space w Ob (qkind_to_pre_qkind k h).
Proof.
intros w k h.
symmetry.
etransitivity.
  {
  exact (pre_space_to_space w (qkind_to_pre_qkind k h)).
  }
f_equal.
apply qkind_to_pre_qkind_and_back.
Qed.


Definition objout {w : ordinal} (c : obj w) : xobj w
  :=
  match transport (obj_unroll w) (fun T => T) c with
  | Some c' =>
      objsome
        (expair
           (pre_qkind_to_qkind (pi1 c'))
           (transport (pre_space_to_space w (pi1 c')) car (pi2 c')))
        (pre_qkind_level w (pi1 c'))

  | None => objnone
  end.


Definition objin {w : ordinal} (c : xobj w) : obj w
  :=
  transport (eqsymm (obj_unroll w)) (fun T => T)
    (match c with
     | objsome Q h =>
         Some
           (expair (qkind_to_pre_qkind (pi1 Q) h)
              (transport (space_to_pre_space w (pi1 Q) h) car (pi2 Q)))

     | objnone => None
     end).


Lemma objout_objin :
  forall w (c : xobj w),
    objout (objin c) = c.
Proof.
intros w c.
unfold objout, objin.
rewrite -> transport_compose.
set (X := eqtrans (eqsymm (obj_unroll w)) (obj_unroll w)).
clearbody X.
substrefl X.
destruct c as [(k, x) h |].
  {
  cbn.
  apply objsome_compat; auto.
  apply expair_compat_heq.
    {
    apply qkind_to_pre_qkind_and_back.
    }
  rewrite -> !transport_compose.
  apply heq_transport.
  }

  {
  cbn.
  reflexivity.
  }
Qed.


Lemma objin_objout :
  forall w (c : obj w),
    objin (objout c) = c.
Proof.
intros w c.
unfold objout, objin.
transitivity (transport (eq_refl (obj w)) (fun T => T) c); [| reflexivity].
rewrite -> (proof_irrelevance (obj w = obj w) (eq_refl (obj w)) (eqtrans (obj_unroll w) (eqsymm (obj_unroll w)))).
rewrite <- transport_compose.
f_equal.
set (d := transport (obj_unroll w) (fun T => T) c).
clearbody d.
clear c.
cbn in d.
destruct d as [d |].
  {
  cbn.
  destruct d as (k, x).
  cbn.
  f_equal.
  apply expair_compat_heq.
    {
    apply pre_qkind_to_qkind_and_back.
    }
  eapply heq_trans; [apply heq_transport |].
  apply heq_transport.
  }

  {
  reflexivity.
  }
Qed.


Global Opaque obj objin objout.


Lemma objin_inj :
  forall w, injective (@objin w).
Proof.
intros w x y Heq.
so (f_equal objout Heq) as H.
rewrite -> !objout_objin in H.
auto.
Qed.
