
Require Import Axioms.

Require Import Tactics.
Require Import Relation.
Require Import Sigma.
Require Import Syntax.
Require Import Hygiene.
Require Import Equivalence.
Require Import Ofe.


Section object.


Local Arguments operator {object}.
Local Arguments term {object}.
Local Arguments row {object}.


Variable object : Type.


(* 1-indexed *)
Definition uniform (R : nat -> relation (@term object)) : Prop :=
  (forall i m n, R i m n -> hygiene clo m /\ hygiene clo n)
  /\
  (forall i m m' n n',
     hygiene clo m'
     -> hygiene clo n'
     -> equiv m m'
     -> equiv n n' 
     -> R i m n
     -> R i m' n')
  /\
  (forall i m n p q,
     R i m n
     -> R i p n
     -> R i p q
     -> R i m q)
  /\
  (forall i m n, R (S i) m n -> R i m n).


Record urel : Type :=
mk_urel
  { rel : nat -> relation term;

    urel_uniform : uniform rel }.


Lemma urel_closed :
  forall R i m n, rel R i m n -> hygiene clo m /\ hygiene clo n.
Proof.
intro R.
exact (urel_uniform R andel).
Qed.


Lemma urel_closed_1 :
  forall R i m n, rel R i m n -> hygiene clo m.
Proof.
intros R i m n H.
exact (urel_closed _#4 H andel).
Qed.


Lemma urel_closed_2 :
  forall R i m n, rel R i m n -> hygiene clo n.
Proof.
intros R i m n H.
exact (urel_closed _#4 H ander).
Qed.


Lemma urel_equiv :
  forall R i m m' n n',
    hygiene clo m'
    -> hygiene clo n'
    -> equiv m m' 
    -> equiv n n'
    -> rel R i m n 
    -> rel R i m' n'.
Proof.
intro R.
exact (urel_uniform R anderl).
Qed.


Lemma urel_equiv_1 :
   forall R i m m' n,
     hygiene clo m'
     -> equiv m m'
     -> rel R i m n
     -> rel R i m' n.
Proof.
intros R i m m' n Hcl Hequiv Hrel.
eapply urel_equiv; eauto using equiv_refl, urel_closed_2.
Qed.


Lemma urel_equiv_2 :
   forall R i m n n',
     hygiene clo n'
     -> equiv n n'
     -> rel R i m n
     -> rel R i m n'.
Proof.
intros R i m n n' Hcl Hequiv Hrel.
eapply urel_equiv; eauto using equiv_refl, urel_closed_1.
Qed.


Lemma urel_zigzag :
  forall R i m n p q,
    rel R i m n
    -> rel R i p n
    -> rel R i p q
    -> rel R i m q.
Proof.
intro R.
exact (urel_uniform R anderrl).
Qed.


Lemma urel_downward :
  forall R i m n, rel R (S i) m n -> rel R i m n.
Proof.
intro R.
exact (urel_uniform R anderrr).
Qed.


Lemma urel_downward_leq :
  forall (R : urel) i j m n,
    i <= j
    -> rel R j m n
    -> rel R i m n.
Proof.
intros R i j m n Hleq Hmn.
revert Hmn.
induct Hleq.

(* eq *) -
auto.

(* S *) -
intros j Hleq IH Hmn.
apply IH; [].
apply urel_downward; auto.
Qed.


Definition urel_dist (i : nat) (R R' : urel) : Prop :=
  forall j, j < i -> rel R j = rel R' j.


Definition urel_limit (ch : nat -> urel) (Hconv : convergent urel_dist ch) : urel.
Proof.
set (trel := fun i m n => rel (ch (S i)) i m n).
apply (mk_urel trel); unfold trel; clear trel.
do2 3 split.
  {  
  intros; eapply urel_closed; eauto.
  }
  
  {
  intros; eapply urel_equiv; eauto.
  }

  {
  intros; eapply urel_zigzag; eauto.
  }

  {
  intros.
  rewrite -> (Hconv (S i)); [| omega].
  apply urel_downward; auto.
  }
Defined.


Lemma convergent_slice_rel :
  forall (ch : nat -> urel),
    convergent urel_dist ch
    -> forall i j, i < j -> rel (ch (S i)) i = rel (ch j) i.
Proof.
intros ch Hconv i j Hleq.
unfold convergent in Hconv.
induct Hleq.

(* refl *) 
{
reflexivity.
}

(* S *)
{
intros j Hleq IH.
rewrite -> IH; [].
apply (Hconv j); [].
omega.
}
Qed.


Lemma urel_complete_dist :
  forall ch i (p : convergent urel_dist ch),
    urel_dist i (urel_limit ch p) (ch i).
Proof.
intros ch i p.
intros j Hlt.
rewrite <- convergent_slice_rel; auto.
Qed.


Lemma empty_uniform : uniform (fun _ _ _ => False).
Proof.
do2 3 split; intros; omega.
Qed.


Definition empty_urel : urel
  :=
  mk_urel _ empty_uniform.


Lemma urel_extensionality :
  forall R R',
    rel R = rel R'
    -> R = R'.
Proof.
intros R R' Heq.
destruct R as [r H].
destruct R' as [r' H'].
simpl in Heq.
subst r'.
f_equal; apply proof_irrelevance.
Qed.


Definition urel_ofe : ofe.
Proof.
apply (mk_ofe urel urel_dist).
  {
  intro i.
  do2 2 split.
    {
    intros R j _; auto.
    }

    {
    intros R1 R2 R3 H12 H23.
    intros j Hlt.
    so (H12 j Hlt).
    so (H23 j Hlt).
    etransitivity; eauto.
    }

    {
    intros R R' H.
    intros j Hlt.
    symmetry; apply H; auto.
    }
  }

  {
  intros R R' Hsim.
  apply urel_extensionality; [].
  apply functional_extensionality; [].
  intro i.
  apply (Hsim (S i)); omega.
  }

  {
  intros i R R' H.
  intros j Hlt.
  apply H; omega.
  }

  {
  intros R R'.
  intros j Hlt.
  omega.
  }
Defined.


Definition urel_complete : complete urel_ofe.
Proof.
apply (mk_complete urel_ofe urel_limit empty_urel).
intros ch n p.
apply urel_complete_dist.
Defined.


Lemma rel_from_dist :
  forall (A B : car urel_ofe) i m n,
    dist (S i) A B
    -> rel A i m n
    -> rel B i m n.
Proof.
intros A B i m n Hdist Hmn.
rewrite <- (Hdist i); auto.
Qed.


End object.


Arguments mk_urel {object}.
Arguments rel {object}.
Arguments urel_dist {object}.
Arguments urel_limit {object}.
Arguments empty_urel {object}.
Arguments urel_complete {object}.
