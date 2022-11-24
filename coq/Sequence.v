
Require Import Coq.Lists.List.
Require Import Tactics.


Inductive index {T:Type} : nat -> list T -> T -> Prop :=
| index_0 {x l}
    : index 0 (x :: l) x
| index_S {n x l y}
    : index n l y
      -> index (S n) (x :: l) y.


Inductive truncate {T:Type} : nat -> list T -> list T -> Prop :=
| truncate_0 {l}
    : truncate 0 l l

| truncate_S {i x l l'}
    : truncate i l l'
      -> truncate (S i) (x :: l) l'.


Lemma index_fun :
  forall (T:Type) i (l:list T) x x',
    index i l x
    -> index i l x'
    -> x = x'.
Proof.
intros T i l x x' H Hindex.
revert Hindex.
induct H.

(* 0 *)
{
intros x l Hindex.
invert Hindex; auto.
}

(* S *)
{
intros n x l y _ IH Hindex.
apply IH.
invert Hindex; auto.
}
Qed.


Lemma index_length :
  forall (T:Type) (l : list T) i x,
    index i l x
    -> i < length l.
Proof.
intros T l i x H.
induct H.
- intros; simpl; omega.

- intros; simpl; omega.
Qed.


Lemma index_truncate :
  forall (T:Type) i l (x:T),
    index i l x
    -> exists l', truncate i l (x :: l').
Proof.
intros T i.
induct i.

(* 0 *)
{
intros l x Hindex.
invert Hindex; [].
intros l' <-.
exists l'.
apply truncate_0.
}

(* S *)
{
intros i IH l x Hindex.
invert Hindex; [].
intros x' l' Hindex' <-.
so (IH l' x Hindex') as (l'' & Htrunc).
exists l''.
apply truncate_S; auto.
}
Qed.


Lemma truncate_index :
  forall (T:Type) i l (x:T) l',
    truncate i l (x :: l')
    -> index i l x.
Proof.
intros T i.
induct i.

(* 0 *)
{
intros l x l' H.
invert H; [].
intros ->.
apply index_0; auto.
}

(* S *)
{
intros i IH l x l' H.
invert H; [].
intros x' l'' H' <-.
apply index_S; [].
eapply IH; eauto.
}
Qed.


Lemma truncate_sum :
  forall (T : Type) i j (l l' l'' : list T),
    truncate i l l'
    -> truncate j l' l''
    -> truncate (i + j) l l''.
Proof.
intros T i j l l' l'' H Htrunc.
revert Htrunc.
induct H.

(* 0 *)
{
intros l Htrunc.
exact Htrunc.
}

(* S *)
{
intros i x l l' _ IH Htrunc.
simpl.
apply truncate_S; auto.
}
Qed.


Lemma index_map :
  forall (T U : Type) (f : T -> U) i l x,
    index i l x
    -> index i (map f l) (f x).
Proof.
intros T U f i l x H.
induct H.

(* 0 *)
{
intros x l.
apply index_0.
}

(* S *)
{
intros i x l l' _ IH.
simpl.
apply index_S; auto.
}
Qed.


Lemma truncate_map :
  forall (T U : Type) (f : T -> U) i l l',
    truncate i l l'
    -> truncate i (map f l) (map f l').
Proof.
intros T U f i l l' H.
induct H.

(* 0 *)
{
intros l.
apply truncate_0.
}

(* S *)
{
intros i x l l' _ IH.
simpl.
apply truncate_S; auto.
}
Qed.


Lemma index_app_lt :
  forall (T:Type) (l1 l2:list T) i x,
    i < length l1
    -> index i (l1 ++ l2) x
    -> index i l1 x.
Proof.
intros T l1 l2 i x Hlt Hindex.
revert l1 Hlt Hindex.
induct i.

(* 0 *)
{
intros.
destruct l1.
  {
  simpl in Hlt; exfalso; omega.
  }

  {
  simpl in Hindex.
  invert Hindex; intros.
  subst t.
  apply index_0; done.
  }
}

(* S *)
{
intros n IH l1 Hlt Hindex.
destruct l1.
  {
  simpl in Hlt; exfalso; omega.
  }

  {
  simpl in Hindex.
  invert Hindex; intros.
  apply index_S.
  apply IH; auto.
  simpl in Hlt; omega.
  }
}
Qed.


Lemma index_app_ge :
  forall (T:Type) (l1 l2:list T) i x,
    i >= length l1
    -> index i (l1 ++ l2) x
    -> index (i - length l1) l2 x.
Proof.
intros T l1 l2 i x Hge Hindex.
revert i Hge Hindex.
induct l1.

(* nil *)
{
intros.
simpl in Hindex.
simpl.
replace (i-0) with i by omega.
assumption.
}

(* cons *)
{
intros a l1 IH i Hge Hindex.
simpl.
replace (i - S (length l1)) with (i - 1 - length l1) by omega.
simpl in Hge.
apply IH.
  { omega. }

  {
  simpl in Hindex.
  invert Hindex; intros.
    { exfalso; omega. }
    
    {
    rewrite <- Heq.
    replace (S n - 1) with n by omega.
    assumption.
    }
  }
}
Qed.


Lemma index_app_left :
  forall (T:Type) (l1 l2:list T) i x,
    index i l1 x
    -> index i (l1 ++ l2) x.
Proof.
intros T l1 l2 i x Hindex.
induct Hindex; intros; cbn; eauto using index_0, index_S.
Qed.


Lemma index_app_right :
  forall (T:Type) (l1 l2:list T) i x,
    index i l2 x
    -> index (i + length l1) (l1 ++ l2) x.
Proof.
intros T l1 l2 i x Hindex.
induct  l1.

(* nil *)
{
simpl.
replace (i+0) with i by omega.
assumption.
}

(* cons *)
{
intros a l1 IH.
simpl.
replace (i + S (length l1)) with (S (i + length l1)) by omega.
apply index_S.
assumption.
}
Qed.


Lemma index_content :
  forall T i l x,
    inhabited (@index T i l x)
    -> index i l x.
Proof.
intros T i l x Hi.
revert l Hi.
induct i.

(* 0 *)
{
intros l Hi.
destruct l as [| y l].
- exfalso.
  destruct Hi as [Hindex].
  invert Hindex; done.

- assert (x = y).
    {
    destruct Hi as [Hindex].
    invert Hindex; auto.
    }
  subst y.
  apply index_0.
}

(* S *)
{
intros i IH l Hi.
destruct l as [| y l].
- exfalso.
  destruct Hi as [Hindex].
  invert Hindex; done.

- apply index_S; [].
  apply IH; [].
  destruct Hi as [Hindex].
  apply inhabits; [].
  invert Hindex; auto.
}
Qed.


Lemma Forall2_index :
  forall (A B : Type) (P : A -> B -> Prop) i l1 l2 x,
    Forall2 P l1 l2
    -> index i l1 x
    -> exists y,
         index i l2 y
         /\ P x y.
Proof.
intros A B P i l1 l2 x Hls Hindex.
revert l2 Hls.
induct Hindex.

(* 0 *)
{
intros x l1 ll Hls.
destruct ll as [| y l2].
  {
  exfalso.
  invert Hls.
  }
exists y.
split.
- apply index_0.

- invert Hls; auto.
}

(* S *)
{
intros n z l1 x _ IH ll Hls.
destruct ll as [| z' l2].
  {
  exfalso.
  invert Hls.
  }
assert (Forall2 P l1 l2) as Hls'.
  {
  invert Hls; auto.
  }
so (IH _ Hls') as (y & Hindex & Hxy).
exists y.
split; auto; [].
apply index_S; auto.
}
Qed.


Lemma map_Forall2 :
  forall (A A' B B' : Type) (P : A -> B -> Prop) (P' : A' -> B' -> Prop)
    (f : A -> A') (g : B -> B') (l1 : list A) (l2 : list B),
      (forall x y, P x y -> P' (f x) (g y))
      -> Forall2 P l1 l2
      -> Forall2 P' (map f l1) (map g l2).
Proof.
intros A A' B B' P P' f g l1 l2 Hmap Hall.
induct Hall;
intros; simpl; eauto using Forall2.
Qed.


Lemma index_skipn :
  forall (A : Type) (l : list A) i j x,
    index (i + j) l x
    -> index j (skipn i l) x.
Proof.
intros A l i j x Hindex.
revert l Hindex.
induct i.

(* 0 *)
{
intros l Hindex.
cbn.
auto.
}

(* S *)
{
intros i IH ll Hindex.
cbn in Hindex.
invert Hindex.
intros y l Hindex' <-.
cbn.
apply IH; auto.
}
Qed.


Lemma map_inj_Forall :
  forall A B (f : A -> B) (l m : list A),
    Forall (fun x => forall y, f x = f y -> x = y) l
    -> map f l = map f m
    -> l = m.
Proof.
intros A B f l m H Heq.
revert m Heq.
induct H.

(* nil *)
{
intros x Heq.
destruct x; auto.
discriminate Heq.
}

(* cons *)
{
intros x l Hinj _ IH mm Heq.
destruct mm as [| y m]; [discriminate Heq |].
cbn in Heq.
injection Heq.
intros Heq2 Heq1.
f_equal; auto.
}
Qed.


Lemma map_inj :
  forall A B (f : A -> B) (l m : list A),
    (forall x y, f x = f y -> x = y)
    -> map f l = map f m
    -> l = m.
Proof.
intros A B f l m Hf Heq.
eapply map_inj_Forall; eauto.
apply Forall_forall.
intros x _ y H.
apply Hf; auto.
Qed.


Hint Rewrite <- app_assoc : canonlist.
Hint Rewrite <- app_comm_cons : canonlist.
Hint Rewrite app_nil_l : canonlist.
