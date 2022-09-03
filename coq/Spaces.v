
Require Import Coq.Relations.Relation_Definitions.

Require Import Axioms.

Require Import Tactics.
Require Import Sigma.
Require Import Equality.
Require Import Ofe.



(* Dependent function spaces *)

Definition dist_pi {A : Type} {B : A -> ofe} n (f g : forall x, car (B x)) :=
  forall x, dist n (f x) (g x).


Definition pi_ofe (A : Type) (B : A -> ofe) : ofe.
Proof.
apply
  (mk_ofe
     (forall x, car (B x))
     (@dist_pi A B)).

(* eqrel *) -
intro n.
do2 2 split.
+ intros f x.
  apply dist_refl.

+ intros f g h Hfg Hgf x.
  eapply dist_trans; eauto.

+ intros f g H x.
  apply dist_symm; auto.

(* limeq *) -
intros f g Hsim.
fextensionality 1.
intro x.
apply dist_limeq; [].
intros n.
apply Hsim.

(* downward *) -
intros n f g Hdist.
intro x.
apply dist_downward; auto.

(* zero *) -
intros f g x.
apply dist_zero.
Defined.


Definition limit_pi {A : Type} {B : A -> ofe} (C : forall x, complete (B x))
  ch (Hconv : convergent (@dist_pi A B) ch) (x : A) : car (B x) :=
  limit (C x) (fun i => ch i x) (fun i => Hconv i x).


Definition pi_complete (A : Type) (B : A -> ofe) (C : forall x, complete (B x)) : complete (pi_ofe A B).
Proof.
apply
  (mk_complete (pi_ofe A B)
     (@limit_pi A B C)
     (fun x => inhabitant (C x))).
intros ch i p.
intro x.
apply complete_dist.
Defined.


(* nearrow-pi *)
Definition neapi_car {T : Type} {A : ofe} {B : T -> ofe} (f : A -n> pi_ofe T B) (x : T) (y : car A) : car (B x)
  :=
  pi1 f y x.


Lemma neapi_nonexpansive :
  forall (T : Type) (A : ofe) (B : T -> ofe) (f : A -n> pi_ofe T B) (x : T),
    nonexpansive (neapi_car f x).
Proof.
intros T A B f x i y z Hyz.
unfold neapi_car.
exact (pi2 f i y z Hyz x).
Qed.


Definition neapi {T : Type} {A : ofe} {B : T -> ofe} (f : A -n> pi_ofe T B) (x : T) : A -n> B x
  :=
  expair (neapi_car f x) (neapi_nonexpansive T A B f x).


(* Half the distance *)

Definition half (A : ofe) : ofe.
Proof.
apply
  (mk_ofe
     (car A)
     (fun n x y => @dist A (pred n) x y)).

(* eqrel *) -
intros n.
do2 2 split.
+ intro x.
  apply dist_refl.

+ intros x y z Hxy Hyz.
  eapply dist_trans; eauto.

+ intros x y Hxy.
  apply dist_symm; auto.

(* limeq *) -
intros x y Hsim.
apply dist_limeq; [].
intros n.
so (Hsim (S n)) as H; [].
simpl in H.
exact H.

(* downward *) -
intros n x y H.
simpl in H.
apply dist_downward_pred; auto.

(* zero *) -
intros x y.
simpl.
apply dist_zero.
Defined.


Lemma half_convergent :
  forall A (ch : nat -> car A),
    convergent (fun n x y => @dist A (pred n) x y) ch
    -> convergent (@dist A) (fun i => ch (S i)).
Proof.
intros A ch Hconv.
intro i.
so (Hconv (S i)) as H.
simpl in H.
exact H.
Qed.


Definition half_limit (A : ofe) (C : complete A) (ch : nat -> car A)
  (Hconv : convergent (fun n x y => @dist A (pred n) x y) ch) : car A
  :=
  @limit A C (fun i => ch (S i)) (half_convergent A ch Hconv).


Definition half_complete (A : ofe) (C : complete A) : complete (half A).
Proof.
apply
  (mk_complete (half A)
     (half_limit A C)
     (inhabitant C)).
intros ch n Hconv.
destruct n as [| n'].
+ simpl.
  apply dist_zero.

+ simpl.
  so (limit_to_limits A C (fun i => ch (S i)) (half_convergent A ch Hconv)) as Hlimits.
  fold (half_limit A C ch Hconv) in Hlimits.
  so (Hlimits n') as H.
  simpl in H.
  apply dist_symm; auto.
Defined.


Lemma half_contracts :
  forall (A : ofe) (x y : car A) n,
    @dist A n x y
    -> @dist (half A) (S n) x y.
Proof.
intros A x y n H.
(* Suppressing the ofe is misleading here! *)
simpl.
exact H.
Qed.


Definition nearrow_half (A B : ofe) (f : A -n> B) : half A -n> half B.
Proof.
exists (pi1 f).
intros n x y Hdist.
apply (pi2 f); [].
exact Hdist.
Defined.


(* Downward-closed sets of nats.  Classically these are isomorphic to the natural numbers
   plus a top element, but limits are not computable in that structure.
*)

Definition nats : Type
  :=
  existsT (P : nat -> Prop),
    forall i, P (S i) -> P i.


Lemma nats_downward :
  forall (I : nats) i j,
    i <= j
    -> pi1 I j -> pi1 I i.
Proof.
intros I i j Hij.
induct Hij; auto.

(* S *)
{
intros j _ IH H.
apply IH.
apply (pi2 I); auto.
}
Qed.
  

Definition nats_dist (n : nat) (I J : nats) : Prop
  :=
  forall i, i < n -> (pi1 I i <-> pi1 J i).


Definition nats_ofe : ofe.
Proof.
apply (mk_ofe nats nats_dist).

(* eqrel *)
{
do2 2 split.
  {
  intros I i Hlt.
  split; auto.
  }

  {
  intros I1 I2 I3 H12 H23 i Hlt.
  split.
    {
    intro.
    apply H23; auto.
    apply H12; auto.
    }

    {
    intro.
    apply H12; auto.
    apply H23; auto.
    }
  }

  {
  intros I J H i Hlt.
  symmetry.
  apply H; auto.
  }
}

(* limeq *)
{
intros I J Hnear.
apply exT_extensionality_prop.
fextensionality 1.
intro i.
pextensionality.
  {
  intro Hi.
  so (Hnear (S i)) as H.
  apply H; auto.
  }

  {
  intro Hi.
  so (Hnear (S i)) as H.
  apply H; auto.
  }
}

(* downward *)
{
intros n I J H i Hlt.
apply H; omega.
}

(* zero *)
{
intros I J i Hlt.
omega.
}
Defined.


Definition nats_limit (ch : nat -> car nats_ofe) (Hconv : convergent dist ch) : car nats_ofe.
Proof.
refine (expair (fun i => pi1 (ch (S i)) i) _).
intros i H.
apply Hconv; [omega |].
apply (pi2 (ch (S (S i)))); auto.
Defined.


Definition nats_inh : nats.
Proof.
refine (expair (fun _ => False) _).
intros _ p.
exact p.
Defined.


Definition nats_complete : complete nats_ofe.
Proof.
refine (mk_complete nats_ofe nats_limit nats_inh _).
intros ch n Hconv.
cbn.
intros i Hlt.
cbn.
assert (S i <= n) as Hle by omega.
so (convergent_leq _ _ Hconv _ _ Hle) as Hdist.
apply Hdist.
omega.
Defined.


Definition nat_nats (n : nat) : nats.
Proof.
refine (expair (fun i => i < n) _).
intros i Hlt.
exact (lt_trans _#3 (Nat.lt_succ_diag_r i) Hlt).
Defined.


Definition le_nats (I J : nats) : Prop :=
  forall i, pi1 I i -> pi1 J i.


Lemma le_impl_le_nats :
  forall i j,
    i <= j
    -> le_nats (nat_nats i) (nat_nats j).
Proof.
intros i j Hij.
intros k Hk.
cbn in Hk |- *.
omega.
Qed.


(* Could be a corollary of nats_min_dist, but easier to to directly. *)
Lemma nat_nats_dist :
  forall i j k,
    min i j = min i k
    -> nats_dist i (nat_nats j) (nat_nats k).
Proof.
intros i j k Heq.
intros l Hli.
cbn.
split.
  {
  intro Hlj.
  so (Nat.min_glb_lt _#3 Hli Hlj) as H.
  rewrite -> Heq in H.
  rewrite -> Nat.min_glb_lt_iff in H.
  destruct H; auto.
  }

  {
  intro Hlk.
  so (Nat.min_glb_lt _#3 Hli Hlk) as H.
  rewrite <- Heq in H.
  rewrite -> Nat.min_glb_lt_iff in H.
  destruct H; auto.
  }
Qed.


Lemma le_nats_refl :
  forall I, le_nats I I.
Proof.
intros I.
intros i Hi.
auto.
Qed.


Lemma le_nats_trans :
  forall I J K, le_nats I J -> le_nats J K -> le_nats I K.
Proof.
intros I J K HIJ HJK.
intros i Hi.
apply HJK.
apply HIJ.
auto.
Qed.


Definition nats_min (I J : nats) : nats.
Proof.
refine (expair (fun i => pi1 I i /\ pi1 J i) _).
intros i (Hlt & Hlt').
split.
  {
  apply (pi2 I); auto.
  }

  {
  apply (pi2 J); auto.
  }
Defined.


Lemma nats_min_l :
  forall I J,
    le_nats I J
    -> nats_min I J = I.
Proof.
intros I J Hle.
apply exT_extensionality_prop.
fextensionality 1.
intro i.
cbn.
pextensionality; auto.
intro H; destruct H; auto.
Qed.


Lemma nats_min_r :
  forall I J,
    le_nats J I
    -> nats_min I J = J.
Proof.
intros I J Hle.
apply exT_extensionality_prop.
fextensionality 1.
intro i.
cbn.
pextensionality; auto.
intro H; destruct H; auto.
Qed.


Lemma nats_min_assoc :
  forall I J K, nats_min I (nats_min J K) = nats_min (nats_min I J) K.
Proof.
intros I J K.
apply exT_extensionality_prop.
fextensionality 1.
intro i.
cbn.
pextensionality; intro H; destruct_all H; auto.
Qed.


Lemma nats_min_min :
  forall i j, nats_min (nat_nats i) (nat_nats j) = nat_nats (min i j).
Proof.
intros i j.
apply exT_extensionality_prop.
cbn.
fextensionality 1.
intro k.
pextensionality.
  {
  intros (Hki & Hkj).
  so (Nat.min_glb i j (S k)).
  omega.
  }

  {
  intro Hk.
  so (Nat.le_min_l i j).
  so (Nat.le_min_r i j).
  omega.
  }
Qed.


Lemma nats_min_dist :
  forall i J K,
    nats_min (nat_nats i) J = nats_min (nat_nats i) K
    -> nats_dist i J K.
Proof.
intros i J K Heq.
intros j Hji.
split.
  {
  intro Hj.
  assert (pi1 (nats_min (nat_nats i) J) j) as H.
    {
    cbn.
    auto.
    }
  rewrite -> Heq in H.
  destruct H; auto.
  }

  {
  intro Hj.
  assert (pi1 (nats_min (nat_nats i) K) j) as H.
    {
    cbn.
    auto.
    }
  rewrite <- Heq in H.
  destruct H; auto.
  }
Qed.


(* Dependent distance *)

Record dofe (A : ofe) (B : car A -> ofe) : Type :=
mk_dofe
  { dist_dep : forall (a a' : car A), nat -> car (B a) -> car (B a') -> Prop;

    dist_dep_eq_dist : forall (a : car A), dist_dep a a = dist ;

    dist_dep_symm :
      forall n (a a' : car A) (b : car (B a)) (b' : car (B a')),
        dist_dep a a' n b b'
        -> dist_dep a' a n b' b ;

    dist_dep_trans :
      forall n (a1 a2 a3 : car A) (b1 : car (B a1)) (b2 : car (B a2)) (b3 : car (B a3)),
        dist_dep a1 a2 n b1 b2
        -> dist_dep a2 a3 n b2 b3
        -> dist_dep a1 a3 n b1 b3 ;

    dist_dep_downward : 
      forall n (a a' : car A) (b : car (B a)) (b' : car (B a')),
        dist_dep a a' (S n) b b'
        -> dist_dep a a' n b b' ;

    dist_dep_zero :
      forall (a a' : car A) (b : car (B a)) (b' : car (B a')),
        dist_dep a a' 0 b b' }.


Arguments dist_dep {A} {B} d a a' n b b'.


Lemma dist_dep_downward_leq :
  forall (A : ofe) (B : car A -> ofe) (d : dofe A B) 
    m n (a a' : car A) (b : car (B a)) (b' : car (B a')),
      m <= n
      -> dist_dep d a a' n b b' 
      -> dist_dep d a a' m b b'.
Proof.
intros A B d m n a a' b b' Hle.
induct Hle; auto.
(* S *)
intros n Hle IH Hdist.
apply IH.
apply (dist_dep_downward _ _ d); auto.
Qed.


Lemma dist_dep_refl :
  forall A (B : car A -> ofe) (d : dofe A B) n (a : car A) (b : car (B a)),
    @dist_dep _ _ d a a n b b.
Proof.
intros A B d n a b.
rewrite -> dist_dep_eq_dist.
apply dist_refl.
Qed.


Lemma dist_dep_refl' :
  forall A (B : car A -> ofe) (d : dofe A B) n (a : car A) (b b' : car (B a)),
    b = b'
    -> @dist_dep _ _ d a a n b b'.
Proof.
intros A B d n a b b' H.
subst b'.
apply dist_dep_refl.
Qed.


(* Dependent product spaces *)

Definition dist_sigma {A : ofe} {B : car A -> ofe} (d : dofe A B) n
  (p q : existsT (a : car A), car (B a))
  : Prop
  :=
  dist n (pi1 p) (pi1 q)
  /\ dist_dep d (pi1 p) (pi1 q) n (pi2 p) (pi2 q).


Definition sigma_ofe (A : ofe) (B : car A -> ofe) (d : dofe A B) : ofe.
Proof.
apply (mk_ofe (existsT (a : car A), car (B a)) (dist_sigma d)).

(* eqrel *)
{
intro n.
do2 2 split.
  {
  intros (a, b).
  split.
    { apply dist_refl. }

    { apply dist_dep_refl. }
  }

  {
  intros (a1, b1) (a2, b2) (a3, b3) (H12a, H12b) (H23a, H23b).
  split.
    { eapply dist_trans; eauto. }

    { eapply dist_dep_trans; eauto. }
  }

  {
  intros (a, b) (a', b') (Ha, Hb).
  split.
    { apply dist_symm; auto. }

    { apply dist_dep_symm; auto. }
  }
}

(* limeq *)
{
intros (a, b) (a', b') Hall.
assert (a = a').
  {
  apply dist_limeq.
  intro i.
  apply Hall.
  }
subst a'.
f_equal.
apply dist_limeq.
intro i.
rewrite <- (dist_dep_eq_dist _ _ d).
apply Hall.  
}

(* downward *)
{
intros n (a, b) (a', b') (Ha, Hb).
split; auto using dist_downward, dist_dep_downward.
}

(* zero *)
{
intros (a, b) (a', b').
split; auto using dist_zero, dist_dep_zero.
}
Defined.


(* Dependent distance for functions with dependent domains *)


(* This could be made more general by making C dependent as well. *)

Definition nearrow_dist_dep {A : ofe} {B : car A -> ofe} {C : ofe} (d : dofe A B)
  (a a' : car A) n (f : nearrow (B a) C) (g : nearrow (B a') C)
  : Prop
  :=
  dist n a a'
  /\
  forall i (b : car (B a)) (b' : car (B a')),
    i <= n
    -> dist_dep d a a' i b b'
    -> dist i (pi1 f b) (pi1 g b').

(* Need the (dist n a a') business to find a neighbor for transivitity.
   Need i <= n business for downward closure.
*)


Definition neighborly {A : ofe} {B : car A -> ofe} (d : dofe A B) : Prop
  :=
  forall n (a a' : car A) (b : car (B a)),
    n > 0
    -> dist n a a'
    -> exists (b' : car (B a')),
         dist_dep d a a' n b b'.


Lemma nearrow_dofe :
  forall (A : ofe) (B : car A -> ofe) (C : ofe) (d : dofe A B),
    neighborly d
    -> dofe A (fun a => nearrow_ofe (B a) C).
Proof.
intros A B C d Hneighbor.
apply (mk_dofe A (fun a => nearrow_ofe (B a) C) (nearrow_dist_dep d)).

(* eq_dist *)
{
intro a.
fextensionality 3.
intros i f g.
pextensionality.
  {
  intro Hdist.
  intro x.
  apply Hdist; auto.
  apply dist_dep_refl.
  }

  {
  intro Hdist.
  split.
    { apply dist_refl. }
  intros j x y Hj Hxy.
  apply (dist_trans _ _ _ (pi1 f y)).
    {
    rewrite -> dist_dep_eq_dist in Hxy.
    apply (pi2 f); auto.
    }

    {
    eapply dist_downward_leq; eauto.
    }
  }
}

(* symm *)
{
intros i a a' f g H.
destruct H as (Ha, Hb).
split.
  { apply dist_symm; auto. }
intros j b b' Hj Hdist.
apply dist_symm.
apply Hb; auto.
apply dist_dep_symm; auto.
}

(* trans *)
{
intros i a1 a2 a3 f1 f2 f3 H12 H23.
destruct H12 as (Ha12, Hf12).
destruct H23 as (Ha23, Hf23).
split.
  { eapply dist_trans; eauto. }
intros j b1 b3 Hj Hb13.
destruct j as [| j].
  {
  apply dist_zero.
  }
so (Hneighbor (S j) a1 a2 b1 (Nat.lt_0_succ j) (dist_downward_leq _#5 Hj Ha12)) as (b2 & Hb12).
apply (dist_trans _ _ _ (pi1 f2 b2)).
  {
  apply Hf12; auto.
  }

  {
  apply Hf23; auto.
  apply (dist_dep_trans _#5 a1 _ _ b1); auto.
  apply dist_dep_symm; auto.
  }
}

(* downward *)
{
intros i a a' f g H.
destruct H as (Ha & Hfg).
split.
  { apply dist_downward; auto. }
intros j b b' Hj Hb.
apply Hfg; auto.
}

(* zero *)
{
intros a a' f g.
split.
  { apply dist_zero. }
intros j b b' Hj _.
assert (j = 0) by omega.
subst j.
apply dist_zero.
}
Defined.
