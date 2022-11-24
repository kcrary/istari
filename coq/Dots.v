
Require Import Tactics.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.

Require Import Axioms.



Section object.

Variable obj : Type.


Fixpoint dots (i : nat) (n : nat) (s : sub) : @sub obj :=
  match n with
  | 0 => s
  | S n' =>
      dots i n' (dot (var (i + n')) s)
  end.


Fixpoint unlift i : @sub obj :=
  match i with
  | 0 => id
  | S i' => dot arb (unlift i')
  end.


Fixpoint dotsgen (f : nat -> term obj) (n : nat) (s : sub) : sub :=
  match n with
  | 0 => s
  | S n' =>
      dotsgen f n' (dot (f n') s)
  end.


Lemma dotsgen_succ :
  forall f j s,
    dotsgen f (S j) s = dot (f 0) (dotsgen (fun i => f (S i)) j s).
Proof.
intros f j.
revert f.
induct j.

(* 0 *)
{
intros f s.
cbn.
auto.
}

(* S *)
{
intros j IH f s.
cbn.
rewrite <- IH.
cbn.
reflexivity.
}
Qed.


Lemma dots_dotsgen :
  forall i n s,
    dots i n s = dotsgen (fun j => var (i+j)) n s.
Proof.
intros i n.
revert i.
induct n.

(* 0 *)
{
intros i s.
cbn.
auto.
}

(* S *)
{
intros n IH i s.
cbn.
apply IH.
}
Qed.


Lemma unlift_dotsgen :
  forall k,
    unlift k = dotsgen (fun _ => arb) k id.
Proof.
intros k.
induct k.

(* 0 *)
{
cbn.
reflexivity.
}

(* S *)
{
intros k IH.
cbn [unlift].
rewrite -> dotsgen_succ.
f_equal.
apply IH.
}
Qed.



(* Dotsgen lemmas *)

Lemma split_dotsgen :
  forall f j k s,
    dotsgen f (j + k) s = dotsgen f j (dotsgen (fun i => f (j+i)) k s).
Proof.
intros f j k s.
revert f.
induct j.

(* 0 *)
{
intro f.
cbn.
auto.
}

(* S *)
{
intros j IH f.
cbn [Nat.add].
rewrite -> !dotsgen_succ.
f_equal.
apply IH.
}
Qed.


Lemma dotsgen_equal :
  forall f f' j j' s s',
    j = j'
    -> (forall i, i < j -> f i = f' i)
    -> s = s'
    -> dotsgen f j s = dotsgen f' j' s'.
Proof.
intros f f' j j' s s' Heqj Heq Heqs.
subst j' s'.
revert f f' Heq.
induct j.

(* 0 *)
{
intros f f' _.
reflexivity.
}

(* S *)
{
intros j IH f f' Heq.
rewrite -> !dotsgen_succ.
f_equal.
  {
  apply Heq.
  omega.
  }

  {
  apply IH.
  intros i Hi.
  apply Heq.
  omega.
  }
}
Qed.


Lemma dotsgen_eqsub :
  forall f f' j j' s s',
    j = j'
    -> (forall i, i < j -> f i = f' i)
    -> eqsub s s'
    -> eqsub (dotsgen f j s) (dotsgen f' j' s').
Proof.
intros f f' j j' s s' Heqj Heq Heqs.
subst j'.
revert f f' Heq.
induct j.

(* 0 *)
{
intros f f' _.
cbn.
auto.
}

(* S *)
{
intros j IH f f' Heq.
rewrite -> !dotsgen_succ.
rewrite -> Heq; [| omega].
apply eqsub_dotv.
apply IH.
intros i Hi.
apply Heq.
omega.
}
Qed.
  

Lemma compose_sh_dotsgen_le :
  forall j f k s,
    j <= k
    -> compose (sh j) (dotsgen f k s) = dotsgen (fun i => f (j+i)) (k-j) s.
Proof.
intros j f k s Hjk.
revert f k Hjk.
induct j.

(* 0 *)
{
intros f k _.
rewrite -> compose_id_left.
f_equal.
omega.
}

(* S *)
{
intros j IH f k Hjk.
destruct k as [| k]; [omega |].
rewrite -> dotsgen_succ.
simpsub.
rewrite -> IH; [| omega].
auto.
}
Qed.


Lemma compose_sh_dotsgen_ge :
  forall j f k s,
    j >= k
    -> compose (sh j) (dotsgen f k s) = compose (sh (j-k)) s.
Proof.
intros j f k s Hjk.
revert j f Hjk.
induct k.

(* 0 *)
{
intros j f _.
cbn [dotsgen].
do 2 f_equal.
omega.
}

(* S *)
{
intros k IH j f Hjk.
rewrite -> dotsgen_succ.
destruct j as [| j]; [omega |].
simpsub.
rewrite -> IH; [| omega].
auto.
}
Qed.


Lemma compose_dotsgen :
  forall f j s s',
    compose (dotsgen f j s) s' = dotsgen (fun i => subst s' (f i)) j (compose s s').
Proof.
intros f j s s'.
revert f.
induct j.

(* 0 *)
{
intros f.
cbn.
reflexivity.
}

(* S *)
{
intros j IH f.
rewrite -> !dotsgen_succ.
simpsub.
f_equal.
apply IH.
}
Qed.


Lemma project_dotsgen_lt :
  forall i f j s,
    i < j
    -> project (dotsgen f j s) i = f i.
Proof.
intros i f j s Hij.
revert f j Hij.
induct i.

(* 0 *)
{
intros f j Hij.
destruct j as [| j]; [omega |].
rewrite -> dotsgen_succ.
simpsub.
reflexivity.
}

(* S *)
{
intros i IH f j Hij.
destruct j as [| j]; [omega |].
rewrite -> dotsgen_succ.
simpsub.
apply IH.
omega.
}
Qed.


Lemma project_dotsgen_ge :
  forall i f j s,
    i >= j
    -> project (dotsgen f j s) i = project s (i-j).
Proof.
intros i f j s Hij.
revert f i Hij.
induct j.

(* 0 *)
{
intros f i _.
cbn.
f_equal.
omega.
}

(* S *)
{
intros j IH f i Hij.
destruct i as [| i]; [omega |].
rewrite -> dotsgen_succ.
simpsub.
apply IH.
omega.
}
Qed.



(* Dots corollaries *)

(* eaiser to prove directly *)
Lemma dots_succ :
  forall i j s,
    dots i (S j) s = dot (var i) (dots (S i) j s).
Proof.
intros i j.
revert i.
induct j.

(* 0 *)
{
intros i s.
cbn.
f_equal.
f_equal.
omega.
}

(* S *)
{
intros j IH i s.
cbn.
rewrite <- IH.
cbn.
repeat f_equal.
omega.
}
Qed.


Lemma project_dots_lt :
  forall i j k s,
    i < k
    -> project (dots j k s) i = var (i+j).
Proof.
intros i j k s Hik.
rewrite -> dots_dotsgen.
rewrite -> project_dotsgen_lt; auto.
f_equal.
omega.
Qed.


Lemma project_dots_ge :
  forall i j k s,
    i >= k
    -> project (dots j k s) i = project s (i-k).
Proof.
intros i j k s Hik.
rewrite -> dots_dotsgen.
rewrite -> project_dotsgen_ge; auto.
Qed.


Lemma compose_dots_sh :
  forall i j s k,
    compose (dots i j s) (sh k) = dots (i + k) j (compose s (sh k)).
Proof.
intros i j s k.
rewrite -> !dots_dotsgen.
rewrite -> compose_dotsgen.
f_equal.
fextensionality 1.
intro x.
simpsub.
f_equal.
omega.
Qed.


Lemma compose_dots_sh_sh :
  forall i j l k,
    compose (dots i j (sh l)) (sh k) = dots (k + i) j (sh (k + l)).
Proof.
intros i j l k.
rewrite -> compose_dots_sh.
rewrite -> compose_sh_sh.
f_equal; [omega |].
f_equal.
omega.
Qed.


Lemma compose_sh_dots_le :
  forall i j k s,
    i <= k
    -> compose (sh i) (dots j k s) = dots (i+j) (k-i) s.
Proof.
intros i j k s Hik.
rewrite -> !dots_dotsgen.
rewrite -> compose_sh_dotsgen_le; auto.
f_equal.
fextensionality 1.
intro x.
f_equal.
omega.
Qed.


Lemma compose_sh_dots_eq :
  forall j k s,
    compose (sh k) (dots j k s) = s.
Proof.
intros j k s.
rewrite -> compose_sh_dots_le; auto.
rewrite -> Nat.sub_diag.
reflexivity.
Qed.



Lemma compose_sh_dots_ge :
  forall i j k s,
    i >= k
    -> compose (sh i) (dots j k s) = compose (sh (i - k)) s.
Proof.
intros i j k s Hik.
replace i with (i - k + k) at 1 by omega.
rewrite <- compose_sh_sh.
rewrite -> compose_assoc.
rewrite -> compose_sh_dots_eq.
reflexivity.
Qed.


Lemma split_dots :
  forall i j k s,
    dots i (j + k) s = dots i j (dots (i+j) k s).
Proof.
intros i j k s.
rewrite -> !dots_dotsgen.
rewrite -> split_dotsgen.
do 2 f_equal.
fextensionality 1.
intro x.
f_equal.
omega.
Qed.


Lemma compose_dots_le :
  forall i j k l s s',
    i + j <= l
    -> compose (dots i j s) (dots k l s') = dots (i+k) j (compose s (dots k l s')).
Proof.
intros i j k l s s' Hle.
rewrite -> !dots_dotsgen.
rewrite -> compose_dotsgen.
apply dotsgen_equal; auto.
intros x Hx.
simpsub.
rewrite -> project_dotsgen_lt; [| omega].
f_equal.
omega.
Qed.


Lemma compose_dots_0_eq :
  forall j k s s',
    compose (dots 0 k s) (dots j k s') = dots j k (compose s (dots j k s')).
Proof.
intros j k s s'.
apply compose_dots_le.
auto.
Qed.


Lemma compose_dots_ge :
  forall i j k l s m,
    i >= l
    -> compose (dots i j s) (dots k l (sh m)) = dots (i-l+m) j (compose s (dots k l (sh m))).
Proof.
intros i j k l s m H.
rewrite -> !dots_dotsgen.
rewrite -> compose_dotsgen.
apply dotsgen_equal; auto.
intros x Hx.
simpsub.
rewrite -> project_dotsgen_ge; [| omega].
simpsub.
f_equal.
omega.
Qed.


Lemma compose_dots_stable :
  forall j k s s',
    (forall i, j <= i -> project s' i = var i)
    -> compose (dots j k s) s' = dots j k (compose s s').
Proof.
intros j k s s' Hstable.
rewrite -> !dots_dotsgen.
rewrite -> compose_dotsgen.
apply dotsgen_equal; auto.
intros i Hi.
simpsub.
apply Hstable.
omega.
Qed.



(* Under corollaries *)

Lemma under_dots :
  forall i s,
    under i s = dots 0 i (compose s (sh i)).
Proof.
intros i.
induct i.

(* 0 *)
{
intro s.
cbn.
rewrite -> compose_id_right.
auto.
}

(* S *)
{
intros i IH s.
rewrite -> under_succ.
unfold varx.
rewrite -> dots_succ.
f_equal.
rewrite -> IH.
rewrite -> compose_dots_sh.
simpsub.
repeat f_equal.
omega.
}
Qed.


Lemma under_dotsgen :
  forall i s,
    under i s = dotsgen var i (compose s (sh i)).
Proof.
intros i s.
rewrite -> under_dots.
apply dots_dotsgen.
Qed.


Lemma eqsub_dots_id :
  forall k,
    eqsub (dots 0 k (sh k)) id.
Proof.
intros k.
eapply eqsub_trans.
2:{
  apply (eqsub_under_id _ k).
  }
rewrite -> under_dots.
simpsub.
reflexivity.
Qed.


Lemma subst1_dots :
  forall i s m,
    compose (dots 1 i s) (dot m id) = dots 0 i (compose s (dot m id)).
Proof.
intros i s m.
rewrite -> !dots_dotsgen.
rewrite -> compose_dotsgen.
apply dotsgen_equal; auto.
intros x _.
simpsub.
auto.
Qed.


Lemma subst1_dots_under :
  forall i j m n,
    subst1
      (subst (sh i) m)
      (subst (dots 1 i (dot (var 0) (sh (S (j + i))))) n)
    =
    subst (under i (dot m (sh j))) n.
Proof.
intros i j m n.
rewrite -> dots_dotsgen.
rewrite -> under_dotsgen.
simpsub.
f_equal.
rewrite -> compose_dotsgen.
simpsub.
apply dotsgen_equal; auto.
intros x _.
simpsub.
auto.
Qed.



(* Unlift corollaries *)

Lemma compose_sh_unlift_ge :
  forall i j,
    i >= j
    -> compose (sh i) (unlift j) = sh (i - j).
Proof.
intros i j H.
rewrite -> unlift_dotsgen.
rewrite -> compose_sh_dotsgen_ge; auto.
simpsub.
f_equal.
omega.
Qed.


Lemma compose_sh_unlift :
  forall k,
    compose (sh k) (unlift k) = id.
Proof.
intros k.
rewrite -> unlift_dotsgen.
rewrite -> compose_sh_dotsgen_ge; auto.
replace (k - k) with 0 by omega.
auto.
Qed.


Lemma compose_sh_unlift_x :
  forall i j s,
    i >= j
    -> compose (sh i) (compose (unlift j) s) = compose (sh (i - j)) s.
Proof.
intros i j s H.
rewrite <- compose_assoc.
rewrite -> compose_sh_unlift_ge; auto.
Qed.


Lemma project_unlift_lt :
  forall i j,
    i < j
    -> project (unlift j) i = arb.
Proof.
intros i j H.
rewrite -> unlift_dotsgen.
rewrite -> project_dotsgen_lt; auto.
Qed.


Lemma project_unlift_ge :
  forall i j,
    i >= j
    -> project (unlift j) i = var (i-j).
Proof.
intros i j H.
rewrite -> unlift_dotsgen.
rewrite -> project_dotsgen_ge; auto.
simpsub.
auto.
Qed.
 


(* Dots/Unlift corollaries *)

Lemma compose_dots_unlift_ge :
  forall i j s k,
    i >= k
    -> compose (dots i j s) (unlift k) = dots (i-k) j (compose s (unlift k)).
Proof.
intros i j s k Hik.
rewrite -> !dots_dotsgen.
rewrite -> compose_dotsgen.
apply dotsgen_equal; auto.
intros x Hx.
simpsub.
rewrite -> project_unlift_ge; [| omega].
f_equal.
omega.
Qed.


Lemma compose_dots_unlift_exact :
  forall j k,
    j <= k
    -> compose (dots 0 j (sh k)) (unlift j) = compose (unlift j) (sh (k-j)).
Proof.
intros j k Hjk.
rewrite -> dots_dotsgen.
rewrite -> unlift_dotsgen.
rewrite -> !compose_dotsgen.
apply dotsgen_equal; auto.
  {
  intros x Hx.
  cbn [Nat.add].
  simpsub.
  rewrite -> project_dotsgen_lt; auto.
  }

  {
  rewrite -> compose_sh_dotsgen_ge; auto.
  simpsub.
  f_equal.
  omega.
  }
Qed.


End object.


Arguments dots {obj} i n s.
Arguments unlift {obj} i.
Arguments dotsgen {obj} f n s.

