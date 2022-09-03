
Require Import Coq.Setoids.Setoid.

Require Import Tactics.
Require Import Syntax.


Section object.

Variable object : Type.


Definition termx := @term object.
Definition varx := @var object.


Inductive sub : Type :=
| dot : termx -> sub -> sub
| sh : nat -> sub.


Fixpoint trunc (i : nat) (s : sub) {struct i} : sub :=
  (match i with
   | 0 => s
   | S i' =>
       (match s with
        | sh n => sh (n + i)
        | dot _ s' => trunc i' s'
        end)
   end).


Definition project (s : sub) (i : nat) : termx :=
  (match trunc i s with
   | dot t _ => t
   | sh n => varx n
   end).


Definition shift (n : nat) (t : termx) : termx :=
  traverse object
    (fun i j =>
       if lt_dec j i then 
         varx j
       else 
         varx (n + j))
  0 t.


Definition subst (s : sub) (t : termx) : termx :=
  traverse object
    (fun i j =>
      if lt_dec j i then
        varx j
      else
        shift i (project s (j-i)))
  0 t.


Definition id : sub := sh 0.
Definition sh1 : sub := sh 1.
Definition subst1 (t : termx) : termx -> termx := @subst (dot t id).


(* Composition is written in diagrammatic order. *)
Fixpoint compose (s1 : sub) (s2 : sub) {struct s1} : sub :=
  (match s1 with
   | dot t s1' => dot (subst s2 t) (compose s1' s2)
   | sh n => trunc n s2
   end).


Fixpoint under (n : nat) (s : sub) {struct n} : sub :=
  (match n with
   | 0 => s
   | S n' =>
       dot (varx 0) (compose (under n' s) (sh 1))
   end).


Lemma traverse_resp :
  forall resolve resolve',
    (forall i j, resolve i j = resolve' i j)
    -> forall i t, traverse object resolve i t = traverse object resolve' i t.
Proof.
intros resolve resolve' Hres i t.
apply (traverse_parametric _ (fun i i' => i = i')); eauto; [].
intros; subst; apply Hres.
Qed.


Lemma traverse_delta :
  forall n resolve i t,
    traverse object resolve (i+n) t
    = traverse object (fun i' j => resolve (i'+n) j) i t.
Proof.
intros n resolve i t.
apply (traverse_parametric _ (fun i1 i2 => i1 = i2 + n)); auto; [].
intros; omega.
Qed.


Lemma traverse_compose_delta :
  forall n resolve resolve' i t,
    traverse object resolve (i+n) (traverse object resolve' i t)
    = traverse object
      (fun i' j => traverse object resolve (i'+n) (resolve' i' j))
      i t.
Proof.
intros n resolve resolve' i t.
rewrite -> traverse_delta; [].
etransitivity.
  apply traverse_compose; done.
apply traverse_resp; [].
clear i t.
intros i j.
rewrite -> traverse_delta; [].
reflexivity.
Qed.


Lemma trunc_sh :
  forall i n,
    trunc i (sh n) = sh (n+i).
Proof.
intros i n.
cases i; eauto; [].
simpl.
f_equal; omega.
Qed.


Lemma project_sh :
  forall n i,
    project (sh n) i = varx (n+i).
Proof.
intros n i.
unfold project.
rewrite -> trunc_sh; [].
reflexivity.
Qed.


Lemma trunc_id :
  forall i,
    trunc i id = sh i.
Proof.
intros i.
unfold id.
apply trunc_sh.
Qed.


Lemma shift_var :
  forall n i,
    shift n (varx i) = varx (n+i).
Proof.
intros n i.
unfold shift.
rewrite -> traverse_var; [].
forget (lt_dec i 0) as b.
destruct b; [omega |].
f_equal; omega.
Qed.


Lemma subst_sh_shift :
  forall n t,
    subst (sh n) t = shift n t.
Proof.
intros n t.
apply traverse_resp; [].
clear t.
intros i j.
forget (lt_dec j i) as b.
destruct b; eauto; [].
unfold project.
rewrite -> trunc_sh; [].
rewrite -> shift_var; [].
f_equal; [].
omega.
Qed.


Lemma shift_sum :
  forall m n t,
    shift m (shift n t) = shift (m+n) t.
Proof.
intros m n t.
unfold shift.
etransitivity.
  apply traverse_compose; done.
apply traverse_resp; [].
clear t.
intros i j.
forget (lt_dec j i) as b.
destruct b as [Hlt | Hnlt].
- rewrite -> traverse_var; [].
  forget (lt_dec j i) as b; destruct b as [| Hnlt]; eauto; destruct Hnlt; eauto; done.

- rewrite -> traverse_var; [].
  forget (lt_dec (n + j) i) as b.
  destruct b.
    omega.

    f_equal; omega.
Qed.


Lemma shift_0 :
  forall t,
    shift 0 t = t.
Proof.
intros t.
unfold shift.
apply traverse_id; [].
clear t.
intros i j.
forget (lt_dec j i) as b; destruct b; reflexivity.
Qed.


Lemma subst_id :
  forall t, subst id t = t.
Proof.
intros t.
unfold id.
rewrite -> subst_sh_shift; [].
apply shift_0; done.
Qed.


Lemma compose_id_left :
  forall s, compose id s = s.
Proof.
auto.
Qed.


Lemma compose_id_right :
  forall s, compose s id = s.
Proof.
intros s.
induct s.

(* dot *)
intros e s IH.
simpl.
f_equal; eauto using subst_id; done.

(* dotv *)
(* sh *)
intros n.
simpl.
apply trunc_id; done.
Qed.


Lemma compose_sh_dot :
  forall t s i, compose (sh (S i)) (dot t s) = compose (sh i) s.
Proof.
intros.
reflexivity.
Qed.


Lemma trunc_sum :
  forall m n s,
    trunc m (trunc n s) = trunc (m+n) s.
Proof.
intros m n s.
revert m s.
induct n.

(* 0 *)
intros m s.
simpl.
f_equal; omega.

(* S *)
intros n IH m s.
replace (m + S n) with (S (m + n)) by omega.
simpl.
destruct s as [t s' | i].
  apply IH; done.

  rewrite -> trunc_sh; [].
  f_equal; omega.
Qed.


Lemma project_trunc :
  forall i s j,
    project (trunc i s) j = project s (j+i).
Proof.
intros i s j.
unfold project.
rewrite -> trunc_sum; [].
reflexivity.
Qed.


Lemma trunc_compose :
  forall m s s',
    trunc m (compose s s') = compose (trunc m s) s'.
Proof.
intros m s s'.
revert m.
induct s.

(* dot *)
intros t s IH m.
destruct m as [| n].
  reflexivity.
simpl.
apply IH; done.

(* sh *)
intros n m.
revert s'.
#2 induct n.
  (* 0 *)
  intros s'.
  rewrite -> trunc_sh; [].
  simpl.
  reflexivity.

  (* S *)
  intros n IH s'.
  rewrite -> trunc_sh; [].
  replace (S n + m) with (S (m + n)) by omega.
  destruct s' as [t s'' | i].
  - simpl.
    apply trunc_sum; done.

  - simpl.
    rewrite -> trunc_sh; [].
    f_equal; omega.
Qed.


Lemma project_compose :
  forall s1 s2 i,
    project (compose s1 s2) i = subst s2 (project s1 i).
Proof.
intros s1 s2 i.
unfold project.
rewrite -> trunc_compose; [].
forget (trunc i s1) as s.
destruct s as [t s' | j].
- simpl.
  reflexivity.

- simpl.
  unfold subst.
  rewrite -> traverse_var; [].
  simpl.
  rewrite -> shift_0; [].
  replace (j - 0) with j by omega.
  reflexivity.
Qed.


Lemma compose_with_sh_sh :
  forall s m n,
    compose (compose s (sh m)) (sh n) = compose s (sh (m+n)).
Proof.
intros s m n.
induct s.

(* dot *)
intros t s IH.
simpl.
rewrite -> !subst_sh_shift; [].
rewrite -> shift_sum; [].
f_equal; auto; [].
f_equal; omega.

(* sh *)
intros i.
simpl.
rewrite -> !trunc_sh; [].
simpl.
rewrite -> trunc_sh; [].
f_equal; omega.
Qed.


Lemma trunc_under_leq :
  forall m n s,
    m <= n
    -> trunc m (under n s) = compose (under (n-m) s) (sh m).
Proof.
intro m.
induct m.

(* 0 *)
intros n s H.
simpl.
replace (n - 0) with n by omega.
rewrite -> compose_id_right; reflexivity.

(* S *)
intros m IH n s Hleq.
replace n with (S (n-1)) at 1 by omega.
simpl.
replace (n - S m) with (n - 1 - m) by omega.
rewrite -> trunc_compose; [].
rewrite -> IH; [| omega].
rewrite -> compose_with_sh_sh; [].
replace (m + 1) with (S m) by omega.
reflexivity.
Qed.


Lemma trunc_under_geq :
  forall m n s,
    m >= n
    -> trunc m (under n s) = trunc (m-n) (compose s (sh n)).
Proof.
intros m n s Hgeq.
replace (trunc m (under n s)) with (trunc (m-n) (trunc n (under n s))).
2:{
  rewrite -> trunc_sum; [].
  f_equal; omega.
  }
rewrite -> trunc_under_leq; [| omega].
replace (n - n) with 0 by omega.
simpl.
reflexivity.
Qed.


Lemma trunc_is_compose_sh :
  forall n s,
    trunc n s = compose (sh n) s.
Proof.
intros n s.
replace n with (0 + n) at 2 by omega.
rewrite <- (trunc_sh n 0).
rewrite <- trunc_compose.
rewrite -> compose_id_left.
reflexivity.
Qed.


Lemma compose_sh_under_leq :
  forall m n s,
    m <= n
    -> compose (sh m) (under n s) = compose (under (n - m) s) (sh m).
Proof.
intros m n s Hle.
rewrite <- trunc_is_compose_sh.
apply trunc_under_leq; auto.
Qed.


Lemma compose_sh_under_geq :
  forall m n s,
    m >= n
    -> compose (sh m) (under n s) = compose (sh (m - n)) (compose s (sh n)).
Proof.
intros m n s Hle.
rewrite <- !trunc_is_compose_sh.
apply trunc_under_geq; auto.
Qed.


Lemma compose_sh_under_eq :
  forall n s,
    compose (sh n) (under n s) = compose s (sh n).
Proof.
intros n s.
exploit (compose_sh_under_leq n n s) as H; [omega |].
replace (n - n) with 0 in H by omega.
exact H.
Qed.


Lemma project_under_lt :
  forall s i j,
    j < i
    -> project (under i s) j = varx j.
Proof.
intros s i j Hlt.
unfold project.
rewrite -> trunc_under_leq; [| omega].
replace (i - j) with (S (i - j - 1)) by omega.
simpl.
unfold subst.
rewrite -> traverse_var; [].
simpl.
unfold project.
simpl.
rewrite -> shift_var; auto.
Qed.


Lemma project_under_geq_shift :
  forall s i j,
    j >= i
    -> project (under i s) j = shift i (project s (j-i)).
Proof.
intros s i j Hgeq.
unfold project.
rewrite -> trunc_under_geq; [| omega].
rewrite -> trunc_compose; [].
forget (trunc (j - i) s) as ss.
clear s.
destruct ss as [t s' | k].
- simpl.
  apply subst_sh_shift; done.

- simpl.
  rewrite -> trunc_sh; [].
  rewrite -> shift_var; auto.
Qed.


Lemma project_under_geq :
  forall s i j,
    j >= i
    -> project (under i s) j = subst (sh i) (project s (j-i)).
Proof.
intros s i j H.
rewrite -> project_under_geq_shift; auto; [].
rewrite <- subst_sh_shift; [].
reflexivity.
Qed.


Lemma project_under_eq :
  forall s i,
    project (under i s) i = subst (sh i) (project s 0).
Proof.
intros s i.
rewrite -> project_under_geq; [| omega].
replace (i - i) with 0 by omega.
reflexivity.
Qed.


Lemma traverse_under :
  forall i s t,
    traverse object
      (fun i j =>
        if lt_dec j i then
          varx j
        else
          shift i (project s (j-i)))
    i t
    =
    subst (under i s) t.
Proof.
intros i s t.
apply (traverse_parametric object (fun i1 i2 => i1 = i + i2)); try (intros; omega); [].
intros ? j k ->.
forget (lt_dec k (i+j)) as b.
destruct b as [Hlt | Hnlt].
  forget (lt_dec k j) as b.
  destruct b as [Hlt' | Hnlt].
    reflexivity.

    rewrite -> project_under_lt; [| omega].
    rewrite -> shift_var; [].
    f_equal; omega.

  forget (lt_dec k j) as b.
  destruct b as [ | _]; [omega |].
  rewrite -> project_under_geq_shift; [| omega].
  rewrite -> shift_sum; [].
  f_equal; [omega |].
  f_equal; omega.
Qed.


Lemma compose_assoc_if :
  forall s1 s2 s3,
    (forall t, subst (compose s2 s3) t = subst s3 (subst s2 t))
    -> compose (compose s1 s2) s3 = compose s1 (compose s2 s3).
Proof.
intros s1 s2 s3 Hcond.
symmetry.
induct s1.

(* dot *)
intros t s1 IH.
simpl.
f_equal; auto; done.

(* sh *)
intros m.
simpl.
apply trunc_compose; done.
Qed.


Lemma subst_compose_sh_left :
  forall n s t,
    subst (compose (sh n) s) t = subst s (subst (sh n) t).
Proof.
intros n s t.
symmetry.
unfold subst.
etransitivity.
  apply traverse_compose; done.

  apply traverse_resp; [].
  clear t.
  intros i j.
  forget (lt_dec j i) as b.
  destruct b as [Hlt | Hnlt].
  - rewrite -> traverse_var; [].
    forget (lt_dec j i) as b; destruct b; eauto; omega.

  - simpl.
    rewrite -> project_sh; [].
    rewrite -> shift_var; [].
    replace (i + (n + (j - i))) with (n + j) by omega.
    forget (lt_dec (n + j) i) as b.
    destruct b as [|]; [omega |].
    rewrite -> project_trunc; [].
    rewrite -> traverse_var; [].
    set (X := lt_dec (n + j) i).
    destruct X as [|]; [omega |].
    f_equal; f_equal; omega.
Qed.


Lemma subst_compose_sh_right :
  forall s n t,
    subst (compose s (sh n)) t = subst (sh n) (subst s t).
Proof.
intros s n t.
symmetry.
unfold subst.
etransitivity.
  apply traverse_compose; done.

  apply traverse_resp; [].
  clear t.
  intros i j.
  forget (lt_dec j i) as b.
  destruct b as [Hlt | Hnlt].
    rewrite -> traverse_var; [].
    forget (lt_dec j i) as b; destruct b; eauto; omega.

    rewrite -> project_compose; [].
    forget (project s (j - i)) as t.
    clear s j Hnlt.
    rewrite -> subst_sh_shift; [].
    rewrite -> shift_sum; [].
    change (traverse object
              (fun i' j =>
                 if lt_dec j i' then varx j else shift i' (project (sh n) (j - i')))
              (0+i) (shift i t)
            = shift (i + n) t).
    unfold shift at 2.
    etransitivity.
      apply (traverse_compose_delta i _ _ 0 t); done.
    apply traverse_resp; [].
    clear t.
    intros i' j.
    forget (lt_dec j i') as b.
    destruct b as [Hlt | Hnlt].
      rewrite -> traverse_var; [].
      forget (lt_dec j (i' + i)) as b.
      destruct b; eauto; omega.

      rewrite -> traverse_var; [].
      forget (lt_dec (i+j) (i'+i)) as b.
      destruct b; try omega; [].
      rewrite -> project_sh; [].
      unfold shift; simpl.
      rewrite -> traverse_var; [].
      set (X := lt_dec (n + (i + j - (i' + i))) 0); destruct X as [|]; [omega |].
      f_equal; omega.
Qed.


Lemma compose_under :
  forall i s s',
    under i (compose s s') = compose (under i s) (under i s').
Proof.
intros i s s'.
induct i.

(* 0 *)
{
reflexivity.
}

(* S *)
{
intros i IH.
cbn.
f_equal.
rewrite -> IH; [].
#2 rewrite -> (compose_assoc_if _ (sh 1) _).
  {
  cbn.
  rewrite -> (compose_assoc_if _ _ (sh 1)); auto.
  intros; apply subst_compose_sh_right; done.
  }

  {
  intros; apply subst_compose_sh_left; done.
  }
}
Qed.


Lemma subst_compose :
  forall s s' t,
    subst (compose s s') t = subst s' (subst s t).
Proof.
intros s s' t.
symmetry.
unfold subst.
etransitivity.
  apply traverse_compose; done.

  apply traverse_resp; [].
  clear t.
  intros i j.
  forget (lt_dec j i) as b.
  destruct b as [Hlt | Hnlt].
    rewrite -> traverse_var; [].
    forget (lt_dec j i) as b; destruct b; eauto; omega.
    
    rewrite -> traverse_under; [].
    rewrite <- !project_under_geq_shift; try omega; [].
    rewrite <- project_compose; [].
    rewrite -> compose_under; [].
    reflexivity.
Qed.


Lemma compose_assoc :
  forall s1 s2 s3,
    compose (compose s1 s2) s3 = compose s1 (compose s2 s3).
Proof.
intros s1 s2 s3.
apply compose_assoc_if; [].
intros; apply subst_compose; done.
Qed.



(* Other simplification rules *)

Lemma subst_var :
  forall s i, subst s (varx i) = project s i.
Proof.
intros.
unfold subst.
rewrite -> traverse_var; [].
set (X := lt_dec i 0); destruct X as [|]; [omega |].
replace (i - 0) with i by omega.
rewrite -> shift_0; [].
reflexivity.
Qed.


Lemma compose_sh_sh :
  forall m n, compose (sh m) (sh n) = sh (m + n).
Proof.
intros m n.
so (compose_with_sh_sh id m n) as H.
rewrite -> !compose_id_left in H.
exact H.
Qed.


Lemma under_zero :
  forall s, under 0 s = s.
Proof.
intro s.
reflexivity.
Qed.


Lemma subst_under_id :
  forall i t,
    subst (under i id) t = t.
Proof.
intros i t.
unfold id.
unfold subst.
apply traverse_id; [].
clear t.
intros j n.
forget (lt_dec n j) as b.
destruct b as [Hlt | Hnlt]; auto; [].
so (lt_dec (n - j) i) as [Hlt | Hnlt'].
  {
  rewrite -> project_under_lt; auto; [].
  unfold shift.
  rewrite -> traverse_var; [].
  set (X := lt_dec (n - j) 0); destruct X as [|]; [omega |].
  unfold varx.
  f_equal; omega.
  }

  {
  rewrite -> project_under_geq_shift; [| omega].
  rewrite -> project_sh; [].
  unfold shift.
  rewrite -> traverse_var; [].
  set (X := lt_dec (0 + (n - j - i)) 0); destruct X as [|]; [omega |].
  rewrite -> traverse_var; [].
  set (X := lt_dec (i + (0 + (n - j - i))) 0); destruct X as [|]; [omega |].
  unfold varx.
  f_equal; omega.
  }
Qed.


Lemma subst_var0_sh1 :
  forall m,
    subst (dot (var 0) sh1) m = m.
Proof.
intros m.
rewrite <- (subst_under_id 1 m) at 2.
auto.
Qed.


Lemma subst_var01_sh2 :
  forall m,
    subst (dot (var 0) (dot (var 1) (sh 2))) m = m.
Proof.
intros m.
rewrite <- (subst_under_id 2 m) at 2.
auto.
Qed.


(* These rules just capture the definitions. *)

Lemma project_dot_zero :
  forall t s,
    project (dot t s) 0 = t.
Proof.
reflexivity.
Qed.


Lemma project_dot_succ :
  forall t s i,
     project (dot t s) (S i) = project s i.
Proof.
intros t s i.
reflexivity.
Qed.


Lemma compose_dot :
  forall t s1 s2,
    compose (dot t s1) s2 = dot (subst s2 t) (compose s1 s2).
Proof.
intros t s1 s2.
reflexivity.
Qed.


Lemma under_succ :
  forall i s, under (S i) s = dot (varx 0) (compose (under i s) (sh 1)).
Proof.
intros i s.
reflexivity.
Qed.


Lemma under_sum :
  forall i j s, under i (under j s) = under (i+j) s.
Proof.
intros i j s.
induct i; auto; [].
(* S *)
intros i IH.
simpl.
rewrite -> IH; [].
reflexivity.
Qed.


Lemma fold_id :
  sh 0 = id.
Proof.
reflexivity.
Qed.


Lemma fold_sh1 :
  sh 1 = sh1.
Proof.
reflexivity.
Qed.


Lemma fold_subst1 :
  forall t,
    subst (dot t id) = subst1 t.
Proof.
intros; reflexivity.
Qed.


(* Additonal rules *)

Lemma split_dot :
  forall t s,
    dot t s = compose (dot (varx 0) (compose s sh1)) (dot t id).
Proof.
intros t s.
rewrite -> compose_dot; [].
simpl.
rewrite -> compose_assoc; [].
unfold sh1, id; rewrite -> compose_sh_dot.
rewrite -> compose_sh_sh.
rewrite -> subst_var.
rewrite -> project_dot_zero.
rewrite -> compose_id_right.
reflexivity.
Qed.



(* Equivalent substitutions *)

Definition eqsub (s s' : sub) :=
  forall i t, subst (under i s) t = subst (under i s') t.


Lemma subst_eqsub :
  forall s s' t,
    eqsub s s'
    -> subst s t = subst s' t.
Proof.
intros s s' t Heq.
so (Heq 0 t) as H.
exact H.
Qed.


Lemma eqsub_refl :
  forall s, eqsub s s.
Proof.
intro s.
intros i t.
reflexivity.
Qed.


Lemma eqsub_refl' :
  forall s s',
    s = s'
    -> eqsub s s'.
Proof.
intros; subst; apply eqsub_refl.
Qed.


Lemma eqsub_symm : 
  forall s s',
    eqsub s s'
    -> eqsub s' s.
Proof.
intros s s' H i t.
symmetry.
apply H.
Qed.


Lemma eqsub_trans :
  forall s1 s2 s3,
    eqsub s1 s2
    -> eqsub s2 s3
    -> eqsub s1 s3.
Proof.
intros s1 s2 s3 H12 H23 i t.
etransitivity; eauto.
Qed.


Lemma eqsub_dotv :
  forall t s s', 
    eqsub s s'
    -> eqsub (dot t s) (dot t s').
Proof.
intros t s s' Heq.
intros j u.
rewrite -> (split_dot t s); rewrite -> (split_dot t s'); [].
rewrite -> !compose_under; [].
rewrite -> !subst_compose; [].
f_equal; [].
so (Heq (j + 1) u) as H.
rewrite <- !under_sum in H; [].
rewrite -> !under_succ in H; [].
exact H.
Qed.


Lemma eqsub_compose :
  forall s1 s1' s2 s2',
    eqsub s1 s1'
    -> eqsub s2 s2'
    -> eqsub (compose s1 s2) (compose s1' s2').
Proof.
intros s1 s1' s2 s2' Heq1 Heq2.
unfold eqsub in *.
intros i m.
rewrite -> !compose_under.
rewrite -> !subst_compose.
rewrite -> Heq1.
rewrite -> Heq2.
reflexivity.
Qed.


Lemma eqsub_under :
  forall i s s',
    eqsub s s'
    -> eqsub (under i s) (under i s').
Proof.
intros i s s' Heq.
intros j t.
rewrite -> !under_sum; [].
apply Heq.
Qed.


Lemma eqsub_under_id :
  forall i, eqsub (under i id) id.
Proof.
intros i.
unfold eqsub.
intros j t.
rewrite -> under_sum; [].
transitivity t.
- apply subst_under_id.

- symmetry.
  apply subst_under_id.
Qed.


Lemma eqsub_expand_sh :
  forall n,
    eqsub (sh n) (dot (varx n) (sh (S n))).
Proof.
intros n i t.
rewrite <- (subst_under_id (S i) t) at 1; [].
replace (S i) with (i + 1) by omega.
rewrite <- under_sum; [].
rewrite <- subst_compose; [].
rewrite <- compose_under; [].
rewrite -> under_succ.
rewrite -> under_zero.
rewrite -> compose_id_left.
rewrite -> compose_dot.
rewrite -> compose_sh_sh.
rewrite -> subst_var.
rewrite -> project_sh.
replace (n + 0) with n by omega.
reflexivity.
Qed.    


Lemma eqsub_expand_id :
  eqsub id (dot (varx 0) sh1).
Proof.
unfold id, sh1.
apply eqsub_expand_sh.
Qed.


Lemma express_as_dot :
  forall s, exists m s', eqsub s (dot m s').
Proof.
intros s.
destruct s as [m s | i].
  {
  exists m, s.
  apply eqsub_refl.
  }

  {
  exists (varx i), (sh (S i)).
  apply eqsub_expand_sh.
  }
Qed.


Lemma project_eqsub :
  forall s s' i,
    eqsub s s'
    -> project s i = project s' i.
Proof.
intros s s' i Heq.
rewrite <- !subst_var.
erewrite -> subst_eqsub; eauto.
Qed.


End object.


Arguments sub {object}.
Arguments dot {object}.
Arguments sh {object}.
Arguments trunc {object}.
Arguments project {object}.
Arguments shift {object}.
Arguments subst {object}.
Arguments id {object}.
Arguments sh1 {object}.
Arguments subst1 {object}.
Arguments compose {object}.
Arguments under {object}.
Arguments eqsub {object}.


(* Least priority first. *)
Hint Unfold id sh1 subst1 : subst.
Hint Rewrite under_sum compose_under subst_under_id : subst.
Hint Rewrite <- subst_compose : subst.
Hint Rewrite compose_assoc project_compose : subst.
Hint Rewrite under_zero under_succ : subst.
Hint Rewrite @subst_id compose_id_left compose_id_right compose_dot compose_sh_dot compose_sh_sh : subst.
Hint Rewrite subst_var project_sh project_dot_zero project_dot_succ : subst.

Hint Rewrite fold_id fold_sh1 fold_subst1 : subst_cleanup.

Hint Unfold termx varx : subst_cleanup.


Ltac simpsub :=
  autounfold with subst;
  autorewrite with subst;
  autounfold with subst_cleanup;
  autorewrite with subst_cleanup.

Ltac simpsubin H :=
  autounfold with subst in H;
  autorewrite with subst in H;
  autounfold with subst_cleanup in H;
  autorewrite with subst_cleanup in H.

Hint Rewrite traverse_var traverse_oper traverse_row_cons traverse_row_nil : traverse.

Ltac prove_subst :=
  intros;
  try (match goal with
       | |- _ = ?t => let v := headvar t in unfold v
       end);
  unfold subst; 
  autorewrite with traverse;
  try (rewrite -> !traverse_under); reflexivity.


Add Parametric Relation object : (@sub object) (@eqsub object)
  reflexivity proved by (eqsub_refl object)
  symmetry proved by (eqsub_symm object)
  transitivity proved by (eqsub_trans object)
  as eqsub_rel.


Add Parametric Morphism object : (@subst object)
  with signature eqsub ==> eq ==> eq
  as subst_mor.
Proof.
intros s s' Hs m.
apply subst_eqsub; auto.
Qed.
