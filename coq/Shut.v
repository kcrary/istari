
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Tactics.
Require Import Sequence.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.
Require Import Hygiene.
Require Import ContextHygiene.
Require Import System.
Require Import Judgement.


Lemma upper_bound_all_list :
  forall (l : list nat),
    exists n,
      list_rect (fun _ => Prop)
        True
        (fun i _ P => i <= n /\ P)
        l.
Proof.
intros l.
cut (exists n,
       forall m,
         n <= m
         -> list_rect (fun _ => Prop)
              True
              (fun i _ P => i <= m /\ P)
              l).
  {
  intros (n & Hn).
  exists n.
  apply Hn; auto.
  }
induct l.

(* nil *)
{
exists 0.
cbn.
auto.
}

(* cons *)
{
intros i l IH.
destruct IH as (j & Hj).
exists (max i j).
intros n Hn.
cbn.
split.
  {
  so (Nat.le_max_l i j).
  omega.
  }

  {
  apply Hj.
  so (Nat.le_max_r i j).
  omega.
  }
}
Qed.


Lemma upper_bound_all :
  forall (n : nat),
    nat_rect (fun _ => list nat -> Prop)
      (fun l =>
         exists n,
           list_rect (fun _ => Prop)
             True
             (fun i _ P => i <= n /\ P)
             (List.rev l))
      (fun _ P l =>
         forall (i : nat), P (cons i l))
      n
      nil.
Proof.
intro n.
generalize (@nil nat).
induct n.

(* 0 *)
{
intros l.
cbn.
apply upper_bound_all_list.
}

(* S *)
{
intros n IH l.
cbn.
intro i.
apply IH.
}
Qed.


Section object.


Variable object : Type.


Lemma can_hygiene :
  forall (m : @term object),
    exists i, hygiene (fun j => j < i) m.
Proof.
intros m.
pattern m.
apply (term_mut_ind _ _
         (fun a r =>
            exists i, hygiene_row (fun j => j < i) r)); clear m.

(* var *)
{
intros i.
exists (S i).
apply hygiene_var.
omega.
}

(* oper *)
{
intros a th r IH.
destruct IH as (i & Hi).
exists i.
apply hygiene_oper; auto.
}

(* nil *)
{
exists 0.
apply hygiene_nil.
}

(* cons *)
{
intros j a m IH1 r IH2.
destruct IH1 as (i1 & Hi1).
destruct IH2 as (i2 & Hi2).
exists (max i1 i2).  (* higher than necessary, but that's fine *)
apply hygiene_cons.
  {
  eapply hygiene_weaken; eauto.
  intros k Hk.
  so (le_gt_dec j k) as [Hjk | Hkj]; auto.
  right.
  split; auto.
  so (Nat.le_max_l i1 i2).
  omega.
  }

  {
  eapply hygiene_row_weaken; eauto.
  intros k Hk.
  so (Nat.le_max_r i1 i2).
  omega.
  }
}
Qed.


Lemma can_hygiene' :
  forall (m : @term object),
    exists i, forall j, i <= j -> hygiene (fun k => k < j) m.
Proof.
intros m.
so (can_hygiene m) as (i & Hi).
exists i.
intros j Hj.
eapply hygiene_weaken; eauto.
intros k.
omega.
Qed.


Lemma can_hygieneh :
  forall (h : @hyp object),
    exists i, hygieneh (fun j => j < i) h.
Proof.
intros h.
induct h.

{
exists 0.
apply hygieneh_tpl.
}

{
exists 0.
apply hygieneh_tp.
}

{
intros a.
so (can_hygiene a) as (i & Hi).
exists i.
apply hygieneh_tml; auto.
}

{
intros a.
so (can_hygiene a) as (i & Hi).
exists i.
apply hygieneh_tm; auto.
}

{
exists 0.
apply hygieneh_emp.
}
Qed.


Lemma can_hygieneh' :
  forall (h : @hyp object),
    exists i, forall j, i <= j -> hygieneh (fun k => k < j) h.
Proof.
intros h.
so (can_hygieneh h) as (i & Hi).
exists i.
intros j Hj.
eapply hygieneh_weaken; eauto.
intros k.
omega.
Qed.


Lemma can_hygienej :
  forall (J : @judgement object),
    exists i, hygienej (fun j => j < i) J.
Proof.
intros J.
induct J.
intros m n a.
so (can_hygiene m) as (i1 & Hm).
so (can_hygiene n) as (i2 & Hn).
so (can_hygiene a) as (i3 & Ha).
so (upper_bound_all 3 i1 i2 i3) as (i & Hi1 & Hi2 & Hi3 & _).
exists i.
apply hygienej_deq; eapply hygiene_weaken; eauto; intros j Hj; omega.
Qed.


Lemma can_hygienej' :
  forall (J : @judgement object),
    exists i, forall j, i <= j -> hygienej (fun k => k < j) J.
Proof.
intros J.
so (can_hygienej J) as (i & Hi).
exists i.
intros j Hj.
eapply hygienej_weaken; eauto.
intros k.
omega.
Qed.


Fixpoint shut n : @context object :=
  match n with
  | 0 => nil

  | S n' => hyp_tm unittp :: shut n'
  end.


Lemma length_shut :
  forall n, length (shut n) = n.
Proof.
intro n.
induct n; auto; intros; cbn; f_equal; auto.
Qed.


Lemma promote_shut :
  forall n, @promote object (shut n) = shut n.
Proof.
intros n.
induct n; intros; cbn; f_equal; auto.
Qed.


Lemma shut_term :
  forall (G : @context object) (m : @term object),
    exists i,
      forall j,
        i <= j
        -> hygiene (ctxpred (G ++ shut j)) m.
Proof.
intros G m.
so (can_hygiene m) as (i & Hi).
exists i.
intros j Hj.
eapply hygiene_weaken; eauto.
intros k Hk.
rewrite ctxpred_length, app_length, length_shut.
omega.
Qed.


Lemma shut_hyp :
  forall (G : @context object) (h : @hyp object),
    exists i,
      forall j,
        i <= j
        -> hygieneh (ctxpred (G ++ shut j)) h.
Proof.
intros G m.
so (can_hygieneh m) as (i & Hi).
exists i.
intros j Hj.
eapply hygieneh_weaken; eauto.
intros k Hk.
rewrite ctxpred_length, app_length, length_shut.
omega.
Qed.


Lemma shut_judgement :
  forall (G : @context object) (J : @judgement object),
    exists i,
      forall j,
        i <= j
        -> hygienej (ctxpred (G ++ shut j)) J.
Proof.
intros G J.
so (can_hygienej J) as (i & Hi).
exists i.
intros j Hj.
eapply hygienej_weaken; eauto.
intros k Hk.
rewrite ctxpred_length, app_length, length_shut.
omega.
Qed.


End object.


Arguments shut {object}.


Definition pseq (G : scontext) (J : judgement) : Prop :=
  exists i,
    forall j,
      i <= j
      -> seq (G ++ shut j) J.


Definition obj := Candidate.obj Page.stop.


(* Given a goal of the form:

   forall G,
     pseq (G1 ++ G) J1
     -> ...
     -> pseq (Gn ++ G) Jn
     -> pseq G J

   refine (seq_pseq m H1 p1 ... Hm pm n G1 J1 ... Gn Jn J _)

   will produce a subgoal of the form:

   forall G,
     hygiene (ctxpred (Hi ++ G)) pi)
     -> ...
     -> hygiene (ctxpred (Hm ++ G)) pm)
     -> seq (G1 ++ G) J1
     -> ...
     -> seq (Gn ++ G) Jn
     -> seq G J

   Note that one can fill in all the Jis with _, and all the
   Gis with [_, ..., _].
*)
Lemma seq_pseq :
  forall m,
    nat_rect (fun _ => list (scontext * term _) -> Prop)
      (fun T =>
         forall n,
           nat_rect (fun _ => list (scontext * judgement) -> Prop)
             (fun L =>
                forall J,
                  (forall G,
                     list_rect (fun _ => Prop)
                       (list_rect (fun _ => Prop)
                          (seq G J)
                          (fun X _ P => 
                             match X with
                             | pair G' J' => seq (G' ++ G) J' -> P
                             end)
                          (rev L))
                        (fun X _ P =>
                           match X with
                           | pair G' p => hygiene (ctxpred (G' ++ G)) p -> P
                           end)
                        (rev T))
                  ->
                  forall G,
                    list_rect (fun _ => Prop)
                      (pseq G J)
                      (fun X _ P => 
                         match X with
                         | pair G' J' => pseq (G' ++ G) J' -> P
                         end)
                      (rev L))
             (fun _ P L =>
                forall (G : scontext) (J : judgement), P ((G, J) :: L))
             n
             nil)
      (fun _ P T =>
         forall (G : scontext) (p : term obj), P ((G, p) :: T))
      m
      nil.
Proof.
intro m.
set (T := @nil (scontext * term obj)).
clearbody T.
revert T.
induct m.
2:{
  intros m IH T.
  cbn.
  intros G p.
  apply IH.
  }
intros T.
cbn.
set (T' := rev T).
clearbody T'.
renameover T' into T.
intro n.
set (L := nil).
clearbody L.
revert L.
induct n.
2:{
  intros n IH L.
  cbn.
  intros G J.
  apply IH.
  }
intros L.
cbn.
set (L' := rev L).
clearbody L'.
renameover L' into L.
intros J Hseqs G.
set (i := 0).
assert (forall j,
          i <= j
          -> list_rect (fun _ => Prop)
               (list_rect (fun _ => Prop)
                  (seq (G ++ shut j) J)
                  (fun X _ P => 
                     match X with
                     | pair G' J' => seq (G' ++ G ++ shut j) J' -> P
                     end)
                  L)
                (fun X _ P =>
                   match X with
                   | pair G' p => hygiene (ctxpred (G' ++ G ++ shut j)) p -> P
                   end)
                T).
  {
  intros j Hj.
  cbn in Hseqs.
  exact (Hseqs (G ++ shut j)).
  }
clear Hseqs.
clearbody i.
revert i H.
induct T.

(* nil *)
{
intros i1 Hseq.
cbn in Hseq.
revert i1 Hseq.
induct L.
  (* nil *)
  {
  cbn.
  intros i Hseq.
  exists i.
  intros j Hj.
  apply Hseq; auto.
  }
  
  (* cons *)
  {
  intros (G', J') L IH i Hseqs.
  cbn.
  intros (j & Hseq).
  apply (IH (max i j)).
  intros k Hk.
  exploit (Hseqs k) as H.
    {
    so (Nat.le_max_l i j).
    omega.
    }
  cbn in H.
  apply H.
  rewrite -> app_assoc.
  apply Hseq.
  so (Nat.le_max_r i j).
  omega.
  }
}

(* cons *)
{
intros (G', p) T IH i Hseqs.
so (shut_term _ (G' ++ G) p) as (j & Hclp).
apply (IH (max i j)).
intros k Hk.
exploit (Hseqs k) as H.
  {
  so (Nat.le_max_l i j).
  omega.
  }
cbn in H.
apply H.
rewrite -> app_assoc.
apply Hclp.
so (Nat.le_max_r i j).
omega.
}
Qed.


(* Given a goal of the form:

   forall G,
     pseq (G1a ++ G1b ++ G) J1
     -> ...
     -> pseq (Gna ++ Gnb ++ G) Jn
     -> pseq (Ga ++ Gb ++ G) J

   refine (seq_pseq_hyp m H1 p1 ... Hm pm n G1a G1b J1 ... Gna Gnb Jn Ga Gb J _)

   will produce a subgoal of the form:

   forall G,
     hygiene (ctxpred (Hi ++ G) pi)
     -> ...
     -> hygiene (ctxpred (Hm ++ G) pm)
     -> seq (G1a ++ G1b ++ G) J1
     -> ...
     -> seq (Gna ++ Gnb ++ G) Jn
     -> hygienej (ctxpred (Ga ++ Gb ++ G)) J
     -> seq (Ga ++ Gb ++ G) J

   Note that one can fill in all the Jis with _, and all the
   Gias and Gibs with [_; ...; _].
*)
Lemma seq_pseq_hyp :
  forall m,
    nat_rect (fun _ => list (scontext * term _) -> Prop)
      (fun T =>
         forall n,
           nat_rect (fun _ => list (scontext * scontext * judgement) -> Prop)
             (fun L =>
                forall G1 G2 J,
                  (forall G,
                     list_rect (fun _ => Prop)
                       (list_rect (fun _ => Prop)
                          (hygienej (ctxpred (G1 ++ G2 ++ G)) J -> seq (G1 ++ G2 ++ G) J)
                          (fun X _ P => 
                             match X with
                             | pair (pair G1' G2') J' => seq (G1' ++ G2' ++ G) J' -> P
                             end)
                          (rev L))
                       (fun X _ P =>
                          match X with
                          | pair G' p => hygiene (ctxpred (G' ++ G)) p -> P
                          end)
                       (rev T))
                  ->
                  forall G,
                    list_rect (fun _ => Prop)
                      (pseq (G1 ++ G2 ++ G) J)
                      (fun X _ P => 
                         match X with
                         | pair (pair G1' G2') J' => pseq (G1' ++ G2' ++ G) J' -> P
                         end)
                      (rev L))
             (fun _ P L =>
                forall (G1 G2 : scontext) (J : judgement), P (((G1, G2), J) :: L))
             n
             nil)
      (fun _ P T =>
         forall (G : scontext) (p : term obj), P ((G, p) :: T))
      m
      nil.
Proof.
intro m.
set (T := @nil (scontext * term obj)).
clearbody T.
revert T.
induct m.
2:{
  intros m IH T.
  cbn.
  intros G p.
  apply IH.
  }
intros T.
cbn.
set (T' := rev T).
clearbody T'.
renameover T' into T.
intro n.
set (L := nil).
clearbody L.
revert L.
induct n.
2:{
  intros n IH L.
  cbn.
  intros G1 G2 J.
  apply IH.
  }
intros L.
cbn.
set (L' := rev L).
clearbody L'.
renameover L' into L.
intros G1 G2 J Hseqs G.
set (i := 0).
assert (forall j,
          i <= j
          -> list_rect (fun _ => Prop)
               (list_rect (fun _ => Prop)
                  (hygienej (ctxpred (G1 ++ G2 ++ G ++ shut j)) J -> seq (G1 ++ G2 ++ G ++ shut j) J)
                  (fun X _ P => 
                     match X with
                     | pair (pair G1' G2') J' => seq (G1' ++ G2' ++ G ++ shut j) J' -> P
                     end)
                  L)
                (fun X _ P =>
                   match X with
                   | pair G' p => hygiene (ctxpred (G' ++ G ++ shut j)) p -> P
                   end)
                T) as H.
  {
  intros j Hj.
  exact (Hseqs (G ++ shut j)).
  }
clear Hseqs.
clearbody i.
revert i H.
induct T.

(* nil *)
{
intros i1 Hseq.
cbn in Hseq.
revert i1 Hseq.
induct L.
  (* nil *)
  {
  cbn.
  intros i1 Hseq.
  so (shut_judgement _ (G1 ++ G2 ++ G) J) as (i2 & HclJ).
  so (upper_bound_all 2 i1 i2) as (i & Hi1 & Hi2 & _).
  exists i.
  intros j Hj.
  rewrite <- !app_assoc.
  apply Hseq; eauto using le_trans.
  lapply (HclJ j); [| omega].
  intro H.
  autorewrite with canonlist in H.
  exact H.
  }
  
  (* cons *)
  {
  intros ((G1', G2'), J') L IH i Hseqs.
  cbn.
  intros (j & Hseq).
  apply (IH (max i j)).
  intros k Hk.
  exploit (Hseqs k) as H.
    {
    so (Nat.le_max_l i j).
    omega.
    }
  cbn in H.
  apply H.
  setoid_rewrite -> app_assoc.
  setoid_rewrite -> app_assoc.
  setoid_rewrite <- app_assoc at 2.
  apply Hseq.
  so (Nat.le_max_r i j).
  omega.
  }
}

(* cons *)
{
intros (G', p) T IH i Hseqs.
so (shut_term _ (G' ++ G) p) as (j & Hclp).
apply (IH (max i j)).
intros k Hk.
exploit (Hseqs k) as H.
  {
  so (Nat.le_max_l i j).
  omega.
  }
cbn in H.
apply H.
rewrite -> app_assoc.
apply Hclp.
so (Nat.le_max_r i j).
omega.
}
Qed.


(* Given a goal of the form:

   forall G,
     pseq (G1 ++ if b1 then promote G else G) J1
     -> ...
     -> pseq (Gn ++ if bn then promote G else G) Jn
     -> pseq G J

   refine (seq_pseq_promote m H1 p1 ... Hm pm n b1 G1 J1 ... bn Gn Jn J _)

   will produce a subgoal of the form:

   forall G,
     hygiene (ctxpred (Hi ++ G) pi)
     -> ...
     -> hygiene (ctxpred (Hm ++ G) pm)
     -> seq (G1 ++ if b1 then promote G else G) J1
     -> ...
     -> seq (Gn ++ if bn then promote G else G) Jn
     -> seq G J

   Note that one can fill in all the Jis with _, and all the
   Gis with [_, ..., _].
*)
Lemma seq_pseq_promote :
  forall m,
    nat_rect (fun _ => list (scontext * term _) -> Prop)
      (fun T =>
         forall n,
           nat_rect (fun _ => list (bool * scontext * judgement) -> Prop)
             (fun L =>
                forall J,
                  (forall G,
                     list_rect (fun _ => Prop)
                       (list_rect (fun _ => Prop)
                          (seq G J)
                          (fun X _ P => 
                             match X with
                             | pair (pair b G') J' => seq (G' ++ match b with true => promote G | false => G end) J' -> P
                             end)
                          (rev L))
                        (fun X _ P =>
                           match X with
                           | pair G' p => hygiene (ctxpred (G' ++ G)) p -> P
                           end)
                        (rev T))
                  ->
                  forall G,
                    list_rect (fun _ => Prop)
                      (pseq G J)
                      (fun X _ P => 
                         match X with
                         | pair (pair b G') J' => pseq (G' ++ match b with true => promote G | false => G end) J' -> P
                         end)
                      (rev L))
             (fun _ P L =>
                forall (b : bool) (G : scontext) (J : judgement), P ((b, G, J) :: L))
             n
             nil)
      (fun _ P T =>
         forall (G : scontext) (p : term obj), P ((G, p) :: T))
      m
      nil.
Proof.
intro m.
set (T := @nil (scontext * term obj)).
clearbody T.
revert T.
induct m.
2:{
  intros m IH T.
  cbn.
  intros G p.
  apply IH.
  }
intros T.
cbn.
set (T' := rev T).
clearbody T'.
renameover T' into T.
intro n.
set (L := nil).
clearbody L.
revert L.
induct n.
2:{
  intros n IH L.
  cbn.
  intros b G J.
  apply IH.
  }
intros L.
cbn.
set (L' := rev L).
clearbody L'.
renameover L' into L.
cbn.
intros J Hseqs G.
set (i := 0).
assert (forall j,
          i <= j
          -> list_rect (fun _ => Prop)
               (list_rect (fun _ => Prop)
                  (seq (G ++ shut j) J)
                  (fun X _ P => 
                     match X with
                     | pair (pair b G') J' => seq (G' ++ match b with true => promote (G ++ shut j) | false => G ++ shut j end) J' -> P
                     end)
                  L)
               (fun X _ P =>
                  match X with
                  | pair G' p => hygiene (ctxpred (G' ++ G ++ shut j)) p -> P
                  end)
               T) as H.
  {
  intros j Hj.
  cbn in Hseqs.
  exact (Hseqs (G ++ shut j)).
  }
clear Hseqs.
clearbody i.
revert i H.
induct T.

(* nil *)
{
intros i1 Hseq.
cbn in Hseq.
revert i1 Hseq.
induct L.
  (* nil *)
  {
  cbn.
  intros i Hseq.
  exists i.
  intros j Hj.
  apply Hseq; auto.
  }
  
  (* cons *)
  {
  intros ((b, G'), J') L IH i Hseqs.
  cbn.
  intros (j & Hseq).
  apply (IH (max i j)).
  intros k Hk.
  exploit (Hseqs k) as H.
    {
    so (Nat.le_max_l i j).
    omega.
    }
  cbn in H.
  apply H.
  destruct b.
    {
    rewrite -> promote_append.
    rewrite -> promote_shut.
    rewrite -> app_assoc.
    apply Hseq.
    so (Nat.le_max_r i j).
    omega.
    }
  
    {
    rewrite -> app_assoc.
    apply Hseq.
    so (Nat.le_max_r i j).
    omega.
    }
  }
}

(* cons *)
{
intros (G', p) T IH i Hseqs.
so (shut_term _ (G' ++ G) p) as (j & Hclp).
apply (IH (max i j)).
intros k Hk.
exploit (Hseqs k) as H.
  {
  so (Nat.le_max_l i j).
  omega.
  }
cbn in H.
apply H.
rewrite -> app_assoc.
apply Hclp.
so (Nat.le_max_r i j).
omega.
}
Qed.


Ltac finish_pseq j :=
eauto using le_trans;
match goal with
| H : forall (x : nat), _ <= x  -> _ |- _ =>
  let H' := fresh
  in
    lapply (H j); [| eauto using le_trans];
    intro H';
    autorewrite with canonlist in H';
    exact H'
end.
