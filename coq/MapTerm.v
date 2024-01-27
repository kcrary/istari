
Require Import Coq.Lists.List.

Require Import Axioms.
Require Import Tactics.
Require Import Equality.
Require Import Relation.
Require Import Syntax.
Require Import SimpSub.
Require Import Hygiene.
Require Import ContextHygiene.
Require Import Dynamic.
Require Import Reduction.
Require Import Equivalence.
Require Import Ofe.
Require Import Sequence.
Require Import Promote.


Arguments rw_nil {object}.
Arguments rw_cons {object i a}.
Arguments reducer {object a}.


Definition map_operator {A B : Type} (f : A -> B) (a : list nat) (th : operator A a)
  : operator B a
  :=
  match th with
  | oper_ext _ x => oper_ext _ (f x)
  | oper_extt _ x => oper_extt _ (f x)

  | oper_univ _ => oper_univ _
  | oper_cty _ => oper_cty _
  | oper_con _ => oper_con _
  | oper_karrow _ => oper_karrow _
  | oper_tarrow _ => oper_tarrow _
  | oper_pi _ => oper_pi _
  | oper_clam _ => oper_clam _
  | oper_capp _ => oper_capp _
  | oper_ctlam _ => oper_ctlam _
  | oper_ctapp _ => oper_ctapp _
  | oper_lam _ => oper_lam _
  | oper_app _ => oper_app _
  | oper_intersect _ => oper_intersect _
  | oper_union _ => oper_union _
  | oper_fut _ => oper_fut _
  | oper_cnext _ => oper_cnext _
  | oper_cprev _ => oper_cprev _
  | oper_next _ => oper_next _
  | oper_prev _ => oper_prev _
  | oper_rec _ => oper_rec _
  | oper_equal _ => oper_equal _
  | oper_triv _ => oper_triv _
  | oper_eqtype _ => oper_eqtype _
  | oper_sequal _ => oper_sequal _
  | oper_subtype _ => oper_subtype _
  | oper_kind _ => oper_kind _
  | oper_all _ => oper_all _
  | oper_alltp _ => oper_alltp _
  | oper_exist _ => oper_exist _
  | oper_mu _ => oper_mu _
  | oper_ispositive _ => oper_ispositive _
  | oper_isnegative _ => oper_isnegative _
  | oper_voidtp _ => oper_voidtp _
  | oper_unittp _ => oper_unittp _
  | oper_cunit _ => oper_cunit _
  | oper_booltp _ => oper_booltp _
  | oper_btrue _ => oper_btrue _
  | oper_bfalse _ => oper_bfalse _
  | oper_bite _ => oper_bite _
  | oper_prod _ => oper_prod _
  | oper_sigma _ => oper_sigma _
  | oper_cpair _ => oper_cpair _
  | oper_cpi1 _ => oper_cpi1 _
  | oper_cpi2 _ => oper_cpi2 _
  | oper_ppair _ => oper_ppair _
  | oper_ppi1 _ => oper_ppi1 _
  | oper_ppi2 _ => oper_ppi2 _
  | oper_set _ => oper_set _
  | oper_iset _ => oper_iset _
  | oper_quotient _ => oper_quotient _
  | oper_guard _ => oper_guard _
  | oper_wt _ => oper_wt _
  end.


Arguments map_operator {A B} f {a}.


Fixpoint map_term {A B : Type} (f : A -> B) (m : term A) {struct m} : @term B
  :=
  (match m with
   | var j => var j
   | oper a th r => oper a (map_operator f th) (map_row f a r)
   end)

with map_row {A B : Type} (f : A -> B) (a : list nat) (r : row _ a) {struct r} : @row B a
  :=
  match r
    in @row _ a
    return @row B a
  with
  | rw_nil => rw_nil
  | @rw_cons _ i a m r => @rw_cons _ i a (map_term f m) (map_row f a r)
  end.


Arguments map_row {A B} f {a}.


Lemma map_ext :
  forall A B (f : A -> B) (x : A),
    map_term f (ext x) = ext (f x).
Proof.
auto.
Qed.


Lemma map_extt :
  forall A B (f : A -> B) (x : A),
    map_term f (extt x) = extt (f x).
Proof.
auto.
Qed.


Lemma map_var :
  forall A B (f : A -> B) i, map_term f (var i) = var i.
Proof.
auto.
Qed.


Lemma map_univ :
  forall A B (f : A -> B) m, map_term f (univ m) = univ (map_term f m).
Proof.
auto.
Qed.


Lemma map_cty :
  forall A B (f : A -> B) m, map_term f (cty m) = cty (map_term f m).
Proof.
auto.
Qed.


Lemma map_con :
  forall A B (f : A -> B) m1 m2, map_term f (con m1 m2) = con (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_karrow :
  forall A B (f : A -> B) m1 m2, map_term f (karrow m1 m2) = karrow (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_tarrow :
  forall A B (f : A -> B) m1 m2, map_term f (tarrow m1 m2) = tarrow (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_pi :
  forall A B (f : A -> B) m1 m2, map_term f (pi m1 m2) = pi (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_clam :
  forall A B (f : A -> B) k a, map_term f (clam k a) = clam (map_term f k) (map_term f a).
Proof.
auto.
Qed.


Lemma map_capp :
  forall A B (f : A -> B) m1 m2, map_term f (capp m1 m2) = capp (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_ctlam :
  forall A B (f : A -> B) a b k, map_term f (ctlam a b k) = ctlam (map_term f a) (map_term f b) (map_term f k).
Proof.
auto.
Qed.


Lemma map_ctapp :
  forall A B (f : A -> B) m1 m2, map_term f (ctapp m1 m2) = ctapp (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_lam :
  forall A B (f : A -> B) m, map_term f (lam m) = lam (map_term f m).
Proof.
auto.
Qed.


Lemma map_app :
  forall A B (f : A -> B) m1 m2, map_term f (app m1 m2) = app (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_intersect :
  forall A B (f : A -> B) m1 m2, map_term f (intersect m1 m2) = intersect (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_union :
  forall A B (f : A -> B) m1 m2, map_term f (union m1 m2) = union (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_fut :
  forall A B (f : A -> B) k, map_term f (fut k) = fut (map_term f k).
Proof.
auto.
Qed.


Lemma map_cnext :
  forall A B (f : A -> B) a, map_term f (cnext a) = cnext (map_term f a).
Proof.
auto.
Qed.


Lemma map_cprev :
  forall A B (f : A -> B) a, map_term f (cprev a) = cprev (map_term f a).
Proof.
auto.
Qed.


Lemma map_next :
  forall A B (f : A -> B) a, map_term f (next a) = next (map_term f a).
Proof.
auto.
Qed.


Lemma map_prev :
  forall A B (f : A -> B) a, map_term f (prev a) = prev (map_term f a).
Proof.
auto.
Qed.


Lemma map_rec :
  forall A B (f : A -> B) k, map_term f (rec k) = rec (map_term f k).
Proof.
auto.
Qed.


Lemma map_equal :
  forall A B (f : A -> B) a m n, map_term f (equal a m n) = equal (map_term f a) (map_term f m) (map_term f n).
Proof.
auto.
Qed.


Lemma map_triv :
  forall A B (f : A -> B), map_term f triv = triv.
Proof.
auto.
Qed.


Lemma map_eqtype :
  forall A B (f : A -> B) m1 m2, map_term f (eqtype m1 m2) = eqtype (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_sequal :
  forall A B (f : A -> B) m1 m2, map_term f (sequal m1 m2) = sequal (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_subtype :
  forall A B (f : A -> B) m1 m2, map_term f (subtype m1 m2) = subtype (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_kind :
  forall A B (f : A -> B) m, map_term f (kind m) = kind (map_term f m).
Proof.
auto.
Qed.


Lemma map_all :
  forall A B (f : A -> B) m1 m2 m3, map_term f (all m1 m2 m3) = all (map_term f m1) (map_term f m2) (map_term f m3).
Proof.
auto.
Qed.


Lemma map_alltp :
  forall A B (f : A -> B) m1, map_term f (alltp m1) = alltp (map_term f m1).
Proof.
auto.
Qed.


Lemma map_exist :
  forall A B (f : A -> B) m1 m2 m3, map_term f (exist m1 m2 m3) = exist (map_term f m1) (map_term f m2) (map_term f m3).
Proof.
auto.
Qed.


Lemma map_mu :
  forall A B (f : A -> B) m, map_term f (mu m) = mu (map_term f m).
Proof.
auto.
Qed.


Lemma map_ispositive :
  forall A B (f : A -> B) m, map_term f (ispositive m) = ispositive (map_term f m).
Proof.
auto.
Qed.


Lemma map_isnegative :
  forall A B (f : A -> B) m, map_term f (isnegative m) = isnegative (map_term f m).
Proof.
auto.
Qed.


Lemma map_voidtp :
  forall A B (f : A -> B), map_term f voidtp = voidtp.
Proof.
auto.
Qed.


Lemma map_unittp :
  forall A B (f : A -> B), map_term f unittp = unittp.
Proof.
auto.
Qed.


Lemma map_cunit :
  forall A B (f : A -> B), map_term f cunit = cunit.
Proof.
auto.
Qed.


Lemma map_booltp :
  forall A B (f : A -> B), map_term f booltp = booltp.
Proof.
auto.
Qed.


Lemma map_btrue :
  forall A B (f : A -> B), map_term f btrue = btrue.
Proof.
auto.
Qed.


Lemma map_bfalse :
  forall A B (f : A -> B), map_term f bfalse = bfalse.
Proof.
auto.
Qed.


Lemma map_bite :
  forall A B (f : A -> B) a m n, map_term f (bite a m n) = bite (map_term f a) (map_term f m) (map_term f n).
Proof.
auto.
Qed.


Lemma map_prod :
  forall A B (f : A -> B) m1 m2, map_term f (prod m1 m2) = prod (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_sigma :
  forall A B (f : A -> B) m1 m2, map_term f (sigma m1 m2) = sigma (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_cpair :
  forall A B (f : A -> B) m1 m2, map_term f (cpair m1 m2) = cpair (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_cpi1 :
  forall A B (f : A -> B) a, map_term f (cpi1 a) = cpi1 (map_term f a).
Proof.
auto.
Qed.


Lemma map_cpi2 :
  forall A B (f : A -> B) a, map_term f (cpi2 a) = cpi2 (map_term f a).
Proof.
auto.
Qed.


Lemma map_ppair :
  forall A B (f : A -> B) m1 m2, map_term f (ppair m1 m2) = ppair (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_ppi1 :
  forall A B (f : A -> B) a, map_term f (ppi1 a) = ppi1 (map_term f a).
Proof.
auto.
Qed.


Lemma map_ppi2 :
  forall A B (f : A -> B) a, map_term f (ppi2 a) = ppi2 (map_term f a).
Proof.
auto.
Qed.


Lemma map_set :
  forall A B (f : A -> B) m1 m2, map_term f (set m1 m2) = set (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_iset :
  forall A B (f : A -> B) m1 m2, map_term f (iset m1 m2) = iset (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_quotient :
  forall A B (f : A -> B) m1 m2, map_term f (quotient m1 m2) = quotient (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_guard :
  forall A B (f : A -> B) m1 m2, map_term f (guard m1 m2) = guard (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Lemma map_wt :
  forall A B (f : A -> B) m1 m2, map_term f (wt m1 m2) = wt (map_term f m1) (map_term f m2).
Proof.
auto.
Qed.


Hint Rewrite map_ext map_extt map_var map_univ map_cty map_con map_karrow map_tarrow map_pi map_clam map_capp map_ctlam map_ctapp map_lam map_app map_intersect map_union map_fut map_cnext map_cprev map_next map_prev map_rec map_equal map_triv map_eqtype map_sequal map_subtype map_kind map_all map_alltp map_exist map_mu map_ispositive map_isnegative map_voidtp map_unittp map_cunit map_booltp map_btrue map_bfalse map_bite map_prod map_sigma map_cpair map_cpi1 map_cpi2 map_ppair map_ppi1 map_ppi2 map_wt map_set map_iset map_quotient map_guard : map.


Lemma map_sumbool :
  forall A B (f : A -> B) P Q (c : {P} + {Q}) m n,
    map_term f (if c then m else n) = if c then map_term f m else map_term f n.
Proof.
intros A B f P Q c m n.
destruct c; auto.
Qed.


Hint Rewrite map_sumbool : map.


Fixpoint map_sub {A B : Type} (f : A -> B) (s : @sub A) {struct s} : @sub B
  :=
  match s with
  | dot m s' => dot (map_term f m) (map_sub f s')
  | sh i => sh i
  end.


Lemma map_dot :
  forall A B (f : A -> B) m s,
    map_sub f (dot m s) = dot (map_term f m) (map_sub f s).
Proof.
auto.
Qed.


Lemma map_sh :
  forall A B (f : A -> B) i,
    map_sub f (sh i) = sh i.
Proof.
auto.
Qed.


Lemma map_id :
  forall A B (f : A -> B),
    map_sub f id = id.
Proof.
auto.
Qed.


Lemma map_project :
  forall A B (f : A -> B) s i,
    map_term f (project s i) = project (map_sub f s) i.
Proof.
intros A B f s i.
revert s.
induct i.

(* 0 *)
{
intros s.
case s; clear s.
  {
  intros m s.
  simpsub.
  rewrite -> map_dot.
  simpsub.
  reflexivity.
  }

  {
  intro i.
  simpsub.
  rewrite -> map_sh.
  simpsub.
  rewrite -> map_var.
  reflexivity.
  }
}

(* S *)
{
intros n IH s.
case s; clear s.
  {
  intros m s.
  simpsub.
  rewrite -> map_dot.
  simpsub.
  apply IH.
  }

  {
  intro i.
  simpsub.
  rewrite -> map_sh.
  simpsub.
  rewrite -> map_var.
  reflexivity.
  }
}
Qed.


Lemma map_traverse_and_row :
  forall A B (f : A -> B) (resolve : nat -> nat -> term A),
    (forall i m,
       map_term f (traverse A resolve i m)
       =
       traverse B (fun i j => map_term f (resolve i j)) i (map_term f m))
    /\
    (forall i a r,
       map_row f (traverse_row A resolve i a r)
       =
       traverse_row B (fun i j => map_term f (resolve i j)) i a (map_row f r)).
Proof.
intros A B f resolve.
exploit
  (syntax_ind A
     (fun m =>
        forall i,
          map_term f (traverse A resolve i m)
          =
          traverse B (fun i j => map_term f (resolve i j)) i (map_term f m))
     (fun a r =>
        forall i,
          map_row f (traverse_row A resolve i a r)
          =
          traverse_row B (fun i j => map_term f (resolve i j)) i a (map_row f r))) as Hprop;
  intros; cbn; f_equal; eauto.

cbn in Hprop.
destruct Hprop.
split; intros; eauto.
Qed.


Lemma map_traverse :
  forall A B (f : A -> B) (resolve : nat -> nat -> term A) i m,
    map_term f (traverse A resolve i m)
    =
    traverse B (fun i j => map_term f (resolve i j)) i (map_term f m).
Proof.
intros A B f resolve.
exact (map_traverse_and_row A B f resolve andel).
Qed.


Lemma map_shift :
  forall A B (f : A -> B) n (m : term A),
    map_term f (shift n m)
    =
    shift n (map_term f m).
Proof.
intros A B f n m.
unfold shift.
etransitivity.
  {
  apply map_traverse.
  }
f_equal.
fextensionality 2.
intros i j.
set (X := Compare_dec.lt_dec j i).
destruct X; auto.
Qed.


Lemma map_subst :
  forall A B (f : A -> B) (s : @sub A) (m : term A),
    map_term f (subst s m)
    =
    subst (map_sub f s) (map_term f m).
Proof.
intros A B f s m.
unfold subst.
etransitivity.
  {
  apply map_traverse.
  }
f_equal.
fextensionality 2.
intros i j.
set (X := Compare_dec.lt_dec j i).
destruct X; auto.
rewrite -> map_shift.
rewrite -> map_project.
reflexivity.
Qed.


Lemma map_trunc :
  forall A B (f : A -> B) n (s : @sub A),
    map_sub f (trunc n s) = trunc n (map_sub f s).
Proof.
intros A B f n s.
revert s.
induct n; auto.
(* S *)
intros n IH s.
cbn.
destruct s as [m s | i]; auto.
rewrite -> map_dot.
apply IH.
Qed.


Lemma map_compose :
  forall A B (f : A -> B) s1 s2,
    map_sub f (compose s1 s2) = compose (map_sub f s1) (map_sub f s2).
Proof.
intros A B f s1 s2.
revert s2.
induct s1.

(* dot *)
{
intros m s1 IH s2.
simpsub.
rewrite -> !map_dot.
simpsub.
rewrite -> IH.
rewrite -> map_subst.
reflexivity.
}

(* sh *)
{
intros n s2.
cbn.
apply map_trunc.
}
Qed.


Lemma map_under :
  forall A B (f : A -> B) i s,
    map_sub f (under i s) = under i (map_sub f s).
Proof.
intros A B f i s.
induct i.

(* 0 *)
{
simpsub.
reflexivity.
}

(* S *)
{
intros n IH.
rewrite -> !under_succ.
rewrite -> map_dot.
rewrite -> map_var.
rewrite -> map_compose.
rewrite -> IH.
rewrite -> map_sh.
reflexivity.
}
Qed.


Lemma map_subst1 :
  forall A B (f : A -> B) (m n : term A),
    map_term f (subst1 m n)
    =
    subst1 (map_term f m) (map_term f n).
Proof.
intros A B f m n.
unfold subst1.
apply map_subst.
Qed.


Lemma map_sh1 :
  forall A B (f : A -> B), map_sub f sh1 = sh1.
Proof.
intros A B f.
unfold sh1.
apply map_sh.
Qed.


Hint Rewrite map_dot map_sh map_id map_project map_subst map_compose map_under map_subst1 map_sh1 : map.


Definition map_hyp {A B : Type} (f : A -> B) (h : @hyp A) : @hyp B :=
  match h with
  | hyp_tpl => hyp_tpl
  | hyp_tp => hyp_tp
  | hyp_tml m => hyp_tml (map_term f m)
  | hyp_tm m => hyp_tm (map_term f m)
  | hyp_emp => hyp_emp
  end.


Lemma map_tpl :
  forall A B (f : A -> B),
    map_hyp f hyp_tpl = hyp_tpl.
Proof.
auto.
Qed.


Lemma map_tp :
  forall A B (f : A -> B),
    map_hyp f hyp_tp = hyp_tp.
Proof.
auto.
Qed.


Lemma map_tml :
  forall A B (f : A -> B) m,
    map_hyp f (hyp_tml m) = hyp_tml (map_term f m).
Proof.
auto.
Qed.


Lemma map_tm :
  forall A B (f : A -> B) m,
    map_hyp f (hyp_tm m) = hyp_tm (map_term f m).
Proof.
auto.
Qed.


Lemma map_emp :
  forall A B (f : A -> B),
    map_hyp f hyp_emp = hyp_emp.
Proof.
auto.
Qed.


Hint Rewrite map_tpl map_tp map_tml map_tm map_emp : map.


Definition map_ctx {A B : Type} (f : A -> B) :=
  map (map_hyp f).


Lemma map_nil :
  forall A B (f : A -> B),
    map_ctx f nil = nil.
Proof.
auto.
Qed.  


Lemma map_cons :
  forall A B (f : A -> B) h G,
    map_ctx f (cons h G) = cons (map_hyp f h) (map_ctx f G).
Proof.
auto.
Qed.


Lemma map_appctx :
  forall A B (f : A -> B) G1 G2,
    map_ctx f (G2 ++ G1) = map_ctx f G2 ++ map_ctx f G1.
Proof.
intros A B f G1 G2.
induct G2; auto.
intros; cbn.
f_equal; auto.
Qed.


Hint Rewrite map_nil map_cons map_appctx : map.


Lemma length_map_ctx :
  forall A B (f : A -> B) (G : @context A),
    length (map_ctx f G) = length G.
Proof.
intros A B f G.
induct G; cbn; auto.
Qed.


Lemma map_index :
  forall A B (f : A -> B) i G h,
    index i G h
    -> index i (map_ctx f G) (map_hyp f h).
Proof.
intros A B f i G h H.
induct H.

(* 0 *)
{
intros; apply index_0.
}

(* S *)
{
intros i h' G h _ IH.
cbn.
apply index_S; auto.
}
Qed.


Lemma map_promote_hyp :
  forall A B (f : A -> B) h,
    map_hyp f (promote_hyp h) = promote_hyp (map_hyp f h).
Proof.
intros A B f h.
induct h; auto.
Qed.


Lemma map_promote :
  forall A B (f : A -> B) G,
    map_ctx f (promote G) = promote (map_ctx f G).
Proof.
intros A B f G.
induct G; auto.
intros h G IH.
cbn.
f_equal; auto using map_promote_hyp.
Qed.


Hint Rewrite map_promote_hyp map_promote : map.


Definition map_jud {A B : Type} (f : A -> B) (J : @judgement A) : @judgement B :=
  match J with
  | deq m1 m2 m3 => deq (map_term f m1) (map_term f m2) (map_term f m3)
  end.


Lemma map_deq :
  forall A B (f : A -> B) m1 m2 m3,
    map_jud f (deq m1 m2 m3) = deq (map_term f m1) (map_term f m2) (map_term f m3).
Proof.
auto.
Qed.


Hint Rewrite map_deq : map.


Ltac simpmap :=
  autorewrite with map.


Ltac simpmapin H :=
  autorewrite with map in H.


Lemma map_substh :
  forall A B (f : A -> B) (s : sub) (h : @hyp A),
    map_hyp f (substh s h) = substh (map_sub f s) (map_hyp f h).
Proof.
intros A B f s h.
cases h; intros; simpsub; simpmap; auto.
Qed.


Lemma map_substctx :
  forall A B (f : A -> B) (s : sub) (G : @context A),
    map_ctx f (substctx s G) = substctx (map_sub f s) (map_ctx f G).
Proof.
intros A B f s G.
induct G; auto.
intros h G IH.
cbn.
f_equal; auto.
rewrite -> map_substh.
simpmap.
rewrite -> length_map_ctx.
reflexivity.
Qed.


Lemma map_substj :
  forall A B (f : A -> B) (s : sub) (J : @judgement A),
    map_jud f (substj s J) = substj (map_sub f s) (map_jud f J).
Proof.
intros A B f s J.
destruct J as [m n a].
simpmap; simpsub.
simpmap.
reflexivity.
Qed.


Hint Rewrite map_substh map_substctx map_substj : map.


Lemma map_hygiene :
  forall A B (f : A -> B) P (m : term A),
    hygiene P m
    -> hygiene P (map_term f m).
Proof.
intros A B f P m Hcl.
induct Hcl
  using (fun X => hygiene_mut_ind _ X
           (fun P a r => hygiene_row P (map_row f r))).

(* var *)
{
intros P i H.
apply hygiene_var; auto.
}

(* oper *)
{
intros P a th r _ IH.
*cbn.
apply hygiene_oper; auto.
}

(* nil *)
{
intros; apply hygiene_nil.
}

(* cons *)
{
intros P i a m r _ IH1 _ IH2.
cbn.
apply hygiene_cons; auto.
}
Qed.


Lemma map_hygiene_conv :
  forall A B (f : A -> B) P (m : term A),
    hygiene P (map_term f m)
    -> hygiene P m.
Proof.
intros A B f P m Hcl.
remember (map_term f m) as m' eqn:Heq.
revert m Heq.
induct Hcl
  using (fun X => hygiene_mut_ind _ X
           (fun P a r' => forall r, r' = map_row f r -> hygiene_row P r)).
Proof.

(* var *)
{
intros P i H m.
cases m.
2:{
  intros; discriminate.
  }
intros ? Heq.
cbn in Heq.
injection Heq.
intros <-.
apply hygiene_var; auto.
}

(* oper *)
{
intros P a' th' r' _ IH m.
cases m.
  {
  intros; discriminate.
  }
intros a th r Heq.
cbn in Heq.
injection Heq.
intros H1 H2 <-.
injectionT H1.
intros ->.
injectionT H2.
intros ->.
apply hygiene_oper; auto.
}

(* nil *)
{
intros P r.
cases r.
intros _.
apply hygiene_nil.
}

(* cons *)
{
intros P i' a' m' r' _ IH1 _ IH2 r.
cases r.
intros i a m r Heq Heq'.
injection Heq.
intros <- <-.
so (proof_irrelevance _ Heq (eq_refl _)); subst Heq.
cbn in Heq'.
injection Heq'.
intros H ->.
injectionT H.
intros ->.
apply hygiene_cons; auto.
}
Qed.


Lemma map_hygieneh :
  forall A B (f : A -> B) P (h : @hyp A),
    hygieneh P h
    -> hygieneh P (map_hyp f h).
Proof.
intros A B f P h H.
cases H; intros; simpmap;
[apply hygieneh_tpl | apply hygieneh_tp | apply hygieneh_tml | apply hygieneh_tm | apply hygieneh_emp]; auto using map_hygiene.
Qed.


Lemma map_hygieneh_conv :
  forall A B (f : A -> B) P (h : @hyp A),
    hygieneh P (map_hyp f h)
    -> hygieneh P h.
Proof.
intros A B f P h H.
revert H.
cases h; intros; [apply hygieneh_tpl | apply hygieneh_tp | apply hygieneh_tml | apply hygieneh_tm | apply hygieneh_emp].
  {
  simpmapin H.
  invert H.
  eauto using map_hygiene_conv.
  }

  {
  simpmapin H.
  invert H.
  eauto using map_hygiene_conv.
  }
Qed.


Lemma map_term_sh1_under_form :
  forall A B i (f : A -> B) (m : term A) (n : term B),
    map_term f m = subst (under i sh1) n
    -> exists m',
         m = subst (under i sh1) m'
         /\ n = map_term f m'.
Proof.
intros A B i f m n Heq.
assert (hygiene (fun j => j <> i) (subst (under i sh1) n)) as Hhyg.
  {
  eapply hygiene_shift_under'.
  refine (hygiene_weaken _#4 _ (hygiene_okay _ _)).
  intros x _.
  omega.
  }
rewrite <- Heq in Hhyg.
so (map_hygiene_conv _#5 Hhyg) as Hhyg'.
so (subst_into_absent_single _#3 unittp Hhyg') as Heq'.
simpsubin Heq'.
exists (subst (under i (dot unittp id)) m).
split.
  {
  rewrite <- subst_compose.
  rewrite <- compose_under.
  simpsub.
  auto.
  }

  {
  so (f_equal (fun z => subst (under i (dot unittp id)) z) Heq) as Heq''.
  cbn in Heq''.
  rewrite <- subst_compose in Heq''.
  rewrite <- compose_under in Heq''.
  simpsubin Heq''.  
  rewrite <- Heq''.
  rewrite -> map_subst.
  simpmap.
  reflexivity.
  }
Qed.


Lemma map_term_sh1_form :
  forall A B (f : A -> B) (m : term A) (n : term B),
    map_term f m = subst sh1 n
    -> exists m',
         m = subst sh1 m'
         /\ n = map_term f m'.
Proof.
intros A B f m n H.
apply (map_term_sh1_under_form A B 0 f m n); auto.
Qed.


Lemma map_term_sh_form :
  forall A B i (f : A -> B) (m : term A) (n : term B),
    map_term f m = subst (sh i) n
    -> exists m',
         m = subst (sh i) m'
         /\ n = map_term f m'.
Proof.
intros A B i f m n H.
revert m n H.
induct i.

(* 0 *)
{
intros m n H.
simpsubin H.
subst n.
exists m.
split; auto.
simpsub; auto.
}

(* S *)
{
intros i IH m n Heq.
replace (S i) with (i + 1) in Heq by omega.
rewrite <- compose_sh_sh in Heq.
rewrite -> subst_compose in Heq.
so (map_term_sh1_form _#5 Heq) as (m' & -> & Heq').
symmetry in Heq'.
so (IH _ _ Heq') as (m'' & -> & Heq'').
exists m''.
split; auto.
simpsub.
replace (i + 1) with (S i) by omega.
reflexivity.
}
Qed.


Definition inverses {A B : Type} (f : B -> A) (g : A -> B) : Prop
  :=
  forall x, f (g x) = x.


Definition injective {A B : Type} (f : A -> B) : Prop
  :=
  forall x y, f x = f y -> x = y.


Lemma inverses_impl_injective :
  forall A B f g,
    @inverses A B f g
    -> injective g.
Proof.
intros A B f g Hinv x y Heq.
so (f_equal f Heq) as Heq'.
rewrite -> !Hinv in Heq'.
auto.
Qed.


Lemma map_operator_inv :
  forall A B f g,
    @inverses A B f g
    -> forall a, inverses (@map_operator _ _ f a) (@map_operator _ _ g a).
Proof.
intros A B f g Hinv a th.
cases th; try (intros; auto; done).

(* ext *)
{
intros a.
cbn.
rewrite -> Hinv.
reflexivity.
}

(* extt *)
{
intros a.
cbn.
rewrite -> Hinv.
reflexivity.
}
Qed.


Lemma map_operator_inj :
  forall A B (f : A -> B),
    injective f
    -> forall a, injective (@map_operator _ _ f a).
Proof.
intros A B f Hinj a th th' Heq.
set (a' := a) in th'.
assert (eq_dep _ (operator B) a (map_operator f th) a' (@map_operator _ _ f a' th')) as Heq'.
  {
  apply eq_impl_eq_dep_snd; auto.
  }
cut (eq_dep _ (operator A) a th a' th').
  {
  apply eq_dep_impl_eq_snd; auto.
  }
renameover Heq' into Heq.
assert (a = a') as Heqa by reflexivity.
clearbody a'.
revert Heqa Heq.
cases th; cases th';
try (intros; discriminate Heqa);
try (intros; so (eq_dep_impl_eq_snd _#5 Heq) as Heqth; discriminate Heqth);
try (intros; apply eq_dep_refl; done);
try (intros; apply eq_impl_eq_dep_snd; f_equal; cbn in Heq; injection (eq_dep_impl_eq_snd _#5 Heq); auto; done).
Qed.


Lemma map_term_inv :
  forall A B f g,
    @inverses A B f g
    -> inverses (map_term f) (map_term g).
Proof.
intros A B f g Hinv m.
induct m using
  (fun z => term_mut_ind _ z
     (fun a r => map_row f (map_row g r) = r)); auto.

(* oper *)
{
intros a th r IH.
cbn.
rewrite -> map_operator_inv; auto.
rewrite -> IH.
reflexivity.
}

(* cons *)
{
intros i a m IH1 r IH2.
cbn.
rewrite -> IH2.
rewrite -> IH1.
reflexivity.
}
Qed.


Lemma map_term_inj :
  forall A B (f : A -> B),
    injective f
    -> injective (map_term f).
Proof.
intros A B f Hinj m n Heq.
revert n Heq.
induct m using
  (fun z => term_mut_ind _ z
     (fun a r => forall s, map_row f r = map_row f s -> r = s)).

(* var *)
{
intros i n Heq.
destruct n as [j |]; cbn in Heq; [| discriminate Heq].
injection Heq.
auto.
}

(* oper *)
{
intros a th r IH n Heq.
destruct n as [| a' th' r']; cbn in Heq; [discriminate Heq |].
injection Heq.
intros H1 H2 <-.
injectionT H1.
injectionT H2.
intros Heqth Heqr.
f_equal.
  {
  eapply map_operator_inj; eauto.
  }
apply IH; auto.
}

(* nil *)
{
intros s H.
so (row_nil_invert _ s); subst s.
reflexivity.
}

(* cons *)
{
intros i a m IH1 r IH2 s Heq.
so (row_cons_invert _#3 s) as (m' & r' & ->).
cbn in Heq.
injectionc Heq.
intros H Heqm.
injectionT H.
intros Heqr.
f_equal; auto.
}
Qed.


Lemma map_reduce :
  forall A B (f : A -> B) (m n : term A),
    reduce m n
    -> reduce (map_term f m) (map_term f n).
Proof.
intros A B f m n Hmn.
induct Hmn using
  (fun z => reduce_mut_ind _ z
     (fun a r s => reducer (map_row f r) (map_row f s)));
try (intros; cbn; eauto using reduce_var, reduce_oper, reducer_nil, reducer_cons; done).

(* tapp_beta *)
{
intros m m' n n' _ IH1 _ IH2.
simpmap.
apply reduce_app_beta; auto.
}

(* prev_beta *)
{
intros m m' _ IH.
simpmap.
apply reduce_prev_beta; auto.
}

(* bite_beta1 *)
{
intros n n' p _ IH.
simpmap.
apply reduce_bite_beta1; auto.
}

(* bite_beta2 *)
{
intros n n' p _ IH.
simpmap.
apply reduce_bite_beta2; auto.
}

(* ppi1_beta *)
{
intros m m' n _ IH.
simpmap.
apply reduce_ppi1_beta; auto.
}

(* ppi2_beta *)
{
intros m m' n _ IH.
simpmap.
apply reduce_ppi2_beta; auto.
}
Qed.


Lemma map_reduces :
  forall A B (f : A -> B) (m n : term A),
    star reduce m n
    -> star reduce (map_term f m) (map_term f n).
Proof.
intros A B f m n H.
eapply star_map; eauto using map_reduce.
Qed.


Lemma map_step :
  forall A B (f : A -> B) (m n : term A),
    step m n
    -> step (map_term f m) (map_term f n).
Proof.
intros A B f m n Hmn.
induct Hmn;
try (intros; simpmap; eauto using step_app1, step_app2, step_prev1, step_prev2, step_bite1, step_bite2, step_bite3, step_ppi11, step_ppi12, step_ppi21, step_ppi22; done).
Qed.


Lemma map_steps :
  forall A B (f : A -> B) (m n : term A),
    star step m n
    -> star step (map_term f m) (map_term f n).
Proof.
intros A B f m n H.
eapply star_map; eauto using map_step.
Qed.


Lemma map_eq_oper_invert :
  forall A B (f : A -> B) m a th r,
    map_term f m = oper a th r
    -> exists th' r',
         m = oper a th' r'
         /\ map_operator f th' = th
         /\ map_row f r' = r.
Proof.
intros A B f m a th r Heq.
destruct m as [n | a' th' r'].
  {
  cbn in Heq.
  discriminate Heq.
  }
cbn in Heq.
injection Heq.
intros Heqr Heqth ->.
exists th', r'.
so (existT_injection_2 _#5 Heqth).
subst th.
so (existT_injection_2 _#5 Heqr).
subst r.
auto.
Qed.


Lemma map_operator_same :
  forall A B (f : A -> B) a (th : operator A a) (th' : operator B a),
    map_operator f th = th'
    -> same_operator a a th th'.
Proof.
intros A B f a th' th Heqth.
revert th Heqth.
induct th';
try (intros;
     so (eq_impl_eq_dep _#6 (eq_refl _) Heqth) as Heq;
     clear Heqth;
     revert Heq;
     induct th;
     try (intros;
          injectionT Heq;
          intros; discriminate);
     intros;
     eauto with same_operator;
     so (eq_dep_impl_eq_snd _#5 Heq) as Heq';
     cbn in Heq';
     injection Heq';
     intros; subst;
     eauto with same_operator;
     done).
Qed.


Lemma map_eq_lam_invert :
  forall A B (f : A -> B) m l,
    map_term f m = lam l
    -> exists l',
         m = lam l'
         /\ map_term f l' = l.
Proof.
intros A B f m l Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr).
so (row_cons_invert _ 1 nil r) as (l' & r' & ->).
so (row_nil_invert _ r'); subst r'.
exists l'.
split.
  {
  unfold lam.
  f_equal.
  so (map_operator_same _#6 Heqth) as H.
  invert H.
  auto.
  }

  {
  cbn in Heqr.
  injection Heqr.
  auto.
  }
Qed.


Lemma map_eq_next_invert :
  forall A B (f : A -> B) m n,
    map_term f m = next n
    -> exists n',
         m = next n'
         /\ map_term f n' = n.
Proof.
intros A B f m n Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr).
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (n' & ->).
exists n'.
split.
  {
  unfold next.
  f_equal.
  so (map_operator_same _#6 Heqth) as H.
  invert H.
  auto.
  }

  {
  cbn in Heqr.
  injection Heqr.
  auto.
  }
Qed.


Lemma map_eq_prev_invert :
  forall A B (f : A -> B) m n,
    map_term f m = prev n
    -> exists n',
         m = prev n'
         /\ map_term f n' = n.
Proof.
intros A B f m n Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr).
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (n' & ->).
exists n'.
split.
  {
  unfold prev.
  f_equal.
  so (map_operator_same _#6 Heqth) as H.
  invert H.
  auto.
  }

  {
  cbn in Heqr.
  injection Heqr.
  auto.
  }
Qed.


Lemma map_eq_triv_invert :
  forall A B (f : A -> B) m,
    map_term f m = triv
    -> m = triv.
Proof.
intros A B f m Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & _).
unfold triv.
f_equal.
2:{
  so (row_nil_invert _ r); subst r.
  reflexivity.
  }
so (map_operator_same _#6 Heqth) as H.
invert H.
intros <-.
reflexivity.
Qed.


Lemma map_eq_bite_invert :
  forall A B (f : A -> B) m n p q,
    map_term f m = bite n p q
    -> exists n' p' q',
         m = bite n' p' q'
         /\ map_term f n' = n
         /\ map_term f p' = p
         /\ map_term f q' = q.
Proof.
intros A B f m n p q Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr).
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (n' & p' & q' & ->).
exists n', p', q'.
split.
  {
  unfold next.
  f_equal.
  so (map_operator_same _#6 Heqth) as H.
  invert H.
  intros <-.
  auto.
  }

  {
  cbn in Heqr.
  injection Heqr.
  auto.
  }
Qed.


Lemma map_eq_btrue_invert :
  forall A B (f : A -> B) m,
    map_term f m = btrue
    -> m = btrue.
Proof.
intros A B f m Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & _).
unfold btrue.
f_equal.
2:{
  so (row_nil_invert _ r); subst r.
  reflexivity.
  }
so (map_operator_same _#6 Heqth) as H.
invert H.
intros <-.
reflexivity.
Qed.


Lemma map_eq_bfalse_invert :
  forall A B (f : A -> B) m,
    map_term f m = bfalse
    -> m = bfalse.
Proof.
intros A B f m Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & _).
unfold bfalse.
f_equal.
2:{
  so (row_nil_invert _ r); subst r.
  reflexivity.
  }
so (map_operator_same _#6 Heqth) as H.
invert H.
intros <-.
reflexivity.
Qed.


Lemma map_eq_ppair_invert :
  forall A B (f : A -> B) m n p,
    map_term f m = ppair n p
    -> exists n' p',
         m = ppair n' p'
         /\ map_term f n' = n
         /\ map_term f p' = p.
Proof.
intros A B f m n p Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr).
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (n' & p' & ->).
exists n', p'.
split.
  {
  unfold next.
  f_equal.
  so (map_operator_same _#6 Heqth) as H.
  invert H.
  intros <-.
  auto.
  }

  {
  cbn in Heqr.
  injection Heqr.
  auto.
  }
Qed.


Lemma map_eq_ppi1_invert :
  forall A B (f : A -> B) m n,
    map_term f m = ppi1 n
    -> exists n',
         m = ppi1 n'
         /\ map_term f n' = n.
Proof.
intros A B f m n Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr).
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (n' & ->).
exists n'.
split.
  {
  unfold ppi1.
  f_equal.
  so (map_operator_same _#6 Heqth) as H.
  invert H.
  auto.
  }

  {
  cbn in Heqr.
  injection Heqr.
  auto.
  }
Qed.


Lemma map_eq_ppi2_invert :
  forall A B (f : A -> B) m n,
    map_term f m = ppi2 n
    -> exists n',
         m = ppi2 n'
         /\ map_term f n' = n.
Proof.
intros A B f m n Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr).
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (n' & ->).
exists n'.
split.
  {
  unfold ppi2.
  f_equal.
  so (map_operator_same _#6 Heqth) as H.
  invert H.
  auto.
  }

  {
  cbn in Heqr.
  injection Heqr.
  auto.
  }
Qed.


Lemma map_eq_ext_invert :
  forall A B (f : A -> B) m x,
    map_term f m = ext x
    -> exists y,
         m = ext y
         /\ f y = x.
Proof.
intros A B f m x Heq.
so (map_eq_oper_invert _#7 Heq) as (th & r & -> & Heqth & Heqr).
so (row_invert_auto _ _ r) as H; cbn in H.
subst r.
clear Heq Heqr.
revert Heqth.
cases th; try (intros; discriminate Heqth).
intros y Heq.
cbn in Heq.
injection Heq.
intros <-.
exists y; auto.
Qed.


Lemma map_step_form :
  forall A B (f : A -> B) (m : term A) (n : term B),
    step (map_term f m) n
    -> exists p,
         n = map_term f p
         /\ step m p.
Proof.
intros A B f m n H.
remember (map_term f m) as x eqn:Heqx.
revert m Heqx.
induct H.

(* tapp1 *)
{
intros m1 m1' m2 _ IH mm Heqx.
so (map_eq_oper_invert _#7 (eqsymm Heqx)) as (th & r & -> & Heqth & Heqr).
clear Heqx.
revert Heqth.
cases th; try (intros; discriminate Heqth).
intros _.
so (row_2_invert _#3 r) as (n1 & n2 & ->).
cbn in Heqr.
injectionc Heqr.
intros <- <-.
so (IH n1 (eq_refl _)) as (n1' & -> & Hstep).
exists (app n1' n2).
split.
  {
  simpmap.
  reflexivity.
  }

  {
  apply step_app1; auto.
  }
}

(* tapp2 *)
{
intros m1 m2 mm Heqx.
so (map_eq_oper_invert _#7 (eqsymm Heqx)) as (th & r & -> & Heqth & Heqr).
clear Heqx.
revert Heqth.
cases th; try (intros; discriminate Heqth).
intros _.
so (row_2_invert _#3 r) as (a & p' & ->).
cbn in Heqr.
injectionc Heqr.
intros <- Heqa.
so (map_eq_lam_invert _#5 Heqa) as (m' & -> & <-).
clear Heqa.
fold (app (lam m') p').
exists (subst1 p' m').
split.
  {
  simpmap.
  reflexivity.
  }

  {
  apply step_app2.
  }
}

(* prev1 *)
{
intros m m' _ IH mm Heq.
so (map_eq_prev_invert _#5 (eqsymm Heq)) as (n & -> & Hn).
so (IH _ (eqsymm Hn)) as (p & -> & Hp).
exists (prev p).
split; auto.
apply step_prev1; auto.
}

(* prev2 *)
{
intros m m' Heq.
so (map_eq_prev_invert _#5 (eqsymm Heq)) as (n & -> & Hn).
so (map_eq_next_invert _#5 Hn) as (p & -> & Hp).
exists p.
split; auto.
apply step_prev2.
}

(* bite1 *)
{
intros m1 m1' m2 m3 _ IH mm Heq.
so (map_eq_bite_invert _#7 (eqsymm Heq)) as (n & p & q & -> & Hn & Hp & Hq).
so (IH _ (eqsymm Hn)) as (n' & -> & Hn').
exists (bite n' p q).
split.
  {
  simpmap.
  f_equal; auto.
  }

  {
  apply step_bite1; auto.
  }
}

(* bite2 *)
{
intros m1 m2 mm Heq.
so (map_eq_bite_invert _#7 (eqsymm Heq)) as (n & p & q & -> & Hn & Hp & Hq).
so (map_eq_btrue_invert _#4 Hn); subst n.
exists p.
split; auto.
apply step_bite2.
}

(* bite3 *)
{
intros m1 m2 mm Heq.
so (map_eq_bite_invert _#7 (eqsymm Heq)) as (n & p & q & -> & Hn & Hp & Hq).
so (map_eq_bfalse_invert _#4 Hn); subst n.
exists q.
split; auto.
apply step_bite3.
}

(* ppi11 *)
{
intros m m' _ IH mm Heq.
so (map_eq_ppi1_invert _#5 (eqsymm Heq)) as (n & -> & Hn).
so (IH _ (eqsymm Hn)) as (p & -> & Hp).
exists (ppi1 p).
split; auto.
apply step_ppi11; auto.
}

(* ppi12 *)
{
intros m m' mm Heq.
so (map_eq_ppi1_invert _#5 (eqsymm Heq)) as (n & -> & Hn).
so (map_eq_ppair_invert _#6 Hn) as (p & q & -> & Hp & Hq).
exists p.
split; auto.
apply step_ppi12.
}

(* ppi21 *)
{
intros m m' _ IH mm Heq.
so (map_eq_ppi2_invert _#5 (eqsymm Heq)) as (n & -> & Hn).
so (IH _ (eqsymm Hn)) as (p & -> & Hp).
exists (ppi2 p).
split; auto.
apply step_ppi21; auto.
}

(* ppi22 *)
{
intros m m' mm Heq.
so (map_eq_ppi2_invert _#5 (eqsymm Heq)) as (n & -> & Hn).
so (map_eq_ppair_invert _#6 Hn) as (p & q & -> & Hp & Hq).
exists q.
split; auto.
apply step_ppi22.
}
Qed.


Lemma map_steps_form :
  forall A B (f : A -> B) (m : term A) (n : term B),
    star step (map_term f m) n
    -> exists p,
         n = map_term f p
         /\ star step m p.
Proof.
intros A B f m n H.
remember (map_term f m) as x eqn:Heqx.
revert m Heqx.
induct H.

(* refl *)
{
intros x m ->.
exists m.
auto using star_refl.
}

(* step *)
{
intros m n p Hmn _ IH m' ->.
so (map_step_form _#5 Hmn) as (n' & -> & Hmn').
so (IH n' (eq_refl _)) as (p' & -> & Hnp').
exists p'.
split; auto.
eapply star_step; eauto.
}
Qed.


Lemma map_reduce_form :
  forall A B (f : A -> B) (m : term A) (n : term B),
    reduce (map_term f m) n
    -> exists p,
         n = map_term f p
         /\ reduce m p.
Proof.
intros A B f m n H.
remember (map_term f m) as x eqn:Heqx.
revert m Heqx.
induct H using
  (fun z => reduce_mut_ind _ z
     (fun a r s => forall r', r = map_row f r' -> exists s', s = map_row f s' /\ reducer r' s')).

(* var *)
{
intros i m.
cases m; try (intros; discriminate Heqx).
intros j Heq.
rewrite -> map_var in Heq.
injection Heq.
intros <-.
exists (var i).
split; auto.
apply reduce_var.
}

(* oper *)
{
intros a th r s _ IH m.
cases m; try (intros; discriminate Heqx).
intros a' th' r' Heq.
cbn in Heq.
injection Heq.
intros Heqr Heqth <-.
so (existT_injection_2 _#5 Heqth); subst th.
so (existT_injection_2 _#5 Heqr); subst r.
clear Heq Heqr Heqth.
so (IH _ (eq_refl _)) as (s' & -> & Hrs).
exists (oper a th' s').
split; auto.
apply reduce_oper; auto.
}

(* tapp_beta *)
{
intros m n p q Hmn IH1 Hpq IH2 x Heqx.
so (map_eq_oper_invert _#7 (eqsymm Heqx)) as (th & r & -> & Heqth & Heqr).
clear Heqx.
revert Heqth.
cases th; try (intros; discriminate Heqth).
intros _.
so (row_2_invert _#3 r) as (a & p' & ->).
cbn in Heqr.
injectionc Heqr.
intros <- Heqa.
so (map_eq_lam_invert _#5 Heqa) as (m' & -> & <-).
clear Heqa.
fold (app (lam m') p').
so (IH1 _ (eq_refl _)) as (n' & -> & Hmn').
so (IH2 _ (eq_refl _)) as (q' & -> & Hpq').
exists (subst1 q' n').
split.
  {
  symmetry.
  apply map_subst.
  }

  {
  apply reduce_app_beta; auto.
  }
}

(* prev_beta *)
{
intros m n Hmn IH x Heqx.
so (map_eq_prev_invert _#5 (eqsymm Heqx)) as (y & -> & Heqy).
so (map_eq_next_invert _#5 Heqy) as (p & -> & Hp).
so (IH _ (eqsymm Hp)) as (q & -> & Hq).
exists q.
split; auto.
apply reduce_prev_beta; auto.
}

(* bite_beta1 *)
{
intros m1 m1' m2 _ IH m Heqx.
so (map_eq_bite_invert _#7 (eqsymm Heqx)) as (n & p & q & -> & Hn & Hp & Hq).
so (map_eq_btrue_invert _#4 Hn); subst n.
so (IH _ (eqsymm Hp)) as (p' & -> & Hp').
exists p'.
split; auto.
apply reduce_bite_beta1; auto.
}

(* bite_beta2 *)
{
intros m1 m1' m2 _ IH m Heqx.
so (map_eq_bite_invert _#7 (eqsymm Heqx)) as (n & p & q & -> & Hn & Hp & Hq).
so (map_eq_bfalse_invert _#4 Hn); subst n.
so (IH _ (eqsymm Hq)) as (q' & -> & Hq').
exists q'.
split; auto.
apply reduce_bite_beta2; auto.
}

(* ppi1_beta *)
{
intros m1 m1' m2 _ IH x Heqx.
so (map_eq_ppi1_invert _#5 (eqsymm Heqx)) as (n & -> & Hn).
so (map_eq_ppair_invert _#6 Hn) as (p & q & -> & Hp & Hq).
so (IH _ (eqsymm Hp)) as (p' & -> & Hp').
exists p'.
split; auto.
apply reduce_ppi1_beta; auto.
}

(* ppi2_beta *)
{
intros m1 m1' m2 _ IH x Heqx.
so (map_eq_ppi2_invert _#5 (eqsymm Heqx)) as (n & -> & Hn).
so (map_eq_ppair_invert _#6 Hn) as (p & q & -> & Hp & Hq).
so (IH _ (eqsymm Hq)) as (p' & -> & Hp').
exists p'.
split; auto.
apply reduce_ppi2_beta; auto.
}

(* nil *)
{
intros r' H.
so (row_nil_invert _ r'); subst r'.
exists rw_nil.
auto using reducer_nil.
}

(* cons *)
{
intros i a m n r s Hmn IH1 Hrs IH2 x Heq.
so (row_cons_invert _#3 x) as (m' & r' & ->).
cbn in Heq.
injectionc Heq.
intros Heqr ->.
injectionT Heqr.
intros ->.
so (IH1 _ (eq_refl _)) as (n' & -> & Hmn').
so (IH2 _ (eq_refl _)) as (s' & -> & Hrs').
exists (rw_cons n' s').
split; eauto using reducer_cons.
}
Qed.


Lemma map_reduces_form :
  forall A B (f : A -> B) (m : term A) (n : term B),
    star reduce (map_term f m) n
    -> exists p,
         n = map_term f p
         /\ star reduce m p.
Proof.
intros A B f m n H.
remember (map_term f m) as x eqn:Heqx.
revert m Heqx.
induct H.

(* refl *)
{
intros x m ->.
exists m.
auto using star_refl.
}

(* step *)
{
intros m n p Hmn _ IH m' ->.
so (map_reduce_form _#5 Hmn) as (n' & -> & Hmn').
so (IH n' (eq_refl _)) as (p' & -> & Hnp').
exists p'.
split; auto.
eapply star_step; eauto.
}
Qed.


Lemma map_equiv :
  forall A B (f : A -> B) (m n : term A),
    equiv m n
    -> equiv (map_term f m) (map_term f n).
Proof.
intros A B f m n H.
eapply (star_map _ _ _ _ (map_term f)); eauto.
clear m n H.
intros m n H.
destruct H; eauto using map_reduce.
Qed.


Lemma map_equivh :
  forall A B (f : A -> B) (h h' : @hyp A),
    equivh h h'
    -> equivh (map_hyp f h) (map_hyp f h').
Proof.
intros A B f h h' Hequiv.
cases Hequiv;
intros;
simpmap;
[apply equivh_tpl | apply equivh_tp | apply equivh_tml | apply equivh_tm | apply equivh_emp]; apply map_equiv; auto.
Qed.


Lemma map_equiv_conv :
  forall A B (f : A -> B) (m n : term A),
    injective f
    -> equiv (map_term f m) (map_term f n)
    -> equiv m n.
Proof.
intros A B f m n Hinj H.
so (church_rosser _#3 H) as (p & Hmp & Hnp).
so (map_reduces_form _#5 Hmp) as (p' & -> & Hmp').
so (map_reduces_form _#5 Hnp) as (p'' & Heq & Hnp').
so (map_term_inj _#3 Hinj _ _ Heq); subst p''.
eapply equiv_trans.
  {
  apply reduces_equiv; eauto.
  }

  {
  apply equiv_symm.
  apply reduces_equiv; auto.
  }
Qed.


Lemma map_term_equiv_inj :
  forall A B (f : A -> B),
    injective f
    -> forall (m n : term A),
         equiv (map_term f m) (map_term f n)
         -> equiv m n.
Proof.
intros v w h m n Heq.
eapply map_equiv_conv; eauto.
Qed.


Lemma map_closub :
  forall A B (f : A -> B) P (s : @sub A),
    closub P s
    -> closub P (map_sub f s).
Proof.
intros A B f P s Hcl.
intros j Hj.
rewrite <- map_project.
apply map_hygiene.
eapply Hcl; eauto.
Qed.


Lemma map_operator_compose :
  forall (A B C : Type) (f : B -> C) (g : A -> B) a (th : @operator A a),
    map_operator f (map_operator g th)
    =
    map_operator (fun z => f (g z)) th.
Proof.
intros A B C f g a th.
case th; reflexivity.
Qed.


Lemma map_term_and_row_compose :
  forall (A B C : Type) (f : B -> C) (g : A -> B),
    (forall (m : term A),
       map_term f (map_term g m)
       =
       map_term (fun z => f (g z)) m)
    /\
    (forall a (r : @row A a),
       map_row f (map_row g r)
       =
       map_row (fun z => f (g z)) r).
Proof.
intros A B C f g.
exploit (syntax_ind A
           (fun m =>
              map_term f (map_term g m)
              =
              map_term (fun z => f (g z)) m)
           (fun a r =>
              map_row f (map_row g r)
              =
              map_row (fun z => f (g z)) r)) as Hprop;
  intros; cbn; f_equal; eauto using map_operator_compose.
Qed.


Lemma map_term_compose :
  forall (A B C : Type) (f : B -> C) (g : A -> B) (m : term A),
    map_term f (map_term g m)
    =
    map_term (fun z => f (g z)) m.
Proof.
intros A B C f g.
exact (map_term_and_row_compose _#5 andel).
Qed.


Lemma map_sub_compose :
  forall (A B C : Type) (f : B -> C) (g : A -> B) (s : @sub A),
    map_sub f (map_sub g s)
    =
    map_sub (fun z => f (g z)) s.
Proof.
intros A B C f g s.
induct s; auto.
(* dot *)
{
intros m s IH.
cbn.
f_equal; auto.
apply map_term_compose.
}
Qed.


Lemma map_operator_id :
  forall A a (th : @operator A a),
    map_operator (fun z => z) th = th.
Proof.
intros A a th.
case th; reflexivity.
Qed.


Lemma map_term_and_row_id :
  forall (A : Type),
    (forall (m : term A), map_term (fun z => z) m = m)
    /\
    (forall a (r : @row A a), map_row (fun z => z) r = r).
Proof.
intros A.
exploit
  (syntax_ind A
     (fun m => map_term (fun z => z) m = m)
     (fun a r => map_row (fun z => z) r = r)) as Hprop;
  intros; cbn; f_equal; eauto using map_operator_id.
Qed.


Lemma map_term_id :
  forall (A : Type) (m : term A),
    map_term (fun z => z) m = m.
Proof.
intro A.
exact (map_term_and_row_id _ andel).
Qed.


Lemma map_sub_id :
  forall (A : Type) (s : @sub A),
    map_sub (fun z => z) s = s.
Proof.
intros A s.
induct s; auto.
intros m s IH.
cbn.
rewrite -> map_term_id.
f_equal; auto.
Qed.


Lemma map_value :
  forall A B (f : A -> B) m,
    value m
    -> value (map_term f m).
Proof.
intros A B f m H.
invertc H.
intros a th r Hcanon <-.
cbn.
apply value_i.
clear r.
cases Hcanon; intros; cbn; auto using canon.
Qed.
