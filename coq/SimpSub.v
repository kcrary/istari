
Require Import Coq.Lists.List.

Require Import Tactics.
Require Export Syntax.
Require Export Subst.


Section object.


Arguments operator {object}.
Arguments term {object}.
Arguments row {object}.


Variable object : Type.


Definition substr (s : sub) {a : list nat} (r : row a) : row a :=
  traverse_row object
    (fun i j =>
       if lt_dec j i then
         var j
       else
         shift i (project s (j-i)))
  0 a r.


Lemma subst_oper :
  forall s a t r, subst s (oper a t r) = oper a t (substr s r).
Proof.
simpsub.
prove_subst.
Qed.


Lemma substr_nil :
  forall s, substr s rw_nil = rw_nil.
Proof.
prove_subst.
Qed.


Lemma substr_cons :
  forall s i a m r, substr s (rw_cons i a m r) = rw_cons i a (subst (under i s) m) (substr s r).
Proof.
intros s i a m r.
unfold subst, substr.
cbn.
f_equal.
replace (i + 0) with i by omega.
fold (traverse object (fun i0 j => if lt_dec j i0 then var j else shift i0 (project s (j - i0))) i m).
rewrite -> !traverse_under; [].
rewrite -> under_zero.
reflexivity.
Qed.


Lemma substr_compose :
  forall s s' a (r : row a),
    substr (compose s s') r = substr s' (substr s r).
Proof.
intros s s' a r.
induct r.

(* nil *) -
rewrite -> !substr_nil; [].
reflexivity.

(* cons *) -
intros i a t r IH.
rewrite -> !substr_cons; [].
f_equal; auto; [].
rewrite -> compose_under; [].
rewrite -> subst_compose; [].
reflexivity.
Qed.


Hint Rewrite subst_oper substr_nil substr_cons : subst.
Hint Rewrite <- substr_compose : subst.


Lemma subst_univ :
  forall (s : @sub object) m, subst s (univ m) = univ (subst s m).
Proof.
prove_subst.
Qed.


Lemma subst_cty :
  forall (s : @sub object) m, subst s (cty m) = cty (subst s m).
Proof.
prove_subst.
Qed.


Lemma subst_con :
  forall (s : @sub object) m1 m2, subst s (con m1 m2) = con (subst s m1) (subst s m2).
Proof.
prove_subst.
Qed.


Lemma subst_karrow :
  forall (s : @sub object) m1 m2, subst s (karrow m1 m2) = karrow (subst s m1) (subst s m2).
Proof.
prove_subst.
Qed.


Lemma subst_tarrow :
  forall (s : @sub object) m1 m2, subst s (tarrow m1 m2) = tarrow (subst s m1) (subst s m2).
Proof.
prove_subst.
Qed.


Lemma subst_pi :
  forall (s : @sub object) m1 m2, subst s (pi m1 m2) = pi (subst s m1) (subst (under 1 s) m2).
Proof.
prove_subst.
Qed.


Lemma subst_clam :
  forall (s : @sub object) k a, subst s (clam k a) = clam (subst s k) (subst (under 1 s) a).
Proof.
prove_subst.
Qed.


Lemma subst_capp :
  forall (s : @sub object) m1 m2, subst s (capp m1 m2) = capp (subst s m1) (subst s m2).
Proof.
prove_subst.
Qed.


Lemma subst_ctlam :
  forall (s : @sub object) a b k, subst s (ctlam a b k) = ctlam (subst s a) (subst (under 1 s) b) (subst s k).
Proof.
prove_subst.
Qed.


Lemma subst_ctapp :
  forall (s : @sub object) m1 m2, subst s (ctapp m1 m2) = ctapp (subst s m1) (subst s m2).
Proof.
prove_subst.
Qed.


Lemma subst_lam :
  forall (s : @sub object) m, subst s (lam m) = lam (subst (under 1 s) m).
Proof.
prove_subst.
Qed.


Lemma subst_app :
  forall (s : @sub object) m1 m2, subst s (app m1 m2) = app (subst s m1) (subst s m2).
Proof.
prove_subst.
Qed.


Lemma subst_intersect :
  forall (s : @sub object) m1 m2, subst s (intersect m1 m2) = intersect (subst s m1) (subst (under 1 s) m2).
Proof.
prove_subst.
Qed.


Lemma subst_union :
  forall (s : @sub object) m1 m2, subst s (union m1 m2) = union (subst s m1) (subst (under 1 s) m2).
Proof.
prove_subst.
Qed.


Lemma subst_constfn :
  forall (s : @sub object), subst s constfn = constfn.
Proof.
prove_subst.
Qed.


Lemma subst_fut :
  forall (s : @sub object) k, subst s (fut k) = fut (subst s k).
Proof.
prove_subst.
Qed.


Lemma subst_cnext :
  forall (s : @sub object) a, subst s (cnext a) = cnext (subst s a).
Proof.
prove_subst.
Qed.


Lemma subst_cprev :
  forall (s : @sub object) a, subst s (cprev a) = cprev (subst s a).
Proof.
prove_subst.
Qed.


Lemma subst_next :
  forall (s : @sub object) a, subst s (next a) = next (subst s a).
Proof.
prove_subst.
Qed.


Lemma subst_prev :
  forall (s : @sub object) a, subst s (prev a) = prev (subst s a).
Proof.
prove_subst.
Qed.


Lemma subst_rec :
  forall (s : @sub object) k, subst s (rec k) = rec (subst (under 1 s) k).
Proof.
prove_subst.
Qed.


Lemma subst_equal :
  forall (s : @sub object) a m n, subst s (equal a m n) = equal (subst s a) (subst s m) (subst s n).
Proof.
prove_subst.
Qed.


Lemma subst_triv :
  forall (s : @sub object), subst s triv = triv.
Proof.
prove_subst.
Qed.


Lemma subst_eqtype :
  forall (s : @sub object) m1 m2, subst s (eqtype m1 m2) = eqtype (subst s m1) (subst s m2).
Proof.
prove_subst.
Qed.


Lemma subst_sequal :
  forall (s : @sub object) m1 m2, subst s (sequal m1 m2) = sequal (subst s m1) (subst s m2).
Proof.
prove_subst.
Qed.


Lemma subst_subtype :
  forall (s : @sub object) m1 m2, subst s (subtype m1 m2) = subtype (subst s m1) (subst s m2).
Proof.
prove_subst.
Qed.


Lemma subst_kind :
  forall (s : @sub object) m, subst s (kind m) = kind (subst s m).
Proof.
prove_subst.
Qed.


Lemma subst_all :
  forall (s : @sub object) m1 m2 m3, subst s (all m1 m2 m3) = all (subst s m1) (subst s m2) (subst (under 1 s) m3).
Proof.
prove_subst.
Qed.


Lemma subst_alltp :
  forall (s : @sub object) m1, subst s (alltp m1) = alltp (subst (under 1 s) m1).
Proof.
prove_subst.
Qed.


Lemma subst_exist :
  forall (s : @sub object) m1 m2 m3, subst s (exist m1 m2 m3) = exist (subst s m1) (subst s m2) (subst (under 1 s) m3).
Proof.
prove_subst.
Qed.


Lemma subst_mu :
  forall (s : @sub object) m, subst s (mu m) = mu (subst (under 1 s) m).
Proof.
prove_subst.
Qed.


Lemma subst_ispositive :
  forall (s : @sub object) m, subst s (ispositive m) = ispositive (subst (under 1 s) m).
Proof.
prove_subst.
Qed.


Lemma subst_isnegative :
  forall (s : @sub object) m, subst s (isnegative m) = isnegative (subst (under 1 s) m).
Proof.
prove_subst.
Qed.


Lemma subst_voidtp :
  forall (s : @sub object), subst s voidtp = voidtp.
Proof.
prove_subst.
Qed.


Lemma subst_unittp :
  forall (s : @sub object), subst s unittp = unittp.
Proof.
prove_subst.
Qed.


Lemma subst_cunit :
  forall (s : @sub object), subst s cunit = cunit.
Proof.
prove_subst.
Qed.


Lemma subst_booltp :
  forall (s : @sub object), subst s booltp = booltp.
Proof.
prove_subst.
Qed.


Lemma subst_btrue :
  forall (s : @sub object), subst s btrue = btrue.
Proof.
prove_subst.
Qed.


Lemma subst_bfalse :
  forall (s : @sub object), subst s bfalse = bfalse.
Proof.
prove_subst.
Qed.


Lemma subst_bite :
  forall (s : @sub object) a m n, subst s (bite a m n) = bite (subst s a) (subst s m) (subst s n).
Proof.
prove_subst.
Qed.


Lemma subst_prod :
  forall (s : @sub object) m1 m2, subst s (prod m1 m2) = prod (subst s m1) (subst s m2).
Proof.
prove_subst.
Qed.


Lemma subst_sigma :
  forall (s : @sub object) m1 m2, subst s (sigma m1 m2) = sigma (subst s m1) (subst (under 1 s) m2).
Proof.
prove_subst.
Qed.


Lemma subst_cpair :
  forall (s : @sub object) m1 m2, subst s (cpair m1 m2) = cpair (subst s m1) (subst s m2).
Proof.
prove_subst.
Qed.


Lemma subst_cpi1 :
  forall (s : @sub object) a, subst s (cpi1 a) = cpi1 (subst s a).
Proof.
prove_subst.
Qed.


Lemma subst_cpi2 :
  forall (s : @sub object) a, subst s (cpi2 a) = cpi2 (subst s a).
Proof.
prove_subst.
Qed.


Lemma subst_ppair :
  forall (s : @sub object) m1 m2, subst s (ppair m1 m2) = ppair (subst s m1) (subst s m2).
Proof.
prove_subst.
Qed.


Lemma subst_ppi1 :
  forall (s : @sub object) a, subst s (ppi1 a) = ppi1 (subst s a).
Proof.
prove_subst.
Qed.


Lemma subst_ppi2 :
  forall (s : @sub object) a, subst s (ppi2 a) = ppi2 (subst s a).
Proof.
prove_subst.
Qed.


Lemma subst_set :
  forall (s : @sub object) m1 m2, subst s (set m1 m2) = set (subst s m1) (subst (under 1 s) m2).
Proof.
prove_subst.
Qed.


Lemma subst_iset :
  forall (s : @sub object) m1 m2, subst s (iset m1 m2) = iset (subst s m1) (subst (under 1 s) m2).
Proof.
prove_subst.
Qed.


Lemma subst_quotient :
  forall (s : @sub object) m1 m2, subst s (quotient m1 m2) = quotient (subst s m1) (subst (under 2 s) m2).
Proof.
prove_subst.
Qed.


Lemma subst_guard :
  forall (s : @sub object) m1 m2, subst s (guard m1 m2) = guard (subst s m1) (subst s m2).
Proof.
prove_subst.
Qed.


Lemma subst_coguard :
  forall (s : @sub object) m1 m2, subst s (coguard m1 m2) = coguard (subst s m1) (subst s m2).
Proof.
prove_subst.
Qed.


Lemma subst_wt :
  forall (s : @sub object) m1 m2, subst s (wt m1 m2) = wt (subst s m1) (subst (under 1 s) m2).
Proof.
prove_subst.
Qed.


Lemma subst_partial :
  forall (s : @sub object) a, subst s (partial a) = partial (subst s a).
Proof.
prove_subst.
Qed.


Lemma subst_admiss :
  forall (s : @sub object) a, subst s (admiss a) = admiss (subst s a).
Proof.
prove_subst.
Qed.


Lemma subst_halts :
  forall (s : @sub object) m, subst s (halts m) = halts (subst s m).
Proof.
prove_subst.
Qed.


Lemma subst_uptype :
  forall (s : @sub object) a, subst s (uptype a) = uptype (subst s a).
Proof.
prove_subst.
Qed.


Lemma subst_seq :
  forall (s : @sub object) m1 m2, subst s (seq m1 m2) = seq (subst s m1) (subst (under 1 s) m2).
Proof.
prove_subst.
Qed.


Lemma subst_ext :
  forall (s : @sub object) x, subst s (ext x) = ext x.
Proof.
prove_subst.
Qed.


Lemma subst_extt :
  forall (s : @sub object) x, subst s (extt x) = extt x.
Proof.
prove_subst.
Qed.


Lemma subst_marker :
  forall (s : @sub object) x, subst s (marker x) = marker x.
Proof.
prove_subst.
Qed.


Hint Rewrite subst_univ subst_cty subst_con subst_karrow subst_tarrow subst_pi subst_clam subst_capp subst_ctlam subst_ctapp subst_lam subst_app subst_intersect subst_union subst_constfn subst_fut subst_cnext subst_cprev subst_next subst_prev subst_rec subst_equal subst_triv subst_eqtype subst_sequal subst_subtype subst_kind subst_all subst_alltp subst_exist subst_mu subst_ispositive subst_isnegative subst_voidtp subst_unittp subst_cunit subst_booltp subst_btrue subst_bfalse subst_bite subst_prod subst_sigma subst_cpair subst_cpi1 subst_cpi2 subst_ppair subst_ppi1 subst_ppi2 subst_set subst_iset subst_quotient subst_guard subst_coguard subst_wt subst_partial subst_halts subst_admiss subst_uptype subst_seq subst_ext subst_extt subst_marker : subst.


Definition substh s (h : @hyp object) :=
  (match h with
   | hyp_tpl => hyp_tpl
   | hyp_tp => hyp_tp
   | hyp_tml m => hyp_tml (subst s m)
   | hyp_tm m => hyp_tm (subst s m)
   | hyp_emp => hyp_emp
   end).


Lemma substh_tpl :
  forall (s : @sub object), substh s hyp_tpl = hyp_tpl.
Proof.
intros; reflexivity.
Qed.


Lemma substh_tp :
  forall (s : @sub object), substh s hyp_tp = hyp_tp.
Proof.
intros; reflexivity.
Qed.


Lemma substh_tml :
  forall (s : @sub object) m, substh s (hyp_tml m) = hyp_tml (subst s m).
Proof.
intros; reflexivity.
Qed.


Lemma substh_tm :
  forall (s : @sub object) m, substh s (hyp_tm m) = hyp_tm (subst s m).
Proof.
intros; reflexivity.
Qed.


Lemma substh_emp :
  forall (s : @sub object), substh s hyp_emp = hyp_emp.
Proof.
intros; reflexivity.
Qed.


Hint Rewrite substh_tpl substh_tp substh_tml substh_tm substh_emp : subst.


Lemma substh_id :
  forall h, substh id h = h.
Proof.
intro h.
destruct h; simpsub; f_equal; reflexivity.
Qed.


Lemma substh_under_id :
  forall i h,
    substh (under i id) h = h.
Proof.
intros i h.
cases h; intros; simpsub; reflexivity.
Qed.


Lemma substh_compose :
  forall s s' h, substh (compose s s') h = substh s' (substh s h).
Proof.
intros s s' h.
destruct h; simpsub; reflexivity.
Qed.


Hint Rewrite substh_id substh_under_id : subst.
Hint Rewrite <- substh_compose : subst.


Lemma substh_eqsub :
  forall s s' h,
    eqsub s s'
    -> substh s h = substh s' h.
Proof.
intros s s' h Heq.
cases h; intros; simpsub; f_equal; auto; apply subst_eqsub; auto.
Qed.


Definition substj (s : @sub object) (J : judgement) :=
  (match J with
   | deq m n a => deq (subst s m) (subst s n) (subst s a)
   end).


Lemma substj_deq :
  forall s m n a,
    substj s (deq m n a) = deq (subst s m) (subst s n) (subst s a).
Proof.
intros; reflexivity.
Qed.


Lemma substj_deqtype :
  forall (s : @sub object) a b,
    substj s (deqtype a b) = deqtype (subst s a) (subst s b).
Proof.
intros; reflexivity.
Qed.


Lemma substj_dsubtype :
  forall (s : @sub object) a b,
    substj s (dsubtype a b) = dsubtype (subst s a) (subst s b).
Proof.
intros; reflexivity.
Qed.


Hint Rewrite substj_deq substj_deqtype substj_dsubtype : subst.


Lemma substj_compose :
  forall s s' J,
    substj (compose s s') J = substj s' (substj s J).
Proof.
intros s s' J.
cases J; intros; simpsub; reflexivity.
Qed.


Lemma substj_id :
  forall J,
    substj id J = J.
Proof.
intros J.
cases J; intros; simpsub; reflexivity.
Qed.


Lemma substj_under_id :
  forall i J,
    substj (under i id) J = J.
Proof.
intros i J.
cases J; intros; simpsub; reflexivity.
Qed.


Lemma substj_eqsub :
  forall s s' (J : @judgement object),
    eqsub s s'
    -> substj s J = substj s' J.
Proof.
intros s s' J H.
destruct J as [m n a].
cbn.
rewrite -> !(subst_eqsub _ s s'); auto.
Qed.


Hint Rewrite <- substj_compose : subst.
Hint Rewrite -> substj_id substj_under_id : subst.


Fixpoint substctx (s : sub) (G : context) {struct G} :=
  match G with
  | nil => nil
  | cons h G' =>
      cons (substh (under (length G') s) h) (substctx s G')
  end.


Lemma substctx_nil :
  forall s,
    substctx s nil = nil.
Proof.
intros; reflexivity.
Qed.


Lemma substctx_cons :
  forall s h G,
    substctx s (cons h G) = cons (substh (under (length G) s) h) (substctx s G).
Proof.
intros; reflexivity.
Qed.


Lemma substctx_append :
  forall (s : @sub object) (G1 G2 : context),
    substctx s (G2 ++ G1) = substctx (under (length G1) s) G2 ++ substctx s G1.
Proof.
intros s G1 G2.
induct G2.

(* nil *)
{
cbn.
auto.
}

(* cons *)
{
intros h G IH.
cbn.
f_equal; auto.
rewrite -> under_sum.
rewrite -> app_length.
auto.
}
Qed.


Lemma substctx_id :
  forall G,
    substctx id G = G.
Proof.
intros G.
induct G; intros; cbn; simpsub; auto.
f_equal; auto.
Qed.


Lemma length_substctx :
  forall s G, length (substctx s G) = length G.
Proof.
intros s G.
induct G; intros; cbn; auto.
Qed.


Lemma substctx_compose :
  forall s s' G,
    substctx (compose s s') G = substctx s' (substctx s G).
Proof.
intros s s' G.
induct G.

(* nil *)
{ intros; reflexivity. }

(* cons *)
{
intros h G IH.
cbn.
rewrite -> length_substctx.
rewrite <- substh_compose.
rewrite <- compose_under.
rewrite -> IH.
reflexivity.
}
Qed.


Lemma substctx_eqsub :
  forall (s s' : sub) (G : @context object),
    eqsub s s'
    -> substctx s G = substctx s' G.
Proof.
intros s s' G Heq.
revert s s' Heq.
induct G.

(* nil *)
{
intros s s' Heq.
cbn.
reflexivity.
}

(* cons *)
{
intros h G IH s s' Heq.
cbn.
f_equal; auto.
apply substh_eqsub.
apply eqsub_under; auto.
}
Qed.


Hint Rewrite substctx_nil substctx_cons substctx_id : subst.
Hint Rewrite <- substctx_compose : subst.


Lemma subst_ite :
  forall (s : @sub object) (b : bool) m n, subst s (if b then m else n) = if b then subst s m else subst s n.
Proof.
intros s b m n.
destruct b; auto.
Qed.


Lemma subst_sumbool :
  forall A B (c : {A} + {B}) s (m n : @term object),
    subst s (if c then m else n) = if c then subst s m else subst s n.
Proof.
intros A B c s m n.
destruct c; auto.
Qed.


End object.


Arguments substr {object} s {a}.
Arguments substh {object}.
Arguments substj {object}.
Arguments substctx {object}.


(* Closing the section dumps all these, so put them back in. *)

Hint Rewrite subst_oper substr_nil substr_cons : subst.
Hint Rewrite <- substr_compose : subst.

Hint Rewrite subst_univ subst_cty subst_con subst_karrow subst_tarrow subst_pi subst_clam subst_capp subst_ctlam subst_ctapp subst_lam subst_app subst_intersect subst_union subst_constfn subst_fut subst_cnext subst_cprev subst_next subst_prev subst_rec subst_equal subst_triv subst_eqtype subst_sequal subst_subtype subst_kind subst_all subst_alltp subst_exist subst_mu subst_ispositive subst_isnegative subst_voidtp subst_unittp subst_cunit subst_booltp subst_btrue subst_bfalse subst_bite subst_prod subst_sigma subst_cpair subst_cpi1 subst_cpi2 subst_ppair subst_ppi1 subst_ppi2 subst_set subst_iset subst_quotient subst_guard subst_coguard subst_wt subst_partial subst_halts subst_admiss subst_uptype subst_seq subst_ext subst_extt subst_marker : subst.

Hint Rewrite substh_tpl substh_tp substh_tml substh_tm substh_emp : subst.

Hint Rewrite substh_id substh_under_id : subst.
Hint Rewrite <- substh_compose : subst.

Hint Rewrite substj_deq substj_deqtype substj_dsubtype : subst.

Hint Rewrite <- substj_compose : subst.
Hint Rewrite -> substj_id substj_under_id : subst.

Hint Rewrite substctx_nil substctx_cons substctx_id : subst.
Hint Rewrite <- substctx_compose : subst.

Hint Rewrite subst_ite subst_sumbool : subst.
