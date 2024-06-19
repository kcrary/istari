
Require Import Axioms.
Require Import Tactics.
Require Import Sigma.
Require Import Ordinal.
Require Import Syntax.
Require Import SimpSub.
Require Import Candidate.
Require Import Semantics.
Require Import System.
Require Import Model.
Require Import MapTerm.
Require Import Extend.
Require Import Ofe.
Require Import Urelsp.
Require Import Intensional.
Require Import SemanticsKnot.
Require Import Spaces.
Require Import Equality.
Require Import Truncate.
Require Import Uniform.
Require Import Standard.
Require Import Hygiene.
Require Import Relation.
Require Import Dynamic.
Require Import ExtendTruncate.
Require Import ProperDownward.

Require Import SemanticsPi.
Require Import SemanticsEqual.
Require Import SemanticsAll.
Require Import SemanticsExist.
Require Import SemanticsMu.
Require Import SemanticsUniv.
Require Import SemanticsFut.
Require Import SemanticsGuard.
Require Import SemanticsKind.
Require Import SemanticsQuotient.
Require Import SemanticsSet.
Require Import SemanticsSigma.
Require Import SemanticsSimple.
Require Import SemanticsSubtype.
Require Import SemanticsWtype.
Require Import SemanticsEqtype.
Require Import ExtSpace.
Require Import PreSpacify.
Require Import Reduction.
Require Import Equivalence.
Require Import ProperEquiv.
Require Import ProperClosed.
Require Import SemanticsPositive.
Require Import SemanticsPartial.
Require Import Approximation.



(* Not true for kinterp and cinterp. *)
Lemma interp_increase :
  forall pg pg' s i a X,
    le_page pg pg'
    -> interp pg s i a X
    -> interp pg' s i a X.
Proof.
exploit 
  (semantics_ind the_system
     (fun pg s i a X => True)
     (fun pg s i a X => True)
     (fun pg s i a X => forall pg', le_page pg pg' -> basicv the_system pg' s i a X)
     (fun pg s i a X => True)
     (fun pg s i a X => True)
     (fun pg s i a X => forall pg', le_page pg pg' -> basic the_system pg' s i a X)
     (fun pg s i A b B => forall pg', le_page pg pg' -> functional the_system pg' s i A b B))
  as Hind;
eauto 6 using le_ord_trans, lt_le_ord_trans, le_ord_refl, str_mono, cex_mono, cin_mono, upd_cin_mono, le_page_trans with semantics.

(* sequal *)
{
intros s i m n Hclm Hcln Hequiv pg' Hlt.
so (le_page_antisymm _ _ Hlt (toppg_max _)) as H.
subst pg'.
apply interp_sequal; auto.
}

(* kind *)
{
intros pg s i m gpg h Hlv Hlt pg' Hlt'.
apply interp_kind; auto.
eapply lt_le_page_trans; eauto.
}

(* wrapup *)
{
destruct Hind as (_ & _ & Hy & _).
intros; eapply Hy; eauto.
}
Qed.


Definition restrict_xobj (w : ordinal) (x : xobj stop) : xobj stop
  :=
  match x with
  | objnone => objnone

  | objsome Q h =>
      match lt_ord_dec (level (pi1 Q)) w with
      | left _ =>
          objsome Q h

      | right _ =>
          objnone
      end
  end.


Definition restrict (w : ordinal) (x : obj stop) : obj stop
  :=
  objin (restrict_xobj w (objout x)).


Definition restrict_term (w : ordinal) (m : wterm stop) : wterm stop
  :=
  map_term (restrict w) m.


Lemma restrict_extend :
  forall w m,
    restrict_term w m
    =
    map_term (extend w stop) (map_term (extend stop w) m).
Proof.
intros w m.
rewrite -> map_term_compose.
unfold restrict_term.
f_equal.
fextensionality 1.
intro x.
unfold restrict, extend, restrict_xobj, extend_xobj.
f_equal.
rewrite -> !objout_objin.
set (y := objout x).
destruct y as [Q h |]; auto.
set (X := lt_ord_dec (level (pi1 Q)) w).
destruct X as [Hlt | Hnlt]; auto.
rewrite -> (lt_ord_dec_is _ _ h).
reflexivity.
Qed.


Lemma restrict_ext :
  forall w x,
    restrict_term w (ext x) = ext (restrict w x).
Proof.
intros w x.
reflexivity.
Qed.


Lemma restrict_extt :
  forall w x,
    restrict_term w (extt x) = extt (restrict w x).
Proof.
intros w x.
reflexivity.
Qed.


(* Don't think we actually use this. *)
Lemma restrict_idem :
  forall w m, restrict_term w (restrict_term w m) = restrict_term w m.
Proof.
intros w m.
rewrite -> !restrict_extend.
(* We know perfectly well that we'll have w <<= stop, but writing it this way
   removes an annoying obligation.
*)
so (le_lt_ord_dec w stop) as [Hle | Hlt].
  {
  rewrite -> !(extend_term_cancel w stop); auto.
  }

  {
  rewrite -> !(extend_term_cancel stop w); auto using lt_ord_impl_le_ord.
  }
Qed.


Lemma extend_iurel_noncontractive :
  forall v w (h : v <<= w) n (A B : car (wiurel_ofe v)),
    @dist (wiurel_ofe w) n (extend_iurel h A) (extend_iurel h B)
    -> dist n A B.
Proof.
intros v w h n A B Hdist.
apply (dist_trans _ _ _ (iutruncate n A)).
  {
  apply dist_symm.
  apply iutruncate_near.
  }
apply (dist_trans _ _ _ (iutruncate n B)).
2:{
  apply iutruncate_near.
  }
apply dist_refl'.
apply (extend_iurel_inj _ _ h).
rewrite <- !iutruncate_extend_iurel.
apply iutruncate_collapse; auto.
Qed.


(* restriction w m n  means that n can be obtained from m by replacing
   objnones with objsomes at level at least w.

   They cannot be replaced with just objsome at any level, because we
   want the restrict_restriction property to hold.  More on why it
   works this way in the comment preceding semantics_restriction.  
*)

Inductive restriction (w : ordinal) : sterm -> sterm -> Prop :=
| restriction_var :
    forall i,
      restriction w (var i) (var i)

| restriction_oper :
    forall a th r s,
      restriction_row w a r s
      -> restriction w (oper a th r) (oper a th s)

| restriction_ext :
    forall Q h,
      w <<= level (pi1 Q)
      -> restriction w (ext (objin objnone)) (ext (objin (objsome Q h)))

| restriction_extt :
    forall Q h,
      w <<= level (pi1 Q)
      -> restriction w (extt (objin objnone)) (extt (objin (objsome Q h)))

with restriction_row (w : ordinal) : forall a, row (obj stop) a -> row (obj stop) a -> Prop :=
| restriction_nil :
    restriction_row w nil rw_nil rw_nil

| restriction_cons :
    forall j a m n r s,
      restriction w m n
      -> restriction_row w a r s
      -> restriction_row w (cons j a) (rw_cons m r) (rw_cons n s)
.


Scheme restriction_term_mut_ind := Minimality for restriction Sort Prop
with   restriction_row_mut_ind := Minimality for restriction_row Sort Prop.
Combined Scheme restriction_mut_ind from restriction_term_mut_ind, restriction_row_mut_ind.


Lemma restrict_restriction :
  forall w m n,
    restriction w m n
    -> map_term (extend stop w) m = map_term (extend stop w) n.
Proof.
intros w m n Hrest.
induct Hrest
  using (fun X => restriction_term_mut_ind w X
           (fun a r r' => map_row (extend stop w) r = map_row (extend stop w) r'));
auto.

(* oper *)
{
intros a th r s _ IH.
cbn.
f_equal.
apply IH.
}

(* ext *)
{
intros Q h Hwv.
cbn.
f_equal.
f_equal.
unfold extend.
rewrite -> !objout_objin.
f_equal.
cbn.
assert (~ level (pi1 Q) << w) as Hnlt.
  {
  intro H.
  apply (lt_ord_irrefl w).
  eapply le_lt_ord_trans; eauto.
  }
rewrite -> (lt_ord_dec_is_not _ _ Hnlt).
reflexivity.
}

(* extt *)
{
intros Q h Hwv.
cbn.
f_equal.
f_equal.
unfold extend.
rewrite -> !objout_objin.
f_equal.
cbn.
assert (~ level (pi1 Q) << w) as Hnlt.
  {
  intro H.
  apply (lt_ord_irrefl w).
  eapply le_lt_ord_trans; eauto.
  }
rewrite -> (lt_ord_dec_is_not _ _ Hnlt).
reflexivity.
}

(* cons *)
{
intros j a m n r s _ IH1 _ IH2.
cbn.
f_equal; auto.
}
Qed.


Lemma restrict_impl_restriction :
  forall w m,
    restriction w (restrict_term w m) m.
Proof.
intros w m.
pattern m.
apply (syntax_ind _ _ (fun a r => restriction_row w a (map_row (restrict w) r) r)); clear m;
eauto using restriction, restriction_row.
(* oper *)
intros a th r IH.
cbn.
revert r IH.
cases th; eauto using restriction_oper.

(* ext *)
intros x r Hr.
invertc Hr.
intros _ <-.
cbn.
rewrite <- (objin_objout _ x) at 2.
unfold restrict, restrict_xobj.
set (y := objout x).
destruct y as [Q h |].
  {
  set (X := lt_ord_dec (level (pi1 Q)) w).
  destruct X as [Hlt | Hnlt].
    {
    apply restriction_oper.
    apply restriction_nil.
    }

    {
    apply restriction_ext.
    apply not_lt_ord_impl_le_ord; auto.
    }
  }

  {
  apply restriction_oper.
  apply restriction_nil.
  }

(* extt *)
intros x r Hr.
invertc Hr.
intros _ <-.
cbn.
rewrite <- (objin_objout _ x) at 2.
unfold restrict, restrict_xobj.
set (y := objout x).
destruct y as [Q h |].
  {
  set (X := lt_ord_dec (level (pi1 Q)) w).
  destruct X as [Hlt | Hnlt].
    {
    apply restriction_oper.
    apply restriction_nil.
    }

    {
    apply restriction_extt.
    apply not_lt_ord_impl_le_ord; auto.
    }
  }

  {
  apply restriction_oper.
  apply restriction_nil.
  }
Qed.


Lemma restriction_decrease :
  forall v w m n, v <<= w -> restriction w m n -> restriction v m n.
Proof.
intros v w m n Hvw Hrest.
induct Hrest
  using (fun X => restriction_term_mut_ind w X
           (fun a r s => restriction_row v a r s)); 
eauto using restriction, restriction_row, le_ord_trans.
Qed.


(* This bobj stuff is pretty clumsy, but it allows us to reuse map_term results for restriction. *)

Inductive bobj w : Type :=
| bobj_some : forall (Q : candidate), option (w <<= level (pi1 Q)) -> level (pi1 Q) << stop -> bobj w

| bobj_none : bobj w
.


Definition bobj_left w (x : bobj w) : obj stop :=
  match x with
  | bobj_some _ Q op h =>
      objin (match op with
             | Some _ => objnone
             | None => objsome Q h
             end)
  | bobj_none _ => objin objnone
  end.


Definition bobj_right w (x : bobj w) : obj stop :=
  match x with
  | bobj_some _ Q _ h => objin (objsome Q h)

  | bobj_none _ => objin objnone
  end.


Definition bobj_in w (x : obj stop) : bobj w :=
  match objout x with
  | objsome Q h => bobj_some _ Q None h
  | objnone => bobj_none _
  end.


Lemma bobj_left_in :
  forall w x, bobj_left w (bobj_in w x) = x.
Proof.
intros w x.
rewrite <- (objin_objout _ x) at 2.
unfold bobj_left, bobj_in.
set (y := objout x).
destruct y as [Q h |]; auto.
Qed.


Lemma bobj_right_in :
  forall w x, bobj_right w (bobj_in w x) = x.
Proof.
intros w x.
rewrite <- (objin_objout _ x) at 2.
unfold bobj_right, bobj_in.
set (y := objout x).
destruct y as [Q h |]; auto.
Qed.


Lemma map_as_restriction :
  forall w m,
    restriction w (map_term (bobj_left w) m) (map_term (bobj_right w) m).
Proof.
intros w m.
induct m using
  (fun X => term_mut_ind _ X
     (fun a r => restriction_row w a (map_row (bobj_left w) r) (map_row (bobj_right w) r)));
eauto using restriction, restriction_row.
(* oper *)
intros a th r IH.
cbn.
revert r IH.
cases th; eauto using restriction_oper.

(* ext *)
{
intros x r _.
so (row_nil_invert _ r); subst r.
cbn.
destruct x as [Q op h |].
  {
  destruct op as [h' |].
    {
    cbn.
    apply restriction_ext; auto.
    }

    {
    cbn.
    apply restriction_oper.
    apply restriction_nil.
    }
  }

  {
  cbn.
  apply restriction_oper.
  apply restriction_nil.
  }
}

(* ext *)
{
intros x r _.
so (row_nil_invert _ r); subst r.
cbn.
destruct x as [Q op h |].
  {
  destruct op as [h' |].
    {
    cbn.
    apply restriction_extt; auto.
    }

    {
    cbn.
    apply restriction_oper.
    apply restriction_nil.
    }
  }

  {
  cbn.
  apply restriction_oper.
  apply restriction_nil.
  }
}
Qed.


Lemma restriction_as_map :
  forall w m n,
    restriction w m n
    -> exists (p : term (bobj w)),
         m = map_term (bobj_left w) p
         /\ n = map_term (bobj_right w) p.
Proof.
intros w m n H.
induct H
  using (fun X => restriction_term_mut_ind w X
           (fun a r s =>
              exists (t : row (bobj w) a),
                r = map_row (bobj_left w) t
                /\ s = map_row (bobj_right w) t)).

(* var *)
{
intro i.
exists (var i).
cbn.
auto.
}

(* oper *)
{
intros a th r s _ IH.
destruct IH as (t & -> & ->).
exists (oper a (map_operator (bobj_in w) th) t).
split.
  {
  cbn.
  rewrite -> map_operator_compose.
  f_equal.
  etransitivity.
    {
    symmetry.
    apply map_operator_id.
    }
  f_equal.
  fextensionality 1.
  intro x.
  symmetry.
  apply bobj_left_in.
  }

  {
  cbn.
  rewrite -> map_operator_compose.
  f_equal.
  etransitivity.
    {
    symmetry.
    apply map_operator_id.
    }
  f_equal.
  fextensionality 1.
  intro x.
  symmetry.
  apply bobj_right_in.
  }
}

(* ext *)
{
intros Q h h'.
exists (ext (bobj_some _ Q (Some h') h)).
cbn.
split; auto.
}

(* extt *)
{
intros Q h h'.
exists (extt (bobj_some _ Q (Some h') h)).
cbn.
split; auto.
}

(* nil *)
{
exists rw_nil.
auto.
}

(* cons *)
{
intros j a m n r s _ (p & -> & ->) _ (t & -> & ->).
exists (rw_cons p t).
auto.
}
Qed.   


Lemma restriction_refl :
  forall w m, restriction w m m.
Proof.
intros w m.
so (map_as_restriction _ (map_term (bobj_in w) m)) as H.
rewrite -> !map_term_compose in H.
force_exact H.
f_equal.
  {
  rewrite <- (map_term_id _ m) at 2.
  f_equal.
  fextensionality 1.
  intro x.
  apply bobj_left_in.
  }

  {
  rewrite <- (map_term_id _ m) at 2.
  f_equal.
  fextensionality 1.
  intro x.
  apply bobj_right_in.
  }
Qed.


Lemma restriction_hygiene :
  forall P w m n, restriction w m n -> hygiene P m -> hygiene P n.
Proof.
intros P w m n Hrest Hhyg.
so (restriction_as_map _#3 Hrest) as (p & -> & ->).
apply map_hygiene.
eapply map_hygiene_conv; eauto.
Qed.


Lemma restriction_subst :
  forall w s m m',
    restriction w m m'
    -> restriction w (subst s m) (subst s m').
Proof.
intros w s m n Hrest.
so (restriction_as_map _#3 Hrest) as (p & -> & ->).
replace s with (map_sub (bobj_left w) (map_sub (bobj_in w) s)) at 1.
2:{
  rewrite -> map_sub_compose.
  rewrite <- (map_sub_id _ s) at 2.
  f_equal.
  fextensionality 1.
  intro x.
  apply bobj_left_in.
  }
replace s with (map_sub (bobj_right w) (map_sub (bobj_in w) s)) at 2.
2:{
  rewrite -> map_sub_compose.
  rewrite <- (map_sub_id _ s) at 2.
  f_equal.
  fextensionality 1.
  intro x.
  apply bobj_right_in.
  }
rewrite <- !map_subst.
apply map_as_restriction.
Qed.


Lemma restriction_funct1_under :
  forall w i n n' m m',
    restriction w n n'
    -> restriction w m m'
    -> restriction w (subst (under i (dot n id)) m) (subst (under i (dot n' id)) m').
Proof.
intros w i n n' m m' Hrestn Hrestm.
so (restriction_as_map _#3 Hrestm) as (p & -> & ->).
so (restriction_as_map _#3 Hrestn) as (q & -> & ->).
replace (under i (dot (map_term (bobj_left w) q) id))
  with  (map_sub (bobj_left w) (under i (dot q id))).
2:{
  simpmap.
  reflexivity.
  }
replace (under i (dot (map_term (bobj_right w) q) id))
  with  (map_sub (bobj_right w) (under i (dot q id))).
2:{
  simpmap.
  reflexivity.
  }
rewrite <- !map_subst.
apply map_as_restriction.
Qed.


Lemma restriction_funct1 :
  forall w n n' m m',
    restriction w n n'
    -> restriction w m m'
    -> restriction w (subst1 n m) (subst1 n' m').
Proof.
intros w n n' m m' Hn Hm.
unfold subst1.
rewrite <- (under_zero _ (dot n id)).
rewrite <- (under_zero _ (dot n' id)).
apply restriction_funct1_under; auto.
Qed.


Lemma restriction_reduces :
  forall w m n p,
    restriction w m n
    -> star reduce m p
    -> exists q,
         restriction w p q
         /\ star reduce n q.
Proof.
intros w m n p Hrest Hsteps.
so (restriction_as_map _#3 Hrest) as (q & -> & ->).
so (map_reduces_form _#5 Hsteps) as (r & -> & Hreduces').
exists (map_term (bobj_right w) r).
split.
  {
  apply map_as_restriction.
  }

  {
  apply map_reduces; auto.
  }
Qed.


Lemma restriction_steps :
  forall w m n p,
    restriction w m n
    -> star step m p
    -> exists q,
         restriction w p q
         /\ star step n q.
Proof.
intros w m n p Hrest Hsteps.
so (restriction_as_map _#3 Hrest) as (q & -> & ->).
so (map_steps_form _#5 Hsteps) as (r & -> & Hsteps').
exists (map_term (bobj_right w) r).
split.
  {
  apply map_as_restriction.
  }

  {
  apply map_steps; auto.
  }
Qed.


Lemma restriction_sh1_form :
  forall w m n,
    restriction w (subst sh1 m) n
    -> exists n', n = subst sh1 n' /\ restriction w m n'.
Proof.
intros w m n Hrest.
so (restriction_as_map _#3 Hrest) as (p & Heq & ->).
symmetry in Heq.
so (map_term_sh1_form _#5 Heq) as (n & -> & ->).
exists (map_term (bobj_right w) n).
split.
  {
  rewrite -> map_subst.
  simpmap.
  reflexivity.
  }

  {
  apply map_as_restriction.
  }
Qed.


Lemma restriction_robust :
  forall w m n,
    restriction w m n
    -> robust 0 m <-> robust 0 n.
Proof.
intros w m n Hrest.
so (restriction_as_map _#3 Hrest) as (p & -> & ->).
split; intro H; apply map_robust; eapply map_robust_conv; eauto.
Qed.


Lemma restriction_positive :
  forall w m n,
    restriction w m n
    -> positive 0 m <-> positive 0 n.
Proof.
intros w m n Hrest.
so (restriction_as_map _#3 Hrest) as (p & -> & ->).
split; intro H; apply map_positive; eapply map_positive_conv; eauto.
Qed.


Lemma restriction_negative :
  forall w m n,
    restriction w m n
    -> negative 0 m <-> negative 0 n.
Proof.
intros w m n Hrest.
so (restriction_as_map _#3 Hrest) as (p & -> & ->).
split; intro H; apply map_negative; eapply map_negative_conv; eauto.
Qed.


(* The outer induction hypothesis. *)
Definition levind (w : ordinal) : Prop
  :=
  (forall pg s i a a' R,
     str pg << w
     -> cex pg <<= stop
     -> restriction (succ (cex pg)) a a'
     -> kinterp pg s i a R
     -> kinterp pg s i a' R)
  /\
  (forall pg s i a a' R,
     str pg << w
     -> cex pg <<= stop
     -> restriction (succ (cex pg)) a a'
     -> interp pg s i a R
     -> interp pg s i a' R)
  /\
  (forall pg s i a R v,
     str pg << w
     -> cex pg << v
     -> v <<= stop
     -> kinterp pg s i a R
     -> kinterp pg s i (restrict_term v a) R)
  /\
  (forall pg s i a R v,
     str pg << w
     -> cex pg << v
     -> v <<= stop
     -> interp pg s i a R
     -> interp pg s i (restrict_term v a) R).


Lemma levind_decrease :
  forall v w,
    v <<= w
    -> levind w
    -> levind v.
Proof.
intros v w Hvw H.
unfold levind in H.
destruct H as (IH1 & IH2 & IH3 & IH4).
do2 3 split.
  {
  intros pg s i a a' R Hstr Hcex Hrest Hint.
  eapply IH1; eauto using lt_le_ord_trans.
  }

  {
  intros pg s i a a' R Hstr Hcex Hrest Hint.
  eapply IH2; eauto using lt_le_ord_trans.
  }

  {
  intros pg s i a R u Hstr Hcex Hu Hint.
  eapply IH3; eauto using lt_le_ord_trans.
  }

  {
  intros pg s i a R u Hstr Hcex Hu Hint.
  eapply IH4; eauto using lt_le_ord_trans.
  }
Qed.


Lemma interp_kext_bound :
  forall pg i k K,
    interp_kext pg i k K
    -> level K <<= cin pg.
Proof.
intros pg i k K H.
destruct H as (Q & h & _ & _ & Hlev & <-).
eapply le_ord_trans; eauto.
apply approx_level.
Qed.


Lemma semantics_level_bound :
  (forall pg s i k K,
     kinterp pg s i k K
     -> level K <<= cin pg)
  /\
  (forall pg s i c Q,
     cinterp pg s i c Q
     -> level (pi1 Q) <<= cin pg).
Proof.
exploit
  (semantics_ind the_system
     (fun pg s i k K => level K <<= cin pg)
     (fun pg s i a Q => level (pi1 Q) <<= cin pg)
     (fun pg s i a R => True)
     (fun pg s i k K => level K <<= cin pg)
     (fun pg s i a Q => level (pi1 Q) <<= cin pg)
     (fun pg s i a R => True)
     (fun pg s i A b B => True))
  as Hind;
try (intros; cbn; eauto using max_ord_lub, le_ord_zero, le_ord_trans, le_ord_refl; done).

(* ext *)
{
intros pg s i Q h Hcin.
cbn.
eapply le_ord_trans; eauto.
apply approx_level.
}

(* clam *)
{
intros pg s i k a K L A h HeqL Hk _ IH.
cbn.
apply max_ord_lub; eauto using interp_kext_bound.
so (IH i (le_refl _) (space_inhabitant _)) as H.
cbn in H.
rewrite <- HeqL in H.
auto.
}

(* capp *)
{
intros pg s i a b K L A B _ IH _ _.
cbn.
cbn in IH.
eapply le_ord_trans; eauto.
apply le_ord_max_r.
}

(* ctlam *)
{
intros pg s i a b k K A f B _ _ Hk _ _ _.
cbn.
apply max_ord_lub; auto using le_ord_refl.
eapply interp_kext_bound; eauto.
}

(* ctapp *)
{
intros pg s i b m l A K B n p Hnp _ _ IH.
cbn.
cbn in IH.
exact (max_ord_lub_r _#3 IH).
}

(* cpi1 *)
{
intros pg s i a K L x _ IH.
cbn.
cbn in IH.
eapply max_ord_lub_l; eauto.
}

(* cpi2 *)
{
intros pg s i a K L x _ IH.
cbn.
cbn in IH.
eapply max_ord_lub_r; eauto.
}

(* wrapup *)
{
destruct_all Hind; split; intros; eauto.
}
Qed.


Lemma kinterp_level_bound :
  forall pg s i k K,
    kinterp pg s i k K
    -> level K <<= cin pg.
Proof.
exact (semantics_level_bound andel).
Qed.


Lemma cinterp_level_bound :
  forall pg s i c Q,
    cinterp pg s i c Q
    -> level (pi1 Q) <<= cin pg.
Proof.
exact (semantics_level_bound ander).
Qed.


(* In retrospect, it might have been better to state the conclusion as
   R = blur (cin pg) stop R.  But I'm not going back and changing it now.
*)
Lemma semantics_level_internal :
  forall pg s i a R (h : cin pg <<= stop),
    levind (str pg)
    -> interp pg s i a R
    -> exists R', R = extend_iurel h R'.
Proof.
exploit
  (semantics_ind the_system
     (fun pg s i k K => True)
     (fun pg s i a Q => True)
     (fun pg s i a R =>
        levind (str pg) -> forall (h : cin pg <<= stop), exists R', R = extend_iurel h R')
     (fun pg s i k K => True)
     (fun pg s i a Q => True)
     (fun pg s i a R =>
        levind (str pg) -> forall (h : cin pg <<= stop), exists R', R = extend_iurel h R')
     (fun pg s i A b B =>
        levind (str pg)
        -> forall
             (A' : wurel (cin pg))
             (heq : A = extend_urel (cin pg) stop A')
             (h : cin pg <<= stop),
               exists (B' : urelsp A' -n> wiurel_ofe (cin pg)),
                 B =
                 nearrow_compose 
                   (extend_iurel_ne h)
                   (nearrow_compose
                      B'
                      (nearrow_compose
                         (deextend_urelsp_ne h A')
                         (transport_ne heq urelsp)))))                   
  as Hind;
try (intros; cbn; eauto using max_ord_lub, le_ord_zero, le_ord_trans; done).

(* con *)
{
intros pg s i lv a gpg R Hlv Hle Ha _ IHo h.
exists (extend_iurel (cin_mono _ _ Hle) R).
rewrite <- extend_iurel_compose.
f_equal.
apply proof_irrelevance.
}

(* karrow *)
{
intros pg s i a b A B _ IH1 _ IH2 IHo h.
so (IH1 IHo h) as (A' & ->).
so (IH2 IHo h) as (B' & ->).
exists (iuarrow (cin pg) i A' B').
rewrite -> extend_iuarrow.
reflexivity.
}

(* tarrow *)
{
intros pg s i a b A B _ IH1 _ IH2 IHo h.
so (IH1 IHo h) as (A' & ->).
so (IH2 IHo h) as (B' & ->).
exists (iuarrow (cin pg) i A' B').
rewrite -> extend_iuarrow.
reflexivity.
}

(* pi *)
{
intros pg s i a b A B _ IH1 _ IH2 IHo h.
so (IH1 IHo h) as (A' & ->).
so (IH2 IHo (den A') (eq_refl _) h) as (B' & ->).
clear IH1 IH2.
exists (iupi (cin pg) i A' B').
rewrite -> extend_iupi.
f_equal.
apply nearrow_extensionality.
intro x.
cbn.
reflexivity.
}

(* intersect *)
{
intros pg s i a b A B _ IH1 _ IH2 IHo h.
so (IH1 IHo h) as (A' & ->).
so (IH2 IHo (den A') (eq_refl _) h) as (B' & ->).
clear IH1 IH2.
exists (iuintersect (cin pg) i A' B').
rewrite -> extend_iuintersect.
f_equal.
apply nearrow_extensionality.
intro x.
cbn.
reflexivity.
}

(* union *)
{
intros pg s i a b A B _ IH1 _ IH2 IHo h.
so (IH1 IHo h) as (A' & ->).
so (IH2 IHo (den A') (eq_refl _) h) as (B' & ->).
clear IH1 IH2.
exists (iuunion (cin pg) A' B').
rewrite -> extend_iuunion; auto using le_ord_refl.
f_equal.
apply nearrow_extensionality.
intro x.
cbn.
reflexivity.
}

(* prod *)
{
intros pg s i a b A B _ IH1 _ IH2 IHo h.
so (IH1 IHo h) as (A' & ->).
so (IH2 IHo h) as (B' & ->).
exists (iuprod (cin pg) A' B').
rewrite -> extend_iuprod.
reflexivity.
}

(* sigma *)
{
intros pg s i a b A B _ IH1 _ IH2 IHo h.
so (IH1 IHo h) as (A' & ->).
so (IH2 IHo (den A') (eq_refl _) h) as (B' & ->).
clear IH1 IH2.
exists (iusigma (cin pg) A' B').
rewrite -> extend_iusigma.
f_equal.
apply nearrow_extensionality.
intro x.
cbn.
reflexivity.
}

(* set *)
{
intros pg s i a b A B _ IH1 _ IH2 IHo h.
so (IH1 IHo h) as (A' & ->).
so (IH2 IHo (den A') (eq_refl _) h) as (B' & ->).
clear IH1 IH2.
exists (iuset (cin pg) A' B').
rewrite -> extend_iuset.
f_equal.
apply nearrow_extensionality.
intro x.
cbn.
reflexivity.
}

(* iset *)
{
intros pg s i a b A B _ IH1 _ IH2 IHo h.
so (IH1 IHo h) as (A' & ->).
so (IH2 IHo (den A') (eq_refl _) h) as (B' & ->).
clear IH1 IH2.
exists (iuiset (cin pg) A' B').
rewrite -> extend_iuiset.
f_equal.
apply nearrow_extensionality.
intro x.
cbn.
reflexivity.
}

(* quotient *)
{
intros pg s i a b A B hs ht _ IH1 _ IH2 IHo h.
so (IH1 IHo h) as (A' & ->).
set (Heq := eqsymm (extend_prod _ _ h (den A') (den A'))).
so (IH2 IHo (prod_urel (cin pg) (den A') (den A')) Heq h) as (B' & ->).
cbn in hs.
so (deextend_symmish _ _ h (den A') (fun x => den (pi1 B' x)) hs) as hs'.
so (deextend_transish _ _ h (den A') (fun x => den (pi1 B' x)) ht) as ht'.
exists (iuquotient (cin pg) A' B' hs' ht').
rewrite -> extend_iuquotient.
apply iuquotient_compat.
apply eq_impl_eq_dep_snd.
apply nearrow_extensionality.
intros; auto.
}

(* guard *)
{
intros pg s i a b A B _ IH1 _ IH2 IHo h.
so (IH1 IHo h) as (A' & ->).
so (IH2 IHo (squash_urel (cin pg) (den A') i) (eqsymm (extend_squash _#4 h)) h) as (B' & ->).
exists (iuguard (cin pg) i A' B').
rewrite -> extend_iuguard.
reflexivity.
}

(* fut zero *)
{
intros pg s a Hcla IHo h.
exists (iufut0 (cin pg)).
rewrite -> extend_iufut0.
reflexivity.
}

(* fut *)
{
intros pg s i a A _ IH IHo h.
so (IH IHo h) as (R & ->).
exists (iufut (cin pg) (S i) R).
rewrite -> extend_iufut.
reflexivity.
}

(* void *)
{
intros pg s i H h.
exists (iubase (void_urel (cin pg))).
rewrite -> extend_iubase.
rewrite -> extend_void; auto.
}

(* unit *)
{
intros pg s i H h.
exists (iubase (unit_urel (cin pg) i)).
rewrite -> extend_iubase.
rewrite -> extend_unit; auto.
}

(* bool *)
{
intros pg s i H h.
exists (iubase (bool_urel (cin pg) i)).
rewrite -> extend_iubase.
rewrite -> extend_bool; auto.
}

(* wt *)
{
intros pg s i a b A B _ IH1 _ IH2 IHo h.
so (IH1 IHo h) as (A' & ->).
so (IH2 IHo (den A') (eq_refl _) h) as (B' & ->).
clear IH1 IH2.
exists (iuwt (cin pg) A' B').
rewrite -> extend_iuwt.
f_equal.
apply nearrow_extensionality.
intro x.
cbn.
reflexivity.
}

(* equal *)
{
intros pg s i a m n p q A Hmp Hnq _ IH IHo h.
so (IH IHo h) as (A' & ->).
assert (srel s (den A') i (map_term (extend stop (cin pg)) m) (map_term (extend stop (cin pg)) p)) as Hmp'.
  {
  cbn in Hmp.
  exact (extend_srel _#7 andel Hmp).
  }
assert (srel s (den A') i (map_term (extend stop (cin pg)) n) (map_term (extend stop (cin pg)) q)) as Hnq'.
  {
  cbn in Hnq.
  exact (extend_srel _#7 andel Hnq).
  }
exists (iuequal (cin pg) s i A' _#4 Hmp' Hnq').
rewrite -> extend_iuequal'.
apply iuequal_equal'; auto.
  {
  cbn.
  rewrite -> extend_srel.
  rewrite -> extend_term_compose_down; auto.
  rewrite -> extend_term_compose_down; auto using le_ord_refl.
  }

  {
  cbn.
  rewrite -> extend_srel.
  rewrite -> extend_term_compose_down; auto.
  rewrite -> extend_term_compose_down; auto using le_ord_refl.
  }
}

(* eqtype *)
{
intros pg s i a b R R' _ IH1 _ IH2 IHo h.
so (IH1 IHo h) as (Q & ->).
so (IH2 IHo h) as (Q' & ->).
exists (iueqtype (cin pg) i Q Q').
unfold extend_iurel at 3.
unfold iueqtype, eqtype_urel.
cbn [fst snd].
f_equal.
  {
  rewrite -> extend_property; auto.
  apply property_urel_extensionality; auto.
  intros j Hj.
  unfold eqtype_property.
  rewrite -> !iutruncate_extend_iurel.
  split.
    {
    intros H.
    eapply extend_iurel_inj.
    exact H.
    }

    {
    intro H.
    f_equal; auto.
    }
  }

  {
  rewrite -> extend_meta_pair.
  rewrite -> !extend_meta_iurel; auto.
  }
}

(* sequal *)
{
intros s i m n Hclm Hcln Hequiv IHo h.
exists (iubase (unit_urel top i)).
rewrite -> extend_iubase.
rewrite -> extend_unit; auto.
}

(* subtype *)
{
intros pg s i a b R R' _ IH1 _ IH2 IHo h.
so (IH1 IHo h) as (Q & ->).
so (IH2 IHo h) as (Q' & ->).
exists (iusubtype (cin pg) i Q Q').
unfold extend_iurel at 3.
unfold iusubtype, subtype_urel.
cbn [fst snd].
f_equal.
  {
  rewrite -> extend_property; auto.
  apply property_urel_extensionality; auto.
  intros j Hj.
  unfold subtype_property.
  split.
    {
    intros Hact k m p Hk Hmp.
    exploit (Hact k (map_term (extend (cin pg) stop) m) (map_term (extend (cin pg) stop) p)) as H; auto.
      {
      cbn.
      rewrite -> !extend_term_cancel; auto.
      }
    cbn in H.
    rewrite -> !extend_term_cancel in H; auto.
    }

    {
    intros Hact k m p Hk Hmp.
    cbn.
    apply Hact; auto.
    }
  }

  {
  rewrite -> extend_meta_pair.
  rewrite -> !extend_meta_iurel; auto.
  }
}

(* all *)
{
intros pg s i lv k a gpg K A lev Hlv HintK _ Hle _ IH IHo h.
set (wc := cin pg).
so (kbasic_impl_approx _#6 HintK) as HeqK.
assert (forall (x : spcar K),
          exists! (R : wiurel wc),
            iutruncate (S i) (pi1 A (std (S i) K x))
            =
            extend_iurel h R)
  as Hexuniq.
  {
  intro x.
  so (IH i (le_refl _) (transport HeqK spcar x) IHo h) as (R & HR).
  exists R.
  split.
    {
    rewrite <- HR.
    rewrite -> embed_approx'.
    reflexivity.
    }

    {
    intros R' HR'.
    apply (extend_iurel_inj _ _ h).
    rewrite <- HR.
    rewrite <- HR'.
    rewrite -> embed_approx'.
    reflexivity.
    }
  }
so (choice _#3 Hexuniq) as (f & Hf).
assert (@nonexpansive (space K) (wiurel_ofe wc) f) as Hne.
  {
  intros n x y Hdist.
  apply (extend_iurel_noncontractive _ _ h).
  rewrite <- !Hf.
  apply iutruncate_nonexpansive.
  apply (pi2 A).
  apply std_nonexpansive; auto.
  }
set (A' := expair f Hne : space K -n> wiurel_ofe wc).
exists (iuall wc K A').
rewrite -> extend_iuall.
f_equal.
rewrite -> std_arrow_is.
cbn.
apply nearrow_extensionality.
intro x.
cbn.
change (std (S i) (qtype stop) (pi1 A (std (S i) K x)) = extend_iurel h (f x)).
rewrite -> std_type_is.
rewrite <- Hf.
reflexivity.
}

(* alltp *)
{
intros pg s i a A _ IH IHo h.
set (wc := cin pg).
so (choice (car (wiurel_ofe top)) (car (wiurel_ofe wc))
      (fun X R => 
         iutruncate (S i) (pi1 A (X)) = extend_iurel h R)) as (f & Hf).
  {
  intro X.
  so (IH i (le_refl _) X IHo h) as (R & Heq).
  exists R.
  split; auto.
  intros R' Heq'.
  exact (extend_iurel_inj _ _ h _ _ (eqtrans (eqsymm Heq) Heq')).
  }
assert (nonexpansive f) as Hne.
  {
  intros n x y Hdist.
  apply (extend_iurel_noncontractive _ _ h).
  rewrite <- !Hf.
  apply iutruncate_nonexpansive.
  apply (pi2 A); auto.
  }
exists (iualltp wc (expair f Hne)).
rewrite -> extend_iualltp.
f_equal.
apply nearrow_extensionality.
intros X.
cbn.
rewrite <- Hf.
reflexivity.
}

(* exist *)
{
intros pg s i lv k a gpg K A lev Hlv HintK _ Hle _ IH IHo h.
set (wc := cin pg).
so (kbasic_impl_approx _#6 HintK) as HeqK.
assert (forall (x : spcar K),
          exists! (R : wiurel wc),
            iutruncate (S i) (pi1 A (std (S i) K x))
            =
            extend_iurel h R)
  as Hexuniq.
  {
  intro x.
  so (IH i (le_refl _) (transport HeqK spcar x) IHo h) as (R & HR).
  exists R.
  split.
    {
    rewrite <- HR.
    rewrite -> embed_approx'.
    reflexivity.
    }

    {
    intros R' HR'.
    apply (extend_iurel_inj _ _ h).
    rewrite <- HR.
    rewrite <- HR'.
    rewrite -> embed_approx'.
    reflexivity.
    }
  }
so (choice _#3 Hexuniq) as (f & Hf).
assert (@nonexpansive (space K) (wiurel_ofe wc) f) as Hne.
  {
  intros n x y Hdist.
  apply (extend_iurel_noncontractive _ _ h).
  rewrite <- !Hf.
  apply iutruncate_nonexpansive.
  apply (pi2 A).
  apply std_nonexpansive; auto.
  }
set (A' := expair f Hne : space K -n> wiurel_ofe wc).
exists (iuexist wc K A').
rewrite -> extend_iuexist; auto using le_ord_refl.
f_equal.
rewrite -> std_arrow_is.
cbn.
apply nearrow_extensionality.
intro x.
cbn.
change (std (S i) (qtype stop) (pi1 A (std (S i) K x)) = extend_iurel h (f x)).
rewrite -> std_type_is.
rewrite <- Hf.
reflexivity.
}

(* extt *)
{
intros pg s i w R hw Hw IHo h.
exists (extend_iurel Hw (iutruncate (S i) R)).
rewrite <- extend_iurel_compose.
f_equal.
apply proof_irrelevance.
}

(* mu *)
{
intros pg w s i a F Hw _ IH Hne Hmono Hrobust IHo h.
exists (iubase (extend_urel w (cin pg) (mu_urel w (fun X => den (F X))))).
rewrite -> extend_iubase.
f_equal.
rewrite <- extend_urel_compose_up; auto using cin_mono.
}

(* ispositive *)
{
intros pg s i a Hcl _ h.
exists (iubase (ispositive_urel (cin pg) i a)).
rewrite -> extend_iubase.
unfold ispositive_urel.
rewrite -> extend_property; auto.
}

(* isnegative *)
{
intros pg s i a Hcl _ h.
exists (iubase (isnegative_urel (cin pg) i a)).
rewrite -> extend_iubase.
unfold isnegative_urel.
rewrite -> extend_property; auto.
}

(* univ *)
{
intros pg s i lv gpg Hlv Hstr Hcex IHo h.
set (wc := cin pg).
exists ((extend_urel stop wc (univ_urel the_system i gpg),
         meta_page gpg)).
unfold iuuniv, extend_iurel.
cbn.
rewrite -> extend_meta_page.
f_equal.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
pextensionality.
  {
  intros (Hj & R & Hm & Hp).
  split; auto.
  exists R.
  rewrite -> sint_unroll in Hm, Hp |- *.
  rewrite <- !restrict_extend.
  split; apply (IHo anderrr); auto.
  }

  {
  intros (Hj & R & Hm & Hp).
  split; auto.
  exists R.
  rewrite -> sint_unroll in Hm, Hp |- *.
  rewrite <- !restrict_extend in Hm, Hp.
  so (le_ord_trans _#3 (cex_top gpg) (succ_nodecrease _)) as Hlestop.
  so (restriction_decrease _#4 Hcex (restrict_impl_restriction wc m)) as Hrestm.
  so (restriction_decrease _#4 Hcex (restrict_impl_restriction wc p)) as Hrestp.
  split; eapply (IHo anderl); eauto.
  }
}

(* kind *)
{
intros pg s i lv gpg hgt Hlv Hlt IHo h.
set (wc := cin pg).
exists ((extend_urel stop wc (kind_urel the_system i gpg hgt),
         meta_page gpg)).
unfold iukind, extend_iurel.
cbn.
rewrite -> extend_meta_page.
f_equal.
apply urel_extensionality.
fextensionality 3.
intros j m p.
cbn.
so (lt_le_page_trans _#3 (lt_page_succ _ hgt) (lt_page_impl_le_page _ _ Hlt)) as Hlt'.
destruct Hlt as (Hstr & Hcex).
destruct Hlt' as (Hstr' & Hcex').
pextensionality.
  {
  intros (Hj & K & R & Hm & Hp & Hmt & Hpt).
  split; auto.
  exists K, R.
  rewrite -> sintk_unroll in Hm, Hp |- *.
  rewrite -> sint_unroll in Hmt, Hpt |- *.
  rewrite <- !restrict_extend.
  do2 3 split.
    {
    apply (IHo anderrl); auto.
    }

    {
    apply (IHo anderrl); auto.
    }

    {
    apply (IHo anderrr); auto.
    }

    {
    apply (IHo anderrr); auto.
    }
  }

  {
  intros (Hj & K & R & Hm & Hp & Hmt & Hpt).
  split; auto.
  exists K, R.
  rewrite -> sintk_unroll in Hm, Hp |- *.
  rewrite -> sint_unroll in Hmt, Hpt |- *.
  rewrite <- !restrict_extend in Hm, Hp, Hmt, Hpt.
  do2 3 split.
    {
    eapply (IHo andel); eauto using lt_ord_impl_le_ord, le_ord_trans.
    eapply restriction_decrease; eauto using restrict_impl_restriction, lt_ord_impl_le_ord.
    }

    {
    eapply (IHo andel); eauto using lt_ord_impl_le_ord, le_ord_trans.
    eapply restriction_decrease; eauto using restrict_impl_restriction, lt_ord_impl_le_ord.
    }

    {
    eapply (IHo anderl); eauto.
      {
      eapply lt_le_ord_trans; eauto.
      }
    eapply restriction_decrease; eauto using restrict_impl_restriction, lt_ord_impl_le_ord.
    }

    {
    eapply (IHo anderl); eauto.
      {
      eapply lt_le_ord_trans; eauto.
      }
    eapply restriction_decrease; eauto using restrict_impl_restriction, lt_ord_impl_le_ord.
    }
  }
}

(* partial *)
{
intros pg s i a A _ IH IHo h.
so (IH IHo h) as (A' & ->).
exists (iupartial (cin pg) i A').
rewrite -> extend_iupartial.
reflexivity.
}

(* halts *)
{
intros pg s i m Hcl IHo h.
exists (iubase (halts_urel (cin pg) i (map_term (extend stop (cin pg)) m))).
rewrite -> extend_iubase.
f_equal.
unfold halts_urel.
rewrite -> extend_property; auto.
apply property_urel_extensionality; auto.
intros j Hj.
split; eauto using map_converges, anti_map_converges.
}

(* admiss *)
{
intros pg s i a A _ IH IHo h.
so (IH IHo h) as (A' & ->).
exists (iuadmiss (cin pg) i A').
rewrite -> extend_iuadmiss.
reflexivity.
}  

(* uptype *)
{
intros pg s i a A _ IH IHo h.
so (IH IHo h) as (A' & ->).
exists (iuuptype (cin pg) i A').
rewrite -> extend_iuuptype.
reflexivity.
}  

(* functional *)
{
intros pg s i A' b B Hcl Hcoarse Hint IH IHo A heq h.
subst A'.
set (wc := cin pg).
assert (forall (C : urelsp_car A),
          exists! (R : wiurel wc),
            pi1 B (extend_urelsp h A C)
            =
            extend_iurel h R)
  as Hexuniq.
  {
  intro C.
  so (urelsp_eta _ _ C) as (j & m & p & Hmp & ->).
  assert (rel (extend_urel wc stop A) j (map_term (extend wc stop) m) (map_term (extend wc stop) p)) as Hmp'.    
    {
    cbn.
    rewrite -> !extend_term_cancel; auto.
    }
  so (transport Hcoarse (fun R => rel R j _ _) Hmp') as (H & _).
  assert (j <= i) as Hj by omega; clear H.
  so (IH j (map_term (extend wc stop) m) (map_term (extend wc stop) p) Hj Hmp' IHo h) as (R & Heq).
  exists R.
  split.
    {
    rewrite -> (extend_urelspinj _#8 Hmp').
    exact Heq.
    }

    {
    intros R' Heq'.
    rewrite -> (extend_urelspinj _#8 Hmp') in Heq'.
    apply (extend_iurel_inj _ _ h).
    etransitivity.
      {
      symmetry.
      exact Heq.
      }
    exact Heq'.
    }
  }
so (choice _#3 Hexuniq) as (f & Hf).
assert (@nonexpansive (urelsp A) (wiurel_ofe wc) f) as Hne.
  {
  intros n C D HCD.
  apply (extend_iurel_noncontractive _ _ h).
  rewrite <- !Hf.
  apply (pi2 B).
  apply extend_urelsp_nonexpansive; auto.
  }
exists (expair f Hne).
apply nearrow_extensionality.
intro C.
cbn.
(* This seems more complicated than it should be. *)
so (urelsp_eta _ _ C) as (j & m & p & Hmp & ->).
rewrite -> deextend_urelsp_urelspinj.
rewrite <- Hf.
f_equal.
cbn in Hmp.
assert (rel (extend_urel wc stop A) j (map_term (extend wc stop) (map_term (extend stop wc) m)) (map_term (extend wc stop) (map_term (extend stop wc) p))) as Hmp'.
  {
  cbn.
  rewrite -> !extend_term_cancel; auto.
  }
rewrite -> (extend_urelspinj _#8 Hmp').
apply urelspinj_equal.
cbn.
rewrite -> extend_term_cancel; auto.
}

(* wrapup *)
{
destruct_all Hind; eauto.
}
Qed.


Lemma natinterp_restriction :
  forall w m m' i,
    restriction w m m'
    -> natinterp m i
    -> natinterp m' i.
Proof.
intros w m m' i Hrest Hint.
revert m' Hrest.
induct Hint.

(* 0 *)
{
intros m n p Hclm Hstepsm Hstepsn Hstepsp m' Hrestm.
so (restriction_steps _#4 Hrestm Hstepsm) as (np & H & Hstepsm').
invertc H.
intros r Hr <-.
invertc Hr.
intros n' r1 Hrestn Hr1 <-.
invertc Hr1.
intros p' r2 Hrestp Hr2 <-.
invertc Hr2.
intros <-.
fold (ppair n' p') in *.
so (restriction_steps _#4 Hrestn Hstepsn) as (q & H & Hstepsn').
invertc H.
intros r Hr <-.
invertc Hr.
intros <-.
fold (@btrue (obj stop)) in *.
so (restriction_steps _#4 Hrestp Hstepsp) as (? & H & Hl').
invertc H.
intros r Hr <-.
invertc Hr.
intros <-.
fold (@triv (obj stop)) in *.
eapply natinterp_0; eauto.
eapply restriction_hygiene; eauto.
}

(* S *)
{
intros m n p i Hclm Hstepsm Hstepsn _ IH m' Hrestm.
so (restriction_steps _#4 Hrestm Hstepsm) as (np & H & Hstepsm').
invertc H.
intros r Hr <-.
invertc Hr.
intros n' r1 Hrestn Hr1 <-.
invertc Hr1.
intros p' r2 Hrestp Hr2 <-.
invertc Hr2.
intros <-.
fold (ppair n' p') in *.
so (restriction_steps _#4 Hrestn Hstepsn) as (q & H & Hstepsn').
invertc H.
intros r Hr <-.
invertc Hr.
intros <-.
fold (@bfalse (obj stop)) in *.
eapply natinterp_S; eauto.
eapply restriction_hygiene; eauto.
}
Qed.


Lemma lvinterp_restriction :
  forall w lv lv' u,
    restriction w lv lv'
    -> lvinterp lv u
    -> lvinterp lv' u.
Proof.
intros w lv lv' u Hrest Hlv.
destruct Hlv as (i & Hi & ->).
exists i.
split; auto.
eapply natinterp_restriction; eauto.
Qed.


Lemma pginterp_restriction :
  forall w lv lv' pg,
    restriction w lv lv'
    -> pginterp lv pg
    -> pginterp lv' pg.
Proof.
intros w lv lv' pg Hrest Hlv.
destruct Hlv as (i & Hint & Hstr & Hcex & Hcin).
exists i.
do2 3 split; auto.
eapply lvinterp_restriction; eauto.
Qed.


Lemma interp_kext_restriction :
  forall w pg i k k' K,
    restriction w k k'
    -> interp_kext pg i k K
    -> interp_kext pg i k' K.
Proof.
intros w pg i k k' K Hrest Hint.
destruct Hint as (Q & h & Hcl & Hsteps & Hlev & <-).
so (restriction_steps _#4 Hrest Hsteps) as (m & Hrest' & Hsteps').
assert (m = ext (objin (objsome Q h))).
  {
  invertc Hrest'.
    {
    intros r Hr <-.
    invertc Hr.
    intros <-.
    reflexivity.
    }

    {
    intros Q' h' _ Heq _.
    discriminate (objin_inj _ _ _ Heq).
    }
  }
subst m.
so (restriction_hygiene _#4 Hrest Hcl) as Hcl'.
exists Q, h.
auto.
Qed.


Lemma interp_uext_restriction :
  forall w pg i m m' R,
    restriction w m m'
    -> interp_uext pg i m R
    -> interp_uext pg i m' R.
Proof.
intros w pg i m m' R Hrest Hint.
destruct Hint as (v & Q & h & Hcl & Hsteps & Hlev & <-).
so (restriction_steps _#4 Hrest Hsteps) as (n & Hrest' & Hsteps').
assert (n = ext (objin (objsome (expair (qtype v) Q) h))).
  {
  invertc Hrest'.
    {
    intros r Hr <-.
    invertc Hr.
    intros <-.
    reflexivity.
    }

    {
    intros Q' h' _ Heq _.
    discriminate (objin_inj _ _ _ Heq).
    }
  }
subst n.
so (restriction_hygiene _#4 Hrest Hcl) as Hcl'.
exists v, Q, h.
auto.
Qed.


Lemma restriction_stop :
  forall m n,
    restriction stop m n
    -> m = n.
Proof.
apply (restriction_term_mut_ind stop
         (fun m n => m = n)
         (fun a r r' => r = r')); auto.

(* oper *)
{
intros a th r s _ <-.
reflexivity.
}

(* ext *)
{
intros Q h Hle.
exfalso.
refine (lt_ord_irrefl stop _).
eapply le_lt_ord_trans; eauto.
}

(* extt *)
{
intros Q h Hle.
exfalso.
refine (lt_ord_irrefl stop _).
eapply le_lt_ord_trans; eauto.
}

(* cons *)
{
intros j a m n r s _ <- _ <-.
reflexivity.
}
Qed.


(* This lemma states that in a semantics interpretation of a term, any
   objnones in the term can be replaced by objsomes, provided that the
   objsomes are at too high a level to be used in the interpretation.

   We have to use restriction here, as opposed to saying something like
   (a = restrict_term (succ w) a'), because the latter isn't preserved in
   some cases.  For instance, in the clam case, you substitute using
   an object that might be restricted away if you applied
   (restrict_term w).

   Note that (restrict_term (succ (cex pg))) returns the same thing
   for each term.

   In principle, we could say something stronger: that an objnone can
   be promoted to any objsome, regardless of level.  But (to get ctapp
   and equal to go through) this would require a similar property for
   membership in uniform relations, which would be a bit messy to
   state and which we would then have to prove for every type.  It
   would be doable, but since we don't seem to need the stronger
   statement, we don't bother.

   (Also, we could imagine some types for which the stronger version
   wouldn't work at all.  For example, a syntactic equality type (that
   internalized equiv) wouldn't handle the term being tinkered with this
   way.)

   We could also say something slightly stronger: use the level (cex pg)
   instead of (succ (cex pg)).  We used to do that, but changed to this
   to allow the syntactic equality type.  We ended up ditching that, but
   this is more principled anyway, so we kept it.
*)

Lemma semantics_restriction :
  (forall pg s i a a' Q,
     levind (str pg)
     -> restriction (succ (cex pg)) a a'
     -> kinterp pg s i a Q
     -> kinterp pg s i a' Q)
  /\
  (forall pg s i a a' Q,
     levind (str pg)
     -> restriction (succ (cex pg)) a a'
     -> cinterp pg s i a Q
     -> cinterp pg s i a' Q)
  /\
  (forall pg s i a a' R,
     levind (str pg)
     -> restriction (succ (cex pg)) a a'
     -> interp pg s i a R
     -> interp pg s i a' R).
Proof.
exploit (semantics_ind the_system
           (fun pg s i m X => forall m', levind (str pg) -> restriction (succ (cex pg)) m m' -> kbasicv the_system pg s i m' X)
           (fun pg s i m X => forall m', levind (str pg) -> restriction (succ (cex pg)) m m' -> cbasicv the_system pg s i m' X)
           (fun pg s i m X => forall m', levind (str pg) -> restriction (succ (cex pg)) m m' -> basicv the_system pg s i m' X)
           (fun pg s i m X => forall m', levind (str pg) -> restriction (succ (cex pg)) m m' -> kbasic the_system pg s i m' X)
           (fun pg s i m X => forall m', levind (str pg) -> restriction (succ (cex pg)) m m' -> cbasic the_system pg s i m' X)
           (fun pg s i m X => forall m', levind (str pg) -> restriction (succ (cex pg)) m m' -> basic the_system pg s i m' X)
           (fun pg s i A m X => forall m', levind (str pg) -> restriction (succ (cex pg)) m m' -> functional the_system pg s i A m' X))
  as Hind;
try (intros;
     match goal with
     | H : restriction _ _ _ |- _ =>
         invertc H
     end;
     intros;
     (* keep from looping with repeat -- no operator has more than 3 subterms *)
     do 4 (try
             match goal with
             | H : restriction_row _ _ _ _ |- _ =>
                 invertc H; intros
             end);
     subst;
     first [eapply interp_kunit
           |eapply interp_kuniv
           |eapply interp_kkarrow
           |eapply interp_ktarrow
           |eapply interp_kprod
           |eapply interp_kfut_zero
           |eapply interp_kfut
           |eapply interp_cunit
           |eapply interp_capp
           |eapply interp_cpair
           |eapply interp_cpi1
           |eapply interp_cpi2
           |eapply interp_cnext_zero
           |eapply interp_cnext
           |eapply interp_cprev
           |eapply interp_cty
           |eapply interp_karrow
           |eapply interp_tarrow
           |eapply interp_pi
           |eapply interp_intersect
           |eapply interp_union
           |eapply interp_prod
           |eapply interp_sigma
           |eapply interp_set
           |eapply interp_iset
           |eapply interp_fut_zero
           |eapply interp_fut
           |eapply interp_void
           |eapply interp_unit
           |eapply interp_bool
           |eapply interp_guard
           |eapply interp_wt
           |eapply interp_eqtype
           |eapply interp_subtype
           |eapply interp_partial
           |eapply interp_admiss
           |eapply interp_uptype
           ];
     eauto using restriction_hygiene, restriction_decrease;
     done).

(* type *)
{
intros pg s i lv H mm IHo Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros lv' r2 Hlv' Hr2 <-.
invertc Hr2.
intros <-.
fold (univ lv').
apply interp_kuniv.
eapply pginterp_restriction; eauto.
}

(* krec *)
{
intros pg s i k K _ IH mm IHo Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros k' r2 Hk Hr2 <-.
invert Hr2.
intros <-.
fold (rec k').
apply interp_krec.
apply IH; auto.
apply restriction_funct1; auto.
apply restriction_oper.
apply restriction_cons; auto.
}

(* ext *)
{
intros pg s i Q h Hcin mm _ Hrest.
invertc Hrest.
  {
  intros r1 Hr1 <-.
  invertc Hr1.
  intros <-.
  apply interp_ext; auto.
  }

  {
  intros Q' h' _ Heq <-.
  discriminate (objin_inj _ _ _ Heq).
  }
}

(* clam *)
{
intros pg s i k a K L A h HeqL Hintk _ IH mm IHo Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros k' r2 Hk Hr2 <-.
invertc Hr2.
intros a' r3 Ha Hr3 <-.
invertc Hr3.
intros <-.
fold (clam k' a').
eapply (interp_clam _#9 h); eauto using restriction_hygiene, interp_kext_restriction.
intros j Hj x.
apply IH; auto.
apply restriction_subst; auto.
}

(* ctlam *)
{
intros pg s i a b k K A f B Hcl Hinta Hintk _ IH Hf mm IHo Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros b' r3 Hb Hr3 <-.
invertc Hr3.
intros k' r4 Hk Hr4 <-.
invertc Hr4.
intros <-.
fold (ctlam a' b' k').
eapply interp_ctlam; eauto using restriction_hygiene, restriction_decrease, interp_kext_restriction, interp_uext_restriction.
intros j m n Hmn.
apply IH; auto.
apply restriction_subst; eauto using restriction_decrease.
}

(* ctapp *)
{
intros pg s i b m l A K B n p Hnp Hm Hintb IH mm IHo Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros b' r2 Hb Hr2 <-.
invertc Hr2.
intros m' r3 Hrestm Hr3 <-.
invertc Hr3.
intros <-.
fold (ctapp b' m').
eapply interp_ctapp; eauto.
so (cinterp_level_bound _#5 Hintb) as Hlev.
cbn in Hlev.
so (le_ord_trans _#3 (le_ord_trans _#3 (le_ord_max_l l (level K)) (le_ord_trans _#3 Hlev (cin_cex pg))) (succ_nodecrease _)) as Hlev'.
rewrite <- (restrict_restriction _#3 (restriction_decrease _#4 Hlev' Hrestm)); auto.
}

(* con *)
{
intros pg s i lv a gpg R Hintlv Hle _ IH mm IHo Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros lv' r2 Hlv Hr2 <-.
invertc Hr2.
intros a' r3 Ha Hr3 <-.
invertc Hr3.
intros <-.
fold (con lv' a').
eapply interp_con; eauto using pginterp_restriction.
apply IH; auto.
  {
  eapply levind_decrease; eauto.
  apply str_mono; auto.
  }

  {
  eapply restriction_decrease; eauto.
  apply le_ord_succ.
  apply cex_mono; auto.
  }
}

(* quotient *)
{
intros pg s i a b A B hs ht _ IH1 _ IH2 mm IHo Hrest.
invertc Hrest.
intros r Hr <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (a' & b' & ->).
fold (quotient a' b') in *.
invertc Hr.
intros Ha Hr.
invertc Hr.
intros Hb _.
apply interp_quotient; auto using restriction_subst.
}

(* guard *)
{
intros pg s i a b A B _ IH1 _ IH2 mm IHo Hrest.
invertc Hrest.
intros r Hr <-.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (a' & b' & ->).
fold (guard a' b') in *.
invertc Hr.
intros Ha Hr.
invertc Hr.
intros Hb _.
apply interp_guard; auto using restriction_subst.
}

(* equal *)
{
intros pg s i a m n p q A Hmp Hnq Hint IH mm IHo Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros m' r3 Hm' Hr3 <-.
invertc Hr3.
intros n' r4 Hn' Hr4 <-.
invertc Hr4.
intros <-.
fold (equal a' m' n').
so (le_ord_trans _#3 (cin_top pg) (succ_nodecrease _)) as h.
so (semantics_level_internal _#5 h IHo Hint) as (A' & ->).
so Hmp as Hmp'.
so Hnq as Hnq'.
rewrite -> den_extend_iurel in Hmp', Hnq'.
rewrite -> extend_srel in Hmp', Hnq'.
rewrite -> (restrict_restriction _ m m') in Hmp'; auto.
2:{
  cbn.
  exact (restriction_decrease _#4 (le_ord_trans _#3 (cin_cex pg) (succ_nodecrease _)) Hm').
  }
rewrite -> (restrict_restriction _ n n') in Hnq'; auto.
2:{
  cbn.
  exact (restriction_decrease _#4 (le_ord_trans _#3 (cin_cex pg) (succ_nodecrease _)) Hn').
  }
rewrite <- extend_srel in Hmp', Hnq'.
rewrite <- (den_extend_iurel _ _ h) in Hmp', Hnq'.
cbn.
match goal with
| |- basicv _ _ _ _ _ ?X =>
  replace X
  with  (iuequal stop s i (extend_iurel h A') m' n' p q Hmp' Hnq')
end.
2:{
  apply iuequal_equal; auto.
  }
apply interp_equal; auto.
}

(* sequal *)
{
intros s i m n Hclm Hln Hequiv mm Iho Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros m' r2 Hm Hr2 <-.
invertc Hr2.
intros n' r3 Hn Hr3 <-.
invertc Hr3.
intros <-.
fold (sequal m' n').
so (restrict_restriction _#3 Hm) as H.
cbn in H.
rewrite -> !extend_term_id in H.
subst m'.
so (restrict_restriction _#3 Hn) as H.
cbn in H.
rewrite -> !extend_term_id in H.
subst n'.
apply interp_sequal; auto.
}

(* all *)
{
intros pg s i lv k a gpg K A h Hintlv _ IH1 Hle _ IH2 mm IHo Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros lv' r2 Hlv Hr2 <-.
invertc Hr2.
intros k' r3 Hk Hr3 <-.
invertc Hr3.
intros a' r4 Ha Hr4 <-.
invertc Hr4.
intros <-.
fold (all lv' k' a').
apply (interp_all _#7 gpg _ _ h); eauto using restriction_hygiene, pginterp_restriction.
  {
  apply IH1.
    {
    eapply levind_decrease; eauto.
    apply str_mono; auto.
    }

    {
    eapply restriction_decrease; eauto.
    apply le_ord_succ.
    apply cex_mono; auto.
    }
  }
intros j Hj x.
apply IH2; auto.
apply restriction_subst; auto.
}

(* alltp *)
{
intros pg s i a A _ IH mm IHo Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros <-.
apply interp_alltp.
intros j Hj x.
apply IH; auto.
apply restriction_subst; auto.
}

(* exist *)
{
intros pg s i lv k a gpg K A h Hintlv _ IH1 Hle _ IH2 mm IHo Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros lv' r2 Hlv Hr2 <-.
invertc Hr2.
intros k' r3 Hk Hr3 <-.
invertc Hr3.
intros a' r4 Ha Hr4 <-.
invertc Hr4.
intros <-.
fold (all lv' k' a').
apply (interp_exist _#7 gpg _ _ h); eauto using restriction_hygiene, pginterp_restriction.
  {
  apply IH1.
    {
    eapply levind_decrease; eauto.
    apply str_mono; auto.
    }

    {
    eapply restriction_decrease; eauto.
    apply le_ord_succ.
    apply cex_mono; auto.
    }
  }
intros j Hj x.
apply IH2; auto.
apply restriction_subst; auto.
}

(* extt *)
{
intros pg s i w R h Hw m' IHo Hrest.
invertc Hrest.
  {
  intros r1 Hr1 <-.
  invertc Hr1.
  intros <-.
  apply interp_extt; auto.
  }

  {
  intros Q' h' _ Heq <-.
  discriminate (objin_inj _ _ _ Heq).
  }
}

(* mu *)
{
intros pg w s i a F Hw _ IH Hne Hmono Hrobust mm IHo Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros <-.
fold (mu a').
apply interp_mu; auto.
  {
  intros X h.
  eapply IH; eauto.
  apply restriction_subst; auto.
  }

  {
  erewrite <- restriction_robust; eauto.
  }
}

(* ispositive *)
{
intros pg s i a Hcl mm _ Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros <-.
fold (ispositive a').
replace (ispositive_urel stop i a) with (ispositive_urel stop i a').
2:{
  apply property_urel_extensionality; auto.
  intros _ _.
  symmetry.
  eapply restriction_positive; eauto.
  }
apply interp_ispositive.
eapply restriction_hygiene; eauto.
}

(* isnegative *)
{
intros pg s i a Hcl mm _ Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros a' r2 Ha Hr2 <-.
invertc Hr2.
intros <-.
fold (isnegative a').
replace (isnegative_urel stop i a) with (isnegative_urel stop i a').
2:{
  apply property_urel_extensionality; auto.
  intros _ _.
  symmetry.
  eapply restriction_negative; eauto.
  }
apply interp_isnegative.
eapply restriction_hygiene; eauto.
}

(* rec *)
{
intros pg s i k K _ IH mm IHo Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros k' r2 Hk Hr2 <-.
invert Hr2.
intros <-.
fold (rec k').
apply interp_rec.
apply IH; auto.
apply restriction_funct1; auto.
apply restriction_oper.
apply restriction_cons; auto.
}

(* univ *)
{
intros pg s i lv gpg Hintlv Hstr Hcex mm IHo Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros lv' r2 Hlv' Hr2 <-.
invertc Hr2.
intros <-.
fold (univ lv').
apply interp_univ; eauto using pginterp_restriction.
}

(* kind *)
{
intros pg s i lv gpg h Hintlv Hlt mm IHo Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros lv' r2 Hlv' Hr2 <-.
invertc Hr2.
intros <-.
fold (kind lv').
apply interp_kind; eauto using pginterp_restriction.
}

(* halts *)
{
intros pg s i m H mm IHo Hrest.
invertc Hrest.
intros r1 Hr1 <-.
invertc Hr1.
intros m' r2 Hm' Hr2 <-.
invertc Hr2.
intros <-.
fold (halts m').
so (le_ord_trans _#3 (cin_top pg) (succ_nodecrease _)) as h.
replace (halts_urel stop i m) with (halts_urel stop i m').
2:{
  apply property_urel_extensionality; auto.
  intros j Hj.
  rewrite -> (map_converges_iff _ _ (extend stop (succ (cex pg))) m).
  rewrite -> (map_converges_iff _ _ (extend stop (succ (cex pg))) m').
  rewrite -> (restrict_restriction _ _ _ Hm').
  reflexivity.
  }
apply interp_halts; auto.
so (restrict_restriction _#3 Hm') as Heq.
apply (map_hygiene_conv _ _ (extend stop (succ (cex pg)))).
rewrite <- Heq.
apply map_hygiene; auto.
}

(* kinterp *)
{
intros pg s i k k' K Hcl Hsteps _ IH l IHo Hrest.
so (restriction_steps _#4 Hrest Hsteps) as (l' & Hrest' & Hsteps').
apply (kinterp_eval _#5 l'); auto.
eapply restriction_hygiene; eauto.
}

(* cinterp *)
{
intros pg s i c c' K Hcl Hsteps _ IH d IHo Hrest.
so (restriction_steps _#4 Hrest Hsteps) as (d' & Hrest' & Hsteps').
apply (cinterp_eval _#5 d'); auto.
eapply restriction_hygiene; eauto.
}

(* interp *)
{
intros pg s i a a' K Hcl Hsteps _ IH b IHo Hrest.
so (restriction_steps _#4 Hrest Hsteps) as (b' & Hrest' & Hsteps').
apply (interp_eval _#5 b'); auto.
eapply restriction_hygiene; eauto.
}

(* functional *)
{
intros pg s i A b B Hclo Hcourse _ IH b' IHo Hrest.
apply functional_i; eauto using restriction_hygiene.
intros j m p Hj Hmp.
apply IH; auto.
apply restriction_subst; auto.
}

(* wrapup *)
{
destruct Hind as (Hk & Hc & Hy & _).
do2 2 split; intros; [eapply Hk | eapply Hc | eapply Hy]; eauto.
}
Qed.


Lemma restrict_natinterp :
  forall w m i,
    natinterp m i
    -> natinterp (map_term (restrict w) m) i.
Proof.
intros w m i Hint.
induct Hint.

(* 0 *)
{
intros m n p Hclm Hstepsm Hstepsn Hstepsp.
apply (natinterp_0 _ (map_term (restrict w) n) (map_term (restrict w) p)); auto using map_hygiene.
  {
  relquest.
    {
    apply map_steps; eauto.
    }
  simpmap.
  reflexivity.
  }

  {
  relquest.
    {
    apply map_steps; eauto.
    }
  simpmap.
  reflexivity.
  }

  {
  relquest.
    {
    apply map_steps; eauto.
    }
  simpmap.
  reflexivity.
  }
}

(* S *)
{
intros m n p i Hclm Hstepsm Hstepsn _ IH.
apply (natinterp_S _ (map_term (restrict w) n) (map_term (restrict w) p)); auto using map_hygiene.
  {
  relquest.
    {
    apply map_steps; eauto.
    }
  simpmap.
  reflexivity.
  }

  {
  relquest.
    {
    apply map_steps; eauto.
    }
  simpmap.
  reflexivity.
  }
}
Qed.


Lemma restrict_lvinterp :
  forall w m u,
    lvinterp m u
    -> lvinterp (map_term (restrict w) m) u.
Proof.
intros w m u Hint.
destruct Hint as (i & Hi & ->).
exists i.
split; auto.
eapply restrict_natinterp; eauto.
Qed.


Lemma restrict_pginterp :
  forall w m pg,
    pginterp m pg
    -> pginterp (map_term (restrict w) m) pg.
Proof.
intros w m pg Hint.
destruct Hint as (i & Hint & Hstr & Hcex & Hcin).
exists i.
do2 3 split; auto.
eapply restrict_lvinterp; eauto.
Qed.


Lemma restrict_interp_kext :
  forall w pg i k K,
    cin pg << w
    -> interp_kext pg i k K
    -> interp_kext pg i (map_term (restrict w) k) K.
Proof.
intros w pg i k K Hcin Hint.
destruct Hint as (Q & h & Hcl & Hsteps & Hlev & <-).
exists Q, h.
do2 3 split; auto.
  {
  apply map_hygiene; auto.
  }

  {
  so (map_steps _ _ (restrict w) _ _ Hsteps) as Hsteps'.
  force_exact Hsteps'.
  f_equal.
  simpmap.
  f_equal.
  unfold restrict.
  rewrite -> objout_objin.
  f_equal.
  unfold restrict_xobj.
  rewrite -> (lt_ord_dec_is _ _ (le_lt_ord_trans _#3 Hlev Hcin)).
  reflexivity.
  }
Qed.
 

Lemma restrict_interp_uext :
  forall w pg i a R,
    cin pg << w
    -> interp_uext pg i a R
    -> interp_uext pg i (map_term (restrict w) a) R.
Proof.
intros w pg i a R Hcin Hint.
destruct Hint as (v & Q & h & Hcl & Hsteps & Hv & <-).
exists v, Q, h.
do2 3 split; auto.
  {
  apply map_hygiene; auto.
  }

  {
  so (map_steps _ _ (restrict w) _ _ Hsteps) as Hsteps'.
  force_exact Hsteps'.
  f_equal.
  simpmap.
  f_equal.
  unfold restrict.
  rewrite -> objout_objin.
  f_equal.
  unfold restrict_xobj.
  cbn.
  rewrite -> (lt_ord_dec_is _ _ (le_lt_ord_trans _#3 Hv Hcin)).
  reflexivity.
  }
Qed.
 

Lemma semantics_level_external :
  (forall pg s i a R w,
     levind (str pg)
     -> cex pg << w
     -> w <<= stop
     -> kinterp pg s i a R
     -> kinterp pg s i (restrict_term w a) R)
  /\
  (forall pg s i a R w,
     levind (str pg)
     -> cex pg << w
     -> w <<= stop
     -> interp pg s i a R
     -> interp pg s i (restrict_term w a) R).
Proof.
exploit (semantics_ind the_system
           (fun pg s i m X => forall w, levind (str pg) -> cex pg << w -> w <<= stop -> kbasicv the_system pg s i (map_term (restrict w) m) X)
           (fun pg s i m X => forall w, levind (str pg) -> cex pg << w -> w <<= stop -> cbasicv the_system pg s i (map_term (restrict w) m) X)
           (fun pg s i m X => forall w, levind (str pg) -> cex pg << w -> w <<= stop -> basicv the_system pg s i (map_term (restrict w) m) X)
           (fun pg s i m X => forall w, levind (str pg) -> cex pg << w -> w <<= stop -> kbasic the_system pg s i (map_term (restrict w) m) X)
           (fun pg s i m X => forall w, levind (str pg) -> cex pg << w -> w <<= stop -> cbasic the_system pg s i (map_term (restrict w) m) X)
           (fun pg s i m X => forall w, levind (str pg) -> cex pg << w -> w <<= stop -> basic the_system pg s i (map_term (restrict w) m) X)
           (fun pg s i A b B => forall w, levind (str pg) -> cex pg << w -> w <<= stop -> functional the_system pg s i A (map_term (restrict w) b) B))
  as Hind;
try (intros;
     simpmap;
     eauto using map_hygiene, le_lt_ord_trans, restrict_pginterp with semantics;
     done).

(* krec *)
{
intros pg s i k K _ IH w IHo Hwc Hw.
simpmap.
apply interp_krec.
so (IH _ IHo Hwc Hw) as H.
simpmapin H.
exact H.
}

(* ext *)
{
intros pg s i Q h Hcin w _ Hw _.
simpmap.
unfold restrict, restrict_xobj.
rewrite -> objout_objin.
rewrite -> (lt_ord_dec_is _ _ (le_lt_ord_trans _#3 (le_ord_trans _#3 Hcin (cin_cex pg)) Hw)).
apply interp_ext; auto.
}

(* clam *)
{
intros pg s i k a K L A h HeqL Hintk _ IH2 w IHo Hwc Hw.
simpmap.
apply (interp_clam _#9 h); eauto using map_hygiene.
  {
  eapply restrict_interp_kext; eauto.
  eapply le_lt_ord_trans; eauto using cin_cex.
  }
intros j Hj x.
so (IH2 j Hj x w IHo Hwc Hw) as H.
simpmapin H.
cbn in H.
refine (semantics_restriction anderl _#6 IHo _ H); clear H.
apply restriction_funct1; auto using restriction_refl.
apply (restriction_decrease _ w); auto using lt_ord_impl_le_ord.
rewrite <- restrict_ext.
apply restrict_impl_restriction.
}

(* ctlam *)
{
intros pg s i a b k K A f B Hcl Hinta Hintk _ IH Hf w IHo Hwc Hw.
simpmap.
so (le_lt_ord_trans _#3 (cin_cex pg) Hwc) as Hcinw.
apply (interp_ctlam _#9 f); auto using map_hygiene, restrict_interp_kext, restrict_interp_uext.
intros j m n Hmn.
so (IH j m n Hmn w IHo Hwc Hw) as H.
simpmapin H.
refine (semantics_restriction anderl _#6 IHo _ H); clear H.
apply restriction_funct1; auto using restriction_refl.
apply (restriction_decrease _ w); auto using lt_ord_impl_le_ord.
apply restrict_impl_restriction.
}

(* ctapp *)
{
intros pg s i b m l A K B n p Hnp Hm Hint IH w IHo Hwc Hw.
simpmap.
apply interp_ctapp; auto.
rewrite <- (restrict_restriction _ (restrict_term w m)) in Hm; auto.
apply (restriction_decrease _ w); auto using restrict_impl_restriction.
so (cinterp_level_bound _#5 Hint) as Hlev.
cbn in Hlev.
exact (le_ord_trans _#3 (le_ord_max_l _ _) (le_ord_trans _#3 Hlev (le_ord_trans _#3 (cin_cex pg) (lt_ord_impl_le_ord _ _ Hwc)))).
}

(* con *)
{
intros pg s i lv a gpg R Hintlv Hle _ IH w IHo Hwc Hw.
simpmap.
apply interp_con; auto using restrict_pginterp.
apply IH; auto.
  {
  eapply levind_decrease; eauto.
  apply str_mono; auto.
  }

  {
  eapply le_lt_ord_trans; eauto.
  apply cex_mono; auto.
  }
}

(* quotient *)
{
intros pg s i a b A B hs ht _ IH1 _ IH2 w IHo Hwc Hw.
simpmap.
apply interp_quotient; auto.
so (IH2 _ IHo Hwc Hw) as H.
simpmapin H.
exact H.
}

(* guard *)
{
intros pg s i a b A B _ IH1 _ IH2 w IHo Hwc Hw.
simpmap.
apply interp_guard; auto.
so (IH2 _ IHo Hwc Hw) as H.
simpmapin H.
exact H.
}

(* equal *)
{
intros pg s i a m n p q A Hmp Hnq Hint IH w IHo Hwc Hstop.
simpmap.
so (le_ord_trans _#3 (cin_top pg) (succ_nodecrease _)) as h.
so (semantics_level_internal _#5 h IHo Hint) as (A' & ->).
assert (srel s (den (extend_iurel h A')) i (restrict_term w m) p) as Hmp'.
  {
  rewrite -> den_extend_iurel.
  rewrite -> extend_srel.
  rewrite -> restrict_extend.
  rewrite -> (extend_term_compose_up w stop (cin pg)); auto.
  rewrite -> extend_term_compose_down; auto.
  eauto using cin_cex, le_ord_trans, lt_ord_impl_le_ord.
  }
assert (srel s (den (extend_iurel h A')) i (restrict_term w n) q) as Hnq'.
  {
  rewrite -> den_extend_iurel.
  rewrite -> extend_srel.
  rewrite -> restrict_extend.
  rewrite -> (extend_term_compose_up w stop (cin pg)); auto.
  rewrite -> extend_term_compose_down; auto.
  eauto using cin_cex, le_ord_trans, lt_ord_impl_le_ord.
  }
cbn.
match goal with
| |- basicv _ _ _ _ _ ?X =>
replace X
  with  (iuequal stop s i (extend_iurel h A') (restrict_term w m) (restrict_term w n) p q Hmp' Hnq')
end.
2:{
  apply iuequal_equal; auto.
  }
apply interp_equal.
apply IH; auto.
}

(* sequal *)
{
intros s i m n Hclm Hcln Hequiv w IHo Hwc Hw.
simpmap.
apply interp_sequal; auto using map_hygiene, map_equiv.
}

(* all *)
{
intros pg s i lv k a gpg K A h Hintlv Hintk IH1 Hle _ IH2 w IHo Hwc Hw.
simpmap.
apply (interp_all _#7 gpg _ _ h); eauto using map_hygiene, restrict_pginterp.
  {
  apply IH1; auto.
    {
    eapply levind_decrease; eauto.
    apply str_mono; auto.
    }
  
    {
    eapply le_lt_ord_trans; eauto.
    apply cex_mono; auto.
    }
  }
intros j Hj x.
so (IH2 j Hj x w IHo Hwc Hw) as H.
simpmapin H.
refine (semantics_restriction anderr _#6 IHo _ H); clear H.
apply restriction_funct1; auto using restriction_refl.
apply (restriction_decrease _ w); auto using lt_ord_impl_le_ord.
rewrite <- restrict_ext.
apply restriction_oper.
apply restriction_cons.
  {
  fold (restrict_term w (fromsp stop gpg (Model.approx j K))).
  rewrite -> restrict_extend.
  so (kinterp_level_bound _#5 Hintk) as HlevK.
  assert (level (Model.approx j K) << w) as HlevKw.
    {
    eapply le_lt_ord_trans.
      {
      apply approx_level.
      }
    eapply le_lt_ord_trans; eauto.
    eapply le_lt_ord_trans.
      {
      exact (cin_mono _ _ Hle).
      }
    eapply le_lt_ord_trans; eauto.
    apply cin_cex.
    }
  so (lt_le_ord_trans _#3 HlevKw Hw) as HlevKstop.
  rewrite -> !extend_fromsp; auto.
  apply restriction_refl.
  }
apply restriction_cons; [| apply restriction_nil].
apply restrict_impl_restriction.
}

(* alltp *)
{
intros pg s i a A _ IH w IHo Hwc Hw.
simpmap.
apply interp_alltp.
intros j Hj X.
so (IH j Hj X w IHo Hwc Hw) as H.
simpmapin H.
refine (semantics_restriction anderr _#6 IHo _ H); clear H.
apply restriction_funct1; auto using restriction_refl.
apply (restriction_decrease _ w); auto using lt_ord_impl_le_ord.
rewrite <- restrict_extt.
apply restrict_impl_restriction.
}

(* exist *)
{
intros pg s i lv k a gpg K A h Hintlv Hintk IH1 Hle _ IH2 w IHo Hwc Hw.
simpmap.
apply (interp_exist _#7 gpg _ _ h); eauto using map_hygiene, restrict_pginterp.
  {
  apply IH1; auto.
    {
    eapply levind_decrease; eauto.
    apply str_mono; auto.
    }
  
    {
    eapply le_lt_ord_trans; eauto.
    apply cex_mono; auto.
    }
  }
intros j Hj x.
so (IH2 j Hj x w IHo Hwc Hw) as H.
simpmapin H.
refine (semantics_restriction anderr _#6 IHo _ H); clear H.
apply restriction_funct1; auto using restriction_refl.
apply (restriction_decrease _ w); auto using lt_ord_impl_le_ord.
rewrite <- restrict_ext.
apply restriction_oper.
apply restriction_cons.
  {
  fold (restrict_term w (fromsp stop gpg (Model.approx j K))).
  rewrite -> restrict_extend.
  so (kinterp_level_bound _#5 Hintk) as HlevK.
  assert (level (Model.approx j K) << w) as HlevKw.
    {
    eapply le_lt_ord_trans.
      {
      apply approx_level.
      }
    eapply le_lt_ord_trans; eauto.
    eapply le_lt_ord_trans.
      {
      exact (cin_mono _ _ Hle).
      }
    eapply le_lt_ord_trans; eauto.
    apply cin_cex.
    }
  so (lt_le_ord_trans _#3 HlevKw Hw) as HlevKstop.
  rewrite -> !extend_fromsp; auto.
  apply restriction_refl.
  }
apply restriction_cons; [| apply restriction_nil].
apply restrict_impl_restriction.
}

(* extt *)
{
intros pg s i w' R h Hw' w IHo Hwc Hw.
simpmap.
unfold restrict.
rewrite -> objout_objin.
cbn.
rewrite -> (lt_ord_dec_is _ _ (le_lt_ord_trans _#3 (le_ord_trans _#3 Hw' (cin_cex pg)) Hwc)).
apply interp_extt; auto.
}

(* mu *)
{
intros pg v s i a F Hv _ IH Hne Hmono Hrobust w IHo Hwc Hw.
simpmap.
apply interp_mu; auto.
  {
  intros X hv.
  so (IH X hv w IHo Hwc Hw) as H.
  simpmapin H.
  force_exact H; clear H.
  do 3 f_equal.
  unfold restrict.
  rewrite -> objout_objin.
  cbn.
  rewrite -> (lt_ord_dec_is _ _ (le_lt_ord_trans _#3 (le_ord_trans _#3 Hv (cin_cex pg)) Hwc)).
  reflexivity.
  }

  {
  eapply map_robust; eauto.
  }
}

(* ispositive *)
{
intros pg s i a Hcl w _ Hwc Hw.
simpmap.
replace (ispositive_urel stop i a) with (ispositive_urel stop i (map_term (restrict w) a)).
2:{
  apply property_urel_extensionality; auto.
  intros _ _.
  split; intro H; [eapply map_positive_conv | apply map_positive]; eauto.
  }
apply interp_ispositive.
apply map_hygiene; auto.
}

(* isnegative *)
{
intros pg s i a Hcl w _ Hwc Hw.
simpmap.
replace (isnegative_urel stop i a) with (isnegative_urel stop i (map_term (restrict w) a)).
2:{
  apply property_urel_extensionality; auto.
  intros _ _.
  split; intro H; [eapply map_negative_conv | apply map_negative]; eauto.
  }
apply interp_isnegative.
apply map_hygiene; auto.
}

(* rec *)
{
intros pg s i k K _ IH w IHo Hwc Hw.
simpmap.
apply interp_rec.
so (IH _ IHo Hwc Hw) as H.
simpmapin H.
exact H.
}

(* halts *)
{
intros pg s i m Hcl w IHo Hwc Hw.
simpmap.
replace (halts_urel stop i m) with (halts_urel stop i (map_term (restrict w) m)).
2:{
  apply property_urel_extensionality; auto.
  intros j Hj.
  symmetry.
  apply map_converges_iff.
  }
apply interp_halts.
apply map_hygiene; auto.
}

(* kinterp *)
{
intros pg s i k k' K Hcl Hsteps _ IH w IHo Hwc Hw.
apply (kinterp_eval _#5 (map_term (restrict w) k')); auto using map_hygiene, map_steps.
}

(* cinterp *)
{
intros pg s i c c' Q Hcl Hsteps _ IH w IHo Hwc Hw.
apply (cinterp_eval _#5 (map_term (restrict w) c')); auto using map_hygiene, map_steps.
}

(* interp *)
{
intros pg s i a a' R Hcl Hsteps _ IH w IHo Hwc Hw.
apply (interp_eval _#5 (map_term (restrict w) a')); auto using map_hygiene, map_steps.
}

(* functional *)
{
intros pg s i A b B Hcl Hcoarse _ IH w IHo Hwc Hw.
apply functional_i; auto using map_hygiene.
intros j m p Hj Hmp.
so (IH j m p Hj Hmp w IHo Hwc Hw) as H.
refine (semantics_restriction anderr _#6 IHo _ H); clear H.
simpmap.
apply restriction_funct1; auto using restriction_refl.
apply (restriction_decrease _ w); auto using lt_ord_impl_le_ord.
apply restrict_impl_restriction.
}

(* wrapup *)
{
destruct Hind as (Hk & _ & Hy & _).
split; intros; [apply Hk | apply Hy]; auto.
}
Qed.


Lemma semantics_levind :
  forall w, levind w.
Proof.
intros w.
wfinduct w using lt_ord_wf.
intros w IH.
do2 3 split.
  {
  intros pg s i a a' R Hwn Hwc Hrest Hint.
  eapply semantics_restriction; eauto.
  }

  {
  intros pg s i a a' R Hwn Hwc Hrest Hint.
  eapply semantics_restriction; eauto.
  }

  {
  intros pg s i a R v Hwn Hwc Hv Hint.
  eapply semantics_level_external; eauto.
  }

  {
  intros pg s i a R v Hwn Hwc Hv Hint.
  eapply semantics_level_external; eauto.
  }
Qed.


Lemma interp_level_internal :
  forall pg s i a R (h : cin pg <<= stop),
    interp pg s i a R
    -> exists R', R = extend_iurel h R'.
Proof.
intros pg s i a R h Hint.
eapply semantics_level_internal; eauto using semantics_levind.
Qed.


(* Not currently used. *)
Lemma interp_level_external :
  forall pg s i a R,
   interp pg s i a R
    -> interp pg s i (restrict_term (succ (cex pg)) a) R.
Proof.
intros pg s i a R Hint.
eapply semantics_level_external; eauto using semantics_levind, succ_increase.
apply le_ord_succ.
apply cex_top.
Qed.


(* Not currently used. *)
Lemma interp_restriction :
  forall pg s i a a' R,
    restriction (succ (cex pg)) a a'
    -> interp pg s i a R
    -> interp pg s i a' R.
Proof.
intros pg s i a a' R Hrest Hint.
eapply semantics_restriction; eauto using semantics_levind.
Qed.


Require Import ProperFun.


Lemma interp_fun :
  forall pg pg' s i a R R',
    interp pg s i a R
    -> interp pg' s i a R'
    -> R = R'.
Proof.
intros pg1 pg2 s i a R R' H1 H2.
so (interp_increase _#6 (le_page_max_l pg1 pg2) H1) as H1'.
so (interp_increase _#6 (le_page_max_r pg1 pg2) H2) as H2'.
exact (basic_fun _#7 H1' H2').
Qed.
