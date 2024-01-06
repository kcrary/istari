
Require Import Coq.Arith.Arith.

Require Import Axioms.

Require Import Tactics.
Require Import Sigma.
Require Import Equality.
Require Import Ordinal.
Require Import Page.

Import List.ListNotations.


Section object.


Variable object : Type.


Inductive operator : list nat -> Type :=
| oper_univ        : operator [0]
| oper_cty         : operator [0]
| oper_con         : operator [0; 0]

| oper_karrow      : operator [0; 0]
| oper_arrow       : operator [0; 0]
| oper_pi          : operator [0; 1]
| oper_clam        : operator [0; 1]
| oper_capp        : operator [0; 0]
| oper_ctlam       : operator [0; 1; 0]
| oper_ctapp       : operator [0; 0]
| oper_lam         : operator [1]
| oper_app         : operator [0; 0]

| oper_intersect   : operator [0; 1]
| oper_union       : operator [0; 1]

| oper_fut         : operator [0]
| oper_cnext       : operator [0]
| oper_cprev       : operator [0]
| oper_next        : operator [0]
| oper_prev        : operator [0]

| oper_rec         : operator [1]
 
| oper_equal       : operator [0; 0; 0]

| oper_triv        : operator nil

| oper_eqtype      : operator [0; 0]

| oper_sequal      : operator [0; 0]

| oper_subtype     : operator [0; 0]

| oper_kuniv       : operator [0]

| oper_all         : operator [0; 0; 1]
| oper_alltp       : operator [1]

| oper_exist       : operator [0; 0; 1]

| oper_mu          : operator [1]
| oper_ispositive  : operator [1]
| oper_isnegative  : operator [1]

| oper_voidtp      : operator nil

| oper_unittp      : operator nil
| oper_cunit       : operator nil

| oper_booltp      : operator nil
| oper_btrue       : operator nil
| oper_bfalse      : operator nil
| oper_bite        : operator [0; 0; 0]

| oper_prod        : operator [0; 0]
| oper_sigma       : operator [0; 1]
| oper_cpair       : operator [0; 0]
| oper_cpi1        : operator [0]
| oper_cpi2        : operator [0]
| oper_ppair       : operator [0; 0]
| oper_ppi1        : operator [0]
| oper_ppi2        : operator [0]

| oper_set         : operator [0; 1]
| oper_iset        : operator [0; 1]

| oper_quotient    : operator [0; 2]

| oper_guard       : operator [0; 0]

| oper_wt          : operator [0; 1]

(* Candidates used for impredicative quantification. *)
| oper_ext         : object -> operator nil

(* Degenerate candidates used for inductive types. *)
| oper_extt        : object -> operator nil
.


Inductive term : Type :=
| var : nat -> term
| oper : forall a, operator a -> row a -> term

with row : list nat -> Type :=
| rw_nil : row nil
| rw_cons : forall i a, term -> row a -> row (i :: a)
.


Scheme term_mut_ind := Induction for term Sort Prop
with   row_mut_ind := Induction for row Sort Prop.
Combined Scheme syntax_ind from term_mut_ind, row_mut_ind.

Scheme term_mut_rect := Induction for term Sort Type
with   row_mut_rect := Induction for row Sort Type.


Lemma row_nil_invert : forall (r : row nil), r = rw_nil.
Proof.
intros r.
apply eq_dep_impl_eq_snd.
set (a := nil) in r |- * at 1.
assert (a = nil) as Heq by reflexivity.
clearbody a.
revert Heq.
cases r; auto.
intros; discriminate.
Qed.


Lemma row_cons_invert :
  forall i a (r : row (cons i a)),
    exists m (s : row a),
      r = rw_cons i a m s.
Proof.
intros i a r.
cut (exists m s, eq_dep _ row (cons i a) r (cons i a) (rw_cons i a m s)).
  {
  intros (m & s & Heq).
  exists m, s.
  exact (eq_dep_impl_eq_snd _#5 Heq).
  }
set (b := cons i a) in r |- * at 1.
assert (b = cons i a) as Heq by reflexivity.
clearbody b.
revert Heq.
cases r; try (intros; discriminate).
intros i' a' m r Heq.
injection Heq.
intros -> ->.
exists m, r.
apply eq_dep_refl.
Qed.


Lemma row_invert_auto :
  forall a (r : row a),
    list_rect (fun a => (row a -> Prop) -> Prop)
      (fun P => P rw_nil)
      (fun i a IH P =>
         exists m,
           IH (fun r => P (rw_cons i a m r)))
      a
      (eq r).
Proof.
intros a.
induct a.

(* nil *)
{
intro r.
cbn.
apply row_nil_invert.
}

(* cons *)
{
intros i a IH rr.
cbn.
so (row_cons_invert _ _ rr) as (m & r & ->).
exists m.
force_exact (IH r).
f_equal.
fextensionality 1.
intro r'.
pextensionality.
  {
  intros <-; auto.
  }

  {
  intros Heq.
  injection Heq.
  intro H.
  injectionT H.
  auto.
  }
}
Qed.


Inductive hyp : Type :=
| hyp_tpl : hyp
| hyp_tp  : hyp
| hyp_tml : term -> hyp
| hyp_tm  : term -> hyp
| hyp_emp : hyp
.


Definition context := list hyp.


Inductive judgement : Type :=
| deq : (* tm *) term -> term -> (* cn *) term -> judgement
.


Fixpoint traverse (resolve : nat -> nat -> term) (i : nat) (m : term) {struct m} : term
  :=
  (match m with
   | var j => resolve i j
   | oper a t r => oper a t (traverse_row resolve i a r)
   end)

with traverse_row (resolve : nat -> nat -> term) (i : nat) (a : list nat) (r : row a) {struct r} : row a
  :=
  (match r
   in row a
   return row a
   with
   | rw_nil => rw_nil
   | rw_cons j a m r => rw_cons j a (traverse resolve (j+i) m) (traverse_row resolve i a r)
   end)
.


Lemma traverse_var :
  forall resolve i j,
    traverse resolve i (var j) = resolve i j.
Proof.
auto.
Qed.


Lemma traverse_oper :
  forall resolve i a t r,
    traverse resolve i (oper a t r)
    =
    oper a t (traverse_row resolve i a r).
Proof.
intros; reflexivity.
Qed.


Lemma traverse_row_cons :
  forall resolve i j a m r,
    traverse_row resolve i (cons j a) (rw_cons j a m r)
    =
    rw_cons j a
      (traverse resolve (j+i) m)
      (traverse_row resolve i a r).
Proof.
intros; reflexivity.
Qed.


Lemma traverse_row_nil :
  forall resolve i,
    traverse_row resolve i nil rw_nil = rw_nil.
Proof.
intros; reflexivity.
Qed.


Lemma traverse_parametric :
  forall (P : nat -> nat -> Prop) resolve resolve',
    (forall i i', P i i' -> P (S i) (S i'))
    -> (forall i i' j, P i i' -> resolve i j = resolve' i' j)
    -> forall i i' t, P i i' -> traverse resolve i t = traverse resolve' i' t.
Proof.
intros P resolve resolve' Pcomp.
revert resolve resolve'.
assert (forall j i i', P i i' -> P (j + i) (j + i')) as Hcomp'.
  intro j.
  induct j.
  (* 0 *)
  intros i i' H.
  exact H.

  (* S *)
  intros j IH i i' HP.
  simpl.
  auto; done.
intros resolve resolve' Hres i i' t.
revert t i i'.
apply
  (term_mut_ind
     (fun m => forall i i', P i i' -> traverse resolve i m = traverse resolve' i' m)
     (fun a r => forall i i', P i i' -> traverse_row resolve i a r = traverse_row resolve' i' a r));
try (intros; simpl; eauto; f_equal; eauto; done).
Qed.


Lemma traverse_id :
  forall resolve,
    (forall i j, resolve i j = var j)
    -> forall i t, traverse resolve i t = t.
Proof.
intros resolve Hres i m.
revert m i.
apply
  (term_mut_ind
     (fun m => forall i, traverse resolve i m = m)
     (fun a r => forall i, traverse_row resolve i a r = r));
intros; simpl; f_equal; eauto.
Qed.


Lemma traverse_compose :
  forall resolve resolve' i t,
    traverse resolve i (traverse resolve' i t)
    = traverse
      (fun i' j => traverse resolve i' (resolve' i' j))
      i t.
Proof.
intros resolve resolve' i m.
revert m i.
apply
  (term_mut_ind
     (fun m =>
        forall i, 
          traverse resolve i (traverse resolve' i m)
          = traverse (fun i' j => traverse resolve i' (resolve' i' j)) i m)
     (fun a r =>
        forall i, 
          traverse_row resolve i a (traverse_row resolve' i a r)
          = traverse_row (fun i' j => traverse resolve i' (resolve' i' j)) i a r));
intros; simpl; f_equal; eauto.
Qed.


(* Obsolete *)
Ltac invert_row_cons r :=
match type of r with
| row ?a =>
    let i := fresh "i"
    in let x := fresh "a"
    in let m := fresh "m"
    in let Heq := fresh "Heq"
    in
      remember a as x eqn:Heq in r;
      revert Heq;
      cases r; [intro Heq; discriminate Heq |];
      intros i' x m r Heq;
      injection Heq;
      clear Heq;
      intros -> ->;
      revert m r
end.


(* Obsolete *)
Ltac invert_row_nil r :=
let x := fresh "a"
in let Heq := fresh "Heq"
in
  remember (@nil nat) as x eqn:Heq in r;
  revert Heq;
  cases r; [| intros ? ? ? ? Heq; discriminate Heq];
  intros _.


Inductive Forallr (P : term -> Type) : forall a, row a -> Type :=
| Forallr_nil
    : Forallr P nil rw_nil

| Forallr_cons {i a m r}
    : P m
      -> Forallr P a r
      -> Forallr P (cons i a) (rw_cons i a m r)
.


Lemma term_row_rect :
  forall (P : term -> Type),
    (forall i, P (var i))
    -> (forall a t r, Forallr P a r -> P (oper a t r))
    -> forall m, P m.
Proof.
intros P H1 H2 m.
apply (term_mut_rect P (Forallr P)); eauto using Forallr.
Qed.


Lemma oper_injection :
  forall a t t' r r',
    oper a t r = oper a t' r'
    -> t = t' /\ r = r'.
Proof.
intros a t t' r r' Heq.
injection Heq.
intros Heqr Heqt.
destruct (eq_dep_impl_eq _#6 (EqdepFacts.eq_sigT_eq_dep _#6 Heqt)) as (h & Heqt').
substrefl h.
cbn in Heqt'.
destruct (eq_dep_impl_eq _#6 (EqdepFacts.eq_sigT_eq_dep _#6 Heqr)) as (h & Heqr').
substrefl h.
cbn in Heqr'.
auto.
Qed.


Lemma rw_cons_injection :
  forall j a m m' r r',
    rw_cons j a m r = rw_cons j a m' r'
    -> m = m' /\ r = r'.
Proof.
intros j a m m' r r' Heq.
injection Heq.
intros Heq' Heqm.
destruct (eq_dep_impl_eq _#6 (EqdepFacts.eq_sigT_eq_dep _#6 Heq')) as (h & Heq'').
substrefl h.
cbn in Heq''.
auto.
Qed.
    

(* obsolete *)
Lemma invertrow :
  forall l (r : row l),
    (fix P (l : list nat) : (row l -> Type) -> Type :=
       match l
         as l
         return (row l -> Type) -> Type
       with
       | nil => fun Q => Q rw_nil

       | cons a l' =>
           fun Q =>
             existsT x,
               P l' (fun r => Q (rw_cons _ _ x r))
       end)
    l (fun r' => r = r').
Proof.
intros l.
induct l.

(* nil *)
{
intro r.
cases r.
reflexivity.
}

(* cons *)
{
intros n a IH r.
cases r.
intros n' a' t r Heq.
injection Heq.
intros -> ->.
substrefl Heq.
exists t.
so (IH r) as H.
replace (fun r' => rw_cons n a t r = rw_cons n a t r') with (fun r' => r = r').
2:{
  fextensionality 1.
  intro r''.
  pextensionality.
  - intro.
    subst r''.
    reflexivity.
  
  - intro Heq.
    injectionc Heq.
    intro Heq.
    eapply inj_pair2_UIP; eauto.
    intros; apply proof_irrelevance; done.
  }
exact H.
}
Qed.


End object.


Arguments var {object}.
Arguments oper {object}.
Arguments rw_nil {object}.
Arguments rw_cons {object}.

Arguments hyp {object}.
Arguments context {object}.
Arguments judgement {object}.

Definition univ {obj} m            : @term obj := oper _ (oper_univ _) (rw_cons _ _ m rw_nil).
Definition cty {obj} m             : @term obj := oper _ (oper_cty _) (rw_cons _ _ m rw_nil).
Definition con {obj} m1 m2         : @term obj := oper _ (oper_con _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition karrow {obj} m1 m2       : @term obj := oper _ (oper_karrow _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition arrow {obj} m1 m2       : @term obj := oper _ (oper_arrow _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition pi {obj} m1 m2          : @term obj := oper _ (oper_pi _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition clam {obj} m1 m2        : @term obj := oper _ (oper_clam _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition capp {obj} m1 m2        : @term obj := oper _ (oper_capp _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition ctlam {obj} m1 m2 m3  : @term obj := oper _ (oper_ctlam _) (rw_cons _ _ m1 (rw_cons _ _ m2 (rw_cons _ _ m3 rw_nil))).
Definition ctapp {obj} m1 m2       : @term obj := oper _ (oper_ctapp _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition lam {obj} m             : @term obj := oper _ (oper_lam _) (rw_cons _ _ m rw_nil).
Definition app {obj} m1 m2         : @term obj := oper _ (oper_app _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition intersect {obj} m1 m2   : @term obj := oper _ (oper_intersect _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition union {obj} m1 m2       : @term obj := oper _ (oper_union _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition fut {obj} m             : @term obj := oper _ (oper_fut _) (rw_cons _ _ m rw_nil).
Definition cnext {obj} m           : @term obj := oper _ (oper_cnext _) (rw_cons _ _ m rw_nil).
Definition cprev {obj} m           : @term obj := oper _ (oper_cprev _) (rw_cons _ _ m rw_nil).
Definition next {obj} m            : @term obj := oper _ (oper_next _) (rw_cons _ _ m rw_nil).
Definition prev {obj} m            : @term obj := oper _ (oper_prev _) (rw_cons _ _ m rw_nil).
Definition rec {obj} m             : @term obj := oper _ (oper_rec _) (rw_cons _ _ m rw_nil).
Definition equal {obj} m1 m2 m3    : @term obj := oper _ (oper_equal _) (rw_cons _ _ m1 (rw_cons _ _ m2 (rw_cons _ _ m3 rw_nil))).
Definition triv {obj}              : @term obj := oper _ (oper_triv _) rw_nil.
Definition eqtype {obj} m1 m2      : @term obj := oper _ (oper_eqtype _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition sequal {obj} m1 m2      : @term obj := oper _ (oper_sequal _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition subtype {obj} m1 m2     : @term obj := oper _ (oper_subtype _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition kuniv {obj} m           : @term obj := oper _ (oper_kuniv _) (rw_cons _ _ m rw_nil).
Definition all {obj} m1 m2 m3      : @term obj := oper _ (oper_all _) (rw_cons _ _ m1 (rw_cons _ _ m2 (rw_cons _ _ m3 rw_nil))).
Definition alltp {obj} m1          : @term obj := oper _ (oper_alltp _) (rw_cons _ _ m1 rw_nil).
Definition exist {obj} m1 m2 m3    : @term obj := oper _ (oper_exist _) (rw_cons _ _ m1 (rw_cons _ _ m2 (rw_cons _ _ m3 rw_nil))).
Definition mu {obj} m              : @term obj := oper _ (oper_mu _) (rw_cons _ _ m rw_nil).
Definition ispositive {obj} m      : @term obj := oper _ (oper_ispositive _) (rw_cons _ _ m rw_nil).
Definition isnegative {obj} m      : @term obj := oper _ (oper_isnegative _) (rw_cons _ _ m rw_nil).
Definition voidtp {obj}            : @term obj := oper _ (oper_voidtp _) rw_nil.
Definition unittp {obj}            : @term obj := oper _ (oper_unittp _) rw_nil.
Definition cunit {obj}             : @term obj := oper _ (oper_cunit _) rw_nil.
Definition booltp {obj}            : @term obj := oper _ (oper_booltp _) rw_nil.
Definition btrue {obj}             : @term obj := oper _ (oper_btrue _) rw_nil.
Definition bfalse {obj}            : @term obj := oper _ (oper_bfalse _) rw_nil.
Definition bite {obj} m1 m2 m3     : @term obj := oper _ (oper_bite _) (rw_cons _ _ m1 (rw_cons _ _ m2 (rw_cons _ _ m3 rw_nil))).
Definition prod {obj} m1 m2        : @term obj := oper _ (oper_prod _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition sigma {obj} m1 m2       : @term obj := oper _ (oper_sigma _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition cpair {obj} m1 m2       : @term obj := oper _ (oper_cpair _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition cpi1 {obj} m            : @term obj := oper _ (oper_cpi1 _) (rw_cons _ _ m rw_nil).
Definition cpi2 {obj} m            : @term obj := oper _ (oper_cpi2 _) (rw_cons _ _ m rw_nil).
Definition ppair {obj} m1 m2       : @term obj := oper _ (oper_ppair _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition ppi1 {obj} m            : @term obj := oper _ (oper_ppi1 _) (rw_cons _ _ m rw_nil).
Definition ppi2 {obj} m            : @term obj := oper _ (oper_ppi2 _) (rw_cons _ _ m rw_nil).
Definition set {obj} m1 m2         : @term obj := oper _ (oper_set _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition iset {obj} m1 m2        : @term obj := oper _ (oper_iset _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition quotient {obj} m1 m2    : @term obj := oper _ (oper_quotient _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition guard {obj} m1 m2       : @term obj := oper _ (oper_guard _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition wt {obj} m1 m2          : @term obj := oper _ (oper_wt _) (rw_cons _ _ m1 (rw_cons _ _ m2 rw_nil)).
Definition ext {obj} x             : @term obj := oper _ (oper_ext _ x) rw_nil.
Definition extt {obj} x            : @term obj := oper _ (oper_extt _ x) rw_nil.


Definition deqtype {object} a b := @deq object triv triv (eqtype a b).
Definition dsubtype {object} a b := @deq object triv triv (subtype a b).


Arguments hyp_tpl  {object}.
Arguments hyp_tp {object}.
Arguments hyp_tml {object}.
Arguments hyp_tm {object}.
Arguments hyp_emp {object}.
Arguments deq {object}.


(* The choice here is arbitrary.  Any value would do. *)
Definition arb {object} := @triv object.


Inductive same_operator {A B : Type} : forall a b, operator A a -> operator B b -> Prop :=
| same_univ :
    same_operator [0] [0] (oper_univ A) (oper_univ B)

| same_cty :
    same_operator [0] [0] (oper_cty A) (oper_cty B)

| same_con :
    same_operator [0; 0] [0; 0] (oper_con A) (oper_con B)

| same_karrow :
    same_operator [0; 0] [0; 0] (oper_karrow A) (oper_karrow B)

| same_arrow :
    same_operator [0; 0] [0; 0] (oper_arrow A) (oper_arrow B)

| same_pi :
    same_operator [0; 1] [0; 1] (oper_pi A) (oper_pi B)

| same_clam :
    same_operator [0; 1] [0; 1] (oper_clam A) (oper_clam B)

| same_capp :
    same_operator [0; 0] [0; 0] (oper_capp A) (oper_capp B)

| same_ctlam :
    same_operator [0; 1; 0] [0; 1; 0] (oper_ctlam A) (oper_ctlam B)

| same_ctapp :
    same_operator [0; 0] [0; 0] (oper_ctapp A) (oper_ctapp B)

| same_lam :
    same_operator [1] [1] (oper_lam A) (oper_lam B)

| same_app :
    same_operator [0; 0] [0; 0] (oper_app A) (oper_app B)

| same_intersect :
    same_operator [0; 1] [0; 1] (oper_intersect A) (oper_intersect B)

| same_union :
    same_operator [0; 1] [0; 1] (oper_union A) (oper_union B)

| same_fut :
    same_operator [0] [0] (oper_fut A) (oper_fut B)

| same_cnext :
    same_operator [0] [0] (oper_cnext A) (oper_cnext B)

| same_cprev :
    same_operator [0] [0] (oper_cprev A) (oper_cprev B)

| same_next :
    same_operator [0] [0] (oper_next A) (oper_next B)

| same_prev :
    same_operator [0] [0] (oper_prev A) (oper_prev B)

| same_rec :
    same_operator [1] [1] (oper_rec A) (oper_rec B)

| same_equal :
    same_operator [0; 0; 0] [0; 0; 0] (oper_equal A) (oper_equal B)

| same_triv :
    same_operator nil nil (oper_triv A) (oper_triv B)

| same_eqtype :
    same_operator [0; 0] [0; 0] (oper_eqtype A) (oper_eqtype B)

| same_sequal :
    same_operator [0; 0] [0; 0] (oper_sequal A) (oper_sequal B)

| same_subtype :
    same_operator [0; 0] [0; 0] (oper_subtype A) (oper_subtype B)

| same_kuniv :
    same_operator [0] [0] (oper_kuniv A) (oper_kuniv B)

| same_all :
    same_operator [0; 0; 1] [0; 0; 1] (oper_all A) (oper_all B)

| same_alltp :
    same_operator [1] [1] (oper_alltp A) (oper_alltp B)

| same_exist :
    same_operator [0; 0; 1] [0; 0; 1] (oper_exist A) (oper_exist B)

| same_mu :
    same_operator [1] [1] (oper_mu A) (oper_mu B)

| same_ispositive :
    same_operator [1] [1] (oper_ispositive A) (oper_ispositive B)

| same_isnegative :
    same_operator [1] [1] (oper_isnegative A) (oper_isnegative B)

| same_voidtp :
    same_operator nil nil (oper_voidtp A) (oper_voidtp B)

| same_unittp :
    same_operator nil nil (oper_unittp A) (oper_unittp B)

| same_cunit :
    same_operator nil nil (oper_cunit A) (oper_cunit B)

| same_booltp :
    same_operator nil nil (oper_booltp A) (oper_booltp B)

| same_btrue :
    same_operator nil nil (oper_btrue A) (oper_btrue B)

| same_bfalse :
    same_operator nil nil (oper_bfalse A) (oper_bfalse B)

| same_bite :
    same_operator [0; 0; 0] [0; 0; 0] (oper_bite A) (oper_bite B)

| same_prod :
    same_operator [0; 0] [0; 0] (oper_prod A) (oper_prod B)

| same_sigma :
    same_operator [0; 1] [0; 1] (oper_sigma A) (oper_sigma B)

| same_cpair :
    same_operator [0; 0] [0; 0] (oper_cpair A) (oper_cpair B)

| same_cpi1 :
    same_operator [0] [0] (oper_cpi1 A) (oper_cpi1 B)

| same_cpi2 :
    same_operator [0] [0] (oper_cpi2 A) (oper_cpi2 B)

| same_ppair :
    same_operator [0; 0] [0; 0] (oper_ppair A) (oper_ppair B)

| same_ppi1 :
    same_operator [0] [0] (oper_ppi1 A) (oper_ppi1 B)

| same_ppi2 :
    same_operator [0] [0] (oper_ppi2 A) (oper_ppi2 B)

| same_set :
    same_operator [0; 1] [0; 1] (oper_set A) (oper_set B)

| same_iset :
    same_operator [0; 1] [0; 1] (oper_iset A) (oper_iset B)

| same_quotient :
    same_operator [0; 2] [0; 2] (oper_quotient A) (oper_quotient B)

| same_guard :
    same_operator [0; 0] [0; 0] (oper_guard A) (oper_guard B)

| same_wt :
    same_operator [0; 1] [0; 1] (oper_wt A) (oper_wt B)

| same_ext {x y} :
    same_operator nil nil (oper_ext A x) (oper_ext B y)

| same_extt {x y} :
    same_operator nil nil (oper_extt A x) (oper_extt B y)
.


Hint Constructors same_operator : same_operator.
