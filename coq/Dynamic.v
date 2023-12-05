
Require Import Tactics.
Require Import Syntax.
Require Import Relation.
Require Import Subst.
Require Import SimpSub.


Section object.


Arguments operator {object}.
Arguments term {object}.
Arguments row {object}.


Variable object : Type.


Inductive canon : forall {a}, @operator object a -> Prop :=
| canon_univ           : canon (oper_univ _)
| canon_cty            : canon (oper_cty _)
| canon_con            : canon (oper_con _)
| canon_karrow         : canon (oper_karrow _)
| canon_arrow          : canon (oper_arrow _)
| canon_pi             : canon (oper_pi _)
| canon_clam           : canon (oper_clam _)
| canon_capp           : canon (oper_capp _)
| canon_ctlam          : canon (oper_ctlam _)
| canon_ctapp          : canon (oper_ctapp _)
| canon_lam            : canon (oper_lam _)
| canon_intersect      : canon (oper_intersect _)
| canon_union          : canon (oper_union _)
| canon_fut            : canon (oper_fut _)
| canon_cnext          : canon (oper_cnext _)
| canon_cprev          : canon (oper_cprev _)
| canon_next           : canon (oper_next _)
| canon_rec            : canon (oper_rec _)
| canon_equal          : canon (oper_equal _)
| canon_triv           : canon (oper_triv _)
| canon_eqtype         : canon (oper_eqtype _)
| canon_subtype        : canon (oper_subtype _)
| canon_kunit          : canon (oper_kuniv _)
| canon_all            : canon (oper_all _)
| canon_alltp          : canon (oper_alltp _)
| canon_exist          : canon (oper_exist _)
| canon_mu             : canon (oper_mu _)
| canon_ispositive     : canon (oper_ispositive _)
| canon_isnegative     : canon (oper_isnegative _)
| canon_voidtp         : canon (oper_voidtp _)
| canon_unittp         : canon (oper_unittp _)
| canon_cunit          : canon (oper_cunit _)
| canon_booltp         : canon (oper_booltp _)
| canon_btrue          : canon (oper_btrue _)
| canon_bfalse         : canon (oper_bfalse _)
| canon_prod           : canon (oper_prod _)
| canon_sigma          : canon (oper_sigma _)
| canon_cpair          : canon (oper_cpair _)
| canon_cpi1           : canon (oper_cpi1 _)
| canon_cpi2           : canon (oper_cpi2 _)
| canon_ppair          : canon (oper_ppair _)
| canon_set            : canon (oper_set _)
| canon_iset           : canon (oper_iset _)
| canon_quotient       : canon (oper_quotient _)
| canon_guard          : canon (oper_guard _)
| canon_wt             : canon (oper_wt _)
| canon_ext {x}        : canon (oper_ext _ x)
| canon_extt {x}       : canon (oper_extt _ x)
.


Inductive value : term -> Prop :=
| value_i {a t r} :
    canon t
    -> value (oper a t r)
.


Inductive step : @term object -> term -> Prop :=
| step_app1 {m1 m1' m2} :
    step m1 m1'
    -> step (app m1 m2) (app m1' m2)

| step_app2 {m1 m2} :
    step (app (lam m1) m2) (subst1 m2 m1)

| step_prev1 {m m'} :
    step m m'
    -> step (prev m) (prev m')

| step_prev2 {m} :
    step (prev (next m)) m

| step_bite1 {m1 m1' m2 m3} :
    step m1 m1'
    -> step (bite m1 m2 m3) (bite m1' m2 m3)

| step_bite2 {m1 m2} :
    step (bite btrue m1 m2) m1

| step_bite3 {m1 m2} :
    step (bite bfalse m1 m2) m2

| step_ppi11 {m m'} :
    step m m'
    -> step (ppi1 m) (ppi1 m')

| step_ppi12 {m1 m2} :
    step (ppi1 (ppair m1 m2)) m1

| step_ppi21 {m m'} :
    step m m'
    -> step (ppi2 m) (ppi2 m')

| step_ppi22 {m1 m2} :
    step (ppi2 (ppair m1 m2)) m2
.


Definition eval m v :=
  star step m v
  /\ value v.


Lemma eval_value :
  forall v, value v -> eval v v.
Proof.
intros v H.
split; eauto using star_refl.
Qed.


Lemma determinism_value :
  forall m m',
    value m
    -> step m m'
    -> False.
Proof.
intros m m' Hval Hstep.
invertc Hval; [].
intros a t r Hcanon <-.
revert r Hstep.
cases Hcanon;
intros; invert Hstep; done.
Qed.


Lemma determinism_step :
  forall m1 m2 m2',
    step m1 m2
    -> step m1 m2'
    -> m2 = m2'.
Proof.
intros m1 m2 m2' Hstep Hstep'.
revert m2' Hstep'.
induct Hstep.

(* app1 *)
{
intros m1 m1' m2 Hstep1 IH n Hstep.
invert Hstep.
  {
  intros m1'' Hstep1' <-.
  f_equal; auto.
  }

  {
  intros m3 <-.
  invert Hstep1.
  }
}

(* app2 *)
{
intros m1 m2 m2' Hstep.
invert Hstep.
  {
  intros m3 Hstep' _.
  invert Hstep'.
  }

  {
  intros <-.
  reflexivity.
  }
}

(* prev1 *)
{
intros m1 m1' Hstep1 IH n Hstep.
invert Hstep.
  {
  intros m2 Hstep' <-.
  f_equal; auto.
  }

  {
  intros <-.
  invert Hstep1.
  }
}

(* prev2 *)
{
intros m1 n Hstep.
invert Hstep.
  {
  intros m2 Hstep' <-.
  invert Hstep'.
  }

  {
  intros <-.
  reflexivity.
  }
}

(* ite1 *)
{
intros m1 m1' m2 m3 Hstep1 IH n Hstep.
invertc Hstep.
  {
  intros m1'' Hstep <-.
  f_equal; auto.
  }

  {
  intros <- <-.
  invert Hstep1.
  }

  {
  intros <- <-.
  invert Hstep1.
  }
}

(* ite2 *)
{
intros m1 m2 n Hstep.
invertc Hstep; auto.
intros m1' Hstep <-.
invert Hstep.
}

(* ite3 *)
{
intros m1 m2 n Hstep.
invertc Hstep; auto.
intros m1' Hstep <-.
invert Hstep.
}

(* ppi11 *)
{
intros m m' Hstep1 IH n Hstep.
invertc Hstep.
  {
  intros m'' Hstep <-.
  f_equal; auto.
  }

  {
  intros n' <-.
  invert Hstep1.
  }
}

(* ppi12 *)
{
intros m1 m2 n Hstep.
invertc Hstep; auto.
intros m1' Hstep <-.
invert Hstep.
}

(* ppi21 *)
{
intros m m' Hstep1 IH n Hstep.
invertc Hstep.
  {
  intros m'' Hstep <-.
  f_equal; auto.
  }

  {
  intros n' <-.
  invert Hstep1.
  }
}

(* ppi22 *)
{
intros m1 m2 n Hstep.
invertc Hstep; auto.
intros m1' Hstep <-.
invert Hstep.
}
Qed.


Lemma eval_first_step :
  forall m m' v,
    step m m'
    -> eval m v
    -> eval m' v.
Proof.
intros m m' v Hstep Heval.
destruct Heval as (Hsteps & Hval).
invert Hsteps.
- intros <-.
  exfalso.
  eapply determinism_value; eauto.

- intros m'' Hstep' Hsteps'.
  so (determinism_step _#3 Hstep Hstep').
  subst m''.
  split; auto.
Qed.


Definition normal (m : term) : Prop :=
  forall n, step m n -> False.


Definition normalize m n :=
  star step m n
  /\ normal n.


Lemma var_normal :
  forall i, normal (var i).
Proof.
intros i.
intros m Hstep.
invert Hstep; done.
Qed.


Lemma value_normal :
  forall v, value v -> normal v.
Proof.
intros v Hval.
intros m Hstep.
eapply determinism_value; eauto.
Qed.


Lemma eval_normalize :
  forall m v, eval m v -> normalize m v.
Proof.
intros m v (Hsteps & Hval).
split; auto; [].
apply value_normal; auto.
Qed.


Lemma normalize_normal :
  forall n, normal n -> normalize n n.
Proof.
intros n H.
exact (conj (star_refl _) H).
Qed.


Lemma determinism :
  forall m n n',
    normalize m n
    -> normalize m n'
    -> n = n'.
Proof.
intros m n n' (Hsteps & Hnorm) (Hsteps' & Hnorm').
revert n' Hnorm Hnorm' Hsteps'.
induct Hsteps.

(* refl *)
{
intros m n Hnorm _ Hsteps.
invert Hsteps; auto; [].
intros m' Hstep _.
exfalso.
eapply Hnorm; eauto.
}

(* step *)
{
intros m1 m2 n Hm1m2 Hm2n IH n' Hnorm Hnorm' Hm1n'.
invert Hm1n'.
- intros <-.
  exfalso.
  eapply Hnorm'; eauto.

- intros m2' Hm1m2' Hm2'n'.
  so (determinism_step _#3 Hm1m2 Hm1m2'); subst m2'.
  apply IH; auto; done.
}
Qed.


Lemma determinism_eval :
  forall m v v',
    eval m v
    -> eval m v'
    -> v = v'.
Proof.
intros m v v' H H'.
eapply determinism; eauto using eval_normalize.
Qed.


Lemma determinism_normal :
  forall m n, normal m -> star step m n -> m = n.
Proof.
intros m n Hnorm Hsteps.
invert Hsteps; auto.
intros n' Hstep _.
exfalso.
eapply Hnorm; eauto.
Qed.


Lemma determinism_normal_value :
  forall m n, value m -> star step m n -> m = n.
Proof.
intros m n Hval Hsteps.
eapply determinism_normal; eauto.
apply value_normal; auto.
Qed.


Lemma subst_step :
  forall s m m',
    step m m'
    -> step (subst s m) (subst s m').
Proof.
intros s m m' H.
revert s.
induct H; intros; simpsub; eauto using step;
try (relquest; [eauto using step | simpsub; reflexivity]; done).
Qed.


Lemma subst_steps :
  forall s m m',
    star step m m'
    -> star step (subst s m) (subst s m').
Proof.
intros s m m' H.
induct H; eauto using star_refl, star_step, subst_step.
Qed.


Lemma subst_value :
  forall s v,
    value v
    -> value (subst s v).
Proof.
intros s v H.
invertc H; [].
intros a t r Hcanon <-.
simpsub.
apply value_i; auto.
Qed.


Lemma subst_eval :
  forall s m v,
    eval m v
    -> eval (subst s m) (subst s v).
Proof.
intros s m v (Hsteps & Hval).
split.
- apply subst_steps; auto.

- apply subst_value; auto.
Qed.


Hint Constructors canon : dynamic.


Lemma value_univ : forall {m1}, value (univ m1).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_cty : forall {m1}, value (cty m1).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_con : forall {m1 m2}, value (con m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_karrow : forall {m1 m2}, value (karrow m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_arrow : forall {m1 m2}, value (arrow m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_pi : forall {m1 m2}, value (pi m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_clam : forall {m1 m2}, value (clam m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_capp : forall {m1 m2}, value (capp m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_ctlam : forall {m1 m2 m3}, value (ctlam m1 m2 m3).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_ctapp : forall {m1 m2}, value (ctapp m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_lam : forall {m1}, value (lam m1).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_intersect : forall {m1 m2}, value (intersect m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_union : forall {m1 m2}, value (union m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_fut : forall {m1}, value (fut m1).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_cnext : forall {m1}, value (cnext m1).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_cprev : forall {m1}, value (cprev m1).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_next : forall {m1}, value (next m1).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_rec : forall {m1}, value (rec m1).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_equal : forall {m1 m2 m3}, value (equal m1 m2 m3).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_triv : value triv.
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_eqtype : forall {m1 m2}, value (eqtype m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_subtype : forall {m1 m2}, value (subtype m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_kuniv : forall {m1}, value (kuniv m1).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_all : forall {m1 m2 m3}, value (all m1 m2 m3).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_alltp : forall {m1}, value (alltp m1).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_exist : forall {m1 m2 m3}, value (exist m1 m2 m3).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_mu : forall {m1}, value (mu m1).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_ispositive : forall {m1}, value (ispositive m1).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_isnegative : forall {m1}, value (isnegative m1).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_voidtp : value voidtp.
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_unittp : value unittp.
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_cunit : value cunit.
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_booltp : value booltp.
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_btrue : value btrue.
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_bfalse : value bfalse.
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_prod : forall {m1 m2}, value (prod m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_sigma : forall {m1 m2}, value (sigma m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_cpair : forall {m1 m2}, value (cpair m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_cpi1 : forall {m1}, value (cpi1 m1).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_cpi2 : forall {m1}, value (cpi2 m1).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_ppair : forall {m1 m2}, value (ppair m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_set : forall {m1 m2}, value (set m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_iset : forall {m1 m2}, value (iset m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_quotient : forall {m1 m2}, value (quotient m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_guard : forall {m1 m2}, value (guard m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_wt : forall {m1 m2}, value (wt m1 m2).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_ext : forall {x}, value (ext x).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_extt : forall {x}, value (extt x).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


End object.


Arguments value {object}.
Arguments step {object}.
Arguments eval {object}.
Arguments normal {object}.
Arguments normalize {object}.

Arguments value_univ {object m1}.
Arguments value_cty {object m1}.
Arguments value_con {object m1 m2}.
Arguments value_karrow {object m1 m2}.
Arguments value_arrow {object m1 m2}.
Arguments value_pi {object m1 m2}.
Arguments value_clam {object m1 m2}.
Arguments value_capp {object m1 m2}.
Arguments value_ctlam {object m1 m2 m3}.
Arguments value_ctapp {object m1 m2}.
Arguments value_lam {object m1}.
Arguments value_intersect {object m1 m2}.
Arguments value_union {object m1 m2}.
Arguments value_fut {object m1}.
Arguments value_cnext {object m1}.
Arguments value_cprev {object m1}.
Arguments value_next {object m1}.
Arguments value_rec {object m1}.
Arguments value_equal {object m1 m2 m3}.
Arguments value_triv {object}.
Arguments value_eqtype {object m1 m2}.
Arguments value_subtype {object m1 m2}.
Arguments value_kuniv {object m1}.
Arguments value_all {object m1 m2 m3}.
Arguments value_alltp {object m1}.
Arguments value_exist {object m1 m2 m3}.
Arguments value_mu {object m1}.
Arguments value_ispositive {object m1}.
Arguments value_isnegative {object m1}.
Arguments value_voidtp {object}.
Arguments value_unittp {object}.
Arguments value_cunit {object}.
Arguments value_booltp {object}.
Arguments value_btrue {object}.
Arguments value_bfalse {object}.
Arguments value_prod {object m1 m2}.
Arguments value_sigma {object m1 m2}.
Arguments value_cpair {object m1 m2}.
Arguments value_cpi1 {object m1}.
Arguments value_cpi2 {object m1}.
Arguments value_ppair {object m1 m2}.
Arguments value_set {object m1 m2}.
Arguments value_iset {object m1 m2}.
Arguments value_quotient {object m1 m2}.
Arguments value_guard {object m1 m2}.
Arguments value_wt {object m1 m2}.
Arguments value_ext {object x}.
Arguments value_extt {object x}.


Hint Constructors canon : dynamic.


Hint Resolve value_univ value_cty value_con value_karrow value_arrow value_pi value_clam value_capp value_ctlam value_ctapp value_lam value_intersect value_union value_fut value_cnext value_cprev value_next value_rec value_equal value_triv value_eqtype value_subtype value_kuniv value_all value_alltp value_exist value_mu value_ispositive value_isnegative value_voidtp value_unittp value_cunit value_booltp value_btrue value_bfalse value_prod value_sigma value_cpair value_cpi1 value_cpi2 value_ppair value_set value_iset value_quotient value_guard value_wt value_ext value_extt : dynamic.


Hint Resolve var_normal value_normal : dynamic.
Hint Resolve eval_normalize eval_value : dynamic.
