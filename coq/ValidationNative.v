
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Tactics.
Require Import Sequence.
Require Import Relation.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.
Require Import Dynamic.
Require Import Promote.
Require Import Hygiene.
Require Import Rules.
Require Import DerivedRules.
Require Defs.
Require Import Obligations.
Require Import Morphism.
Require Import DefsEquiv.
Require Import Equivalence.
Require Import Equivalences.
Require Import Dots.

Require Import ValidationUtil.
Require Import Defined.
Require Import PageType.
Require Import Native.
Require Import NatLemmas.


Lemma subst_sum_case :
  forall s,
    subst s Defs.sum_case = Defs.sum_case.
Proof.
intro s.
unfold Defs.sum_case.
simpsub.
reflexivity.
Qed.
Hint Rewrite subst_sum_case : subst.


Lemma subst_nat_case :
  forall s,
    subst s Defs.nat_case = Defs.nat_case.
Proof.
intro s.
unfold Defs.nat_case.
simpsub.
reflexivity.
Qed.
Hint Rewrite subst_nat_case : subst.


Lemma subst_nat_to_integer :
  forall s,
    subst s Defs.nat_to_integer = Defs.nat_to_integer.
Proof.
intro s.
unfold Defs.nat_to_integer.
simpsub.
reflexivity.
Qed.
Hint Rewrite subst_nat_to_integer : subst.


Lemma subst_plusz :
  forall s,
    subst s Defs.plusz = Defs.plusz.
Proof.
intro s.
unfold Defs.plusz.
simpsub.
reflexivity.
Qed.
Hint Rewrite subst_plusz : subst.


Lemma nat_to_integer_equiv :
  forall n,
    equiv (app Defs.nat_to_integer (PageCode.natlit n)) (native_elem (native_integer (Native.nat_to_integer n))).
Proof.
intros n.
induct n.
 
(* 0 *)
{
unfold Defs.nat_to_integer.
eapply equiv_trans.
  {
  apply equiv_app.
    {
    apply theta_equiv.
    }

    {
    apply equiv_refl.
    }
  }
eapply equiv_trans.
  {
  apply equiv_app.
    {
    apply equiv_beta.
    }

    {
    apply equiv_refl.
    }
  }
simpsub.
eapply equiv_trans.
  {
  apply equiv_beta.
  }
simpsub.
cbn [PageCode.natlit].
eapply equiv_trans.
  {
  apply def_natcase.
  }
eapply equiv_trans.
  {
  apply natcase_zero.
  }
cbn.
apply equiv_refl.
}

(* S *)
{
intros n IH.
unfold Defs.nat_to_integer.
eapply equiv_trans.
  {
  apply equiv_app.
    {
    apply theta_equiv.
    }

    {
    apply equiv_refl.
    }
  }
fold Defs.nat_to_integer.
eapply equiv_trans.
  {
  apply equiv_app.
    {
    apply equiv_beta.
    }

    {
    apply equiv_refl.
    }
  }
simpsub.
eapply equiv_trans.
  {
  apply equiv_beta.
  }
simpsub.
cbn [PageCode.natlit].
eapply equiv_trans.
  {
  apply def_natcase.
  }
eapply equiv_trans.
  {
  apply natcase_succ.
  }
simpsub.
cbn.
eapply equiv_trans.
  {
  apply equiv_app; [apply equiv_refl |].
  exact IH.
  }
unfold Defs.plusz.
eapply equiv_trans.
  {
  apply equiv_app; [| apply equiv_refl].
  apply equiv_beta.
  }
simpsub.
eapply equiv_trans.
  {
  apply equiv_beta.
  }
simpsub.
apply steps_equiv.
eapply star_step.
  {
  apply step_native_binary2.
  }
eapply star_one.
apply step_native_unary2.
cbn.
reflexivity.
}
Qed.


Lemma equiv_native_unary_eval :
  forall f x y,
    f x = Some y
    -> equiv (@native_unary obj f (native_elem x)) (native_elem y).
Proof.
intros f x y Heq.
apply steps_equiv.
apply star_one.
apply step_native_unary2; auto.
Qed.


Lemma equiv_native_binary_eval :
  forall f x y z,
    f x y = Some z
    -> equiv (@native_binary obj f (native_elem x) (native_elem y)) (native_elem z).
Proof.
intros f x y z Heq.
apply steps_equiv.
eapply star_step.
  {
  apply step_native_binary2.
  }
apply star_one.
apply step_native_unary2; auto.
Qed.


Lemma tr_nativetp_istype :
  forall A f G,
    tr G (deqtype (nativetp A f) (nativetp A f)).
Proof.
intros A f G.
apply (tr_formation_weaken _ nzero).
apply tr_nativetp_formation.
Qed.


Lemma tr_booltp_intro_native :
  forall G b,
    tr G (deq (native_elem (native_bool b)) (native_elem (native_bool b)) booltp).
Proof.
intros G b.
destruct b; [fold (@btrue obj) | fold (@bfalse obj)]; [apply tr_booltp_intro_btrue | apply tr_booltp_intro_bfalse].
Qed.


Lemma tr_nativetp_total :
  forall A f G m,
    tr G (deq m m (nativetp A f))
    -> tr G (deq triv triv (halts m)).
Proof.
intros A f G m Hm.
assert (tr G (deq (lam triv) (lam triv) (pi (nativetp A f) (halts (var 0))))) as Hprop.
  {
  apply tr_pi_intro.
    {
    apply tr_nativetp_istype.
    }
  apply tr_native_left.
  intro x.
  simpsub.
  apply tr_halts_value.
  apply value_native_elem.
  }
apply (tr_halts_eta2 _ (app (lam triv) m) (app (lam triv) m)).
eapply tr_pi_elim'; eauto.
simpsub.
reflexivity.
Qed.


Lemma nat_to_integer_type :
  forall G,
    tr G (deq Defs.nat_to_integer Defs.nat_to_integer (pi nattp (nativetp integer native_integer))).
Proof.
intro G.
eapply tr_pi_of_ext.
  {
  apply tr_nattp_formation.
  }

2:{
  unfold Defs.nat_to_integer.
  eapply equiv_trans.
    {
    apply theta_equiv.
    }
  eapply equiv_trans.
    {
    apply equiv_beta.
    }
  simpsub.
  apply equiv_refl.
  }
apply tr_nattp_left.
intro x.
simpsub.
eapply (tr_compute _#4 (native_elem (native_integer (Native.nat_to_integer x))) _ (native_elem (native_integer (Native.nat_to_integer x)))); eauto using equiv_refl, nat_to_integer_equiv.
apply tr_nativetp_intro.
Qed.


Lemma def_integer : eq Defs.integer (nativetp integer native_integer).
Proof.
auto.
Qed.


Lemma def_integer_zero : eq Defs.integer_zero (native_elem (native_integer zeroz)).
Proof.
auto.
Qed.


Lemma def_integer_one : eq Defs.integer_one (native_elem (native_integer onez)).
Proof.
auto.
Qed.


Lemma def_plusz :
  forall a b,
    equiv (app (app Defs.plusz a) b) (native_binary plusz_native a b).
Proof.
intros a b.
unfold Defs.plusz.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_negz :
  forall a,
    equiv (app Defs.negz a) (native_unary negz_native a).
Proof.
intros a.
unfold Defs.negz.
apply steps_equiv.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_timesz :
  forall a b,
    equiv (app (app Defs.timesz a) b) (native_binary timesz_native a b).
Proof.
intros a b.
unfold Defs.timesz.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_eqzb :
  forall a b,
    equiv (app (app Defs.eqzb a) b) (native_binary eqzb_native a b).
Proof.
intros a b.
unfold Defs.eqzb.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_leqzb :
  forall a b,
    equiv (app (app Defs.leqzb a) b) (native_binary leqzb_native a b).
Proof.
intros a b.
unfold Defs.eqzb.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_symbol_eqb :
  forall a b,
    equiv (app (app Defs.symbol_eqb a) b) (native_binary symbol_eqb_native a b).
Proof.
intros a b.
unfold Defs.symbol_eqb.
apply steps_equiv.
eapply star_step.
  {
  apply step_app1.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma def_leqz :
  forall a b,
    equiv (app (app Defs.leqz a) b)
      (isquash
         (sigma nattp
            (equal 
               (nativetp integer native_integer)
               (native_binary plusz_native (subst sh1 a) (app Defs.nat_to_integer (var 0)))
               (subst sh1 b)))).
Proof.
intros a b.
unfold Defs.leqz.
eapply equiv_trans.
  {
  apply equiv_app; [| apply equiv_refl].
  apply equiv_app; [| apply equiv_refl].
  apply equiv_lam.
  apply equiv_lam.
  apply def_isquash.
  }
eapply equiv_trans.
  {
  apply equiv_app; [| apply equiv_refl].
  apply equiv_beta.
  }
simpsub.
cbn [Nat.add].
eapply equiv_trans.
  {
  apply equiv_beta.
  }
simpsub.
apply equiv_refl.
Qed.


Hint Rewrite def_integer def_integer_zero def_integer_one def_plusz def_negz def_timesz def_eqzb def_leqzb def_symbol_eqb def_leqz : prepare.
Hint Rewrite def_pi def_arrow def_nat def_zero def_succ : prepare.


Lemma integerForm_valid : integerForm_obligation.
Proof.
prepare.
intro G.
apply tr_nativetp_istype.
Qed.


Lemma integerEq_valid : integerEq_obligation.
Proof.
prepare.
intro G.
apply tr_nativetp_istype.
Qed.


Lemma integerFormUniv_valid : integerFormUniv_obligation.
Proof.
prepare.
intros G lv ext0 Htr.
apply (tr_univ_cumulative _ nzero); auto.
  {
  apply tr_nativetp_formation.
  }

  {
  unfold leqpagetp.
  rewrite -> unroll_leqtp.
  unfold nzero.
  rewrite -> sumcase_left.
  simpsub.
  apply tr_unittp_intro.
  }
Qed.


Lemma integerEqUniv_valid : integerEqUniv_obligation.
Proof.
prepare.
intros G lv ext0 Htr.
apply (tr_univ_cumulative _ nzero); auto.
  {
  apply tr_nativetp_formation.
  }

  {
  unfold leqpagetp.
  rewrite -> unroll_leqtp.
  unfold nzero.
  rewrite -> sumcase_left.
  simpsub.
  apply tr_unittp_intro.
  }
Qed.


Lemma pluszType_valid : pluszType_obligation.
Proof.
prepare.
intro G.
unfold Defs.plusz.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
simpsub.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_native_left.
intro y.
apply tr_native_left.
intro x.
simpsub.
eapply tr_native_binary; eauto using tr_nativetp_intro.
intros z z'.
cbn.
reflexivity.
Qed.


Lemma negzType_valid : negzType_obligation.
Proof.
prepare.
intro G.
unfold Defs.plusz.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_native_left.
intro x.
simpsub.
eapply tr_native_unary; eauto using tr_nativetp_intro.
intros z.
cbn.
reflexivity.
Qed.


Lemma timeszType_valid : timeszType_obligation.
Proof.
prepare.
intro G.
unfold Defs.timesz.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
simpsub.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_native_left.
intro y.
apply tr_native_left.
intro x.
simpsub.
eapply tr_native_binary; eauto using tr_nativetp_intro.
intros z z'.
cbn.
reflexivity.
Qed.


Lemma eqzbType_valid : eqzbType_obligation.
Proof.
prepare.
intro G.
unfold Defs.eqzb.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
simpsub.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_native_left.
intro y.
apply tr_native_left.
intro x.
simpsub.
rewrite -> (equiv_native_binary_eval _#3 (native_bool (eqzb x y))); auto.
apply tr_booltp_intro_native.
Qed.



Lemma leqzbType_valid : leqzbType_obligation.
Proof.
prepare.
intro G.
unfold Defs.leqzb.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
simpsub.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_native_left.
intro y.
apply tr_native_left.
intro x.
simpsub.
rewrite -> (equiv_native_binary_eval _#3 (native_bool (leqzb x y))); auto.
apply tr_booltp_intro_native.
Qed.


Lemma pluszCommute_valid : pluszCommute_obligation.
Proof.
prepare.
intro G.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_equal_intro.
apply tr_native_left.
intros y.
apply tr_native_left.
intro x.
simpsub.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (plusz x y))); auto.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (plusz y x))); auto.
rewrite -> plusz_commute.
apply tr_nativetp_intro.
Qed.


Lemma timeszCommute_valid : timeszCommute_obligation.
Proof.
prepare.
intro G.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_equal_intro.
apply tr_native_left.
intros y.
apply tr_native_left.
intro x.
simpsub.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (timesz x y))); auto.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (timesz y x))); auto.
rewrite -> timesz_commute.
apply tr_nativetp_intro.
Qed.


Lemma pluszAssoc_valid : pluszAssoc_obligation.
Proof.
prepare.
intro G.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_equal_intro.
cbn.
apply tr_native_left.
intros z.
apply tr_native_left.
intros y.
apply tr_native_left.
intro x.
simpsub.
cbn.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (plusz x y))); auto.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (plusz (plusz x y) z))); auto.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (plusz y z))); auto.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (plusz x (plusz y z)))); auto.
rewrite -> plusz_assoc.
apply tr_nativetp_intro.
Qed.


Lemma timeszAssoc_valid : timeszAssoc_obligation.
Proof.
prepare.
intro G.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_equal_intro.
cbn.
apply tr_native_left.
intros z.
apply tr_native_left.
intros y.
apply tr_native_left.
intro x.
simpsub.
cbn.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (timesz x y))); auto.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (timesz (timesz x y) z))); auto.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (timesz y z))); auto.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (timesz x (timesz y z)))); auto.
rewrite -> timesz_assoc.
apply tr_nativetp_intro.
Qed.


Lemma pluszIdentity_valid : pluszIdentity_obligation.
Proof.
prepare.
intro G.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_equal_intro.
cbn.
apply tr_native_left.
intros x.
simpsub.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (plusz zeroz x))); auto.
rewrite -> Native.plusz_identity.
apply tr_nativetp_intro.
Qed.


Lemma timeszIdentity_valid : timeszIdentity_obligation.
Proof.
prepare.
intro G.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_equal_intro.
cbn.
apply tr_native_left.
intros x.
simpsub.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (timesz onez x))); auto.
rewrite -> Native.timesz_identity.
apply tr_nativetp_intro.
Qed.


Lemma pluszInverse_valid : pluszInverse_obligation.
Proof.
prepare.
intro G.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_equal_intro.
cbn.
apply tr_native_left.
intros x.
simpsub.
rewrite -> (equiv_native_unary_eval _ _(native_integer (negz x))); auto.
rewrite -> (equiv_native_binary_eval _ _ _(native_integer (plusz x (negz x)))); auto.
rewrite -> Native.plusz_inverse.
apply tr_nativetp_intro.
Qed.


Lemma timeszDistPlusz_valid : timeszDistPlusz_obligation.
Proof.
prepare.
intro G.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_equal_intro.
cbn.
apply tr_native_left.
intros z.
apply tr_native_left.
intros y.
apply tr_native_left.
intro x.
simpsub.
cbn.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (plusz y z))); auto.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (timesz x (plusz y z)))); auto.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (timesz x y))); auto.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (timesz x z))); auto.
rewrite -> (equiv_native_binary_eval _#3 (native_integer (plusz (timesz x y) (timesz x z)))); auto.
rewrite -> timesz_dist_plusz.
apply tr_nativetp_intro.
Qed.


Lemma native_eq_spec1 :
  forall A f (eqb : A -> A -> bool) (eqb' : native -> native -> option native),
    (forall x y, eqb x y = true <-> x = y)
    -> (forall x y, eqb' (f x) (f y) = Some (native_bool (eqb x y)))
    -> (forall x y, f x = f y -> x = y)
    -> forall G m n,
         tr G (deq m n (nativetp A f))
         -> tr G (deq (native_binary eqb' m n) btrue booltp).
Proof.
intros A f eqb eqb' Heqb Heqb' Hinj G m n Hmn.
assert (tr G (deq 
                (lam (lam (lam triv)))
                (lam (lam (lam triv)))
                (pi (nativetp A f)
                   (pi (nativetp A f)
                      (pi (equal (nativetp A f) (var 1) (var 0))
                         (equal booltp (native_binary eqb' (var 2) (var 1)) btrue))))))
  as Hprop.
  {
  apply tr_pi_intro.
    {
    apply tr_nativetp_istype.
    }
  apply tr_pi_intro.
    {
    apply tr_nativetp_istype.
    }
  apply tr_native_left.
  intro y.
  apply tr_native_left.
  intro x.
  simpsub.
  apply tr_pi_intro.
    {
    apply tr_equal_formation.
      {
      simpsub.
      apply tr_nativetp_istype.
      }

      {
      apply tr_nativetp_intro.
      }

      {
      apply tr_nativetp_intro.
      }
    }
  apply tr_equal_intro.
  rewrite -> (equiv_native_binary_eval _#3 (native_bool (eqb x y))); auto.
  remember (eqb x y) as b eqn:Hb.
  destruct b.
    {
    unfold btrue.
    apply tr_booltp_intro_native.
    }

    {
    apply (tr_native_contradiction A f x y).
      {
      intro H.
      so (Hinj _ _ H) as H'.
      subst y.
      symmetry in Hb.
      rewrite -> (Heqb x x ander (eq_refl _)) in Hb.
      discriminate Hb.
      }
    
      {
      apply tr_equal_elim.
      apply (tr_equal_eta2 _#4 (var 0) (var 0)).
      eapply hypothesis; eauto using index_0.
      }
    }
  }
apply tr_equal_elim.
apply (tr_equal_eta2 _#4 (app (app (app (lam (lam (lam triv))) m) n) triv) (app (app (app (lam (lam (lam triv))) m) n) triv)).
eapply tr_pi_elim3'; eauto.
  {
  eapply tr_eq_reflexivity; eauto.
  }

  {
  simpsub.
  apply (tr_eq_reflexivity _ _ m).
  apply tr_symmetry; auto.
  }

  {
  simpsub.
  apply tr_equal_intro; auto.
  }

  {
  simpsub.
  reflexivity.
  }
Qed.


Lemma native_eq_spec2 :
  forall A f (eqb : A -> A -> bool) (eqb' : native -> native -> option native),
    (forall x y, eqb x y = true <-> x = y)
    -> (forall x y, eqb' (f x) (f y) = Some (native_bool (eqb x y)))
    -> (forall x y, f x = f y -> x = y)
    -> forall G m n,
         tr G (deq m m (nativetp A f))
         -> tr G (deq n n (nativetp A f))
         -> tr G (deq (native_binary eqb' m n) btrue booltp)
         -> tr G (deq m n (nativetp A f)).
Proof.
intros A f eqb eqb' Heqb Heqb' Hinj G m n Hm Hn Hmn.
assert (tr G (deq 
                (lam (lam (lam triv)))
                (lam (lam (lam triv)))
                (pi (nativetp A f)
                   (pi (nativetp A f)
                      (pi (equal booltp (native_binary eqb' (var 1) (var 0)) btrue)
                         (equal (nativetp A f) (var 2) (var 1)))))))
  as Hprop.
  {
  apply tr_pi_intro.
    {
    apply tr_nativetp_istype.
    }
  apply tr_pi_intro.
    {
    apply tr_nativetp_istype.
    }
  apply tr_native_left.
  intro y.
  apply tr_native_left.
  intro x.
  simpsub.
  apply tr_pi_intro.
    {
    apply tr_equal_formation.
      {
      simpsub.
      apply tr_booltp_istype.
      }

      {
      rewrite -> (equiv_native_binary_eval _#3 (native_bool (eqb x y))); auto.
      apply tr_booltp_intro_native.
      }

      {
      apply tr_booltp_intro_btrue.
      }
    }
  apply tr_equal_intro.
  rewrite -> (equiv_native_binary_eval _#3 (native_bool (eqb x y))); auto.
  remember (eqb x y) as b eqn:Hb.
  destruct b.
    {
    symmetry in Hb.
    rewrite -> Heqb in Hb.
    subst y.
    apply tr_nativetp_intro.
    }

    {
    fold (@bfalse obj).
    apply tr_booltp_contradiction.
    apply tr_symmetry.
    apply tr_equal_elim.
    apply (tr_equal_eta2 _#4 (var 0) (var 0)).
    eapply hypothesis; eauto using index_0.
    }
  }
apply tr_equal_elim.
apply (tr_equal_eta2 _#4 (app (app (app (lam (lam (lam triv))) m) n) triv) (app (app (app (lam (lam (lam triv))) m) n) triv)).
eapply tr_pi_elim3'; eauto.
  {
  simpsub.
  apply tr_equal_intro; auto.
  }

  {
  simpsub.
  reflexivity.
  }
Qed.


Lemma eqzbSpec1_valid : eqzbSpec1_obligation.
Proof.
prepare.
intros G m n ext0 Hmn.
unfold Defs.true, Defs.bool.
apply (native_eq_spec1 integer native_integer eqzb eqzb_native); auto.
  {
  apply eqzb_spec.
  }

  {
  intros x y H.
  injection H; auto.
  }
Qed.


Lemma eqzbSpec2_valid : eqzbSpec2_obligation.
Proof.
prepare.
intros G m n ext0 ext1 ext2 Hm Hn Htest.
unfold Defs.true, Defs.bool.
apply (native_eq_spec2 integer native_integer eqzb eqzb_native); auto.
  {
  apply eqzb_spec.
  }

  {
  intros x y H.
  injection H; auto.
  }
Qed.


Lemma leqzbSpec1_valid : leqzbSpec1_obligation.
Proof.
prepare.
intros G m n ext0 ext1 p Hm Hn Hmn.
assert (tr G (deq 
                (lam (lam (lam triv)))
                (lam (lam (lam triv)))
                (pi (nativetp integer native_integer)
                   (pi (nativetp integer native_integer)
                      (pi (isquash (sigma nattp
                                      (equal
                                         (nativetp integer native_integer)
                                         (native_binary plusz_native (var 2) (app Defs.nat_to_integer (var 0)))
                                         (var 1))))
                         (equal booltp (native_binary leqzb_native (var 2) (var 1)) btrue))))))
  as Hprop.
  {
  apply tr_pi_intro.
    {
    apply tr_nativetp_istype.
    }
  apply tr_pi_intro.
    {
    apply tr_nativetp_istype.
    }
  apply tr_native_left.
  intro y.
  apply tr_native_left.
  intro x.
  simpsub.
  apply tr_pi_intro.
    {
    apply tr_isquash_formation.
    apply tr_sigma_formation.
      {
      apply tr_nattp_formation.
      }
    apply tr_nattp_left.
    intro z.
    simpsub.
    apply tr_equal_formation.
      {
      apply tr_nativetp_istype.
      }

      {
      eapply (tr_native_binary integer integer integer native_integer native_integer native_integer plusz plusz_native); auto.
        {
        apply tr_nativetp_intro.
        }

        {
        rewrite -> nat_to_integer_equiv.
        apply tr_nativetp_intro.
        }
      }

      {
      apply tr_nativetp_intro.
      }
    }
  apply tr_equal_intro.
  rewrite -> (equiv_native_binary_eval _#3 (native_bool (leqzb x y))); auto.
  remember (leqzb x y) as b eqn:Heqb.
  destruct b.
    {
    unfold btrue.
    apply tr_booltp_intro_native.
    }

    {
    apply (tr_voidtp_elim _ triv triv).
    replace (deq triv triv voidtp) with (@substj obj sh1 (deq triv triv voidtp)) by (simpsub; reflexivity).
    apply tr_isquash_left.
    simpsub.
    replace (deq triv triv voidtp) with (@deq obj (subst (under 0 (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) sh1))) triv) (subst (under 0 (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) sh1))) triv) voidtp) by (simpsub; auto).
    apply (tr_sigma_eta_hyp _ []).
    cbn [length].
    simpsub.
    cbn [List.app].
    apply revert.
    apply tr_nattp_left.
    intros z.
    simpsub.
    apply tr_pi_intro.
      {
      apply tr_equal_formation.
        {
        apply tr_nativetp_istype.
        }

        {
        rewrite -> nat_to_integer_equiv.
        eapply (tr_native_binary integer integer integer native_integer native_integer native_integer plusz plusz_native); auto using tr_nativetp_intro.
        }

        {
        apply tr_nativetp_intro.
        }
      }
    rewrite -> nat_to_integer_equiv.
    rewrite -> (equiv_native_binary_eval _#3 (native_integer (plusz x (nat_to_integer z)))); auto.
    apply (tr_native_contradiction _ native_integer (plusz x (nat_to_integer z)) y).
      {
      intro H.
      injectionc H.
      intro H.
      assert (leqz x y) as Hxy.
        {
        unfold leqz.
        exists z.
        rewrite -> plusz_commute.
        exact H.
        }
      rewrite <- leqzb_spec in Hxy.
      rewrite <- Heqb in Hxy.
      discriminate Hxy.
      }
    
      {
      apply tr_equal_elim.
      apply (tr_equal_eta2 _#4 (var 0) (var 0)).
      eapply hypothesis; eauto using index_0.
      }
    }
  }
unfold Defs.bool, Defs.true.
apply tr_equal_elim.
apply (tr_equal_eta2 _#4 (app (app (app (lam (lam (lam triv))) m) n) triv) (app (app (app (lam (lam (lam triv))) m) n) triv)).
eapply tr_pi_elim3'; eauto.
  {
  simpsub.
  eapply tr_isquash_eta2; eauto.
  }

  {
  simpsub.
  reflexivity.
  }
Qed.


Lemma leqzbSpec2_valid : leqzbSpec2_obligation.
Proof.
prepare.
intros G m n ext0 ext1 ext2 Hm Hn Htest.
assert (tr G (deq 
                (lam (lam (lam triv)))
                (lam (lam (lam triv)))
                (pi (nativetp integer native_integer)
                   (pi (nativetp integer native_integer)
                      (pi (equal booltp (native_binary leqzb_native (var 1) (var 0)) btrue)
                         (isquash (sigma nattp
                                     (equal
                                        (nativetp integer native_integer)
                                        (native_binary plusz_native (var 3) (app Defs.nat_to_integer (var 0)))
                                        (var 2)))))))))
  as Hprop.
  {
  apply tr_pi_intro.
    {
    apply tr_nativetp_istype.
    }
  apply tr_pi_intro.
    {
    apply tr_nativetp_istype.
    }
  apply tr_native_left.
  intro y.
  apply tr_native_left.
  intro x.
  simpsub.
  apply tr_pi_intro.
    {
    apply tr_equal_formation.
      {
      simpsub.
      apply tr_booltp_istype.
      }

      {
      rewrite -> (equiv_native_binary_eval _#3 (native_bool (leqzb x y))); auto.
      apply tr_booltp_intro_native.
      }

      {
      apply tr_booltp_intro_btrue.
      }
    }
  rewrite -> (equiv_native_binary_eval _#3 (native_bool (leqzb x y))); auto.
  remember (leqzb x y) as b eqn:Heqb.
  symmetry in Heqb.
  destruct b.
    {
    rewrite -> leqzb_spec in Heqb.
    destruct Heqb as (z & <-).
    apply (tr_isquash_intro _ _ (ppair (PageCode.natlit z) triv)).
    apply tr_sigma_intro.
      {
      apply tr_natlit_nattp.
      }

      {
      simpsub.
      rewrite -> nat_to_integer_equiv.
      rewrite -> (equiv_native_binary_eval _#3 (native_integer (plusz x (nat_to_integer z)))); auto.
      rewrite -> plusz_commute.
      apply tr_equal_intro.
      apply tr_nativetp_intro.
      }

      {
      apply tr_equal_formation.
        {
        apply tr_nativetp_istype.
        }

        {
        apply (tr_native_binary _ _ _ native_integer native_integer native_integer plusz plusz_native); auto.
          {
          apply tr_nativetp_intro.
          }

          {
          eapply tr_pi_elim'.
            {
            apply nat_to_integer_type.
            }

            {
            eapply hypothesis; eauto using index_0.
            }

            {
            simpsub.
            auto.
            }
          }
        }

        {
        apply tr_nativetp_intro.
        }
      }
    }

    {
    fold (@bfalse obj).
    apply tr_booltp_contradiction.
    apply tr_symmetry.
    apply tr_equal_elim.
    apply (tr_equal_eta2 _#4 (var 0) (var 0)).
    eapply hypothesis; eauto using index_0.
    }
  }
unfold Defs.bool, Defs.true in Htest.
apply (tr_isquash_eta2 _#2 (app (app (app (lam (lam (lam triv))) m) n) triv) (app (app (app (lam (lam (lam triv))) m) n) triv)).
eapply tr_pi_elim3'; eauto.
  {
  simpsub.
  apply tr_equal_intro; auto.
  }

  {
  simpsub.
  reflexivity.
  }
Qed.


Lemma integerCharacteristic_valid : integerCharacteristic_obligation.
Proof.
prepare.
intro G.
unfold Defs.integer, Defs.integer_zero.
simpsub.
apply tr_pi_intro.
  {
  apply tr_nattp_formation.
  }
apply tr_nattp_left.
intro x.
simpsub.
apply tr_pi_intro.
  {
  apply tr_equal_formation.
    {
    apply tr_nativetp_istype.
    }

    {
    eapply tr_pi_elim'; eauto using nat_to_integer_type.
    apply tr_nsucc_nattp.
    apply tr_natlit_nattp.
    }

    {
    apply tr_nativetp_intro.
    }
  }
apply (tr_native_contradiction integer native_integer (nat_to_integer (S x)) zeroz).
  {
  intro H.
  injectionc H.
  intro H.
  exact (integer_characteristic x H).
  }
eapply (tr_compute _ _ _ _ (app Defs.nat_to_integer (PageCode.natlit (S x)))); eauto using equiv_refl.
  {
  apply equiv_symm.
  apply nat_to_integer_equiv.
  }
apply tr_equal_elim.
apply (tr_equal_eta2 _#4 (var 0) (var 0)).
eapply hypothesis; eauto using index_0.
simpsub; auto.
Qed.


Lemma integerElements_valid : integerElements_obligation.
Proof.
prepare.
intro G.
rewrite -> def_sum.
rewrite -> def_sigma.
rewrite -> def_isquash.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_native_left.
intro x.
simpsub.
assert 
  (tr (hyp_tm nattp :: G)
     (deqtype
        (sumtype
           (equal (nativetp integer native_integer) (native_elem (native_integer x))
              (native_unary negz_native (app Defs.nat_to_integer (nsucc (var 0)))))
           (equal (nativetp integer native_integer) (native_elem (native_integer x))
              (app Defs.nat_to_integer (var 0))))
        (sumtype
           (equal (nativetp integer native_integer) (native_elem (native_integer x))
              (native_unary negz_native (app Defs.nat_to_integer (nsucc (var 0)))))
           (equal (nativetp integer native_integer) (native_elem (native_integer x))
              (app Defs.nat_to_integer (var 0)))))) as Htype.
  {
  apply SumLemmas.tr_sumtype_formation.
    {
    apply tr_equal_formation.
      {
      apply tr_nativetp_istype.
      }

      {
      apply tr_nativetp_intro.
      }

      {
      eapply (tr_native_unary Native.integer Native.integer native_integer native_integer negz); auto.
      apply tr_nattp_left.
      intro y.
      simpsub.
      replace (nsucc (PageCode.natlit y)) with (@PageCode.natlit obj (S y)) by auto.
      rewrite -> nat_to_integer_equiv.
      apply tr_nativetp_intro.
      }
    }

    {
    apply tr_equal_formation.
      {
      apply tr_nativetp_istype.
      }

      {
      apply tr_nativetp_intro.
      }

      {
      apply tr_nattp_left.
      intro y.
      simpsub.
      rewrite -> nat_to_integer_equiv.
      apply tr_nativetp_intro.
      }
    }
  }
so (Native.integer_elements x) as (n & [Hneg | Hpos]).
  {
  apply (tr_isquash_intro _ _ (ppair (PageCode.natlit n) (sumleft triv))).
  apply tr_sigma_intro; auto.
    {
    apply tr_natlit_nattp.
    }

    {
    simpsub.
    apply SumLemmas.tr_sumtype_intro1.
      {
      apply tr_equal_intro.
      replace (nsucc (PageCode.natlit n)) with (@PageCode.natlit obj (S n)) by auto.
      rewrite -> (nat_to_integer_equiv (S n)).
      subst x.
      rewrite -> (equiv_native_unary_eval _ _ (native_integer (negz (nat_to_integer (S n))))); auto.
      apply tr_nativetp_intro.
      }

      {
      apply tr_equal_formation; auto using tr_nativetp_istype.
        {
        apply tr_nativetp_intro.
        }

        {
        rewrite -> nat_to_integer_equiv.
        apply tr_nativetp_intro.
        }
      }
    }
  }

  {
  apply (tr_isquash_intro _ _ (ppair (PageCode.natlit n) (sumright triv))).
  apply tr_sigma_intro; auto.
    {
    apply tr_natlit_nattp.
    }

    {
    simpsub.
    apply SumLemmas.tr_sumtype_intro2.
      {
      apply tr_equal_intro.
      rewrite -> (nat_to_integer_equiv n).
      subst x.
      apply tr_nativetp_intro.
      }

      {
      apply tr_equal_formation; auto using tr_nativetp_istype.
        {
        apply tr_nativetp_intro.
        }

        {
        replace (nsucc (PageCode.natlit n)) with (@PageCode.natlit obj (S n)) by auto.
        rewrite -> (nat_to_integer_equiv (S n)).
        subst x.
        rewrite -> (equiv_native_unary_eval _ _ (native_integer (negz (nat_to_integer (S n))))); auto.
        apply tr_nativetp_intro.
        }
      }
    }
  }
Qed.


Lemma integerHalts_valid : integerHalts_obligation.
Proof.
prepare.
intros G m ext0 Htr.
rewrite -> def_halts.
eapply tr_nativetp_total; eauto.
Qed.


Lemma integerStrict_valid : integerStrict_obligation.
Proof.
prepare.
intro G.
rewrite -> def_strict.
apply tr_total_strict.
  {
  apply tr_nativetp_istype.
  }

  {
  eapply tr_nativetp_total.
  eapply hypothesis; eauto using index_0.
  simpsub.
  auto.
  }
Qed.


Lemma integerUptype_valid : integerUptype_obligation.
Proof.
prepare.
intro G.
rewrite -> def_uptype.
apply tr_nativetp_uptype.
Qed.


Lemma integerAdmiss_valid : integerAdmiss_obligation.
Proof.
prepare.
intro G.
rewrite -> def_admiss.
apply tr_uptype_admiss.
apply tr_nativetp_uptype.
Qed.


Lemma tr_native_sequal :
  forall A f,
    (forall (x y : A), x = y \/ x <> y)
    -> (forall x y, f x = f y -> x = y)
    -> forall G m n,
         tr G (deq m n (nativetp A f))
         -> tr G (deq triv triv (sequal m n)).
Proof.
intros A f Hdec Hinj G m n Hmn.
assert (tr G (deq (lam (lam (lam triv))) (lam (lam (lam triv))) (pi (nativetp A f) (pi (nativetp A f) (pi (equal (nativetp A f) (var 1) (var 0)) (sequal (var 2) (var 1))))))) as Hprop.
  {
  apply tr_pi_intro.
    {
    apply tr_nativetp_istype.
    }
  apply tr_pi_intro.
    {
    apply tr_nativetp_istype.
    }
  apply tr_native_left.
  intro y.
  apply tr_native_left.
  intro x.
  simpsub.
  apply tr_pi_intro.
    {
    apply tr_equal_formation.
      {
      apply tr_nativetp_istype.
      }

      {
      apply tr_nativetp_intro.
      }
  
      {
      apply tr_nativetp_intro.
      }
    }
  so (Hdec x y) as [Heq | Hneq].
    {
    subst y.
    apply tr_sequal_intro.
    }

    {
    apply (tr_native_contradiction _ f x y).
      {
      contradict Hneq.
      apply Hinj; auto.
      }

      {
      apply tr_equal_elim.
      apply (tr_equal_eta2 _#4 (var 0) (var 0)).
      eapply hypothesis; eauto using index_0.
      }
    }
  }
apply (tr_sequal_eta2 _ (app (app (app (lam (lam (lam triv))) m) n) triv) (app (app (app (lam (lam (lam triv))) m) n) triv)).
eapply tr_pi_elim3'; eauto.
  {
  simpsub.
  eapply tr_eq_reflexivity; eauto.
  }

  {
  simpsub.
  eapply tr_eq_reflexivity; eauto.
  apply tr_symmetry; eauto.
  }

  {
  simpsub.
  apply tr_equal_intro; auto.
  }

  {
  simpsub.
  auto.
  }
Qed.


Lemma integerSequal_valid : integerSequal_obligation.
Proof.
prepare.
intros G m n ext0 Hsequal.
rewrite -> def_sequal.
eapply (tr_native_sequal integer native_integer); auto.
  {
  intros x y.
  remember (eqzb x y) as b eqn:Heqb.
  symmetry in Heqb.
  destruct b.
    {
    rewrite -> eqzb_spec in Heqb.
    subst y.
    left; auto.
    }

    {
    right.
    intro H.
    subst y.
    rewrite -> (eqzb_spec x x ander (eq_refl _)) in Heqb.
    discriminate Heqb.
    }
  }

  {
  intros x y Heq.
  injection Heq; auto.
  }
Qed.


Lemma symbolForm_valid : symbolForm_obligation.
Proof.
prepare.
intro G.
apply tr_nativetp_istype.
Qed.


Lemma symbolEq_valid : symbolEq_obligation.
Proof.
prepare.
intro G.
apply tr_nativetp_istype.
Qed.


Lemma symbolFormUniv_valid : symbolFormUniv_obligation.
Proof.
prepare.
intros G lv ext0 Htr.
apply (tr_univ_cumulative _ nzero); auto.
  {
  apply tr_nativetp_formation.
  }

  {
  unfold leqpagetp.
  rewrite -> unroll_leqtp.
  unfold nzero.
  rewrite -> sumcase_left.
  simpsub.
  apply tr_unittp_intro.
  }
Qed.


Lemma symbolEqUniv_valid : symbolEqUniv_obligation.
Proof.
prepare.
intros G lv ext0 Htr.
apply (tr_univ_cumulative _ nzero); auto.
  {
  apply tr_nativetp_formation.
  }

  {
  unfold leqpagetp.
  rewrite -> unroll_leqtp.
  unfold nzero.
  rewrite -> sumcase_left.
  simpsub.
  apply tr_unittp_intro.
  }
Qed.


Lemma symbol_eqbType_valid : symbol_eqbType_obligation.
Proof.
prepare.
intro G.
unfold Defs.symbol_eqb.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
simpsub.
apply tr_pi_intro.
  {
  apply tr_nativetp_istype.
  }
apply tr_native_left.
intro y.
apply tr_native_left.
intro x.
simpsub.
rewrite -> (equiv_native_binary_eval _#3 (native_bool (symbol_eqb x y))); auto.
apply tr_booltp_intro_native.
Qed.


Lemma symbol_eqbSpec1_valid : symbol_eqbSpec1_obligation.
Proof.
prepare.
intros G m n ext0 Hmn.
unfold Defs.true, Defs.bool.
apply (native_eq_spec1 symbol native_symbol symbol_eqb symbol_eqb_native); auto.
  {
  apply symbol_eqb_spec.
  }

  {
  intros x y H.
  injection H; auto.
  }
Qed.


Lemma symbol_eqbSpec2_valid : symbol_eqbSpec2_obligation.
Proof.
prepare.
intros G m n ext0 ext1 ext2 Hm Hn Htest.
unfold Defs.true, Defs.bool.
apply (native_eq_spec2 symbol native_symbol symbol_eqb symbol_eqb_native); auto.
  {
  apply symbol_eqb_spec.
  }

  {
  intros x y H.
  injection H; auto.
  }
Qed.


Lemma symbolHalts_valid : symbolHalts_obligation.
Proof.
prepare.
intros G m ext0 Htr.
rewrite -> def_halts.
eapply tr_nativetp_total; eauto.
Qed.


Lemma symbolStrict_valid : symbolStrict_obligation.
Proof.
prepare.
intro G.
unfold Defs.symbol.
rewrite -> def_strict.
apply tr_total_strict.
  {
  apply tr_nativetp_istype.
  }

  {
  eapply tr_nativetp_total.
  eapply hypothesis; eauto using index_0.
  simpsub.
  reflexivity.
  }
Qed.


Lemma symbolUptype_valid : symbolUptype_obligation.
Proof.
prepare.
intro G.
rewrite -> def_uptype.
apply tr_nativetp_uptype.
Qed.


Lemma symbolAdmiss_valid : symbolAdmiss_obligation.
Proof.
prepare.
intro G.
rewrite -> def_admiss.
apply tr_uptype_admiss.
apply tr_nativetp_uptype.
Qed.


Lemma symbolSequal_valid : symbolSequal_obligation.
Proof.
prepare.
intros G m n ext0 Hsequal.
rewrite -> def_sequal.
eapply (tr_native_sequal symbol native_symbol); auto.
  {
  intros x y.
  remember (symbol_eqb x y) as b eqn:Heqb.
  symmetry in Heqb.
  destruct b.
    {
    rewrite -> symbol_eqb_spec in Heqb.
    subst y.
    left; auto.
    }

    {
    right.
    intro H.
    subst y.
    rewrite -> (symbol_eqb_spec x x ander (eq_refl _)) in Heqb.
    discriminate Heqb.
    }
  }

  {
  intros x y Heq.
  injection Heq; auto.
  }
Qed.
