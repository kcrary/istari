
(* This really should be called ChainCompletePoset, but that's a mouthful. *)

Require Import Tactics.
Require Import Axioms.
Require Import Relation.


Definition is_chain {T : Type} (R : relation T) (P : T -> Prop) : Prop
  :=
  forall x y,
    P x
    -> P y
    -> R x y \/ R y x.


(* chain-complete poset *)
Record ccp : Type :=
mk_lat
  { lat_car : Type;
    lat_le : lat_car -> lat_car -> Prop;
    lat_join : forall (P : lat_car -> Prop), is_chain lat_le P -> lat_car;

    lat_le_refl : forall x, lat_le x x;

    lat_le_trans :
      forall x y z,
        lat_le x y
        -> lat_le y z
        -> lat_le x z;

    lat_le_antisymm :
      forall x y,
        lat_le x y
        -> lat_le y x
        -> x = y;

    lat_join_ub :
      forall (P : lat_car -> Prop) h x,
        P x
        -> lat_le x (lat_join P h);

    lat_join_least :
      forall (P : lat_car -> Prop) h x,
        (forall y, P y -> lat_le y x)
        -> lat_le (lat_join P h) x
  }.


Lemma lat_le_refl' :
  forall L (x y : lat_car L),
    x = y
    -> lat_le L x y.
Proof.
intros L x y H.
subst y.
apply lat_le_refl.
Qed.


Lemma empty_chain :
  forall L, is_chain (lat_le L) (fun _ => False).
Proof.
intros L.
intros x y H.
destruct H.
Qed.


Definition lat_bot (L : ccp) : lat_car L
  :=
  lat_join L (fun _ => False) (empty_chain L).


Lemma lat_bot_least :
  forall L x,
    lat_le L (lat_bot L) x.
Proof.
intros L x.
apply lat_join_least.
intros y H.
destruct H.
Qed.


Definition impl {S T : Type} (Q : S -> S -> Prop) (R : T -> T -> Prop) (F : S -> T) 
  : Prop 
  :=
  forall A B, Q A B -> R (F A) (F B).


Lemma impl_compose :
  forall S T U (P : S -> S -> Prop) (Q : T -> T -> Prop) (R : U -> U -> Prop)
    (F : S -> T) (G : T -> U),
      impl P Q F
      -> impl Q R G
      -> impl P R (fun X => G (F X)).
Proof.
intros S T U P Q R F G HmonoF HmonoG.
intros x y Hxy.
auto.
Qed.


(* Proof technique borrowed from Proving Fixed Points, by Herve Grall. *)


Inductive iterand (L : ccp) (F : lat_car L -> lat_car L) : lat_car L -> Prop :=
| iterand_intro :
    forall C (h : is_chain (lat_le L) C),
      (forall x,
         C x
         -> iterand L F x)
      -> iterand L F (F (lat_join L C h)).


Lemma iterand_chain :
  forall L F,
    impl (lat_le L) (lat_le L) F
    -> is_chain (lat_le L) (iterand L F).
Proof.
intros L F Hmono.
intros x y Hx Hy.
revert y Hy.
induct Hx.
intros C1 Hchain1 _ IH y Hy.
invertc Hy.
intros C2 Hchain2 HC2 <-.
so (excluded_middle (exists x, C1 x /\ forall y, C2 y -> lat_le L y x)) as [Hyes | Hno].
  {
  destruct Hyes as (x & Hx & Hall).
  right.
  apply Hmono.
  apply lat_join_least.
  intros y Hy.
  apply (lat_le_trans _ _ x).
    {
    apply Hall; auto.
    }

    {
    apply lat_join_ub; auto.
    }
  }
assert (forall x, C1 x -> exists y, C2 y /\ ~ lat_le L y x) as Hyes.
  {
  intros x Hx.
  apply proof_by_contradiction.
  contradict Hno.
  exists x.
  split; auto.
  intros y Hy.
  so (excluded_middle (lat_le L y x)) as [Hyx | Hnyx]; auto.
  destruct Hno.
  exists y.
  auto.
  }
left.
apply Hmono.
apply lat_join_least.
intros x Hx.
so (Hyes x Hx) as (y & Hy & Hnyx).
so (IH x Hx y (HC2 y Hy)) as [Hxy | Hyx].
2:{
  contradiction.
  }
apply (lat_le_trans _ _ y); auto.
apply lat_join_ub; auto.
Qed.


Lemma iterand_least :
  forall L F x y,
    impl (lat_le L) (lat_le L) F
    -> lat_le L (F x) x
    -> iterand L F y
    -> lat_le L y x.
Proof.
intros L F x y Hmono Hprefix Hy.
induct Hy.
intros C Hchain _ IH.
apply (lat_le_trans _ _ (F x)); auto.
apply Hmono.
apply lat_join_least.
intros y Hy.
apply IH; auto.
Qed.


Definition lfp L F (h : impl (lat_le L) (lat_le L) F) : lat_car L
  :=
  lat_join L (iterand L F) (iterand_chain L F h).


Lemma lfp_least :
  forall L F x (h : impl (lat_le L) (lat_le L) F),
    lat_le L (F x) x
    -> lat_le L (lfp L F h) x.
Proof.
intros L F x Hmono Hprefix.
apply lat_join_least.
intros y Hy.
eapply iterand_least; eauto.
Qed.


Lemma lfp_prefix :
  forall L F (h : impl (lat_le L) (lat_le L) F),
    lat_le L (F (lfp L F h)) (lfp L F h).
Proof.
intros L F h.
apply lat_join_ub.
apply iterand_intro.
auto.
Qed.


Lemma lfp_postfix :
  forall L F (h : impl (lat_le L) (lat_le L) F),
    lat_le L (lfp L F h) (F (lfp L F h)).
Proof.
intros L F h.
apply lfp_least.
apply h.
apply lfp_prefix.
Qed.


Lemma lfp_fix :
  forall L F (h : impl (lat_le L) (lat_le L) F),
    lfp L F h = F (lfp L F h).
Proof.
intros L F h.
apply lat_le_antisymm; auto using lfp_prefix, lfp_postfix.
Qed.


Lemma fixpoint_iteration :
  forall L (F : lat_car L -> lat_car L) (P : lat_car L -> Prop)
    (h : impl (lat_le L) (lat_le L) F),
      (forall x, P x -> P (F x))
      -> (forall C (h : is_chain (lat_le L) C),
            (forall x, C x -> P x)
            -> P (lat_join L C h))
      -> P (lfp L F h).
Proof.
intros L F P Hmono Hinc Hjoin.
rewrite -> lfp_fix.
assert (iterand L F (F (lfp L F Hmono))) as H.
  {
  apply iterand_intro; auto.
  }
set (x := F (lfp L F Hmono)) in H |- *.
clearbody x.
induct H.
intros C Hchain _ IH.
apply Hinc.
apply Hjoin; auto.
Qed.
  

Definition map_set {T : Type} (f : T -> T) (P : T -> Prop) : T -> Prop
  :=
  fun x => exists y, x = f y /\ P y.


Lemma map_chain :
  forall T (R : relation T) (f : T -> T) (P : T -> Prop),
    impl R R f
    -> is_chain R P
    -> is_chain R (map_set f P).
Proof.
intros T R f P Hmono Hchain.
intros x y Hx Hy.
destruct Hx as (x' & -> & Hx).
destruct Hy as (y' & -> & Hy).
so (Hchain x' y' Hx Hy) as [Hxy | Hyx].
  {
  left.
  apply Hmono; auto.
  }

  {
  right.
  apply Hmono; auto.
  }
Qed.


Definition chain_continuous (L : ccp) (F : lat_car L -> lat_car L)
  : Prop
  :=
  exists (Hmono : impl (lat_le L) (lat_le L) F),
    forall C (h : is_chain (lat_le L) C),
      F (lat_join L C h) = lat_join L (map_set F C) (map_chain _#4 Hmono h).


Lemma chain_continuous_impl_monotone :
  forall L F,
    chain_continuous L F
    -> impl (lat_le L) (lat_le L) F.
Proof.
intros L F H.
destruct H; auto.
Qed.


Lemma vanish :
  forall L (F G : lat_car L -> lat_car L)
    (HF : chain_continuous L F)
    (HG : impl (lat_le L) (lat_le L) G),
      (forall x, F (G (F x)) = G (F x))
      -> lfp L (fun x => G (F x)) (impl_compose _#8 (chain_continuous_impl_monotone _ _ HF) HG)
         =
         lfp L G HG.
Proof.
intros L F G HcontF HmonoG Hequation.
destruct HcontF as (HmonoF & HcontF).
match goal with
| |- lfp _ _ ?X = _ => set (HmonoGF := X)
end.
clearbody HmonoGF.
apply (lat_le_antisymm L).
2:{
  apply lfp_least.
  rewrite -> lfp_fix at 1; auto.
  rewrite <- Hequation.
  rewrite <- (lfp_fix L (fun X => G (F X))).
  rewrite <- (lfp_fix L (fun X => G (F X))).
  apply lat_le_refl.
  }
apply lfp_least.
rewrite -> lfp_fix at 2; auto.
apply HmonoG.
exploit (fixpoint_iteration _ G (fun x => x = F x) HmonoG) as H; auto.
  {
  intros x Heq.
  rewrite -> Heq at 2.
  rewrite -> Hequation.
  rewrite <- Heq.
  reflexivity.
  }

  {
  intros C Hchain IH.
  rewrite -> HcontF.
  (* with the dependent types, it's easier to go with inequalities *)
  apply lat_le_antisymm.
    {
    apply lat_join_least.
    intros x Hx.
    apply lat_join_ub.
    exists x; auto.
    }

    {
    apply lat_join_least.
    intros x Hx.
    apply lat_join_ub.
    destruct Hx as (x' & -> & Hx).
    rewrite <- IH; auto.
    }
  }
cbn in H.
rewrite -> H at 2.
apply lat_le_refl.
Qed.


Lemma vanish' :
  forall L (F G : lat_car L -> lat_car L) gf g,
    chain_continuous L F
    -> impl (lat_le L) (lat_le L) G
    -> (forall x, F (G (F x)) = G (F x))
    -> lat_le L (G (F gf)) gf
    -> (forall x, lat_le L (G (F x)) x -> lat_le L gf x)
    -> lat_le L (G g) g
    -> (forall x, lat_le L (G x) x -> lat_le L g x)
    -> gf = g.
Proof.
intros L F G gf g HcontF HmonoG Hequation Hprefixgf Hleastgf Hprefixg Hleastg.
transitivity (lfp L (fun x => G (F x)) (impl_compose _#8 (chain_continuous_impl_monotone _ _ HcontF) HmonoG)).
  {
  apply lat_le_antisymm.
    {
    apply Hleastgf.
    apply (lfp_prefix L (fun x => G (F x))).
    }

    {
    apply lfp_least.
    auto.
    }
  }
transitivity (lfp L G HmonoG).
  {
  apply vanish; auto.
  }
apply lat_le_antisymm.
  {
  apply lfp_least; auto.
  }

  {
  apply Hleastg.
  apply lfp_prefix.
  }
Qed.
