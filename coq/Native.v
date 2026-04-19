
Require Import Tactics.

Parameter integer : Type.

Parameter zeroz : integer.
Parameter onez : integer.
Parameter plusz : integer -> integer -> integer.
Parameter negz : integer -> integer.
Parameter timesz : integer -> integer -> integer.
Parameter divz : integer -> integer -> option integer.
Parameter modz : integer -> integer -> option integer.
Parameter eqzb : integer -> integer -> bool.
Parameter leqzb : integer -> integer -> bool.

Fixpoint nat_to_integer (n : nat) : integer :=
  match n with
  | 0 => zeroz
  | S n' => plusz onez (nat_to_integer n')
  end.

Definition leqz (x y : integer) : Prop :=
  exists n, plusz (nat_to_integer n) x = y.

Axiom plusz_commute : forall x y, plusz x y = plusz y x.
Axiom plusz_assoc : forall x y z, plusz (plusz x y) z = plusz x (plusz y z).
Axiom plusz_identity : forall x, plusz zeroz x = x.
Axiom plusz_inverse : forall x, plusz x (negz x) = zeroz.
Axiom timesz_commute : forall x y, timesz x y = timesz y x.
Axiom timesz_assoc : forall x y z, timesz (timesz x y) z = timesz x (timesz y z).
Axiom timesz_identity : forall x, timesz onez x = x.
Axiom timesz_dist_plusz : forall x y z, timesz x (plusz y z) = plusz (timesz x y) (timesz x z).
Axiom divz_nonzero : forall x y, y <> zeroz -> exists z, divz x y = Some z.
Axiom modz_nonzero : forall x y, y <> zeroz -> exists z, modz x y = Some z.
Axiom modz_spec : forall x y r, y <> zeroz -> modz x y = Some r -> leqz zeroz r /\ leqz (plusz onez r) (if leqzb zeroz y then y else negz y).
Axiom divz_spec : forall x y q r, y <> zeroz -> divz x y = Some q -> modz x y = Some r -> plusz (timesz q y) r = x.
Axiom eqzb_spec : forall x y, eqzb x y = true <-> x = y.
Axiom leqzb_spec : forall x y, leqzb x y = true <-> leqz x y.
Axiom integer_characteristic : forall n, ~ (nat_to_integer (S n) = zeroz).
Axiom integer_elements : forall x, (exists n, x = negz (nat_to_integer (S n)) \/ x = nat_to_integer n).

Parameter symbol : Type.

Parameter symbol_eqb : symbol -> symbol -> bool.

Axiom symbol_eqb_spec : forall x y, symbol_eqb x y = true <-> x = y.



Inductive native : Type :=
| native_bool : bool -> native
| native_integer : integer -> native
| native_symbol : symbol -> native.


Definition unary_integer (f : integer -> integer) (x : native) : option native :=
  (match x with
   | (native_integer x') => Some (native_integer (f x'))
   | _ => None
   end).

Definition binary_integer (f : integer -> integer -> integer) (x y : native) : option native :=
  (match (x, y) with
   | (native_integer x', native_integer y') => Some (native_integer (f x' y'))
   | _ => None
   end).

Definition binary_integer_test (f : integer -> integer -> bool) (x y : native) : option native :=
  (match (x, y) with
   | (native_integer x', native_integer y') => Some (native_bool (f x' y'))
   | _ => None
   end).

Definition zeroz_native := native_integer zeroz.
Definition onez_native := native_integer onez.
Definition plusz_native := binary_integer plusz.
Definition negz_native := unary_integer negz.
Definition timesz_native := binary_integer timesz.
Definition eqzb_native := binary_integer_test eqzb.
Definition leqzb_native := binary_integer_test leqzb.


Definition divz_native (x y : native) : option native :=
  (match (x, y) with
   | (native_integer x', native_integer y') => 
       match divz x' y' with
       | Some z => Some (native_integer z)
       | None => None
       end

   | _ => None
   end).

Definition modz_native (x y : native) : option native :=
  (match (x, y) with
   | (native_integer x', native_integer y') => 
       match modz x' y' with
       | Some z => Some (native_integer z)
       | None => None
       end

   | _ => None
   end).

Definition symbol_eqb_native (x y : native) : option native :=
  (match (x, y) with
   | (native_symbol x', native_symbol y') => Some (native_bool (symbol_eqb x' y'))
   | _ => None
   end).
