Require Import Coq.Arith.EqNat.
Require Import Coq.Structures.DecidableType.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Bool.Sumbool.

Require Import SpecCert.Interval.
Require Import SpecCert.Address.AddressSpace.
Require Import SpecCert.Utils.

(**
Definitions
 *)

Inductive Address
          (T: Type)
  : Type :=
| address (t: T)
          (n:nat)
          (h: is_inside_interval n address_space)
  : Address T.

Arguments address [T] (t n h).

Definition address_offset
           {T: Type}
           (a:Address T) :=
  match a with
  | address _ x _ => x
  end.

Definition address_scope
           {T: Type}
           (a: Address T)
  : T :=
  match a with
  | address t _ _ => t
  end.

(**
   Equality
 *)

Definition addr_eq
           {T: Type}
           (a a':Address T) :=
  address_offset a = address_offset a'
  /\ address_scope a = address_scope a'.

Axiom addr_eq_eq: forall {T: Type} (a a':Address T),
    addr_eq a a' -> a = a'.
Axiom eq_addr_eq: forall {T: Type} (a a': Address T),
    a = a' -> addr_eq a a'.

Lemma addr_eq_refl
      {T: Type}
  : forall (a: Address T), addr_eq a a.
Proof.
  intros a.
  unfold addr_eq.
  split; reflexivity.
Qed.

Lemma addr_eq_trans
      {T :Type}
  : forall (a a' a'':Address T),
    addr_eq a a' -> addr_eq a' a'' -> addr_eq a a''.
Proof.
  intros a a' a'' [Ha1 Ha2] [Ha1' Ha2'].
  unfold addr_eq in *.
  rewrite <- Ha1'; rewrite <- Ha2'; rewrite <- Ha1; rewrite <- Ha2.
  split; reflexivity.
Qed.

Lemma addr_eq_sym
      {T: Type}
  : forall (a a':Address T),
    addr_eq a a' -> addr_eq a' a.
Proof.
  unfold addr_eq in *.
  intros a a' [Heq Heq'].
  rewrite Heq; rewrite Heq'.
  split; reflexivity.
Qed.

Definition addr_eq_dec
           {T:    Type}
           (scope_eq_dec: forall (t t' :T), {t = t'}+{t <> t'})
           (a a': Address T)
  : {addr_eq a a'}+{~addr_eq a a'}.
refine (
    decide_dec (sumbool_and _
                            _
                            _
                            _
                            (eq_nat_decide (address_offset a) (address_offset a'))
                            (scope_eq_dec (address_scope a) (address_scope a'))
               )
); unfold addr_eq; intuition.
Defined.

Parameters (T: Type)
           (eqT: forall (t t': T), {t = t'}+{t <> t'}).

Module Type Eq.
  Parameter A: Type.
  Parameter eq_dec: forall (a a': A), {a = a'}+{a <> a'}.
End Eq.

Module AddressDec (scope: Eq) <: DecidableType with Definition t := Address scope.A.
  Definition t := Address scope.A.
  Definition eq := @addr_eq scope.A.
  Definition eq_refl := @addr_eq_refl scope.A.
  Definition eq_sym := @addr_eq_sym scope.A.
  Definition eq_trans := @addr_eq_trans scope.A.
  Definition eq_dec := @addr_eq_dec scope.A scope.eq_dec.
End AddressDec.