Require Import Coq.Arith.EqNat.
Require Import Coq.Structures.DecidableType.

Require Import SpecCert.Address.Address_ind.
Require Import SpecCert.Utils.

Definition addr_eq (a a':Address) :=
  address_offset a = address_offset a'.

Axiom addr_eq_eq: forall a a':Address,
    addr_eq a a' -> a = a'.


Axiom eq_addr_eq: forall a a':Address,
    a = a' -> addr_eq a a'.

Lemma addr_eq_refl: forall a:Address, addr_eq a a.
Proof.
  intro a.
  unfold addr_eq.
  reflexivity.
Qed.

Lemma addr_eq_trans: forall a a' a'':Address, addr_eq a a' -> addr_eq a' a'' -> addr_eq a a''.
Proof.
  intros a a' a'' Ha Ha'.
  unfold addr_eq in *.
  rewrite <- Ha'; rewrite <- Ha.
  reflexivity.
Qed.

Lemma addr_eq_sym: forall a a':Address, addr_eq a a' -> addr_eq a' a.
Proof.
  unfold addr_eq in *.
  intros a a' Heq.
  rewrite Heq.
  reflexivity.
Qed.

Definition addr_eq_dec (a a':Address): {addr_eq a a'}+{~addr_eq a a'}.
refine (
  decide_dec (eq_nat_decide (address_offset a) (address_offset a'))
); unfold addr_eq; intuition.
Defined.

Module AddressDec <: DecidableType with
      Definition t := Address.
                       Definition t := Address.
                       
                       Definition eq := addr_eq.
                       Definition eq_refl := addr_eq_refl.
                       Definition eq_sym := addr_eq_sym.
                       Definition eq_trans := addr_eq_trans.
                       Definition eq_dec := addr_eq_dec.
End AddressDec.