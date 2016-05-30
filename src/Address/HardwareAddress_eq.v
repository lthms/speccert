Require Import Coq.Bool.Sumbool.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Structures.DecidableType.

Require Import SpecCert.Address.Address_ind.
Require Import SpecCert.Address.Address_eq.
Require Import SpecCert.Address.Address_proofs.
Require Import SpecCert.Address.HardwareAddress_ind.
Require Import SpecCert.Address.HardwareAddress_prop.
Require Import SpecCert.Address.HardwareAddress_dec.
Require Import SpecCert.Address.HardwareAddress_func.
Require Import SpecCert.Utils.

Definition hardware_addr_eq (a a':HardwareAddress) :=
  is_same_memory a a' /\ addr_eq (hardware_address a) (hardware_address a').

Lemma hardware_addr_eq_refl: forall a:HardwareAddress, hardware_addr_eq a a.
Proof.
  intros a.
  unfold hardware_addr_eq.
  split.
  + unfold is_same_memory.
    induction a; unfold is_dram, is_vga; intuition.
  + apply addr_eq_refl.
Qed.

Lemma hardware_addr_eq_eq: forall a a':HardwareAddress,
  hardware_addr_eq a a' -> a = a'.
Proof.
  intros a a' Haddr.
  unfold hardware_addr_eq in Haddr.
  destruct Haddr as [Hsame Haddr_eq].
  apply addr_eq_eq in Haddr_eq.
  induction a; induction a';
  unfold hardware_address in Haddr_eq;
  rewrite Haddr_eq; try reflexivity; try (
  unfold is_same_memory in Hsame;
  unfold is_dram, is_vga in Hsame;
  intuition).
Qed.

Lemma eq_hardware_addr_eq: forall a a':HardwareAddress,
  a = a' -> hardware_addr_eq a a'.
Proof.
  intros a a' Haddr_eq.
  rewrite Haddr_eq.
  apply hardware_addr_eq_refl.
Qed.

Definition hardware_addr_eq_dec (a a':HardwareAddress)
  :{hardware_addr_eq a a'}+{~hardware_addr_eq a a'}.
refine (
  decide_dec (sumbool_and _ _ _ _ (is_same_memory_dec a a')
                                  (addr_eq_dec (hardware_address a) 
                                               (hardware_address a')))
); unfold hardware_addr_eq; trivial.
apply or_not_and; trivial.
Defined.

Lemma hardware_addr_eq_sym: forall a a':HardwareAddress,
  hardware_addr_eq a a' -> hardware_addr_eq a' a.
Proof.
  intros a a' Haddr.
  apply hardware_addr_eq_eq in Haddr.
  rewrite Haddr.
  apply hardware_addr_eq_refl.
Qed.

Lemma hardware_addr_eq_trans: forall a a' a'':HardwareAddress,
  hardware_addr_eq a a' -> hardware_addr_eq a' a'' -> hardware_addr_eq a a''.
Proof.
  intros a a' a'' Ha Ha'.
  apply hardware_addr_eq_eq in Ha.
  rewrite Ha.
  trivial.
Qed.

Module HardwareAddressDec <: DecidableType with
      Definition t := HardwareAddress.
                       Definition t := HardwareAddress.
                       Definition eq := hardware_addr_eq.
                       Definition eq_trans := hardware_addr_eq_trans.
                       Definition eq_refl := hardware_addr_eq_refl.
                       Definition eq_sym := hardware_addr_eq_sym.
                       Definition eq_dec := hardware_addr_eq_dec.
End HardwareAddressDec.