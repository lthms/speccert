Require Import SpecCert.Address.
Require Import SpecCert.Formalism.
Require Import SpecCert.LTS.
Require Import SpecCert.Smm.Delta.Behavior.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Delta.Secure.Secure_def.
Require Import SpecCert.Smm.Software.
Require Import SpecCert.x86.

Lemma receive_interrupt_inv_is_secure: forall i:Interrupt,
  inv_is_secure (hardware (ReceiveInterrupt i)).
Proof.
  intro i.
  trivial_inv_is_secure.
Qed.
