Require Import SpecCert.LTS.
Require Import SpecCert.Security.
Require Import SpecCert.x86.

Require Import SpecCert.Smm.Software.
Require Import SpecCert.Smm.Delta.Behavior.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Delta.Secure.Secure_def.

Lemma receive_interrupt_inv_is_secure: forall i:Interrupt,
  inv_is_secure (hardware (ReceiveInterrupt i)).
Proof.
  unfold inv_is_secure.
  intros i a a' Hinv Htrans.
  unfold x86Sec, transition.
  simpl.
  unfold trans_cons.
  split; [split | split]; try constructor; try (apply Htrans).
Qed.
