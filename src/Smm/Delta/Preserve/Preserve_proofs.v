Require Import SpecCert.Formalism.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Delta.Preserve.CloseSmram.
Require Import SpecCert.Smm.Delta.Preserve.DisableInterrupt.
Require Import SpecCert.Smm.Delta.Preserve.EnableInterrupt.
Require Import SpecCert.Smm.Delta.Preserve.LockSmramc.
Require Import SpecCert.Smm.Delta.Preserve.NextInstruction.
Require Import SpecCert.Smm.Delta.Preserve.OpenSmram.
Require Import SpecCert.Smm.Delta.Preserve.Read.
Require Import SpecCert.Smm.Delta.Preserve.ReceiveInterrupt.
Require Import SpecCert.Smm.Delta.Preserve.Write.
Require Import SpecCert.x86.

Theorem software_transitions_preserve_inv:
  forall ev :SoftwareEvent,
    software_preserve_inv ev.
Proof.
  induction ev; unfold software_preserve_inv; intros a a' Hinv Hsmm Htrans.
  + apply (disable_interrupt_inv a a' Hinv Htrans).
  + apply (enable_interrupt_inv a a' Hinv Htrans).
  + eapply (read_inv _ a a' Hinv Htrans).
  + apply (write_inv _ a a' Hinv Htrans).
  + apply (open_smram_inv a a' Hinv Htrans).
  + apply (close_smram_inv a a' Hinv Htrans).
  + apply (lock_smramc_inv a a' Hinv Htrans).
  + eapply (nextinstr_inv _ a a' Hinv Hsmm Htrans).
Qed.

Theorem hardware_transitions_preserve_inv: forall ev, preserve_inv (hardware ev).
Proof.
  induction ev.
  + apply exec_inv.
  + apply receive_interrupt_inv.
Qed.