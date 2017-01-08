Require Import Program.

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

Program Theorem software_transitions_preserve_inv
        (ev: { e: x86Event | x86_software e })
  : software_preserve_inv ev.
Proof.
  induction ev as [ev Hev]; induction ev;
    unfold software_preserve_inv;
    intros a a' Hinv Hsmm Htrans;
    simpl in *;
    try destruct Hev. (* deal with hardware events very quickly *)
  + apply (disable_interrupt_inv a a' Hinv Htrans).
  + apply (enable_interrupt_inv a a' Hinv Htrans).
  + apply (read_inv _ _ _ a a' Hinv Htrans).
  + apply (write_inv _ _ a a' Hinv Htrans).
  + apply (open_smram_inv a a' Hinv Htrans).
  + apply (close_smram_inv a a' Hinv Htrans).
  + apply (lock_smramc_inv a a' Hinv Htrans).
  + apply (nextinstr_inv _ a a' Hinv Hsmm Htrans).
Qed.

Program Theorem hardware_transitions_preserve_inv
        (ev : { ev: x86Event | ~ x86_software ev })
  : preserve_inv ev.
Proof.
  (* TODO We have to find a better way to discard software event *)
  assert ((~ True) -> False) as H by (intuition).
  induction ev as [ev Hev];
    induction ev;
    try (simpl in Hev;
         assert (~ True) as H' by (exact Hev);
         apply H in H';
         destruct H'); simpl in *.
  + apply read_inv.
  + apply receive_interrupt_inv.
Qed.