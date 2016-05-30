Require Import SpecCert.Smm.Delta.Secure.Secure_def.
Require Import SpecCert.Smm.Delta.Secure.EnableInterrupt.
Require Import SpecCert.Smm.Delta.Secure.DisableInterrupt.
Require Import SpecCert.Smm.Delta.Secure.ReceiveInterrupt.
Require Import SpecCert.Smm.Delta.Secure.Read.
Require Import SpecCert.Smm.Delta.Secure.Write.
Require Import SpecCert.Smm.Delta.Secure.OpenSmram.
Require Import SpecCert.Smm.Delta.Secure.CloseSmram.
Require Import SpecCert.Smm.Delta.Secure.LockSmramc.
Require Import SpecCert.Smm.Delta.Secure.NextInstruction.

Theorem invariant_permits_security: forall ev, inv_is_secure ev.
Proof.
  induction ev as [h|s]; [
  induction h; [ apply exec_inv_is_secure
               | apply receive_interrupt_inv_is_secure ]
  | induction s ;[
       apply disable_interrupt_inv_is_secure
     | apply enable_interrupt_inv_is_secure
     | apply read_inv_is_secure
     | apply write_inv_is_secure
     | apply open_smram_inv_is_secure
     | apply close_smram_inv_is_secure
     | apply lock_smramc_inv_is_secure
     | apply nextinstr_inv_is_secure ]].
Qed.