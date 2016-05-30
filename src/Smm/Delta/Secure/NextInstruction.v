Require Import SpecCert.Address.
Require Import SpecCert.Security.
Require Import SpecCert.LTS.
Require Import SpecCert.x86.

Require Import SpecCert.Smm.Software.
Require Import SpecCert.Smm.Delta.Behavior.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Delta.Secure.Secure_def.

Lemma nextinstr_inv_is_secure:
  forall pa :PhysicalAddress,
    inv_is_secure (software (NextInstruction pa)).
Proof.
  unfold inv_is_secure.
  intros pa a a' Hinv Htrans.
  unfold x86Sec, transition.
  simpl.
  unfold trans_cons.
  split; [split | split]; try constructor; try (apply Htrans).
Qed.