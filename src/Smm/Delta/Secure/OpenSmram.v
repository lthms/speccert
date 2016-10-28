Require Import Coq.Sets.Ensembles.

Require Import SpecCert.Address.
Require Import SpecCert.Formalism.
Require Import SpecCert.Smm.Delta.Behavior.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Delta.Secure.Secure_def.
Require Import SpecCert.Smm.Software.
Require Import SpecCert.x86.

Lemma open_smram_inv_is_secure: inv_is_secure (software OpenSmram).
Proof.
  unfold inv_is_secure.
  intros a a' Hinv Hpre Hpost.
  unfold software_step_isolation.
  intros t u Htrusted Huntrusted.
  unfold software_tampering.
  unfold fetched.
  unfold is.
  intros [H H'].
  destruct H'.
Qed.

