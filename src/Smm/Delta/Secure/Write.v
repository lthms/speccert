Require Import SpecCert.Address.
Require Import SpecCert.Formalism.
Require Import SpecCert.Smm.Delta.Behavior.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Delta.Secure.Secure_def.
Require Import SpecCert.Smm.Software.
Require Import SpecCert.x86.
Require Import SpecCert.Cache.

Lemma write_inv_is_secure:
  forall (pa :PhysicalAddress) (v: Value),
    inv_is_secure (software (Write pa v)).
Proof.
  intros pa v.
  trivial_inv_is_secure.
Qed.