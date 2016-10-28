Require Import Coq.Sets.Ensembles.

Require Import SpecCert.Address.
Require Import SpecCert.Formalism.
Require Import SpecCert.Smm.Delta.Behavior.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Delta.Secure.Secure_def.
Require Import SpecCert.Smm.Software.
Require Import SpecCert.x86.

Lemma nextinstr_inv_is_secure:
  forall pa :PhysicalAddress,
    inv_is_secure (software (NextInstruction pa)).
Proof.
  intro pa.
  trivial_inv_is_secure.
Qed.