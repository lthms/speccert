Require Import Coq.Sets.Ensembles.

Require Import SpecCert.Address.
Require Import SpecCert.Formalism.
Require Import SpecCert.Smm.Delta.Behavior.
Require Import SpecCert.Smm.Delta.Invariant.
Require Import SpecCert.Smm.Delta.Secure.Secure_def.
Require Import SpecCert.Smm.Software.
Require Import SpecCert.x86.

Lemma close_smram_inv_is_secure:
  inv_is_secure CloseSmram.
Proof.
  trivial_inv_is_secure.
Qed.
