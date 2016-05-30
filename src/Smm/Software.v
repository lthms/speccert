Require Export SpecCert.Smm.Software.Software_ind.
Require Export SpecCert.Smm.Software.Software_eq.
Require Export SpecCert.Smm.Software.Software_security.

Require Import SpecCert.x86.

Definition context
           (p :ProcessorUnit)
           :Software :=
  if is_in_smm_dec p
  then smm
  else unprivileged.