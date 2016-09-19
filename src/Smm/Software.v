Require Export SpecCert.Smm.Software.Software_ind.
Require Export SpecCert.Smm.Software.Software_eq.
Require Export SpecCert.Smm.Software.Software_security.

Require Import SpecCert.x86.

Definition smm_context
           (p :Architecture Software)
           :Software :=
  if is_in_smm_dec (proc p)
  then smm
  else unprivileged.