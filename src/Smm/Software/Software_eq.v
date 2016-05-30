Require Import SpecCert.Smm.Software.Software_ind.

Definition software_eq_dec:
  forall s1 s2 :Software,
    {s1 = s2}+{s1 <> s2}.
Proof.
  repeat decide equality.
Qed.