Require Import SpecCert.x86.Architecture.

Definition lock_smramc_pre
           {Label: Type} :=
  fun (a:Architecture Label) =>
    smramc_is_unlocked (memory_controller a).

Definition lock_smramc_post
           {Label: Type} :=
  fun (a a':Architecture Label) =>
    exists h, let m' := lock_smramc (memory_controller a) h
    in a' = update_memory_controller a m'.
