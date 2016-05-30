Require Import SpecCert.x86.Architecture.

Definition lock_smramc_pre
           {S :Set} :=
  fun (a:Architecture S) =>
    smramc_is_unlocked (memory_controller a).

Definition lock_smramc_post
           {S :Set} :=
  fun (a a':Architecture S) =>
    exists h, let m' := lock_smramc (memory_controller a) h
    in a' = update_memory_controller a m'.
