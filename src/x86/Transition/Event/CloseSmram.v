Require Import SpecCert.x86.Architecture.

Definition close_smram_pre
           {S :Set} :=
  fun (a:Architecture S) =>
    smramc_is_unlocked (memory_controller a).

Definition close_smram_post
           {S :Set} :=
  fun (a a':Architecture S) =>
    exists h, let m' := close_smram (memory_controller a) h
    in a' = update_memory_controller a m'.
