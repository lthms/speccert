Require Import SpecCert.x86.Architecture.

Definition close_smram_pre
           {Label: Type}
           (a:     Architecture Label) :=
  smramc_is_unlocked (memory_controller a).

Definition close_smram_post
           {Label: Type}
           (a a':Architecture Label) :=
  exists h, let m' := close_smram (memory_controller a) h
            in a' = update_memory_controller a m'.