Require Import SpecCert.x86.Architecture.

Definition open_smram_pre
           {Label: Type}
           (a:     Architecture Label) :=
  smramc_is_unlocked (memory_controller a).

Definition open_smram_post
           {Label: Type}
           (a a':  Architecture Label) :=
    exists h, let m' := open_smram (memory_controller a) h
    in a' = update_memory_controller a m'.
