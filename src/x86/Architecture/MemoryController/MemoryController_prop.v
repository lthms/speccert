Require Import SpecCert.x86.Architecture.MemoryController.MemoryController_rec.

Definition smramc_is_locked
           (mc :MemoryController) :=
  smramc_is_ro (smramc mc).

Definition smramc_is_unlocked
           (mc :MemoryController) :=
  smramc_is_rw (smramc mc).

Definition can_access_smram
           (mc     :MemoryController)
           (smiact :bool) :=
  smiact = true
  \/ d_open (smramc mc) = true.
