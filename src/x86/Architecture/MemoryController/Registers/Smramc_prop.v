Require Import SpecCert.x86.Architecture.MemoryController.Registers.Smramc_rec.

Definition smramc_is_ro (s:SmramcRegister):Prop :=
  (d_lock s) = true.

Definition smramc_is_rw (s:SmramcRegister):Prop :=
  (d_lock s) = false.

