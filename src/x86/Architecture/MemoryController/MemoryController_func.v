Require Import Coq.Program.Tactics.

Require Import SpecCert.x86.Architecture.MemoryController.Registers.
Require Import SpecCert.x86.Architecture.MemoryController.MemoryController_rec.
Require Import SpecCert.x86.Architecture.MemoryController.MemoryController_prop.
Require Import SpecCert.x86.Architecture.MemoryController.MemoryController_dec.
Require Import SpecCert.Address.

Program Definition open_smram
        (mc: MemoryController)
        (h:  smramc_is_unlocked mc)
  : MemoryController :=
  {| smramc := set_d_open (smramc mc) _ |}.

Program Definition close_smram
        (mc: MemoryController)
        (h:  smramc_is_unlocked mc)
  : MemoryController :=
  {| smramc := unset_d_open (smramc mc) _ |}.

Program Definition lock_smramc
        (mc: MemoryController)
        (h:  smramc_is_unlocked mc)
  : MemoryController :=
  {| smramc := set_d_lock (smramc mc) _ |}.

Definition translate_physical_address
           (mc:     MemoryController)
           (smiact: bool)
           (pa:     PhysicalAddress)
  : HardwareAddress :=
  if is_inside_smram_dec pa then
    if can_access_smram_dec mc smiact then
      dram pa
    else
      vga pa
  else
    dram pa.
