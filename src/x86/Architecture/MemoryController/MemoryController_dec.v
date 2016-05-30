Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.

Require Import SpecCert.Utils.
Require Import SpecCert.x86.Architecture.MemoryController.MemoryController_rec.
Require Import SpecCert.x86.Architecture.MemoryController.MemoryController_prop.
Require Import SpecCert.x86.Architecture.MemoryController.Registers.

Definition smramc_is_locked_dec
           (mc :MemoryController)
           :{smramc_is_locked mc}+{~smramc_is_locked mc}.
refine (
  decide_dec (smramc_is_ro_dec (smramc mc))
); unfold smramc_is_locked; trivial.
Defined.

Definition smramc_is_unlocked_dec
           (mc :MemoryController)
           :{smramc_is_unlocked mc}+{~smramc_is_unlocked mc}.
refine (
  decide_dec (smramc_is_rw_dec (smramc mc))
); unfold smramc_is_locked; trivial.
Defined.

Definition can_access_smram_dec
           (mc     :MemoryController)
           (smiact :bool)
           :{can_access_smram mc smiact}+{~can_access_smram mc smiact}.
refine (
  decide_dec (sumbool_or _ _ _ _ (bool_dec smiact true)
                                 (bool_dec (d_open (smramc mc)) true))
); firstorder.
Qed.
