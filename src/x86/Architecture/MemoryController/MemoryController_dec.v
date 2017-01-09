Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.

Require Import SpecCert.Utils.
Require Import SpecCert.x86.Architecture.MemoryController.MemoryController_rec.
Require Import SpecCert.x86.Architecture.MemoryController.MemoryController_prop.
Require Import SpecCert.x86.Architecture.MemoryController.Registers.

Definition smramc_is_locked_dec
           (mc: MemoryController)
  : { smramc_is_locked mc } + { ~ smramc_is_locked mc } :=
  smramc_is_ro_dec (smramc mc).

Definition smramc_is_unlocked_dec
           (mc: MemoryController)
  : { smramc_is_unlocked mc } + { ~ smramc_is_unlocked mc } :=
  smramc_is_rw_dec (smramc mc).

Program Definition can_access_smram_dec
        (mc:     MemoryController)
        (smiact: bool)
  : { can_access_smram mc smiact } + { ~ can_access_smram mc smiact } :=
  (bool_dec smiact true) :|| (bool_dec (d_open (smramc mc)) true).
Next Obligation.
  unfold can_access_smram.
  intros [H'|H'].
  + apply H in H'; exact H'.
  + apply H0 in H'; exact H'.
Qed.
