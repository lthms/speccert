Require Import Coq.Bool.Bool.

Require Import SpecCert.x86.Architecture.MemoryController.Registers.Smramc_rec.
Require Import SpecCert.x86.Architecture.MemoryController.Registers.Smramc_prop.
Require Import SpecCert.Utils.

Definition smramc_is_ro_dec (s:SmramcRegister):{smramc_is_ro s}+{~smramc_is_ro s}.
refine (
  decide_dec (bool_dec (d_lock s) true)
); unfold smramc_is_ro; trivial.
Defined.

Definition smramc_is_rw_dec (s:SmramcRegister):{smramc_is_rw s}+{~smramc_is_rw s}.
refine (
  decide_dec (bool_dec (d_lock s) false)
); unfold smramc_is_rw; trivial.
Defined.
