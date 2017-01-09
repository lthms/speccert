Require Import Coq.Bool.Bool.

Require Import SpecCert.x86.Architecture.MemoryController.Registers.Smramc_rec.
Require Import SpecCert.x86.Architecture.MemoryController.Registers.Smramc_prop.
Require Import SpecCert.Utils.

Definition smramc_is_ro_dec
           (s: SmramcRegister)
  : { smramc_is_ro s } + { ~ smramc_is_ro s } :=
  bool_dec (d_lock s) true.

Definition smramc_is_rw_dec
           (s: SmramcRegister)
  : { smramc_is_rw s } + { ~ smramc_is_rw s } :=
  bool_dec (d_lock s) false.
