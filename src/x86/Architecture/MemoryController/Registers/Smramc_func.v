Require Import Coq.Program.Tactics.

Require Import SpecCert.x86.Architecture.MemoryController.Registers.Smramc_rec.
Require Import SpecCert.x86.Architecture.MemoryController.Registers.Smramc_prop.

Program Definition set_d_lock
        (s:   SmramcRegister)
        (pre: smramc_is_rw s)
  : SmramcRegister :=
  {| d_open := false ;
     d_lock := true
   |}.

Program Definition set_d_open
        (s:   SmramcRegister)
        (pre: smramc_is_rw s)
  : SmramcRegister :=
  {| d_open := true ;
     d_lock := d_lock s
   |}.
Next Obligation.
  unfold smramc_is_rw in pre.
  rewrite pre in H.
  destruct H.
  reflexivity.
Qed.

Program Definition unset_d_open
        (s:   SmramcRegister)
        (pre: smramc_is_rw s)
  : SmramcRegister :=
  {| d_open := false ;
     d_lock := d_lock s
   |}.
