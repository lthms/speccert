Require Import SpecCert.x86.Architecture.MemoryController.Registers.Smramc_rec.
Require Import SpecCert.x86.Architecture.MemoryController.Registers.Smramc_prop.

Definition set_d_lock (s:SmramcRegister)(pre:smramc_is_rw s):SmramcRegister.
refine (
  {| d_open := false ;
     d_lock := true 
   |}
); intuition.
Defined.

Definition set_d_open (s:SmramcRegister)(pre:smramc_is_rw s):SmramcRegister.
refine (
  {| d_open := true ;
     d_lock := d_lock s 
   |}
); intuition.
unfold smramc_is_rw in pre.
rewrite H in pre.
discriminate pre.
Defined.

Definition unset_d_open (s:SmramcRegister)(pre:smramc_is_rw s):SmramcRegister.
refine (
  {| d_open := false ;
     d_lock := d_lock s 
   |}
); intuition.
Defined.
