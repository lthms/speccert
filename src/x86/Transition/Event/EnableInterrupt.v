Require Import SpecCert.x86.Architecture.
Require Import SpecCert.Address.

Definition enable_interrupt_post
           {Label: Type}
           (a a':Architecture Label) :=
  let p' := enable_interrupt (proc a)
  in a' = update_proc a p'.
