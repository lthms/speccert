Require Import SpecCert.x86.Architecture.
Require Import SpecCert.Address.

Definition receive_interrupt_post
           {Label: Type}
           (i:     Interrupt)
           (a a':Architecture Label) :=
  let p' := receive_interrupt (proc a) i in
  a' = update_proc a p'.
