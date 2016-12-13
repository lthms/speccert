Require Import SpecCert.x86.Architecture.
Require Import SpecCert.Address.

Definition disable_interrupt_post
           {Label: Type}
           (a a':Architecture Label) :=
  let p' := disable_interrupt (proc a)
  in a' = update_proc a p'.
