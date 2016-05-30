Require Import SpecCert.x86.Architecture.
Require Import SpecCert.Address.

Definition enable_interrupt_post
           {S :Set} :=
  fun (a a':Architecture S) =>
    let p' := enable_interrupt (proc a)
    in a' = update_proc a p'.
