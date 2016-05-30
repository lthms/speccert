Require Import SpecCert.x86.Architecture.
Require Import SpecCert.Address.

Definition receive_interrupt_post
           {S :Set}
           (i :Interrupt) :=
  fun (a a':Architecture S) =>
    let p' := receive_interrupt (proc a) i in
    a' = update_proc a p'.
