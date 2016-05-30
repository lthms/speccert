Require Import SpecCert.x86.Architecture.
Require Import SpecCert.Address.

Definition nextinstr_post
           {S  :Set}
           (pa :PhysicalAddress) :=
  fun (a a':Architecture S) =>
    a' = update_proc a (next_instruction (proc a) pa).