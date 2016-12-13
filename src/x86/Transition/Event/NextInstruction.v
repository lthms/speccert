Require Import SpecCert.x86.Architecture.
Require Import SpecCert.Address.

Definition nextinstr_post
           {Label: Type}
           (pa: PhysicalAddress)
           (a a':Architecture Label) :=
  a' = update_proc a (next_instruction (proc a) pa).