Require Import Program.

Require Import SpecCert.Address.
Require Import SpecCert.Smm.Software.
Require Import SpecCert.x86.

Definition nextinstr_behavior
           (pa :PhysicalAddress)
           (h  :Architecture Software) :=
   is_inside_smram pa.

Program Definition smm_behavior
        (h: Architecture Software)
        (e: { e: x86Event | x86_software e })
  : Prop :=
  smm_context h = smm -> match e with
                         | NextInstruction pa => nextinstr_behavior pa h
                         | _ => True
                         end.
