Require Import SpecCert.Address.
Require Import SpecCert.x86.

Require Import SpecCert.Smm.Software.

Definition nextinstr_behavior
           (pa :PhysicalAddress)
           (a  :Architecture Software) :=
   is_inside_smram pa.

Definition smm_behavior
           (a :Architecture Software)
           (e :SoftwareEvent)
           :Prop
  := context (proc a) = smm -> match e with
                              | NextInstruction pa => nextinstr_behavior pa a
                              | _ => True
                              end.