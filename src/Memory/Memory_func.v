Require Import SpecCert.Address.
Require Import SpecCert.Memory.Memory_def.
Require Import SpecCert.Map.

Definition find_in_memory
           {S:   Type}
           (mem: Memory S)
           (ha:  HardwareAddress)
           :S :=
  find_in_map mem ha.

Definition update_in_memory
           {S:      Type}
           (mem:    Memory S)
           (ha:     HardwareAddress)
           (value:  S)
           :Memory S :=
  add_in_map mem ha value.
