Require Import SpecCert.Address.
Require Import SpecCert.Memory.Memory_def.

Definition find_in_memory
           {S   :Set}
           (mem :Memory S)
           (ha  :HardwareAddress)
           :S :=
  _HardAddrMap.find_in_map mem ha.

Definition update_in_memory
           {S      :Set}
           (mem    :Memory S)
           (ha     :HardwareAddress)
           (owner :S)
           :Memory S :=
  _HardAddrMap.add_in_map mem ha owner.
