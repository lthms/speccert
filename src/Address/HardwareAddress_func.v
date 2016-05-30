Require Import SpecCert.Address.HardwareAddress_ind.

Definition hardware_address (ha:HardwareAddress) :=
  match ha with
  | dram x => x
  | vga x => x
  end.
