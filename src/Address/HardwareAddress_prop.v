Require Import SpecCert.Address.HardwareAddress_ind.

Definition is_dram (ha:HardwareAddress) :=
  match ha with
  | dram _ => True
  | _ => False
  end.

Definition is_vga (ha:HardwareAddress) :=
  match ha with
  | vga _ => True
  | _ => False
  end.

Definition is_same_memory (ha ha':HardwareAddress) :=
  (is_dram ha /\ is_dram ha') \/ (is_vga ha /\ is_vga ha').
