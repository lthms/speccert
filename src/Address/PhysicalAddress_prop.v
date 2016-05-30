Require Import SpecCert.Address.Address_ind.
Require Import SpecCert.Address.PhysicalAddress_def.
Require Import SpecCert.Interval.
Require Import SpecCert.Address.AddressSpace.

Definition is_inside_smram (pa:PhysicalAddress) :=
  is_inside_interval (address_offset pa) smram_space.
