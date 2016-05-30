Require Import SpecCert.Address.Address_ind.
Require Import SpecCert.Address.PhysicalAddress_def.
Require Import SpecCert.Address.PhysicalAddress_prop.
Require Import SpecCert.Address.AddressSpace.
Require Import SpecCert.Interval.
Require Import SpecCert.Utils.

Definition is_inside_smram_dec (pa:PhysicalAddress)
  : {is_inside_smram pa}+{~is_inside_smram pa}.
refine (
  decide_dec(is_inside_interval_dec (address_offset pa) smram_space)
); unfold is_inside_smram; trivial.
Defined.
